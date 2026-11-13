/// Lowering: Fable AST -> ownership IR. Anything with control flow or effects that sits in an
/// argument position is let-bound first (ANF), keeping F# evaluation order.
module Fable.Transforms.Zig.Lower

open System.Collections.Generic
open Fable
open Fable.AST
open Fable.Transforms
open Fable.Transforms.Zig.IR

type MemberKind =
    /// a function: its type parameters, the types of its arguments, and its result type
    | MFunction of typeParams: string list * argTypes: Fable.Type list * ret: Fable.Type
    | MConst of Ty

/// A lambda, or a function declared inside another one. It is compiled as a function of the
/// file that takes the variables it uses from its surroundings as extra, leading parameters,
/// so calling it by name is a plain call: no environment is allocated, its parameters can be
/// borrowed, and a self tail call is a loop.
type LocalFn =
    {
        FnName: string
        /// the surrounding variables it uses, by their names there
        CaptureNames: string list
        /// the type parameters of the function it is declared in (it has them too), and the
        /// ones of its own (F# lets `let pair x = (x, x)` inside a function be generic)
        OuterTypeParams: string list
        TypeParams: string list
        ArgTypes: Fable.Type list
        Ret: Fable.Type
    }

type Ctx =
    {
        Com: Compiler
        State: FileState
        /// locals in scope (Fable gives every local a name that is unique in its function)
        Vars: Dictionary<string, Var>
        /// the functions and constants this file declares
        Members: Dictionary<string, MemberKind>
        /// the functions declared inside the function being lowered
        LocalFns: Dictionary<string, LocalFn>
        /// the name of the module-level function being lowered, and its type parameters
        FnBase: string
        TypeParams: string list
        /// the names of the file's functions, to give the ones made here names of their own
        Reserved: HashSet<string>
        DecisionTargets: (Fable.Ident list * Fable.Expr) list
        /// inside a `with` handler: the exception it caught (for `reraise ()`)
        CaughtExn: Var option
    }

/// Something that is called by name.
type Callable =
    {
        /// a function of this file, or `alias.name`
        Target: string
        /// the values it takes before its own arguments
        Captures: Expr list
        /// the type arguments it always gets: a function declared inside another one has
        /// that one's type parameters
        OuterTypeArgs: Ty list
        /// its type parameters, the types of its arguments and of its result as declared
        TypeParams: string list
        ArgTypes: Fable.Type list
        Ret: Fable.Type
    }

    member c.Arity = c.ArgTypes.Length

let private exprKind (e: Fable.Expr) =
    match e with
    | Fable.Value _ -> "this kind of value"
    | Fable.Lambda _
    | Fable.Delegate _ -> "function values"
    | Fable.ObjectExpr _ -> "object expressions"
    | Fable.TypeCast _ -> "this type conversion"
    | Fable.Test _ -> "type and pattern tests"
    | Fable.Call _ -> "this kind of call"
    | Fable.CurriedApply _ -> "applying a function value"
    | Fable.Import _ -> "imported values"
    | Fable.Emit _ -> "Emit"
    | Fable.LetRec _ -> "local recursive functions"
    | Fable.Get _ -> "field, index and property access"
    | Fable.Set _ -> "this kind of assignment"
    | Fable.TryCatch _ -> "try/with and try/finally"
    | Fable.Extended _ -> "raise"
    | _ -> "this construct"

/// Does a record or union contain itself, directly or through other records and unions?
/// With `throughUnions = false` the search stops at unions.
let private reachesSelf (com: Compiler) (throughUnions: bool) (start: Fable.Entity) : bool =
    let seen = HashSet<string>()

    let rec typeRefs (t: Fable.Type) : Fable.EntityRef list =
        match t with
        | Fable.DeclaredType(e, gen) -> e :: List.collect typeRefs gen
        | _ -> List.collect typeRefs t.Generics

    let fieldTypes (ent: Fable.Entity) =
        if ent.IsFSharpUnion then
            ent.UnionCases
            |> List.collect (fun c -> c.UnionCaseFields |> List.map (fun f -> f.FieldType))
        else
            ent.FSharpFields |> List.map (fun f -> f.FieldType)

    let rec go (ent: Fable.Entity) =
        fieldTypes ent
        |> List.collect typeRefs
        |> List.exists (fun r ->
            r.FullName = start.FullName
            || (seen.Add r.FullName
                && (
                    match com.TryGetEntity r with
                    | Some e when e.IsFSharpRecord || (e.IsFSharpUnion && throughUnions) -> go e
                    | _ -> false
                ))
        )

    go start

/// Managed = holds references to cells: a recursive union, or anything that holds a managed
/// value. Least fixpoint over every type the file has mentioned so far.
let private settleManaged (state: FileState) =
    let mutable changed = true

    while changed do
        changed <- false

        for e in state.Ents.Values do
            let m =
                e.Kind = KHeapUnion
                || e.Kind = KRefRecord
                || e.Cases |> List.exists (fun (_, fs) -> fs |> List.exists (snd >> isManagedDecl))

            if m <> e.Managed then
                e.Managed <- m
                changed <- true

/// Which types can be part of a reference cycle?
///
/// A cell that is never assigned after it was made can only point at cells that were there
/// before it, so data without assignable fields cannot form a cycle however recursive its
/// type is. A cycle needs an assignable field to close it. So: in the graph of which cell type
/// can point at which, a type can be part of a cycle only if it is in a strongly connected
/// component that contains an assignable field.
///
/// A function value and an exception can hold anything, and their type does not say what. A
/// type that can reach one of them (`ReachesOpaque`) can be part of a cycle if they can, and
/// that depends on the whole program: see `settleCycles` below.
///
/// The answer depends only on the declarations of the types, so every file that mentions a
/// type gets the same one. (For a generic type it is the answer whatever the type arguments
/// are; whether an instance is cyclic because of its arguments is decided when the Zig is
/// compiled: `fable_rt.holdsCyclic`.)
let private settleCyclic (state: FileState) =
    let isCell (e: Ent) =
        e.Kind = KHeapUnion || e.Kind = KRefRecord

    let cells = state.Ents.Values |> Seq.filter isCell |> List.ofSeq

    /// the cell types a value of this type refers to directly (looking through plain values),
    /// each with whether the reference is one that can be assigned later (what an array or a
    /// ref cell holds), and whether the value holds a function value or an exception
    let rec targets (seen: HashSet<Ent>) (t: Ty) : (Ent * bool) list * bool =
        let all (parts: ((Ent * bool) list * bool) list) =
            parts |> List.collect fst, parts |> List.exists snd

        match t with
        | TFn _
        | TPrim "fable_rt.Exn" -> [], true
        | TEnt(e, args) ->
            let own =
                if isCell e then
                    [ e, false ], false
                elif seen.Add e then
                    e.Cases |> List.collect snd |> List.map (snd >> targets seen) |> all
                else
                    [], false

            // (the type arguments of a cell with assignable fields are what those fields hold)
            let assignable = isCell e && not e.MutableFields.IsEmpty

            let inArgs =
                args
                |> List.map (fun arg ->
                    let tgts, any = targets seen arg
                    tgts |> List.map (fun (tgt, a) -> tgt, a || assignable), any
                )

            all (own :: inArgs)
        | TOpt t -> targets seen t
        | TTuple ts -> all (ts |> List.map (targets seen))
        | _ -> [], false

    // (from, to, through an assignable field)
    let edges = List<Ent * Ent * bool>()
    let reachesAny = HashSet<Ent>()

    for e in cells do
        for (_, fields) in e.Cases do
            for (f, t) in fields do
                let tgts, any = targets (HashSet()) t

                if any then
                    reachesAny.Add e |> ignore

                for (tgt, assignable) in tgts do
                    edges.Add((e, tgt, assignable || List.contains f e.MutableFields))

    let succ (e: Ent) =
        edges
        |> Seq.choose (fun (a, b, _) ->
            if obj.ReferenceEquals(a, e) then
                Some b
            else
                None
        )
        |> List.ofSeq

    let reach = Dictionary<Ent, HashSet<Ent>>()

    for e in cells do
        let seen = HashSet<Ent>()

        let rec go (x: Ent) =
            for y in succ x do
                if seen.Add y then
                    go y

        go e
        reach[e] <- seen

    // what points at a type that reaches a function value or an exception reaches one too
    let mutable changed = true

    while changed do
        changed <- false

        for e in cells do
            if not (reachesAny.Contains e) && reach[e] |> Seq.exists reachesAny.Contains then
                reachesAny.Add e |> ignore
                changed <- true

    let sameComponent (a: Ent) (b: Ent) =
        reach.ContainsKey a
        && reach.ContainsKey b
        && reach[a].Contains b
        && reach[b].Contains a

    for e in cells do
        e.ReachesOpaque <- reachesAny.Contains e

        e.Cyclic <-
            reach[e].Contains e
            && edges
               |> Seq.exists (fun (a, b, assignable) -> assignable && sameComponent e a && sameComponent e b)

/// Can a function value or an exception be part of a cycle? Only if some record with an
/// assignable field that can hold one (directly or through other data) is ever made: a cycle
/// needs an assignable field to close it. Whether the program makes such a record is known
/// only for the whole program, so every file says what its own code does, and Zig joins the
/// answers along the imports (`fable_rt.Cycles`):
/// - holds: the file makes a record with an assignable field that can hold a function value
///   or an exception;
/// - generic: it makes one in generic code, with an assignable field whose type depends on a
///   type parameter (what that stands for is not known here);
/// - instantiated: it uses a generic function with a type argument that can hold a function
///   value or an exception (which is what `generic` needs to matter).
/// (When arrays come, a new array of such elements is a record with an assignable field too.)
let private settleCycles (state: FileState) =
    let rec reachesOpaque (t: Ty) : bool =
        match t with
        | TFn _
        | TPrim "fable_rt.Exn" -> true
        | TEnt(e, args) ->
            List.exists reachesOpaque args
            || (if e.Kind = KHeapUnion || e.Kind = KRefRecord then
                    e.ReachesOpaque
                else
                    e.Cases
                    |> List.exists (fun (c, _) -> caseFields t c |> List.exists (snd >> reachesOpaque)))
        | TOpt t -> reachesOpaque t
        | TTuple ts -> List.exists reachesOpaque ts
        | _ -> false

    let mutable holds = false
    let mutable generic = false
    let mutable instantiated = false

    let look (e: Expr) =
        match e with
        | ECon(TEnt({ Kind = KRefRecord } as ent, _) as t, _, _, _) ->
            for (f, fieldTy) in caseFields t "" do
                if List.contains f ent.MutableFields then
                    if reachesOpaque fieldTy then
                        holds <- true

                    if not (freeGens [ fieldTy ]).IsEmpty then
                        generic <- true
        // (a new array is a cell whose items can be assigned)
        | EEmit(_, _, TEnt({ Name = "fable_rt.Array" }, [ item ]))
        | ERt(_, _, TEnt({ Name = "fable_rt.Array" }, [ item ])) ->
            if reachesOpaque item then
                holds <- true

            if not (freeGens [ item ]).IsEmpty then
                generic <- true
        | ECall(_, typeArgs, _, _)
        | EClosure(_, typeArgs, _, _) ->
            if List.exists reachesOpaque typeArgs then
                instantiated <- true
        | _ -> ()

        false

    for fn in state.Fns do
        exists look fn.Body |> ignore

    state.Cycles <- (holds, generic, instantiated)

let private listName = "Microsoft.FSharp.Collections.FSharpList`1"

/// F#'s list: a generic recursive union that the runtime library declares.
let private listEnt (state: FileState) : Ent =
    match state.Ents.TryGetValue listName with
    | true, e -> e
    | _ ->
        let e =
            {
                Name = "fable_rt.List"
                Ref =
                    {
                        FullName = listName
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KHeapUnion
                TypeParams = [ "T" ]
                Cases = []
                MutableFields = []
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
            }

        e.Cases <- [ "Empty", []; "Cons", [ "Head", TGen "T"; "Tail", TEnt(e, [ TGen "T" ]) ] ]
        state.Ents[listName] <- e
        e

let private refName = "Microsoft.FSharp.Core.FSharpRef`1"

/// The .NET exception classes that the runtime library declares: each holds a message.
let private dotnetExceptions =
    [
        "ArgumentException"
        "ArgumentNullException"
        "ArgumentOutOfRangeException"
        "InvalidOperationException"
        "NotSupportedException"
        "NotImplementedException"
        "IndexOutOfRangeException"
        "DivideByZeroException"
        "OverflowException"
        "FormatException"
        "SystemException"
        "ArithmeticException"
        "NullReferenceException"
    ]
    |> List.map (fun name -> "System." + name, "fable_rt." + name)
    |> List.append
        [
            "System.Exception", "fable_rt.Failure"
            "System.Collections.Generic.KeyNotFoundException", "fable_rt.KeyNotFoundException"
            "Microsoft.FSharp.Core.MatchFailureException", "fable_rt.MatchFailureException"
        ]
    |> Map.ofList

/// A .NET exception class that the runtime library declares (`System.Exception` is what
/// `failwith` raises). Its one field is the message.
let private dotnetExnEntIn (state: FileState) (fullName: string) : Ent =
    let key = "$exn:" + fullName

    match state.Ents.TryGetValue key with
    | true, e -> e
    | _ ->
        let e =
            {
                Name = dotnetExceptions[fullName]
                Ref =
                    {
                        FullName = fullName
                        Path = Fable.CoreAssemblyName "System.Runtime"
                    }
                Kind = KExn
                TypeParams = []
                Cases = [ "", [ "Message", tStr ] ]
                MutableFields = []
                Managed = false
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
            }

        state.Ents[key] <- e
        state.UsesRuntime <- true
        e

/// F#'s `ref` cell: a generic reference record that the runtime library declares.
/// F#'s array: a cell of the runtime library whose items can be assigned.
let private arrayEnt (state: FileState) : Ent =
    match state.Ents.TryGetValue "$array" with
    | true, e -> e
    | _ ->
        let e =
            {
                Name = "fable_rt.Array"
                Ref =
                    {
                        FullName = "System.Array"
                        Path = Fable.CoreAssemblyName "System.Runtime"
                    }
                Kind = KRefRecord
                TypeParams = [ "T" ]
                Cases = [ "", [ "items", TGen "T" ] ]
                MutableFields = [ "items" ]
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
            }

        state.Ents["$array"] <- e
        state.UsesRuntime <- true
        e

let private isArrayTy (t: Ty) =
    match t with
    | TEnt({ Name = "fable_rt.Array" }, _) -> true
    | _ -> false

let private refEnt (state: FileState) : Ent =
    match state.Ents.TryGetValue refName with
    | true, e -> e
    | _ ->
        let e =
            {
                Name = "fable_rt.Ref"
                Ref =
                    {
                        FullName = refName
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KRefRecord
                TypeParams = [ "T" ]
                Cases = [ "", [ "contents", TGen "T" ] ]
                MutableFields = [ "contents" ]
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
            }

        state.Ents[refName] <- e
        e

let rec mapType (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : Ty =
    match t with
    | Fable.Unit -> tVoid
    | Fable.Boolean -> tBool
    | Fable.Char -> TPrim "u16"
    | Fable.Number(kind, _) ->
        match kind with
        | Int8 -> TPrim "i8"
        | UInt8 -> TPrim "u8"
        | Int16 -> TPrim "i16"
        | UInt16 -> TPrim "u16"
        | Int32 -> TPrim "i32"
        | UInt32 -> TPrim "u32"
        | Int64 -> TPrim "i64"
        | UInt64 -> TPrim "u64"
        | Int128 -> TPrim "i128"
        | UInt128 -> TPrim "u128"
        | NativeInt -> TPrim "isize"
        | UNativeInt -> TPrim "usize"
        | Float16 -> TPrim "f16"
        | Float32 -> TPrim "f32"
        | Float64 -> TPrim "f64"
        | BigInt -> fail r "the Zig target does not support bigint yet"
        | Decimal -> fail r "the Zig target does not support decimal yet"
    | Fable.String -> tStr
    // (a unit argument stays, as `void`: a function value has one shape whatever its type
    // parameters stand for)
    | Fable.LambdaType(arg, ret) -> TFn([ mapType ctx r arg ], mapType ctx r ret)
    | Fable.DelegateType(args, ret) -> TFn(args |> List.map (mapType ctx r), mapType ctx r ret)
    | Fable.Tuple(ts, _) -> TTuple(ts |> List.map (mapType ctx r))
    | Fable.Option(t, _) -> TOpt(mapType ctx r t)
    | Fable.List t -> TEnt(listEnt ctx.State, [ mapType ctx r t ])
    | Fable.Array(t, _) -> TEnt(arrayEnt ctx.State, [ mapType ctx r t ])
    | Fable.GenericParam(name = name) -> TGen name
    | Fable.DeclaredType(ent, _) when dotnetExceptions.ContainsKey ent.FullName -> tExn
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = refName -> TEnt(refEnt ctx.State, [ mapType ctx r t ])
    | Fable.DeclaredType(ent, _) when (tryExnEnt ctx r ent).IsSome -> tExn
    | Fable.DeclaredType(ent, genArgs) -> TEnt(entOf ctx r ent, genArgs |> List.map (mapType ctx r))
    | _ -> fail r "the Zig target does not support this type yet (%A)" t

/// The record or union behind an entity reference. Immutable, non-recursive records and
/// unions are plain Zig values: a `struct`, or a `union(enum)` with one payload per case.
/// A union that contains itself is a handle: a `union(enum)` whose cases with fields point to
/// reference-counted cells. (A record that reaches itself only through such unions is still a
/// plain value.)
and entOf (ctx: Ctx) (r: SourceLocation option) (entRef: Fable.EntityRef) : Ent =
    match ctx.State.Ents.TryGetValue entRef.FullName with
    | true, e -> e
    | _ ->
        let ent =
            match ctx.Com.TryGetEntity entRef with
            | Some e -> e
            | None -> fail r "the Zig target cannot find the type %s" entRef.FullName

        if not (ent.IsFSharpRecord || ent.IsFSharpUnion) then
            fail r "the Zig target does not support the type %s yet" entRef.FullName

        let recursive = reachesSelf ctx.Com true ent

        // A record that can be assigned to (and is not a struct), or that contains itself, is a
        // reference: a pointer to a counted cell.
        let isReference =
            ent.IsFSharpRecord
            && ((recursive && reachesSelf ctx.Com false ent)
                || (not ent.IsValueType && ent.FSharpFields |> List.exists (fun f -> f.IsMutable)))

        // a name in this file, or `alias.name` for a type another file declares
        let name, isLocal =
            match FSharp2Fable.Util.entityIdent ctx.Com entRef with
            | Fable.IdentExpr id -> id.Name, true
            | Fable.Import(imp, _, _) -> importAlias ctx imp.Path + "." + imp.Selector, false
            | _ -> fail r "the Zig target cannot reference the type %s" entRef.FullName

        let e =
            {
                Name = name
                Ref = entRef
                Kind =
                    if isReference then
                        KRefRecord
                    elif not ent.IsFSharpUnion then
                        KRecord
                    elif recursive then
                        KHeapUnion
                    else
                        KValueUnion
                TypeParams = ent.GenericParameters |> List.map (fun g -> g.Name)
                Cases = []
                MutableFields =
                    if ent.IsFSharpRecord then
                        ent.FSharpFields
                        |> List.filter (fun f -> f.IsMutable)
                        |> List.map (fun f -> f.Name)
                    else
                        []
                Managed = false
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = isLocal
            }

        ctx.State.Ents[entRef.FullName] <- e
        ctx.State.EntDepth <- ctx.State.EntDepth + 1

        try
            e.Cases <-
                if ent.IsFSharpUnion then
                    ent.UnionCases
                    |> List.map (fun c ->
                        c.Name, c.UnionCaseFields |> List.map (fun f -> f.Name, mapType ctx r f.FieldType)
                    )
                else
                    [
                        "", ent.FSharpFields |> List.map (fun f -> f.Name, mapType ctx r f.FieldType)
                    ]
        with _ ->
            ctx.State.EntDepth <- ctx.State.EntDepth - 1
            ctx.State.Ents.Remove entRef.FullName |> ignore
            reraise ()

        ctx.State.EntDepth <- ctx.State.EntDepth - 1

        if isLocal then
            ctx.State.LocalEnts.Add e

        // (the types this one refers to are all known once the outermost one is finished)
        if ctx.State.EntDepth = 0 then
            settleManaged ctx.State

        e

/// The F# `exception` declaration behind an entity reference, if it is one. Its values have
/// the type `exn`; the declaration says what fields they have.
and tryExnEnt (ctx: Ctx) (r: SourceLocation option) (entRef: Fable.EntityRef) : Ent option =
    match ctx.State.Ents.TryGetValue entRef.FullName with
    | true, e when e.Kind = KExn -> Some e
    | true, _ -> None
    | _ when
        entRef.FullName <> "System.Exception"
        && dotnetExceptions.ContainsKey entRef.FullName
        ->
        Some(dotnetExnEntIn ctx.State entRef.FullName)
    | _ ->
        match ctx.Com.TryGetEntity entRef with
        | Some ent when ent.IsFSharpExceptionDeclaration ->
            let name, isLocal =
                match FSharp2Fable.Util.entityIdent ctx.Com entRef with
                | Fable.IdentExpr id -> id.Name, true
                | Fable.Import(imp, _, _) -> importAlias ctx imp.Path + "." + imp.Selector, false
                | _ -> fail r "the Zig target cannot reference the exception %s" entRef.FullName

            let e =
                {
                    Name = name
                    Ref = entRef
                    Kind = KExn
                    TypeParams = []
                    Cases = []
                    MutableFields = []
                    Managed = false
                    Cyclic = false
                    ReachesOpaque = false
                    Copyable = true
                    IsLocal = isLocal
                }

            ctx.State.Ents[entRef.FullName] <- e

            try
                e.Cases <-
                    [
                        "", ent.FSharpFields |> List.map (fun f -> f.Name, mapType ctx r f.FieldType)
                    ]
            with _ ->
                ctx.State.Ents.Remove entRef.FullName |> ignore
                reraise ()

            if isLocal then
                ctx.State.LocalEnts.Add e

            Some e
        | _ -> None

and importAlias (ctx: Ctx) (path: string) =
    match ctx.State.Imports.TryGetValue path with
    | true, alias -> alias
    | _ ->
        let fileName = System.IO.Path.GetFileNameWithoutExtension(path)

        let baseName =
            "m_"
            + System.Text.RegularExpressions.Regex.Replace(fileName.Replace(".fs", ""), "[^A-Za-z0-9_]", "_")

        let mutable alias = baseName
        let mutable i = 1

        while ctx.State.Imports.ContainsValue alias do
            alias <- $"%s{baseName}_%d{i}"
            i <- i + 1

        ctx.State.Imports[path] <- alias
        alias

let private isUnit (t: Fable.Type) =
    match t with
    | Fable.Unit -> true
    | _ -> false

let private floatLit (ty: string) (x: float) =
    if System.Double.IsNaN x then
        $"std.math.nan(%s{ty})"
    elif System.Double.IsPositiveInfinity x then
        $"std.math.inf(%s{ty})"
    elif System.Double.IsNegativeInfinity x then
        $"(-std.math.inf(%s{ty}))"
    else
        let s = x.ToString("R", System.Globalization.CultureInfo.InvariantCulture)

        if s.Contains "." || s.Contains "E" || s.Contains "e" then
            s
        else
            s + ".0"

let private numberLit (r: SourceLocation option) (v: Fable.NumberValue) : string * Ty =
    match v with
    | Fable.NumberValue.Int8 x -> string<sbyte> x, TPrim "i8"
    | Fable.NumberValue.UInt8 x -> string<byte> x, TPrim "u8"
    | Fable.NumberValue.Int16 x -> string<int16> x, TPrim "i16"
    | Fable.NumberValue.UInt16 x -> string<uint16> x, TPrim "u16"
    | Fable.NumberValue.Int32 x -> string<int> x, tI32
    | Fable.NumberValue.UInt32 x -> string<uint32> x, TPrim "u32"
    | Fable.NumberValue.Int64 x -> string<int64> x, TPrim "i64"
    | Fable.NumberValue.UInt64 x -> string<uint64> x, TPrim "u64"
    | Fable.NumberValue.NativeInt x -> string<int64>(int64 x), TPrim "isize"
    | Fable.NumberValue.UNativeInt x -> string<uint64>(uint64 x), TPrim "usize"
    | Fable.NumberValue.Float32 x -> floatLit "f32" (float x), TPrim "f32"
    | Fable.NumberValue.Float64 x -> floatLit "f64" x, TPrim "f64"
    | _ -> fail r "the Zig target does not support this kind of number yet"

/// ANF for argument lists: an argument that is not a flat expression or that produces a managed
/// value is let-bound, and so is any impure argument evaluated before it.
let bindArgsIn (conArgs: bool) (ctx: Ctx) (irs: Expr list) (k: Expr list -> Expr) : Expr =
    let needsBind ir =
        not (isFlat ir)
        || (isManaged (typeOf ir)
            && (
                match ir with
                | ECall _
                | ECallClo _
                | EClosure _
                | ERt _
                | EEmit _ -> true
                // (a constructor argument is an owning position)
                | ECon(TEnt({ Kind = KRefRecord }, _), _, _, _) -> not conArgs
                | ECon(_, _, xs, _) -> not conArgs && not xs.IsEmpty
                | EExnNew _ -> not conArgs
                // (what a field that can be assigned holds is read where the program reads it)
                | EGet _ -> touchesMutable ir
                | _ -> false
            ))

    let arr = List.toArray irs

    match arr |> Array.tryFindIndexBack needsBind with
    | None -> k irs
    | Some last ->
        let binds = List<Var * Expr>()

        let rec hoist (ir: Expr) =
            match ir with
            | ELet(v, r, b) ->
                binds.Add((v, r))
                hoist b
            | _ -> ir

        let outs =
            arr
            |> Array.mapi (fun i ir ->
                if i <= last && (needsBind ir || not (isPure ir)) && not (isVoid (typeOf ir)) then
                    let ir = hoist ir

                    // (what is left after hoisting may need no name: a variable, a literal)
                    if isFlat ir && isPure ir && not (needsBind ir) then
                        ir
                    else
                        let v = ctx.State.NewVar(tempName ir, typeOf ir, VLocal, false)
                        binds.Add((v, ir))
                        EVar v
                else
                    ir
            )

        List.foldBack (fun (v, ir) acc -> ELet(v, ir, acc)) (List.ofSeq binds) (k (List.ofArray outs))

let bindArgs (ctx: Ctx) (irs: Expr list) (k: Expr list -> Expr) : Expr = bindArgsIn false ctx irs k

/// The surrounding variables that `bodies` use, in the order they are first used. A use of a
/// function declared in the surroundings counts as a use of what that function captures.
let private freeNames (ctx: Ctx) (bodies: (Fable.Ident list * Fable.Expr) list) : string list =
    let found = List<string>()
    let seen = HashSet<string>()

    let add (bound: Set<string>) (name: string) =
        if not (bound.Contains name) && ctx.Vars.ContainsKey name && seen.Add name then
            found.Add name

    let names (ids: Fable.Ident list) =
        ids |> List.map (fun i -> i.Name) |> Set.ofList

    let rec walk (bound: Set<string>) (e: Fable.Expr) =
        match e with
        | Fable.IdentExpr id ->
            if bound.Contains id.Name || ctx.Vars.ContainsKey id.Name then
                add bound id.Name
            else
                match ctx.LocalFns.TryGetValue id.Name with
                | true, fn -> fn.CaptureNames |> List.iter (add bound)
                | _ -> ()
        | Fable.Lambda(arg, body, _) -> walk (bound.Add arg.Name) body
        | Fable.Delegate(args, body, _, _) -> walk (Set.union bound (names args)) body
        | Fable.Let(id, value, body) ->
            walk bound value
            walk (bound.Add id.Name) body
        | Fable.LetRec(bindings, body) ->
            let bound = Set.union bound (names (bindings |> List.map fst))
            bindings |> List.iter (snd >> walk bound)
            walk bound body
        | Fable.ForLoop(id, start, limit, body, _, _) ->
            walk bound start
            walk bound limit
            walk (bound.Add id.Name) body
        | Fable.DecisionTree(expr, targets) ->
            walk bound expr

            for (ids, target) in targets do
                walk (Set.union bound (names ids)) target
        | Fable.TryCatch(body, catch, finalizer, _) ->
            walk bound body
            catch |> Option.iter (fun (id, handler) -> walk (bound.Add id.Name) handler)
            finalizer |> Option.iter (walk bound)
        | _ -> AST.getSubExpressions e |> List.iter (walk bound)

    for (args, body) in bodies do
        walk (names args) body

    List.ofSeq found

let private uniqueName (ctx: Ctx) (wanted: string) =
    let mutable name = wanted
    let mutable i = 1

    while not (ctx.Reserved.Add name) do
        name <- $"%s{wanted}_%d{i}"
        i <- i + 1

    name

let private captureExprs (ctx: Ctx) (r: SourceLocation option) (names: string list) : Expr list =
    names
    |> List.map (fun n ->
        match ctx.Vars.TryGetValue n with
        | true, v -> EVar v
        | _ -> fail r "internal: the captured variable `%s` is not in scope" n
    )

/// What `e` is, if it names a function: one declared inside the function being lowered, one of
/// this file, or one of another file.
let private tryCallable (ctx: Ctx) (e: Fable.Expr) : Callable option =
    match e with
    | Fable.IdentExpr id when not (ctx.Vars.ContainsKey id.Name) ->
        match ctx.LocalFns.TryGetValue id.Name with
        | true, fn ->
            Some
                {
                    Target = fn.FnName
                    Captures = captureExprs ctx id.Range fn.CaptureNames
                    OuterTypeArgs = fn.OuterTypeParams |> List.map TGen
                    TypeParams = fn.TypeParams
                    ArgTypes = fn.ArgTypes
                    Ret = fn.Ret
                }
        | _ ->
            match ctx.Members.TryGetValue id.Name with
            | true, MFunction(typeParams, argTypes, ret) ->
                Some
                    {
                        Target = id.Name
                        Captures = []
                        OuterTypeArgs = []
                        TypeParams = typeParams
                        ArgTypes = argTypes
                        Ret = ret
                    }
            | _ -> None
    | Fable.Import(imp, _, _) ->
        match imp.Kind with
        | Fable.MemberImport memberRef ->
            match ctx.Com.TryGetMember memberRef with
            | Some m when not m.IsValue ->
                let argTypes =
                    match m.CurriedParameterGroups |> List.concat |> List.map (fun p -> p.Type) with
                    | [] -> [ Fable.Unit ]
                    | ts -> ts

                Some
                    {
                        Target = importAlias ctx imp.Path + "." + imp.Selector
                        Captures = []
                        OuterTypeArgs = []
                        TypeParams =
                            // (those of the type it is a member of, then its own)
                            (match m.DeclaringEntity |> Option.bind ctx.Com.TryGetEntity with
                             | Some ent when not ent.IsFSharpModule ->
                                 ent.GenericParameters |> List.map (fun g -> g.Name)
                             | _ -> [])
                            @ (m.GenericParameters |> List.map (fun g -> g.Name))
                            |> List.distinct
                        ArgTypes = argTypes
                        Ret = m.ReturnParameter.Type
                    }
            | _ -> None
        | _ -> None
    | _ -> None

/// What the type parameters of `pattern` stand for, if `actual` is an instance of it.
let rec private unify (found: Dictionary<string, Fable.Type>) (pattern: Fable.Type) (actual: Fable.Type) : unit =
    let all (ps: Fable.Type list) (xs: Fable.Type list) =
        if ps.Length = xs.Length then
            List.iter2 (unify found) ps xs

    /// a function type as the list of its arguments and its last result
    let rec uncurried (t: Fable.Type) : Fable.Type list * Fable.Type =
        match t with
        | Fable.LambdaType(a, ret) ->
            let rest, last = uncurried ret
            a :: rest, last
        | Fable.DelegateType(args, ret) ->
            let rest, last = uncurried ret
            args @ rest, last
        | _ -> [], t

    match pattern, actual with
    | Fable.GenericParam(name = name), _ ->
        if not (found.ContainsKey name) then
            found[name] <- actual
    | Fable.LambdaType(a1, r1), Fable.LambdaType(a2, r2) ->
        unify found a1 a2
        unify found r1 r2
    | (Fable.LambdaType _ | Fable.DelegateType _), (Fable.LambdaType _ | Fable.DelegateType _) ->
        // (one of them is written with its arguments in one step, the other is not)
        let args1, ret1 = uncurried pattern
        let args2, ret2 = uncurried actual

        if args1.Length = args2.Length then
            all args1 args2
            unify found ret1 ret2
    | Fable.Tuple(ts1, _), Fable.Tuple(ts2, _) -> all ts1 ts2
    | Fable.Option(t1, _), Fable.Option(t2, _) -> unify found t1 t2
    | Fable.DeclaredType(_, g1), Fable.DeclaredType(_, g2) -> all g1 g2
    | _ -> all pattern.Generics actual.Generics

/// The text of a Zig string literal (UTF-8) for F# text (UTF-16), or None when the text is
/// not well-formed (a surrogate on its own). `$` is written as an escape: the text may become
/// part of an `Emit` macro, where `$0` stands for an argument.
let private zigQuoted (text: string) : string option =
    let sb = System.Text.StringBuilder("\"")
    let mutable ok = true
    let mutable i = 0

    while ok && i < text.Length do
        let c = text[i]

        if
            System.Char.IsHighSurrogate c
            && i + 1 < text.Length
            && System.Char.IsLowSurrogate text[i + 1]
        then
            sb.Append($"\\u{{%X{System.Char.ConvertToUtf32(c, text[i + 1])}}}") |> ignore
            i <- i + 1
        elif System.Char.IsSurrogate c then
            ok <- false
        else
            match c with
            | '"' -> sb.Append("\\\"") |> ignore
            | '\\' -> sb.Append("\\\\") |> ignore
            | '\n' -> sb.Append("\\n") |> ignore
            | '\r' -> sb.Append("\\r") |> ignore
            | '\t' -> sb.Append("\\t") |> ignore
            | '$' -> sb.Append("\\x24") |> ignore
            | c when c < ' ' || c = '\127' -> sb.Append($"\\x%02x{int c}") |> ignore
            | c when c < '\128' -> sb.Append(c) |> ignore
            | c -> sb.Append($"\\u{{%X{int c}}}") |> ignore

        i <- i + 1

    if ok then
        Some(sb.Append('"').ToString())
    else
        None

/// A string literal: static data of the generated program.
let private stringLiteral (text: string) : string =
    match zigQuoted text with
    | Some quoted -> $"fable_rt.str(%s{quoted})"
    | None ->
        let units = text |> Seq.map (fun c -> string<int>(int c)) |> String.concat ", "
        $"fable_rt.strOf(&[_]u16{{ %s{units} }})"

/// One part of an F# format string: literal text, or a specifier that takes a value.
type private FormatPart =
    | Text of string
    /// flags, width, precision, the letter, and the .NET format of a hole (`{x:N2}`)
    | Spec of string * int * int option * char * string

/// "%5d items%%" -> [ Spec("", 5, None, 'd'); Text " items%" ]. In an interpolated string every
/// hole is `%P()`, after a specifier of its own if it has one (`%d%P()`).
let private parseFormat (r: SourceLocation option) (fmt: string) : FormatPart list =
    let parts = List<FormatPart>()
    let text = System.Text.StringBuilder()

    let flush () =
        if text.Length > 0 then
            parts.Add(Text(text.ToString()))
            text.Clear() |> ignore

    let mutable i = 0
    // the last part is a specifier that has not got its hole yet
    let mutable pending = false

    while i < fmt.Length do
        if fmt[i] <> '%' then
            text.Append(fmt[i]) |> ignore
            pending <- false
            i <- i + 1
        elif i + 1 < fmt.Length && fmt[i + 1] = '%' then
            text.Append('%') |> ignore
            pending <- false
            i <- i + 2
        else
            i <- i + 1
            let start = i

            while i < fmt.Length && "0-+ ".IndexOf(fmt[i]) >= 0 do
                i <- i + 1

            let flags = fmt.Substring(start, i - start)
            let widthStart = i

            while i < fmt.Length && System.Char.IsDigit fmt[i] do
                i <- i + 1

            let width =
                if i > widthStart then
                    int (fmt.Substring(widthStart, i - widthStart))
                else
                    0

            let precision =
                if i < fmt.Length && fmt[i] = '.' then
                    i <- i + 1
                    let precisionStart = i

                    while i < fmt.Length && System.Char.IsDigit fmt[i] do
                        i <- i + 1

                    Some(int (fmt.Substring(precisionStart, i - precisionStart)))
                else
                    None

            if i >= fmt.Length then
                fail r "the format string ends in the middle of a specifier"

            let letter = fmt[i]
            i <- i + 1

            if letter = 'P' then
                // (the hole of an interpolated string: `%P()`, or `%P(format)` with a .NET format)
                let net =
                    if i < fmt.Length && fmt[i] = '(' then
                        let close = fmt.IndexOf(')', i)
                        let text = fmt.Substring(i + 1, close - i - 1)
                        i <- close + 1
                        text
                    else
                        ""

                // a specifier right before the hole is the hole's (`%d{x}`)
                if pending then
                    pending <- false
                else
                    flush ()
                    parts.Add(Spec(flags, width, precision, 'P', net))
            else
                flush ()
                parts.Add(Spec(flags, width, precision, letter, ""))
                pending <- true

    flush ()
    List.ofSeq parts

/// `printfn "..."` and its relatives, and an interpolated string: which of them, the format
/// string, and the values of the holes of an interpolated string.
let private (|PrintfCall|_|) (e: Fable.Expr) : (string * string * Fable.Expr list) option =
    let rec uncast (x: Fable.Expr) =
        match x with
        | Fable.TypeCast(inner, _) -> uncast inner
        | _ -> x

    let isDotnet (imp: Fable.ImportInfo) (entityPrefix: string) =
        imp.Path.StartsWith(Replacements.DotnetPrefix + entityPrefix, System.StringComparison.Ordinal)

    match e with
    | Fable.Call(Fable.Import(imp, _, _), info, _, _) when
        isDotnet imp "Microsoft.FSharp.Core.ExtraTopLevelOperators"
        && imp.Selector.StartsWith("PrintFormat", System.StringComparison.Ordinal)
        ->
        match info.Args |> List.map uncast with
        | [ Fable.Call(Fable.Import(ctor, _, _), ctorInfo, _, _) ] when
            ctor.Selector = ".ctor" && isDotnet ctor "Microsoft.FSharp.Core.PrintfFormat"
            ->
            match ctorInfo.Args with
            | Fable.Value(Fable.StringConstant fmt, _) :: rest ->
                let holes =
                    match rest with
                    | Fable.Value(Fable.NewArray(Fable.ArrayValues values, _, _), _) :: _ ->
                        values
                        |> List.map (fun v ->
                            match uncast v with
                            | Fable.Call(Fable.Import(box, _, _), boxInfo, _, _) when box.Selector = "Box" ->
                                boxInfo.Args.Head
                            | other -> other
                        )
                    | _ -> []

                Some(imp.Selector, fmt, holes)
            | _ -> None
        | _ -> None
    | _ -> None

/// (for the names of the values of a printf that is used as a function)
let mutable private printfValues = 0

/// A printf that has not been given all the values its format takes: the printf, and the
/// values it has.
let private (|PrintfPartial|_|) (e: Fable.Expr) : (Fable.Expr * Fable.Expr list) option =
    let holes (fmt: string) =
        parseFormat None fmt
        |> List.filter (
            function
            | Spec _ -> true
            | Text _ -> false
        )
        |> List.length

    match e with
    | PrintfCall(_, fmt, []) when holes fmt > 0 -> Some(e, [])
    | Fable.CurriedApply(PrintfCall(_, fmt, []) as call, given, _, _) when given.Length < holes fmt -> Some(call, given)
    | _ -> None

/// The expression under the casts that F# puts where a list is given for a sequence.
let rec private (|Uncast|) (e: Fable.Expr) : Fable.Expr =
    match e with
    | Fable.TypeCast(Uncast inner, _) -> inner
    | _ -> e

/// A string that is certainly not null: its length needs no test.
let rec private neverNull (e: Fable.Expr) : bool =
    match e with
    | Fable.Value(Fable.StringConstant _, _) -> true
    | Fable.TypeCast(x, _) -> neverNull x
    | PrintfCall("PrintFormatToString", _, _)
    | Fable.CurriedApply(PrintfCall("PrintFormatToString", _, _), _, _, _) -> true
    | Fable.Call(Fable.Import(imp, _, _), _, Fable.String, _) ->
        imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.StringModule"
        || (imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
            && (imp.Selector = "op_Addition" || imp.Selector = "ToString"))
    | _ -> false

let rec lw (ctx: Ctx) (e: Fable.Expr) : Expr =
    match e with
    | Fable.Value(kind, r) ->
        match kind with
        | Fable.UnitConstant -> EUnit
        | Fable.BoolConstant b ->
            ELit(
                (if b then
                     "true"
                 else
                     "false"),
                tBool
            )
        | Fable.NumberConstant(v, _) -> ELit(numberLit r v)
        | Fable.CharConstant c -> ELit(string<int>(int c), TPrim "u16")
        | Fable.StringConstant text -> ELit(stringLiteral text, tStr)
        // (what a match without a case raises, when F# writes it out: its file, line and column
        // are not kept, its message is)
        | Fable.NewRecord(_, entRef, _) when entRef.FullName = "Microsoft.FSharp.Core.MatchFailureException" ->
            let message = ELit(stringLiteral "The match cases were incomplete", tStr)
            EExnNew(dotnetExnEnt ctx entRef.FullName, [ message ])
        | Fable.NewRecord(values, entRef, _) when (tryExnEnt ctx r entRef).IsSome ->
            let ent = (tryExnEnt ctx r entRef).Value
            bindArgsIn true ctx (values |> List.map (lw ctx)) (fun xs -> EExnNew(ent, xs))
        | Fable.NewRecord(values, entRef, genArgs) ->
            let ty = TEnt(entOf ctx r entRef, genArgs |> List.map (mapType ctx r))
            bindArgsIn true ctx (values |> List.map (lw ctx)) (fun xs -> ECon(ty, "", xs, None))
        | Fable.NewUnion(values, tag, entRef, genArgs) ->
            let ent = entOf ctx r entRef
            let ty = TEnt(ent, genArgs |> List.map (mapType ctx r))
            let case = fst (List.item tag ent.Cases)
            bindArgsIn true ctx (values |> List.map (lw ctx)) (fun xs -> ECon(ty, case, xs, None))
        | Fable.NewTuple(values, _) ->
            bindArgsIn
                true
                ctx
                (values |> List.map (lw ctx))
                (fun xs -> ECon(TTuple(xs |> List.map typeOf), "", xs, None))
        // `[| a; b |]`, and an array of a given length
        | Fable.NewArray(Fable.ArrayValues values, t, _) ->
            let ty = TEnt(arrayEnt ctx.State, [ mapType ctx r t ])
            let holes = values |> List.mapi (fun i _ -> $"$%d{i}") |> String.concat ", "

            bindArgs
                ctx
                (values |> List.map (lw ctx))
                (fun xs -> EEmit($"fable_rt.arrayOf($R, .{{ %s{holes} }})", xs, ty))
        | Fable.NewArray(Fable.ArrayAlloc size, t, _) ->
            let ty = TEnt(arrayEnt ctx.State, [ mapType ctx r t ])
            bindArgs ctx [ lw ctx size ] (fun xs -> ERt("fable_rt.arrayZero($R, $0)", xs, ty))
        | Fable.NewArray(Fable.ArrayFrom(Uncast source), t, _) when source.Type = Fable.List t ->
            let ty = TEnt(arrayEnt ctx.State, [ mapType ctx r t ])
            bindArgs ctx [ lw ctx source ] (fun xs -> EEmit("fable_rt.arrayOfList($R, $0)", xs, ty))
        | Fable.NewList(headAndTail, t) ->
            let ty = TEnt(listEnt ctx.State, [ mapType ctx r t ])

            match headAndTail with
            | Some(head, tail) ->
                bindArgsIn true ctx [ lw ctx head; lw ctx tail ] (fun xs -> ECon(ty, "Cons", xs, None))
            | None -> ECon(ty, "Empty", [], None)
        | Fable.NewOption(value, t, _) ->
            let ty = TOpt(mapType ctx r t)

            match value with
            | Some v -> bindArgsIn true ctx [ lw ctx v ] (fun xs -> ECon(ty, "Some", xs, None))
            | None -> ECon(ty, "None", [], None)
        | _ -> fail r "the Zig target does not support %s yet" (exprKind e)

    // (unit has one value: a variable of that type is never read)
    | Fable.IdentExpr id when isUnit id.Type -> EUnit

    | Fable.IdentExpr id ->
        match ctx.Vars.TryGetValue id.Name with
        | true, v -> EVar v
        | _ ->
            match ctx.Members.TryGetValue id.Name with
            | true, MConst ty ->
                EVar
                    {
                        Id = 0
                        Base = id.Name
                        Ty = ty
                        Kind = VGlobal
                        FMutable = false
                    }
            | _ ->
                match tryCallable ctx e with
                | Some c -> fnValue ctx id.Range e c id.Type
                | None -> fail id.Range "the Zig target cannot resolve `%s` yet" id.Name

    // a function of another file, as a value
    | Fable.Import(_, t, r) when (tryCallable ctx e).IsSome -> fnValue ctx r e (tryCallable ctx e).Value t

    // A function declared inside this one becomes a function of the file (see `LocalFn`).
    | Fable.Let(id, (Fable.Lambda _ | Fable.Delegate _ as fnExpr), body) when not id.IsMutable ->
        liftGroup ctx id.Range [ Some id.Name, id.Name, fnExpr ] |> ignore
        lw ctx body

    | Fable.LetRec(bindings, body) ->
        for (id, value) in bindings do
            match value with
            | Fable.Lambda _
            | Fable.Delegate _ -> ()
            | _ -> fail id.Range "the Zig target does not support recursive values yet (`%s`)" id.Name

        liftGroup ctx e.Range (bindings |> List.map (fun (id, value) -> Some id.Name, id.Name, value))
        |> ignore

        lw ctx body

    | Fable.Lambda _
    | Fable.Delegate _ ->
        let fn = liftGroup ctx e.Range [ None, "lambda", e ] |> List.head

        EClosure(
            fn.FnName,
            ctx.TypeParams |> List.map TGen,
            captureExprs ctx e.Range fn.CaptureNames,
            mapType ctx e.Range e.Type
        )

    // a match that no case covers
    | Fable.Extended(Fable.Throw(Some(Fable.Value(Fable.StringConstant text, _)), t), r) when
        text.StartsWith("Match failure", System.StringComparison.Ordinal)
        ->
        let message = ELit(stringLiteral "The match cases were incomplete", tStr)

        let failure =
            EExnNew(dotnetExnEnt ctx "Microsoft.FSharp.Core.MatchFailureException", [ message ])

        // (Fable gives the raise no type: where it stands, nothing is expected of it)
        ERaise(
            failure,
            match t with
            | Fable.Any -> tVoid
            | _ -> mapType ctx r t
        )

    // a function with several arguments that is used one argument at a time
    | Fable.Extended(Fable.Curry(f, arity), _) -> lw ctx (Replacements.Api.curryExprAtRuntime ctx.Com arity f)

    | Fable.Let(id, value, body) ->
        let rhs = lw ctx value
        let ty = mapType ctx id.Range id.Type

        if isVoid ty then
            ESeq(asStmt ctx rhs, lw ctx body)
        else
            match rhs with
            // an immutable name for an immutable variable is that variable
            | EVar x when not id.IsMutable && not x.FMutable && x.Kind <> VGlobal ->
                ctx.Vars[id.Name] <- x
                lw ctx body
            | _ ->
                let v = ctx.State.NewVar(id.Name, ty, VLocal, id.IsMutable)
                ctx.Vars[id.Name] <- v
                ELet(v, rhs, lw ctx body)

    | Fable.Sequential es ->
        match List.rev es with
        | [] -> EUnit
        | last :: restRev ->
            let lastIr = lw ctx last
            restRev |> List.fold (fun acc s -> ESeq(lwStmt ctx s, acc)) lastIr

    | Fable.IfThenElse(guard, thenExpr, elseExpr, r) ->
        let ty = mapType ctx r e.Type
        bindArgs ctx [ lw ctx guard ] (fun xs -> EIf(xs.Head, lw ctx thenExpr, lw ctx elseExpr, ty))

    | Fable.Operation(kind, _, t, r) ->
        let ty = mapType ctx r t

        match kind with
        | Fable.Unary(op, x) ->
            let ir = lw ctx x

            match op with
            | UnaryPlus -> ir
            | UnaryMinus -> bindArgs ctx [ ir ] (fun xs -> EPrim("neg", xs, ty))
            | UnaryNot -> bindArgs ctx [ ir ] (fun xs -> EPrim("not", xs, ty))
            | UnaryNotBitwise -> bindArgs ctx [ ir ] (fun xs -> EPrim("bnot", xs, ty))
            | UnaryAddressOf -> fail r "the Zig target does not support address-of yet"
        | Fable.Binary(op, a, b) ->
            let name =
                match op with
                | BinaryEqual -> "eq"
                | BinaryUnequal -> "ne"
                | BinaryLess -> "lt"
                | BinaryLessOrEqual -> "le"
                | BinaryGreater -> "gt"
                | BinaryGreaterOrEqual -> "ge"
                | BinaryShiftLeft -> "shl"
                | BinaryShiftRightSignPropagating
                | BinaryShiftRightZeroFill -> "shr"
                | BinaryMinus -> "sub"
                | BinaryPlus -> "add"
                | BinaryMultiply -> "mul"
                | BinaryDivide -> "div"
                | BinaryModulus -> "mod"
                | BinaryOrBitwise -> "bor"
                | BinaryXorBitwise -> "bxor"
                | BinaryAndBitwise -> "band"
                | BinaryExponent -> fail r "the Zig target does not support `**` yet"

            // (only numbers, booleans and chars get this far: anything else fails in mapType)
            let operandTy = mapType ctx a.Range a.Type

            // A whole number divided by zero raises, as does the smallest one divided by -1. A
            // divisor that is written out and is neither needs no test.
            let safeDivisor =
                match b with
                | Fable.Value(Fable.NumberConstant(value, _), _) ->
                    match value with
                    | Fable.NumberValue.Int8 n -> n <> 0y && n <> -1y
                    | Fable.NumberValue.Int16 n -> n <> 0s && n <> -1s
                    | Fable.NumberValue.Int32 n -> n <> 0 && n <> -1
                    | Fable.NumberValue.Int64 n -> n <> 0L && n <> -1L
                    | Fable.NumberValue.UInt8 n -> n <> 0uy
                    | Fable.NumberValue.UInt16 n -> n <> 0us
                    | Fable.NumberValue.UInt32 n -> n <> 0u
                    | Fable.NumberValue.UInt64 n -> n <> 0UL
                    | _ -> false
                | _ -> false

            match name, operandTy with
            | ("div" | "mod"), TPrim prim when intBits operandTy > 0 && not safeDivisor ->
                let f =
                    if name = "div" then
                        "div"
                    else
                        "rem"

                ctx.State.UsesRuntime <- true
                bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> ERt($"fable_rt.%s{f}(%s{prim}, $0, $1)", xs, ty))
            | _ -> bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim(name, xs, ty))
        | Fable.Logical(op, a, b) ->
            let rhs = lw ctx b

            bindArgs
                ctx
                [ lw ctx a ]
                (fun xs ->
                    match op with
                    | LogicalAnd -> EIf(xs.Head, rhs, ELit("false", tBool), tBool)
                    | LogicalOr -> EIf(xs.Head, ELit("true", tBool), rhs, tBool)
                )

    // printf, sprintf, failwithf and interpolated strings: the format is taken apart here
    | Fable.CurriedApply(Fable.CurriedApply(PrintfCall(selector, fmt, []), first, _, _), rest, t, r) ->
        formatted ctx r selector fmt (first @ rest) t
    // A printf that is not given all its values where it stands (`List.iter (printfn "%d") xs`)
    // is the function that takes the values that are missing.
    | PrintfPartial(call, given) ->
        let rec split (t: Fable.Type) (taken: int) : Fable.Type list * Fable.Type =
            match t with
            | Fable.LambdaType(arg, rest) ->
                let args, ret = split rest (taken + 1)
                arg :: args, ret
            | ret -> [], ret

        let argTypes, ret = split e.Type 0
        let n = System.Threading.Interlocked.Increment(&printfValues)

        let names =
            argTypes
            |> List.mapi (fun i t ->
                {
                    Name = $"fmt%d{n}_%d{i}"
                    Type = t
                    IsMutable = false
                    IsThisArgument = false
                    IsCompilerGenerated = true
                    Range = None
                    IsInlineIfLambda = false
                }
                : Fable.Ident
            )

        let all = given @ (names |> List.map Fable.IdentExpr)
        let body = Fable.CurriedApply(call, all, ret, e.Range)
        lw ctx (List.foldBack (fun name body -> Fable.Lambda(name, body, None)) names body)
    | Fable.CurriedApply(PrintfCall(selector, fmt, []), args, t, r) -> formatted ctx r selector fmt args t

    // `printfn "%d"` that is not given all its values at once. F# names the function it stands
    // for and applies the name where the values are (`let clo = printfn "%d" in fun x -> clo x`),
    // so the name is put back: what has been given is evaluated here, the rest where it is used.
    | Fable.Let(id, PrintfPartial(call, given), body) ->
        let binds = List<Fable.Ident * Fable.Expr>()

        let args =
            given
            |> List.mapi (fun i arg ->
                match arg with
                | Fable.Value _ -> arg
                | Fable.IdentExpr x when not x.IsMutable -> arg
                | _ ->
                    let name =
                        { id with
                            Name = $"%s{id.Name}_given%d{i}"
                            Type = arg.Type
                            IsMutable = false
                        }

                    binds.Add((name, arg))
                    Fable.IdentExpr name
            )

        let applied =
            if args.IsEmpty then
                call
            else
                Fable.CurriedApply(call, args, Fable.Any, None)

        let body = FableTransforms.replaceValues (Map.ofList [ id.Name, applied ]) body
        lw ctx (Seq.foldBack (fun (name, value) rest -> Fable.Let(name, value, rest)) binds body)

    | PrintfCall(selector, fmt, holes) -> formatted ctx e.Range selector fmt holes e.Type

    // A call that the replacements kept under its .NET name.
    | Fable.Call(Fable.Import(imp, _, _), info, t, r) when
        imp.Path.StartsWith(Replacements.DotnetPrefix, System.StringComparison.Ordinal)
        ->
        dotnetCall ctx r (imp.Path.Substring Replacements.DotnetPrefix.Length) imp.Selector info t

    // `[<Emit("...")>]`: Zig text, with `$0`, `$1`, ... standing for the arguments
    | Fable.Emit(info, t, r) ->
        let ty = mapType ctx r t

        if info.CallInfo.ThisArg.IsSome then
            fail r "the Zig target does not support Emit on instance members yet"

        if info.Macro.Contains "fable_rt." then
            ctx.State.UsesRuntime <- true

        let args =
            info.CallInfo.Args
            |> List.filter (fun a -> not (isUnit a.Type))
            |> List.map (lw ctx)

        bindArgs ctx args (fun xs -> EEmit(info.Macro, xs, ty))

    // a field of an exception, which is known to be of the declared type
    | Fable.Get(x, Fable.FieldGet info, t, r) when
        (match x.Type with
         | Fable.DeclaredType(entRef, _) -> (tryExnEnt ctx r entRef).IsSome
         | _ -> false)
        ->
        let ent =
            match x.Type with
            | Fable.DeclaredType(entRef, _) -> (tryExnEnt ctx r entRef).Value
            | _ -> fail r "internal: not an exception"

        let ty = mapType ctx r t
        bindArgs ctx [ lw ctx x ] (fun xs -> EExnGet(xs.Head, ent, info.Name, ty))

    | Fable.Get(x, kind, t, r) ->
        let ty = mapType ctx r t

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let v = xs.Head

                match kind, typeOf v with
                | Fable.FieldGet info, TEnt(ent, _) when ent.Kind = KRecord || ent.Kind = KRefRecord ->
                    EGet(v, PField info.Name, ty)
                | Fable.TupleIndex i, TTuple _ -> EGet(v, PItem i, ty)
                | Fable.UnionField info, TEnt(ent, _) ->
                    let case, fields = List.item info.CaseIndex ent.Cases
                    EGet(v, PCase(case, fst (List.item info.FieldIndex fields)), ty)
                | Fable.UnionTag, TEnt _ -> EPrim("tag", [ v ], tI32)
                | Fable.ListHead, TEnt _ -> EGet(v, PCase("Cons", "Head"), ty)
                | Fable.ListTail, TEnt _ -> EGet(v, PCase("Cons", "Tail"), ty)
                | Fable.OptionValue, TOpt _ -> EGet(v, PSome, ty)
                | _ -> fail r "the Zig target does not support %s yet" (exprKind e)
            )

    // `:? SomeException`, and the patterns of a `with` handler
    | Fable.Test(x, Fable.TypeTest(Fable.DeclaredType(entRef, _)), r) when (tryExnEnt ctx r entRef).IsSome ->
        let ent = (tryExnEnt ctx r entRef).Value
        bindArgs ctx [ lw ctx x ] (fun xs -> EExnTest(xs.Head, ent))

    | Fable.Test(x, Fable.TypeTest(Fable.DeclaredType(entRef, _)), _) when entRef.FullName = "System.Exception" ->
        ESeq(lwStmt ctx x, ELit("true", tBool))

    // try/with: the handler owns the exception it caught. try/finally: the finalizer runs when
    // the body has finished, and when it raised, before the exception goes on.
    | Fable.TryCatch(body, catch, finalizer, r) ->
        let ty = mapType ctx r e.Type

        let guarded =
            match catch with
            | Some(id, handler) ->
                let exV = ctx.State.NewVar(id.Name, tExn, VLocal, false)
                let bodyIr = lw ctx body
                ctx.Vars[id.Name] <- exV
                ETry(bodyIr, exV, lw { ctx with CaughtExn = Some exV } handler, ty)
            | None -> lw ctx body

        match finalizer with
        | None -> guarded
        | Some fin ->
            let exV = ctx.State.NewVar("exn", tExn, VLocal, false)
            let onRaise = ESeq(lwStmt ctx fin, ERaise(EVar exV, ty))
            let tried = ETry(guarded, exV, onRaise, ty)

            if isVoid ty then
                ESeq(tried, lwStmt ctx fin)
            else
                let result = ctx.State.NewVar("result", ty, VLocal, false)
                ELet(result, tried, ESeq(lwStmt ctx fin, EVar result))

    | Fable.Test(x, kind, r) ->
        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let v = xs.Head

                match kind, typeOf v with
                | Fable.UnionCaseTest tag, (TEnt(ent, _) as t) -> ETest(v, fst (List.item tag ent.Cases), t)
                | Fable.ListTest isCons, (TEnt _ as t) ->
                    ETest(
                        v,
                        (if isCons then
                             "Cons"
                         else
                             "Empty"),
                        t
                    )
                | Fable.OptionTest isSome, (TOpt _ as t) ->
                    ETest(
                        v,
                        (if isSome then
                             "Some"
                         else
                             "None"),
                        t
                    )
                | _ -> fail r "the Zig target does not support %s yet" (exprKind e)
            )

    | Fable.Call(callee, info, t, r) ->
        let ty = mapType ctx r t

        // (a member of a type is a function whose first argument is the object)
        let allArgs = Option.toList info.ThisArg @ info.Args
        let args = allArgs |> List.map (lw ctx)

        match tryCallable ctx callee, callee with
        | Some c, _ ->
            let typeArgs, _ =
                typeArgsOf ctx r c (Some info.GenericArgs) (allArgs |> List.map (fun a -> a.Type)) (Some t)

            bindArgs ctx args (fun xs -> ECall(c.Target, typeArgs, c.Captures @ xs, ty))
        | None, Fable.Import(imp, _, _) ->
            fail r "the Zig target does not support this library call yet (%s from %s)" imp.Selector imp.Path
        // a function value: all its arguments at once
        | None, _ -> bindArgs ctx (lw ctx callee :: args) (fun xs -> ECallClo(xs.Head, xs.Tail, ty))

    | Fable.CurriedApply(applied, args, t, r) ->
        match tryCallable ctx applied with
        | Some c when args.Length >= c.Arity ->
            let now, rest = List.splitAt c.Arity args
            let nowIr = now |> List.map (lw ctx)

            let typeArgs, subst =
                typeArgsOf
                    ctx
                    r
                    c
                    None
                    (now |> List.map (fun a -> a.Type))
                    (if rest.IsEmpty then
                         Some t
                     else
                         None)

            if rest.IsEmpty then
                bindArgs ctx nowIr (fun xs -> ECall(c.Target, typeArgs, c.Captures @ xs, mapType ctx r t))
            else
                // the function returns a function, which gets the other arguments
                let first =
                    bindArgs
                        ctx
                        nowIr
                        (fun xs -> ECall(c.Target, typeArgs, c.Captures @ xs, substTy subst (mapType ctx r c.Ret)))

                applyValue ctx r subst first c.Ret rest t
        | Some c -> applyValue ctx r Map.empty (fnValue ctx r applied c applied.Type) applied.Type args t
        | None -> applyValue ctx r Map.empty (lw ctx applied) applied.Type args t

    // `record.Field <- value`
    | Fable.Set(x, Fable.FieldSet name, t, value, r) ->
        bindArgs
            ctx
            [ lw ctx x; lw ctx value ]
            (fun xs ->
                match typeOf xs[0] with
                | TEnt(ent, _) as recTy when List.contains name ent.MutableFields ->
                    let fieldTy =
                        caseFields recTy "" |> List.tryFind (fun (f, _) -> f = name) |> Option.map snd

                    EStore(EGet(xs[0], PField name, defaultArg fieldTy (mapType ctx r t)), xs[1])
                | _ -> fail r "the Zig target does not support this kind of assignment yet"
            )

    | Fable.Set(Fable.IdentExpr id, Fable.ValueSet, _, value, r) ->
        match ctx.Vars.TryGetValue id.Name with
        | true, v -> EAssign(v, lw ctx value)
        | _ -> fail r "the Zig target does not support assigning to module-level values yet (`%s`)" id.Name

    | Fable.WhileLoop(guard, body, r) ->
        let c = lw ctx guard

        if isFlat c then
            EWhile(c, lwStmt ctx body)
        else
            // (a condition with control flow in it, like `a && b`, is tested inside the loop)
            let go = ctx.State.NewVar("go", tBool, VLocal, true)
            let stop = EAssign(go, ELit("false", tBool))
            let step = bindArgs ctx [ c ] (fun xs -> EIf(xs.Head, lwStmt ctx body, stop, tVoid))
            ELet(go, ELit("true", tBool), EWhile(EVar go, step))

    | Fable.ForLoop(id, start, limit, body, isUp, _) ->
        let iv = ctx.State.NewVar(id.Name, mapType ctx id.Range id.Type, VLocal, false)
        ctx.Vars[id.Name] <- iv
        bindArgs ctx [ lw ctx start; lw ctx limit ] (fun xs -> EFor(iv, xs[0], xs[1], isUp, lwStmt ctx body))

    | Fable.TypeCast(x, t) ->
        let ir = lw ctx x

        if typeOf ir = mapType ctx e.Range t then
            ir
        else
            fail e.Range "the Zig target does not support %s yet" (exprKind e)

    // Pattern matching arrives as a decision tree whose leaves name a target and the values
    // its variables are bound to. A target reached from several leaves is lowered once per leaf.
    | Fable.DecisionTree(expr, targets) -> lw { ctx with DecisionTargets = targets } expr

    | Fable.DecisionTreeSuccess(idx, boundValues, _) ->
        let idents, target = List.item idx ctx.DecisionTargets

        List.foldBack2 (fun id v body -> Fable.Let(id, v, body)) idents boundValues target
        |> lw ctx

    | _ -> fail e.Range "the Zig target does not support %s yet" (exprKind e)

/// The type arguments of a call of `c`, and what its type parameters stand for. They are what
/// Fable says they are when it says; otherwise they follow from the types of the arguments
/// and of the result.
and typeArgsOf
    (ctx: Ctx)
    (r: SourceLocation option)
    (c: Callable)
    (given: Fable.Type list option)
    (argTypes: Fable.Type list)
    (resultType: Fable.Type option)
    : Ty list * Map<string, Ty>
    =
    if c.TypeParams.IsEmpty then
        c.OuterTypeArgs, Map.empty
    else
        let tys =
            match given with
            | Some given when given.Length = c.TypeParams.Length -> given |> List.map (mapType ctx r)
            | _ ->
                let found = Dictionary<string, Fable.Type>()

                for (declared, actual) in
                    List.zip (List.truncate argTypes.Length c.ArgTypes) (List.truncate c.Arity argTypes) do
                    unify found declared actual

                resultType |> Option.iter (unify found c.Ret)

                c.TypeParams
                |> List.map (fun name ->
                    match found.TryGetValue name with
                    | true, t -> mapType ctx r t
                    | _ ->
                        fail
                            r
                            "the Zig target cannot tell what the type parameter '%s of `%s` stands for here"
                            name
                            c.Target
                )

        c.OuterTypeArgs @ tys, Map.ofList (List.zip c.TypeParams tys)

and dotnetExnEnt (ctx: Ctx) (fullName: string) : Ent = dotnetExnEntIn ctx.State fullName

and failureEnt (ctx: Ctx) : Ent = dotnetExnEnt ctx "System.Exception"

/// Raise a .NET exception of the given class with the given message.
and raiseDotnet (ctx: Ctx) (r: SourceLocation option) (fullName: string) (message: Expr) (t: Fable.Type) : Expr =
    bindArgsIn true ctx [ message ] (fun xs -> ERaise(EExnNew(dotnetExnEnt ctx fullName, xs), mapType ctx r t))

/// "message (Parameter 'name')", as .NET puts the name of a parameter into a message
and withParameter (ctx: Ctx) (message: Expr) (parameter: Fable.Expr) : Expr =
    bindArgs
        ctx
        [ message; lw ctx parameter ]
        (fun xs -> EEmit("fable_rt.format(.{ $0, \" (Parameter '\", $1, \"')\" })", xs, tStr))

/// The function that is the `ToString` a record or a union declares for itself, if it does.
and ownToString (ctx: Ctx) (t: Fable.Type) : string option =
    match t with
    | Fable.DeclaredType(entRef, _) ->
        match ctx.Com.TryGetEntity entRef with
        | Some ent when
            (ent.IsFSharpRecord || ent.IsFSharpUnion)
            && ent.MembersFunctionsAndValues
               |> Seq.exists (fun m -> m.CompiledName = "ToString" && m.IsOverrideOrExplicitInterfaceImplementation)
            ->
            match FSharp2Fable.Util.entityIdent ctx.Com entRef with
            | Fable.IdentExpr id -> Some(id.Name + "__ToString")
            | Fable.Import(imp, _, _) -> Some(importAlias ctx imp.Path + "." + imp.Selector + "__ToString")
            | _ -> None
        | _ -> None
    | _ -> None

/// `x.ToString()`, as an expression of Fable's.
and toStringCall (x: Fable.Expr) : Fable.Expr =
    let callee =
        Fable.Import(
            {
                Selector = "ToString"
                Path = Replacements.DotnetPrefix + "System.Object"
                Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = true))
            },
            Fable.Any,
            None
        )

    Fable.Call(callee, Fable.CallInfo.Create(thisArg = x), Fable.String, x.Range)

/// Can `%A` write a value of this type as F# does? Two pairs of F# types are one type in Zig
/// (`uint16` and `char`, `option` and `voption`), a struct tuple is a tuple, and a function
/// value has no name here: a type that mentions one of them is refused, so that what is
/// written is never different from .NET's.
and checkShowable (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : unit =
    let seen = HashSet<string>()

    let rec go (t: Fable.Type) =
        match t with
        | Fable.Number(UInt16, _) -> fail r "the Zig target cannot write a uint16 inside a value with %%A yet"
        | Fable.Number _
        | Fable.Boolean
        | Fable.Char
        | Fable.String
        | Fable.Unit
        | Fable.GenericParam _ -> ()
        | Fable.Option(inner, false)
        | Fable.Array(inner, _)
        | Fable.List inner -> go inner
        | Fable.Option(_, true) -> fail r "the Zig target cannot write a voption with %%A yet"
        | Fable.Tuple(ts, false) -> List.iter go ts
        | Fable.Tuple(_, true) -> fail r "the Zig target cannot write a struct tuple with %%A yet"
        | Fable.LambdaType _
        | Fable.DelegateType _ -> fail r "the Zig target cannot write a function value with %%A yet"
        | Fable.DeclaredType(entRef, genArgs) ->
            List.iter go genArgs

            if not (dotnetExceptions.ContainsKey entRef.FullName) && seen.Add entRef.FullName then
                match ctx.Com.TryGetEntity entRef with
                | Some ent when ent.IsFSharpUnion ->
                    for case in ent.UnionCases do
                        for field in case.UnionCaseFields do
                            go field.FieldType
                | Some ent when ent.IsFSharpRecord || ent.IsFSharpExceptionDeclaration ->
                    for field in ent.FSharpFields do
                        go field.FieldType
                | _ -> fail r "the Zig target cannot write a value of the type %s with %%A yet" entRef.FullName
        | other -> fail r "the Zig target cannot write a value of this type with %%A yet (%A)" other

    go t

/// Argument `i` of a macro, with its type: a number that is written out in the program has
/// no type of its own in Zig, and how it is formatted depends on the type it has in F#.
and typedArg (ctx: Ctx) (r: SourceLocation option) (value: Fable.Expr) (i: int) : string =
    match mapType ctx r value.Type with
    | TPrim name when not (name.StartsWith("fable_rt.", System.StringComparison.Ordinal)) -> $"@as(%s{name}, $%d{i})"
    | _ -> $"$%d{i}"

/// The text of `fable_rt.format`'s parts for a format string and its arguments, and the
/// arguments in the order the macro names them.
and formatParts (ctx: Ctx) (r: SourceLocation option) (fmt: string) (args: Fable.Expr list) : string * Fable.Expr list =
    let parts = parseFormat r fmt

    let specs =
        parts
        |> List.filter (
            function
            | Spec _ -> true
            | Text _ -> false
        )

    if specs.Length <> args.Length then
        fail
            r
            "the Zig target needs a format with all its %d value(s) given at once here (it has %d)"
            specs.Length
            args.Length

    let mutable next = 0
    let values = Array.ofList args

    let texts =
        parts
        |> List.map (fun part ->
            match part with
            | Text text ->
                match zigQuoted text with
                | Some quoted -> quoted
                | None -> fail r "the Zig target does not support this text in a format string"
            | Spec(flags, width, precision, letter, net) ->
                let i = next
                next <- next + 1

                // (`{x}` and `%O` of a value whose type has a `ToString` of its own)
                if (letter = 'P' || letter = 'O') && (ownToString ctx args[i].Type).IsSome then
                    values[i] <- toStringCall args[i]

                let value = values[i]

                let isWhole =
                    match value.Type with
                    | Fable.Number((Float32 | Float64), _) -> false
                    | Fable.Number _ -> true
                    | _ -> false

                // a .NET format: the standard ones for numbers (anything else ignores it)
                let net =
                    match value.Type with
                    | Fable.Number _ when net <> "" ->
                        let known =
                            System.Text.RegularExpressions.Regex.IsMatch(net, "^[DdXxBbNnFfEeGgRrPpCc][0-9]{0,2}$")

                        if not known then
                            fail r "the Zig target does not support the .NET format `%s` yet" net

                        if "DdXxBb".IndexOf(net[0]) >= 0 && not isWhole then
                            fail r "the .NET format `%s` is for whole numbers" net

                        net
                    | Fable.String
                    | Fable.Char
                    | Fable.Boolean -> ""
                    | _ when net = "" -> ""
                    | other ->
                        fail r "the Zig target does not support a .NET format for this type of value yet (%A)" other

                // what the specifier means for the type of its value
                let kind =
                    match letter, value.Type with
                    | 'P', Fable.String -> 's'
                    | 'O', Fable.String -> 'O'
                    | ('P' | 'O'), Fable.Char -> 'c'
                    | ('P' | 'O'), (Fable.Boolean | Fable.Number _) -> 'P'
                    // (a record or a union is written by its `ToString`, which is `%A`)
                    | ('P' | 'O'), Fable.DeclaredType(entRef, _) when
                        (match ctx.Com.TryGetEntity entRef with
                         | Some ent -> ent.IsFSharpRecord || ent.IsFSharpUnion
                         | None -> false)
                        ->
                        'A'
                    | 's', Fable.String -> 's'
                    | 'b', Fable.Boolean -> 'b'
                    | 'c', Fable.Char -> 'c'
                    | ('d' | 'i'), Fable.Number _ when isWhole -> 'd'
                    | ('u' | 'x' | 'X' | 'o'), Fable.Number _ when isWhole -> letter
                    | ('f' | 'F' | 'e' | 'E' | 'g' | 'G'), Fable.Number((Float32 | Float64), _) -> letter
                    | 'A', _ -> 'A'
                    | _, (Fable.String | Fable.Char | Fable.Boolean | Fable.Number _) ->
                        fail r "the Zig target does not support the format %%%c for this type of value yet" letter
                    | _, other -> fail r "the Zig target cannot turn a value of this type into text yet (%A)" other

                if kind = 'A' then
                    if width > 0 || precision.IsSome || flags.Trim('+') <> "" then
                        fail r "the Zig target does not support a width or flags on %%A yet"

                    match value.Type with
                    // (a number of 16 bits without a sign and a char are the same type in Zig; at
                    // the top the compiler can tell them apart, inside a value it cannot)
                    | Fable.Number(UInt16, _) -> $"fable_rt.arg(.{{ .kind = 'd' }}, @as(u16, $%d{i})), \"us\""
                    | t ->
                        checkShowable ctx r t
                        $"fable_rt.arg(.{{ .kind = 'A' }}, %s{typedArg ctx r value i})"
                else

                    let fields =
                        [
                            $".kind = '%c{kind}'"
                            if width > 0 then
                                $".width = %d{width}"
                            match precision with
                            | Some p -> $".precision = %d{p}"
                            | None -> ()
                            if flags.IndexOf('0') >= 0 then
                                ".zero = true"
                            if flags.IndexOf('-') >= 0 then
                                ".left = true"
                            if flags.IndexOf('+') >= 0 then
                                ".plus = true"
                            if flags.IndexOf(' ') >= 0 then
                                ".space = true"
                            if net <> "" then
                                $".net = \"%s{net}\""
                        ]
                        |> String.concat ", "

                    $"fable_rt.arg(.{{ %s{fields} }}, %s{typedArg ctx r value i})"
        )

    (match texts with
     | [] -> ".{}"
     | _ -> texts |> String.concat ", " |> sprintf ".{ %s }"),
    List.ofArray values

/// printf and its relatives: text is built from the format's parts and printed, returned or
/// raised.
and formatted
    (ctx: Ctx)
    (r: SourceLocation option)
    (selector: string)
    (fmt: string)
    (args: Fable.Expr list)
    (t: Fable.Type)
    : Expr
    =
    let parts, values = formatParts ctx r fmt args
    ctx.State.UsesRuntime <- true
    let irs = values |> List.map (lw ctx)

    let emit (macro: string) (ty: Ty) =
        bindArgs ctx irs (fun xs -> EEmit(macro, xs, ty))

    match selector with
    | "PrintFormatToString" -> emit $"fable_rt.format(%s{parts})" tStr
    | "PrintFormat" -> emit $"fable_rt.print(%s{parts}, false)" tVoid
    | "PrintFormatLine" -> emit $"fable_rt.print(%s{parts}, true)" tVoid
    | "PrintFormatToError" -> emit $"fable_rt.printErr(%s{parts}, false)" tVoid
    | "PrintFormatLineToError" -> emit $"fable_rt.printErr(%s{parts}, true)" tVoid
    | "PrintFormatToStringThenFail" ->
        // failwithf
        bindArgs
            ctx
            [ emit $"fable_rt.format(%s{parts})" tStr ]
            (fun xs -> ERaise(EExnNew(failureEnt ctx, xs), mapType ctx r t))
    | _ -> fail r "the Zig target does not support this kind of printf yet (%s)" selector

/// Apply a function value to arguments, as many at a time as its type takes. (`subst` says
/// what the type parameters in `fTy` stand for, when it is the declared result type of a
/// generic function.)
and applyValue
    (ctx: Ctx)
    (r: SourceLocation option)
    (subst: Map<string, Ty>)
    (f: Expr)
    (fTy: Fable.Type)
    (args: Fable.Expr list)
    (finalTy: Fable.Type)
    : Expr
    =
    match args with
    | [] -> f
    | _ ->
        let take, ret =
            match fTy with
            | Fable.LambdaType(_, ret) -> 1, ret
            | Fable.DelegateType(ts, ret) -> ts.Length, ret
            | _ ->
                // (Fable does not always say what type an item of an array has: the value does)
                match typeOf f with
                | TFn(ps, _) when ps.Length = args.Length -> ps.Length, finalTy
                | other -> fail r "the Zig target cannot apply a value of this type (%A, %A)" fTy other

        if args.Length < take then
            fail r "the Zig target does not support applying a function to some of its arguments here yet"

        let now, rest = List.splitAt take args

        let resultTy =
            if rest.IsEmpty then
                mapType ctx r finalTy
            else
                substTy subst (mapType ctx r ret)

        let call =
            bindArgs ctx (f :: (now |> List.map (lw ctx))) (fun xs -> ECallClo(xs.Head, xs.Tail, resultTy))

        applyValue ctx r subst call ret rest finalTy

/// A function that is called by name, used as a value of type `valueTy`.
and fnValue (ctx: Ctx) (r: SourceLocation option) (orig: Fable.Expr) (c: Callable) (valueTy: Fable.Type) : Expr =
    let sameShape =
        match valueTy with
        | Fable.LambdaType _ -> c.Arity = 1
        | Fable.DelegateType(ts, _) -> ts.Length = c.Arity
        | _ -> false

    if sameShape then
        let argTypes, resultType =
            match valueTy with
            | Fable.LambdaType(a, ret) -> [ a ], ret
            | Fable.DelegateType(ts, ret) -> ts, ret
            | _ -> [], valueTy

        let typeArgs, _ = typeArgsOf ctx r c None argTypes (Some resultType)
        EClosure(c.Target, typeArgs, c.Captures, mapType ctx r valueTy)
    else
        // The value takes its arguments in other steps than the function does (`let add a b`
        // used as `int -> int -> int`): lambdas that collect them, then the call.
        // (a variable is made only for its number, which no other name of the file has)
        let fresh (t: Fable.Type) =
            let n = ctx.State.NewVar("eta", tVoid, VLocal, false).Id
            AST.makeTypedIdent t $"eta%d{n}"

        let rec build (t: Fable.Type) (acc: Fable.Expr list) : Fable.Expr =
            if acc.Length >= c.Arity then
                Fable.CurriedApply(orig, acc, t, r)
            else
                match t with
                | Fable.LambdaType(a, ret) ->
                    let x = fresh a
                    Fable.Lambda(x, build ret (acc @ [ Fable.IdentExpr x ]), None)
                | Fable.DelegateType(ts, ret) ->
                    let xs = ts |> List.map fresh
                    Fable.Delegate(xs, build ret (acc @ (xs |> List.map Fable.IdentExpr)), None, [])
                | _ -> fail r "the Zig target cannot use this function as a value of this type"

        let lambda = build valueTy []
        lw ctx lambda

/// Compile lambdas (one, or a group that refer to each other) as functions of the file.
and liftGroup
    (ctx: Ctx)
    (r: SourceLocation option)
    (bindings: (string option * string * Fable.Expr) list)
    : LocalFn list
    =
    let parts =
        bindings
        |> List.map (fun (ident, hint, fnExpr) ->
            match fnExpr with
            | Fable.Lambda(arg, body, _) -> ident, hint, [ arg ], body
            | Fable.Delegate(args, body, _, _) -> ident, hint, args, body
            | _ -> fail r "internal: not a lambda"
        )

    let own = parts |> List.choose (fun (ident, _, _, _) -> ident) |> Set.ofList

    let captureNames =
        freeNames ctx (parts |> List.map (fun (_, _, args, body) -> args, body))
        |> List.filter (fun n -> not (own.Contains n))

    for n in captureNames do
        if ctx.Vars[n].FMutable then
            fail
                r
                "the Zig target does not support a function that uses the mutable variable `%s` of its surroundings"
                n

    // The types of the parameters and of the result, and the type parameters that are not
    // the surrounding function's: they are the function's own.
    let signatures =
        parts
        |> List.map (fun (ident, _, args, body) ->
            let argTys = args |> List.map (fun a -> mapType ctx a.Range a.Type)
            let ret = mapType ctx body.Range body.Type

            let ownGens =
                freeGens (ret :: argTys)
                |> List.filter (fun g -> not (List.contains g ctx.TypeParams))

            if ident.IsNone && not ownGens.IsEmpty then
                fail r "internal: a lambda with a type parameter of its own ('%s)" ownGens.Head

            argTys, ret, ownGens
        )

    let fns =
        List.zip parts signatures
        |> List.map (fun ((_, hint, args, body), (_, _, ownGens)) ->
            {
                FnName = uniqueName ctx $"%s{ctx.FnBase}_%s{hint}"
                CaptureNames = captureNames
                OuterTypeParams = ctx.TypeParams
                TypeParams = ownGens
                ArgTypes = args |> List.map (fun a -> a.Type)
                Ret = body.Type
            }
        )

    // (the functions of a group see each other, and the code after them sees them)
    let localFns = Dictionary<string, LocalFn>(ctx.LocalFns)

    for ((ident, _, _, _), fn) in List.zip parts fns do
        match ident with
        | Some name ->
            localFns[name] <- fn
            ctx.LocalFns[name] <- fn
        | None -> ()

    for (((_, _, args, body), fn), (argTys, ret, ownGens)) in List.zip (List.zip parts fns) signatures do
        let vars = Dictionary<string, Var>()

        let inner =
            { ctx with
                Vars = vars
                LocalFns = Dictionary<string, LocalFn>(localFns)
                TypeParams = ctx.TypeParams @ ownGens
                DecisionTargets = []
                CaughtExn = None
            }

        let captured =
            captureNames
            |> List.map (fun n ->
                let v = ctx.State.NewVar(n, ctx.Vars[n].Ty, VParam, false)
                vars[n] <- v
                v
            )

        let ps =
            List.zip args argTys
            |> List.map (fun (a, ty) ->
                let v = ctx.State.NewVar(a.Name, ty, VParam, false)
                vars[a.Name] <- v
                v
            )

        let bodyIr = lw inner body

        ctx.State.Fns.Add
            {
                Name = fn.FnName
                TypeParams = ctx.TypeParams @ ownGens
                Params = captured @ ps
                Modes = (captured @ ps) |> List.map (fun _ -> MPlain)
                Ret = ret
                Body = bodyIr
                RetFrom = None
                Raises = RNever
                Stores = false
                IsLocal = true
                IsEntryPoint = false
                Range = body.Range
            }

    fns

/// What the target does for a .NET or FSharp.Core member. This table is keyed by .NET names
/// only, so it does not depend on how any other target implements the same member.
and dotnetCall
    (ctx: Ctx)
    (r: SourceLocation option)
    (entity: string)
    (name: string)
    (info: Fable.CallInfo)
    (t: Fable.Type)
    : Expr
    =
    let isNumber (ty: Ty) = intBits ty > 0 || isFloatTy ty

    // (the object of a property or method comes first)
    let args =
        match info.ThisArg with
        | Some this -> this :: info.Args
        | None -> info.Args

    let contents (cell: Expr) =
        match typeOf cell with
        | TEnt(_, [ elem ]) -> EGet(cell, PField "contents", elem)
        | _ -> fail r "internal: not a ref cell"

    /// a call into the runtime library that can raise
    let rt (macro: string) (xs: Fable.Expr list) (ty: Ty) : Expr =
        ctx.State.UsesRuntime <- true
        bindArgs ctx (xs |> List.map (lw ctx)) (fun irs -> ERt(macro, irs, ty))

    /// a call into the runtime library that cannot
    let pure' (macro: string) (xs: Fable.Expr list) (ty: Ty) : Expr =
        ctx.State.UsesRuntime <- true
        bindArgs ctx (xs |> List.map (lw ctx)) (fun irs -> EEmit(macro, irs, ty))

    let tChar = TPrim "u16"

    let isInt (x: Fable.Expr) =
        match x.Type with
        | Fable.Number(Int32, _) -> true
        | _ -> false

    match entity, name, args with
    // ref cells: `ref x`, `!r` and `r.Value`, `r := x` and `r.Value <- x`, `incr`, `decr`
    | "Microsoft.FSharp.Core.Operators", "Ref", [ x ] ->
        bindArgsIn true ctx [ lw ctx x ] (fun xs -> ECon(TEnt(refEnt ctx.State, [ typeOf xs.Head ]), "", xs, None))
    | "Microsoft.FSharp.Core.Operators", "op_Dereference", [ cell ]
    | "Microsoft.FSharp.Core.FSharpRef`1", ("get_Value" | "get_contents"), cell :: _ ->
        bindArgs ctx [ lw ctx cell ] (fun xs -> contents xs.Head)
    | "Microsoft.FSharp.Core.Operators", "op_ColonEquals", [ cell; value ]
    | "Microsoft.FSharp.Core.FSharpRef`1", ("set_Value" | "set_contents"), [ cell; value ] ->
        bindArgs ctx [ lw ctx cell; lw ctx value ] (fun xs -> EStore(contents xs[0], xs[1]))
    | "Microsoft.FSharp.Core.Operators", ("Increment" | "Decrement"), [ cell ] ->
        let op =
            if name = "Increment" then
                "add"
            else
                "sub"

        bindArgs
            ctx
            [ lw ctx cell ]
            (fun xs -> EStore(contents xs.Head, EPrim(op, [ contents xs.Head; ELit("1", tI32) ], tI32)))
    // lists: what does not need a loop is a test or a field
    | ("Microsoft.FSharp.Collections.FSharpList`1" | "Microsoft.FSharp.Collections.ListModule"),
      ("get_IsEmpty" | "IsEmpty"),
      x :: _ -> bindArgs ctx [ lw ctx x ] (fun xs -> ETest(xs.Head, "Empty", typeOf xs.Head))
    | ("Microsoft.FSharp.Collections.FSharpList`1" | "Microsoft.FSharp.Collections.ListModule"),
      ("get_Head" | "Head"),
      x :: _ -> bindArgs ctx [ lw ctx x ] (fun xs -> EGet(xs.Head, PCase("Cons", "Head"), mapType ctx r t))
    | ("Microsoft.FSharp.Collections.FSharpList`1" | "Microsoft.FSharp.Collections.ListModule"),
      ("get_Tail" | "Tail"),
      x :: _ -> bindArgs ctx [ lw ctx x ] (fun xs -> EGet(xs.Head, PCase("Cons", "Tail"), mapType ctx r t))
    // structural equality of records, unions, tuples and options: plain values, compared
    // field by field
    | "Microsoft.FSharp.Core.Operators", "op_Equality", [ a; b ] ->
        bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim("eql", xs, tBool))
    | "Microsoft.FSharp.Core.Operators", "op_Inequality", [ a; b ] ->
        bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim("not", [ EPrim("eql", xs, tBool) ], tBool))
    // ---- numbers that are not numbers ----
    | "Microsoft.FSharp.Core.Operators", "NaN", [] -> ELit("std.math.nan(f64)", TPrim "f64")
    | "Microsoft.FSharp.Core.Operators", "NaNSingle", [] -> ELit("std.math.nan(f32)", TPrim "f32")
    | "Microsoft.FSharp.Core.Operators", "Infinity", [] -> ELit("std.math.inf(f64)", TPrim "f64")
    | "Microsoft.FSharp.Core.Operators", "InfinitySingle", [] -> ELit("std.math.inf(f32)", TPrim "f32")
    // (a cast that changes nothing here: an exception of a known class is an `exn`)
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", ("UnboxFast" | "UnboxGeneric"), [ x ] when
        mapType ctx r x.Type = mapType ctx r t
        ->
        lw ctx x
    // ---- arrays ----
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "GetArray", [ a; i ]
    | "Microsoft.FSharp.Collections.ArrayModule", "Get", [ a; i ] ->
        // (where the item is a function that is applied at once, Fable gives the read the type
        // of the application: the type of the array is the one to go by)
        let itemTy =
            match a.Type with
            | Fable.Array(item, _) -> item
            | _ -> t

        rt "fable_rt.arrayGet($0, $1)" [ a; i ] (mapType ctx r itemTy)
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "SetArray", [ a; i; x ]
    | "Microsoft.FSharp.Collections.ArrayModule", "Set", [ a; i; x ] ->
        rt "fable_rt.arraySet($0, $1, $2)" [ a; i; x ] tVoid
    | "System.Array", "get_Length", [ a ]
    | "Microsoft.FSharp.Collections.ArrayModule", "Length", [ a ] -> pure' "fable_rt.arrayLen($0)" [ a ] tI32
    | "Microsoft.FSharp.Collections.ArrayModule", "IsEmpty", [ a ] -> pure' "(fable_rt.arrayLen($0) == 0)" [ a ] tBool
    | "Microsoft.FSharp.Collections.ArrayModule", "Empty", [] -> pure' "fable_rt.arrayOf($R, .{})" [] (mapType ctx r t)
    | "Microsoft.FSharp.Core.Operators.OperatorIntrinsics", "GetArraySlice", [ a; lo; hi ] ->
        pure' "fable_rt.arraySlice($0, $1, $2)" [ a; lo; hi ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "ZeroCreate", [ n ] ->
        rt "fable_rt.arrayZero($R, $0)" [ n ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Create", [ n; x ] ->
        rt "fable_rt.arrayCreate($R, $0, $1)" [ n; x ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Initialize", [ n; f ] ->
        rt "fable_rt.arrayInit($R, $0, $1)" [ n; f ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Copy", [ a ] ->
        pure' "fable_rt.arrayCopy($0)" [ a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Append", [ a; b ] ->
        pure' "fable_rt.arrayAppend($0, $1)" [ a; b ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Reverse", [ a ] ->
        pure' "fable_rt.arrayRev($0)" [ a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "GetSubArray", [ a; start; n ] ->
        rt "fable_rt.arraySub($0, $1, $2)" [ a; start; n ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Fill", [ a; start; n; x ] ->
        rt "fable_rt.arrayFill($0, $1, $2, $3)" [ a; start; n; x ] tVoid
    | "Microsoft.FSharp.Collections.ArrayModule", "OfList", [ xs ] ->
        pure' "fable_rt.arrayOfList($R, $0)" [ xs ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "ToList", [ a ] ->
        pure' "fable_rt.arrayToList($0)" [ a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Contains", [ x; a ] ->
        pure' "fable_rt.arrayContains(@as(fable_rt.ItemOf(@TypeOf($1)), $0), $1)" [ x; a ] tBool
    | "Microsoft.FSharp.Collections.ArrayModule", "Map", [ f; a ] ->
        rt "fable_rt.arrayMap($R, $0, $1)" [ f; a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "MapIndexed", [ f; a ] ->
        rt "fable_rt.arrayMapi($R, $0, $1)" [ f; a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Iterate", [ f; a ] -> rt "fable_rt.arrayIter($0, $1)" [ f; a ] tVoid
    | "Microsoft.FSharp.Collections.ArrayModule", "IterateIndexed", [ f; a ] ->
        rt "fable_rt.arrayIteri($0, $1)" [ f; a ] tVoid
    | "Microsoft.FSharp.Collections.ArrayModule", "Fold", [ f; state; a ] ->
        rt "fable_rt.arrayFold($0, @as($R, $1), $2)" [ f; state; a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Filter", [ f; a ] ->
        rt "fable_rt.arrayFilter($0, $1)" [ f; a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Exists", [ f; a ] -> rt "fable_rt.arrayExists($0, $1)" [ f; a ] tBool
    | "Microsoft.FSharp.Collections.ArrayModule", "ForAll", [ f; a ] -> rt "fable_rt.arrayForall($0, $1)" [ f; a ] tBool

    // ---- chars: each code unit to what .NET maps it to (there is no current culture) ----
    | "System.Char", ("ToUpper" | "ToUpperInvariant"), [ c ] -> pure' "fable_rt.unicode.toUpper($0)" [ c ] tChar
    | "System.Char", ("ToLower" | "ToLowerInvariant"), [ c ] -> pure' "fable_rt.unicode.toLower($0)" [ c ] tChar
    | "System.Char", "IsWhiteSpace", [ c ] -> pure' "fable_rt.unicode.isWhiteSpace($0)" [ c ] tBool
    // ---- strings ----
    // (what a null string or an argument out of range raises on .NET, it raises here: those
    // calls are `ERt`. The `String` module takes a null string for an empty one.)
    | "Microsoft.FSharp.Core.Operators.Unchecked", "DefaultOf", [] when t = Fable.String ->
        ELit("@as(fable_rt.String, null)", tStr)
    | "Microsoft.FSharp.Core.Operators", "IsNull", [ x ] when x.Type = Fable.String -> pure' "($0 == null)" [ x ] tBool
    | "System.String", "get_Length", [ s ] when neverNull s -> pure' "fable_rt.strLength($0)" [ s ] tI32
    | "System.String", "get_Length", [ s ] -> rt "fable_rt.strLen($0)" [ s ] tI32
    | "Microsoft.FSharp.Core.StringModule", "Length", [ s ] -> pure' "fable_rt.strLength($0)" [ s ] tI32
    | "System.String", "get_Chars", [ s; i ]
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "GetString", [ s; i ] ->
        rt "fable_rt.strAt($0, $1)" [ s; i ] tChar
    | "System.String", "IsNullOrEmpty", [ s ] -> pure' "fable_rt.strIsNullOrEmpty($0)" [ s ] tBool
    | "System.String", "IsNullOrWhiteSpace", [ s ] -> pure' "fable_rt.strIsNullOrWhiteSpace($0)" [ s ] tBool
    | "System.String", "CompareOrdinal", [ a; b ] -> pure' "fable_rt.strCompare($0, $1)" [ a; b ] tI32
    | "System.String", "Equals", [ a; b ] when a.Type = Fable.String && b.Type = Fable.String ->
        if info.ThisArg.IsSome then
            rt "fable_rt.strEquals($0, $1)" [ a; b ] tBool
        else
            pure' "fable_rt.strEql($0, $1)" [ a; b ] tBool
    | "System.String", "ToString", [ s ] -> lw ctx s
    | "System.String", ".ctor", [ c; n ] when c.Type = Fable.Char -> rt "fable_rt.strOfChar($0, $1)" [ c; n ] tStr
    | "System.String", "Substring", [ s; start ] -> rt "fable_rt.strSubstring($0, $1, null)" [ s; start ] tStr
    | "System.String", "Substring", [ s; start; n ] -> rt "fable_rt.strSubstring($0, $1, $2)" [ s; start; n ] tStr
    | "System.String", "IndexOf", [ s; x ] when x.Type = Fable.Char ->
        rt "fable_rt.strIndexOfChar($0, $1, 0)" [ s; x ] tI32
    | "System.String", "IndexOf", [ s; x; start ] when x.Type = Fable.Char && isInt start ->
        rt "fable_rt.strIndexOfChar($0, $1, $2)" [ s; x; start ] tI32
    | "System.String", "IndexOf", [ s; x ] when x.Type = Fable.String ->
        rt "fable_rt.strIndexOf($0, $1, 0)" [ s; x ] tI32
    | "System.String", "IndexOf", [ s; x; start ] when x.Type = Fable.String && isInt start ->
        rt "fable_rt.strIndexOf($0, $1, $2)" [ s; x; start ] tI32
    | "System.String", "LastIndexOf", [ s; x ] when x.Type = Fable.Char ->
        rt "fable_rt.strLastIndexOfChar($0, $1)" [ s; x ] tI32
    | "System.String", "LastIndexOf", [ s; x ] when x.Type = Fable.String ->
        rt "fable_rt.strLastIndexOf($0, $1)" [ s; x ] tI32
    | "System.String", "Contains", [ s; x ] when x.Type = Fable.Char ->
        rt "fable_rt.strContainsChar($0, $1)" [ s; x ] tBool
    | "System.String", "Contains", [ s; x ] when x.Type = Fable.String ->
        rt "fable_rt.strContains($0, $1)" [ s; x ] tBool
    | "System.String", "StartsWith", [ s; x ] when x.Type = Fable.Char ->
        rt "fable_rt.strStartsWithChar($0, $1)" [ s; x ] tBool
    | "System.String", "StartsWith", [ s; x ] when x.Type = Fable.String ->
        rt "fable_rt.strStartsWith($0, $1)" [ s; x ] tBool
    | "System.String", "EndsWith", [ s; x ] when x.Type = Fable.Char ->
        rt "fable_rt.strEndsWithChar($0, $1)" [ s; x ] tBool
    | "System.String", "EndsWith", [ s; x ] when x.Type = Fable.String ->
        rt "fable_rt.strEndsWith($0, $1)" [ s; x ] tBool
    // (there is no current culture here: `ToUpper` is `ToUpperInvariant`)
    | "System.String", ("ToUpper" | "ToUpperInvariant"), [ s ] -> rt "fable_rt.strCase($0, true)" [ s ] tStr
    | "System.String", ("ToLower" | "ToLowerInvariant"), [ s ] -> rt "fable_rt.strCase($0, false)" [ s ] tStr
    | "System.String", "Trim", [ s ] -> rt "fable_rt.strTrim($0, true, true, null)" [ s ] tStr
    | "System.String", "TrimStart", [ s ] -> rt "fable_rt.strTrim($0, true, false, null)" [ s ] tStr
    | "System.String", "TrimEnd", [ s ] -> rt "fable_rt.strTrim($0, false, true, null)" [ s ] tStr
    | "System.String", "Trim", [ s; c ] when c.Type = Fable.Char ->
        rt "fable_rt.strTrim($0, true, true, $1)" [ s; c ] tStr
    | "System.String", "TrimStart", [ s; c ] when c.Type = Fable.Char ->
        rt "fable_rt.strTrim($0, true, false, $1)" [ s; c ] tStr
    | "System.String", "TrimEnd", [ s; c ] when c.Type = Fable.Char ->
        rt "fable_rt.strTrim($0, false, true, $1)" [ s; c ] tStr
    | "System.String", "Replace", [ s; a; b ] when a.Type = Fable.Char && b.Type = Fable.Char ->
        rt "fable_rt.strReplaceChar($0, $1, $2)" [ s; a; b ] tStr
    | "System.String", "Replace", [ s; a; b ] when a.Type = Fable.String && b.Type = Fable.String ->
        rt "fable_rt.strReplace($0, $1, $2)" [ s; a; b ] tStr
    | "System.String", "Insert", [ s; at; x ] -> rt "fable_rt.strInsert($0, $1, $2)" [ s; at; x ] tStr
    | "System.String", "Remove", [ s; start ] -> rt "fable_rt.strRemove($0, $1, null)" [ s; start ] tStr
    | "System.String", "Remove", [ s; start; n ] -> rt "fable_rt.strRemove($0, $1, $2)" [ s; start; n ] tStr
    | "System.String", "PadLeft", [ s; n ] -> rt "fable_rt.strPad($0, true, $1, ' ')" [ s; n ] tStr
    | "System.String", "PadLeft", [ s; n; c ] -> rt "fable_rt.strPad($0, true, $1, $2)" [ s; n; c ] tStr
    | "System.String", "PadRight", [ s; n ] -> rt "fable_rt.strPad($0, false, $1, ' ')" [ s; n ] tStr
    | "System.String", "PadRight", [ s; n; c ] -> rt "fable_rt.strPad($0, false, $1, $2)" [ s; n; c ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Concat", [ sep; Uncast xs ] when xs.Type = Fable.List Fable.String ->
        pure' "fable_rt.strJoin($0, $1)" [ sep; xs ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Replicate", [ n; s ] -> rt "fable_rt.strReplicate($0, $1)" [ n; s ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Initialize", [ n; f ] -> rt "fable_rt.strInit($0, $1)" [ n; f ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Map", [ f; s ] -> rt "fable_rt.strMap($0, $1)" [ f; s ] tStr
    | "Microsoft.FSharp.Core.StringModule", "MapIndexed", [ f; s ] -> rt "fable_rt.strMapi($0, $1)" [ f; s ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Iterate", [ f; s ] -> rt "fable_rt.strIter($0, $1)" [ f; s ] tVoid
    | "Microsoft.FSharp.Core.StringModule", "IterateIndexed", [ f; s ] -> rt "fable_rt.strIteri($0, $1)" [ f; s ] tVoid
    | "Microsoft.FSharp.Core.StringModule", "ForAll", [ f; s ] -> rt "fable_rt.strForall($0, $1)" [ f; s ] tBool
    | "Microsoft.FSharp.Core.StringModule", "Exists", [ f; s ] -> rt "fable_rt.strExists($0, $1)" [ f; s ] tBool
    | "Microsoft.FSharp.Core.StringModule", "Filter", [ f; s ] -> rt "fable_rt.strFilter($0, $1)" [ f; s ] tStr
    | "Microsoft.FSharp.Core.StringModule", "Collect", [ f; s ] -> rt "fable_rt.strCollect($0, $1)" [ f; s ] tStr
    | "System.String", "Concat", parts when not parts.IsEmpty && parts |> List.forall (fun x -> x.Type = Fable.String) ->
        let holes = parts |> List.mapi (fun i _ -> $"$%d{i}") |> String.concat ", "
        pure' $"fable_rt.format(.{{ %s{holes} }})" parts tStr
    // `a + b + c`: one new string, whatever the number of parts
    | "Microsoft.FSharp.Core.Operators", "op_Addition", [ a; b ] when a.Type = Fable.String && b.Type = Fable.String ->
        let rec parts (x: Fable.Expr) : Fable.Expr list =
            match x with
            | Fable.Call(Fable.Import(imp, _, _), inner, Fable.String, _) when
                imp.Selector = "op_Addition"
                && imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
                && inner.Args.Length = 2
                && inner.Args |> List.forall (fun arg -> arg.Type = Fable.String)
                ->
                inner.Args |> List.collect parts
            | _ -> [ x ]

        match parts a @ parts b with
        | [ a; b ] -> bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EEmit("fable_rt.strConcat($0, $1)", xs, tStr))
        | many ->
            // (literal text among the parts is written into the result directly)
            let values = List<Fable.Expr>()

            let texts =
                many
                |> List.map (fun part ->
                    match part with
                    | Fable.Value(Fable.StringConstant text, _) when (zigQuoted text).IsSome -> (zigQuoted text).Value
                    | _ ->
                        values.Add part
                        $"$%d{values.Count - 1}"
                )
                |> String.concat ", "

            bindArgs
                ctx
                (values |> Seq.map (lw ctx) |> List.ofSeq)
                (fun xs -> EEmit($"fable_rt.format(.{{ %s{texts} }})", xs, tStr))
    // `string x`
    | ("Microsoft.FSharp.Core.Operators" | "System.Object"), "ToString", [ x ] when (ownToString ctx x.Type).IsSome ->
        bindArgs ctx [ lw ctx x ] (fun xs -> ECall((ownToString ctx x.Type).Value, [], xs @ [ EUnit ], tStr))
    | ("Microsoft.FSharp.Core.Operators" | "System.Object"), "ToString", [ x ] ->
        match x.Type with
        // (the text of a null string is the empty string)
        | Fable.String when neverNull x -> lw ctx x
        | Fable.String -> pure' "fable_rt.strConcat($0, null)" [ x ] tStr
        // (a record or a union is written by its `ToString`, which is `%A`)
        | Fable.DeclaredType(entRef, _) when
            (match ctx.Com.TryGetEntity entRef with
             | Some ent -> ent.IsFSharpRecord || ent.IsFSharpUnion
             | None -> false)
            ->
            checkShowable ctx r x.Type
            pure' "fable_rt.anyText($0)" [ x ] tStr
        | Fable.Char ->
            bindArgs
                ctx
                [ lw ctx x ]
                (fun xs -> EEmit("fable_rt.format(.{ fable_rt.arg(.{ .kind = 'c' }, @as(u16, $0)) })", xs, tStr))
        | Fable.Boolean
        | Fable.Number _ ->
            bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.format(.{{ %s{typedArg ctx r x 0} }})", xs, tStr))
        | other -> fail r "the Zig target cannot turn a value of this type into text yet (%A)" other
    // ---- comparison of what is not a number: by `compare` ----
    | "Microsoft.FSharp.Core.Operators",
      ("op_LessThan" | "op_GreaterThan" | "op_LessThanOrEqual" | "op_GreaterThanOrEqual" | "Compare"),
      [ a; b ] when
        (match a.Type with
         | Fable.String
         | Fable.Number _
         | Fable.Char
         | Fable.Boolean -> true
         | _ -> false)
        ->
        let op =
            match name with
            | "op_LessThan" -> Some "lt"
            | "op_GreaterThan" -> Some "gt"
            | "op_LessThanOrEqual" -> Some "le"
            | "op_GreaterThanOrEqual" -> Some "ge"
            | _ -> None

        bindArgs
            ctx
            [ lw ctx a; lw ctx b ]
            (fun xs ->
                let order = EEmit("fable_rt.compare($0, $1)", xs, tI32)

                match op with
                | Some op -> EPrim(op, [ order; ELit("0", tI32) ], tBool)
                | None -> order
            )
    // ---- failures ----
    | "Microsoft.FSharp.Core.Operators", "FailWith", [ msg ] -> raiseDotnet ctx r "System.Exception" (lw ctx msg) t
    | "Microsoft.FSharp.Core.Operators", "InvalidOp", [ msg ] ->
        raiseDotnet ctx r "System.InvalidOperationException" (lw ctx msg) t
    | "Microsoft.FSharp.Core.Operators", "InvalidArg", [ arg; msg ] ->
        raiseDotnet ctx r "System.ArgumentException" (withParameter ctx (lw ctx msg) arg) t
    | "Microsoft.FSharp.Core.Operators", "NullArg", [ arg ] ->
        let message = ELit(stringLiteral "Value cannot be null.", tStr)
        raiseDotnet ctx r "System.ArgumentNullException" (withParameter ctx message arg) t
    // `System.Exception("...")` and the other classes: a new exception with that message
    | cls, ".ctor", args when
        dotnetExceptions.ContainsKey cls
        && args |> List.forall (fun a -> a.Type = Fable.String)
        ->
        let message =
            match cls, args with
            | "System.Exception", [] -> ELit(stringLiteral "Exception of type 'System.Exception' was thrown.", tStr)
            | "System.ArgumentNullException", [ parameter ] ->
                withParameter ctx (ELit(stringLiteral "Value cannot be null.", tStr)) parameter
            | "System.ArgumentOutOfRangeException", [ parameter ] ->
                let text = "Specified argument was out of the range of valid values."
                withParameter ctx (ELit(stringLiteral text, tStr)) parameter
            | ("System.ArgumentNullException" | "System.ArgumentOutOfRangeException"), [ parameter; message ] ->
                withParameter ctx (lw ctx message) parameter
            | "System.ArgumentException", [ message; parameter ] -> withParameter ctx (lw ctx message) parameter
            | _, [ message ] -> lw ctx message
            | _ -> fail r "the Zig target does not support this way of making a %s yet" cls

        bindArgsIn true ctx [ message ] (fun xs -> EExnNew(dotnetExnEnt ctx cls, xs))
    // `Failure msg` in a pattern: the message, if the exception is a failure
    | "Microsoft.FSharp.Core.Operators", "FailurePattern", [ x ] ->
        let failure = failureEnt ctx

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                EIf(
                    EExnTest(xs.Head, failure),
                    ECon(TOpt tStr, "Some", [ EExnGet(xs.Head, failure, "Message", tStr) ], None),
                    ECon(TOpt tStr, "None", [], None),
                    TOpt tStr
                )
            )
    | "System.Exception", "get_Message", x :: _ ->
        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.exnMessage($0)", xs, tStr))
    | "Microsoft.FSharp.Core.Operators", "Raise", [ x ] ->
        bindArgs ctx [ lw ctx x ] (fun xs -> ERaise(xs.Head, mapType ctx r t))
    | "Microsoft.FSharp.Core.Operators", "Reraise", _ ->
        match ctx.CaughtExn with
        | Some exV -> ERaise(EVar exV, mapType ctx r t)
        | None -> fail r "`reraise ()` is only possible inside a `with` handler"
    | "Microsoft.FSharp.Core.Operators", "Ignore", [ x ] -> lwStmt ctx x
    | "Microsoft.FSharp.Core.Operators", "Identity", [ x ] -> lw ctx x
    | "Microsoft.FSharp.Core.Operators", "Fst", [ x ] ->
        bindArgs ctx [ lw ctx x ] (fun xs -> EGet(xs.Head, PItem 0, mapType ctx r t))
    | "Microsoft.FSharp.Core.Operators", "Snd", [ x ] ->
        bindArgs ctx [ lw ctx x ] (fun xs -> EGet(xs.Head, PItem 1, mapType ctx r t))
    // int, int64, byte, float, char, ...: conversions between numbers, with .NET's results
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.ExtraTopLevelOperators"), _, [ x ] when
        name.StartsWith("To", System.StringComparison.Ordinal)
        ->
        let ty = mapType ctx r t

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let from = typeOf xs.Head

                if from = ty then
                    xs.Head
                elif isNumber from && isNumber ty then
                    ctx.State.UsesRuntime <- true
                    EPrim("conv", xs, ty)
                else
                    fail r "the Zig target does not support %s.%s yet" entity name
            )
    | _ -> fail r "the Zig target does not support %s.%s yet" entity name

/// A statement: its value, if it has one, is not used.
and asStmt (ctx: Ctx) (ir: Expr) : Expr =
    if isVoid (typeOf ir) then
        ir
    else
        ELet(ctx.State.NewVar("discard", typeOf ir, VLocal, false), ir, EUnit)

and lwStmt (ctx: Ctx) (e: Fable.Expr) : Expr = asStmt ctx (lw ctx e)

let private isEntryPoint (info: Fable.MemberFunctionOrValue) =
    info.Attributes
    |> Seq.exists (fun att -> att.Entity.FullName = "Microsoft.FSharp.Core.EntryPointAttribute")

let lowerFile (com: Compiler) (file: Fable.File) : FileState =
    let state = FileState()
    let members = Dictionary<string, MemberKind>()

    let reserved = HashSet<string>()

    let newCtx (fnBase: string) =
        {
            Com = com
            State = state
            Vars = Dictionary()
            Members = members
            LocalFns = Dictionary()
            FnBase = fnBase
            TypeParams = []
            Reserved = reserved
            DecisionTargets = []
            CaughtExn = None
        }

    let report (r: SourceLocation option) (msg: string) =
        com.AddLog(msg, Severity.Error, ?range = r, fileName = com.CurrentFile)

    let attached = List<Fable.MemberDecl>()

    let rec membersOf (decls: Fable.Declaration list) : Fable.MemberDecl list =
        decls
        |> List.collect (fun d ->
            match d with
            | Fable.MemberDeclaration m -> [ m ]
            | Fable.ModuleDeclaration m -> membersOf m.Members
            | Fable.ActionDeclaration a ->
                report a.Body.Range "the Zig target does not support top-level statements yet"
                []
            | Fable.ClassDeclaration c ->
                match com.TryGetEntity c.Entity with
                | Some ent when ent.IsFSharpRecord || ent.IsFSharpUnion ->
                    try
                        entOf (newCtx c.Name) None c.Entity |> ignore
                    with ZigError(msg, r) ->
                        report r msg

                    // What a type overrides is a function like its other members. So far only
                    // `ToString` is called where .NET would call it.
                    attached.AddRange(
                        c.AttachedMembers
                        |> List.choose (fun m ->
                            if m.Name = "ToString" then
                                Some { m with Name = c.Name + "__ToString" }
                            else
                                report
                                    m.Body.Range
                                    $"the Zig target does not support this kind of member yet (%s{c.Name}.%s{m.Name})"

                                None
                        )
                    )
                | Some ent when ent.IsFSharpExceptionDeclaration ->
                    try
                        tryExnEnt (newCtx c.Name) None c.Entity |> ignore
                    with ZigError(msg, r) ->
                        report r msg
                | _ -> report None $"the Zig target does not support this kind of type declaration yet (%s{c.Name})"

                []
        )

    let decls = membersOf file.Declarations
    let decls = decls @ List.ofSeq attached

    // (for work on the target: what Fable hands over for a file)
    if System.Environment.GetEnvironmentVariable "FABLE_ZIG_DUMP" = "1" then
        for d in file.Declarations do
            eprintfn "DUMP %A" d

    /// the type parameters of a function: those of the type it is a member of, then its own
    let typeParamsOf (info: Fable.MemberFunctionOrValue) : string list =
        let ofType =
            match info.DeclaringEntity |> Option.bind com.TryGetEntity with
            | Some ent when not ent.IsFSharpModule -> ent.GenericParameters |> List.map (fun g -> g.Name)
            | _ -> []

        ofType @ (info.GenericParameters |> List.map (fun g -> g.Name)) |> List.distinct

    // What the file declares is known before any body is lowered: bodies call each other.
    for d in decls do
        let info = com.GetMember d.MemberRef

        try
            reserved.Add d.Name |> ignore

            if info.IsValue then
                members[d.Name] <- MConst(mapType (newCtx d.Name) d.Body.Range d.Body.Type)
            else
                members[d.Name] <- MFunction(typeParamsOf info, d.Args |> List.map (fun a -> a.Type), d.Body.Type)
        with ZigError(msg, r) ->
            report r msg

    for d in decls do
        let info = com.GetMember d.MemberRef
        let typeParams = typeParamsOf info
        let ctx = { newCtx d.Name with TypeParams = typeParams }

        try
            if info.IsValue then
                match members.TryGetValue d.Name, lw ctx d.Body with
                | (true, MConst ty), ELit(text, _) -> state.Consts.Add((d.Name, ty, text))
                | (true, MConst _), _ ->
                    fail d.Body.Range "the Zig target only supports literal module-level values so far (`%s`)" d.Name
                | _ -> () // its type was rejected above
            else
                let entry = isEntryPoint info

                let ps =
                    if entry then
                        [] // (the argument array is not available yet)
                    else
                        d.Args
                        |> List.map (fun a ->
                            let v = state.NewVar(a.Name, mapType ctx a.Range a.Type, VParam, false)
                            ctx.Vars[a.Name] <- v
                            v
                        )

                let ret = mapType ctx d.Body.Range d.Body.Type
                let body = lw ctx d.Body

                state.Fns.Add
                    {
                        Name = d.Name
                        TypeParams = typeParams
                        Params = ps
                        Modes = ps |> List.map (fun _ -> MPlain)
                        Ret = ret
                        Body = body
                        RetFrom = None
                        Raises = RNever
                        Stores = false
                        IsLocal = false
                        IsEntryPoint = entry
                        Range = d.Body.Range
                    }
        with ZigError(msg, r) ->
            report
                (match r with
                 | Some _ -> r
                 | None -> d.Body.Range)
                msg

    settleCyclic state
    settleCycles state
    state
