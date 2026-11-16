/// The lowering's context (Ctx), the functions declared inside a function, and what is called by name; part of Fable2Zig.Lower.fs
module Fable.Transforms.Zig.LowerContext

open System.Collections.Generic
open Fable
open Fable.AST
open Fable.Transforms
open Fable.Transforms.Zig.IR

type MemberKind =
    /// a function: its type parameters, the types of its arguments, and its result type
    | MFunction of typeParams: string list * argTypes: Fable.Type list * ret: Fable.Type
    | MConst of Ty
    /// a module-level value that can be assigned
    | MValue of Ty

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
        /// the `let mutable` variables that a function inside the function assigns or reads:
        /// each is a ref cell, as F# makes it on .NET
        Boxed: HashSet<string>
        /// variables that hold an object made where they were bound (a constructor's call, an
        /// object expression) and are never assigned: not null, so used without a check
        NonNull: HashSet<string>
        /// whole-number variables known to be greater than zero where they are used (a guard
        /// tested it): a divisor that needs no test
        Positive: HashSet<string>
        /// whole-number variables known to be non-negative (>= 0) where they are used
        NonNeg: HashSet<string>
        /// i32 variables known to be strictly less than Int32.MaxValue (so `v + 1` cannot wrap negative)
        BoundedBelowMax: HashSet<string>
        /// immutable int var `n -> (collection/string var, collection/string type)` from `let n = c.Length`
        Lengths: Dictionary<string, string * Fable.Type>
        /// immutable array var `a -> known constant length`
        ConstLen: Dictionary<string, int>
        /// variables bound to a `Type` that is known here (`typeof<T>`, a `MakeGenericType` of known
        /// types): what it stands for
        KnownTypes: Dictionary<string, Fable.Type>
        /// `coll|i`: inside `for i in 0 .. coll.Length - 1` or guarded `while i < coll.Length`,
        /// `coll.[i]` is in range (and the string not null: its length was read)
        InBounds: HashSet<string>
        /// inside a `for ... in` loop: the enumerator's name, and the variable that holds the
        /// item of this round
        Enumerators: Dictionary<string, Var>
        /// `(ok, value)` of a `TryGet...(&value)` whose value has no default here: the option
        /// that stands for it
        OutTuples: Dictionary<string, Var>
        /// inside a `with` handler: the exception it caught (for `reraise ()`)
        CaughtExn: Var option
        /// inside an `Obj` constructor: writes to fields of `Obj` use `objInitField`
        InCtor: bool
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

let exprKind (e: Fable.Expr) =
    match e with
    | Fable.Value _ -> "this kind of value"
    | Fable.Lambda _
    | Fable.Delegate _ -> "function values"
    | Fable.ObjectExpr _ -> "object expressions"
    | Fable.TypeCast(x, t) ->
        let name (t: Fable.Type) =
            match t with
            | Fable.DeclaredType(e, _) -> e.FullName
            | t -> (sprintf "%A" t).Split('\n').[0]

        $"this type conversion (%s{name x.Type} to %s{name t})"
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

/// .NET's standard numeric formats (`N2`); anything else is a custom one (`0.00`).
let isStandardNetFormat (net: string) =
    System.Text.RegularExpressions.Regex.IsMatch(net, "^[A-Za-z][0-9]{0,2}$")

/// A .NET numeric format the runtime knows: a standard one, or a custom one of ASCII text.
let checkNetFormat (r: SourceLocation option) (net: string) =
    if isStandardNetFormat net then
        if not (System.Text.RegularExpressions.Regex.IsMatch(net, "^[DdXxBbNnFfEeGgRrPpCc][0-9]{0,2}$")) then
            fail r "the Zig target does not support the .NET format `%s` yet" net
    elif net |> Seq.exists (fun c -> int c > 127) then
        fail r "the Zig target does not support a .NET format with characters beyond ASCII yet (`%s`)" net

/// Text inside a Zig string literal.
let zigEscape (text: string) =
    text.Replace("\\", "\\\\").Replace("\"", "\\\"")

/// The function that implements a member of an interface for a type: `Counter__Probe_IShape_Area`
/// (the compiled name of the implementation is the interface's name and the member's).
let implName (typeName: string) (compiledName: string) : string =
    typeName
    + "__"
    + System.Text.RegularExpressions.Regex.Replace(compiledName, "[^A-Za-z0-9_]", "_")

/// The members of an interface, as the fields of the struct of function values that stands
/// for it: the compiled name (`Area`, `get_Name`), and the types of the arguments and result.
/// A short name of a type, to tell overloads apart (`get_Item$Int32`)
let rec typeTag (t: Fable.Type) : string =
    match t with
    | Fable.Number(k, _) -> string k
    | Fable.DeclaredType(e, []) -> e.FullName.Substring(e.FullName.LastIndexOf '.' + 1).Replace("`", "_")
    | Fable.DeclaredType(e, gs) ->
        e.FullName.Substring(e.FullName.LastIndexOf '.' + 1).Replace("`", "_")
        + "_"
        + (gs |> List.map typeTag |> String.concat "_")
    | Fable.GenericParam(n, _, _) -> n
    | Fable.Array(t, _) -> typeTag t + "Array"
    | Fable.List t -> typeTag t + "List"
    | Fable.Option(t, _) -> typeTag t + "Option"
    | Fable.Tuple(ts, _) -> "Tuple_" + (ts |> List.map typeTag |> String.concat "_")
    | Fable.LambdaType _
    | Fable.DelegateType _ -> "Fn"
    | other -> (sprintf "%A" other).Split([| ' '; '(' |]).[0]

let internal paramTypesOf (m: Fable.MemberFunctionOrValue) =
    m.CurriedParameterGroups |> List.concat |> List.map (fun p -> p.Type)

/// The dispatch slots of an interface (a property is there as itself and as its getter)
let internal dispatchSlots (ent: Fable.Entity) =
    ent.MembersFunctionsAndValues
    |> Seq.filter (fun m -> m.IsDispatchSlot && not (m.IsProperty && not m.IsGetter && not m.IsSetter))

/// The name of a member's field in the struct of an interface: its compiled name, and when the
/// interface has overloads of that name, the types of its parameters (`get_Item$Int32`)
let slotKey (ent: Fable.Entity) (compiled: string) (paramTypes: Fable.Type list) : string =
    let signatures =
        dispatchSlots ent
        |> Seq.filter (fun m -> m.CompiledName = compiled)
        |> Seq.map (fun m -> paramTypesOf m |> List.map typeTag)
        |> Seq.distinct
        |> Seq.length

    if signatures > 1 then
        compiled + "$" + (paramTypes |> List.map typeTag |> String.concat "_")
    else
        compiled

/// A type of a member of an interface with the type parameters that are not the interface's
/// (those of a generic method) as `obj`
let eraseForeign (ent: Fable.Entity) (t: Fable.Type) : Fable.Type =
    let own = ent.GenericParameters |> List.map (fun g -> g.Name) |> set

    let rec erase (t: Fable.Type) =
        match t with
        | Fable.GenericParam(name, _, _) when not (own.Contains name) -> Fable.Any
        | t -> t.MapGenerics erase

    erase t

let interfaceMembers (ent: Fable.Entity) : (string * Fable.Type list * Fable.Type) list =
    dispatchSlots ent
    |> Seq.distinctBy (fun m -> slotKey ent m.CompiledName (paramTypesOf m))
    // (a generic member, `abstract Encode<'J>: ...`: one field of the struct, of its type
    // parameters erased to `obj`, as Koka compiles polymorphism; its callers box and unbox, and
    // adapt an interface of them, see fable_rt.erasedConv)
    |> Seq.map (fun m ->
        let args =
            match m.CurriedParameterGroups |> List.concat |> List.map (fun p -> p.Type) with
            | [] -> [ Fable.Unit ]
            | ts -> ts

        slotKey ent m.CompiledName (paramTypesOf m),
        List.map (eraseForeign ent) args,
        eraseForeign ent m.ReturnParameter.Type
    )
    |> List.ofSeq

/// Substitute type parameters in a Fable AST type using `subst`.
/// The constructors of the classes of the file being compiled: their declaration's name, their
/// member, and the types of their parameters, by the class's full name (see `lowerFile`)
/// (Fable compiles files at once on several threads, each file whole on a thread of its own, see
/// Fable2Zig.transformFile: what belongs to the file being compiled is kept per thread)
let internal fileCtorsHere =
    new System.Threading.ThreadLocal<Dictionary<string, (string * Fable.MemberRef * Fable.Type list) list>>(fun () ->
        Dictionary()
    )

let fileCtors () = fileCtorsHere.Value

let rec substFableType (subst: Map<string, Fable.Type>) (t: Fable.Type) : Fable.Type =
    if subst.IsEmpty then
        t
    else
        match t with
        | Fable.GenericParam(n, _, _) when subst.ContainsKey n -> subst[n]
        | _ -> t.MapGenerics(substFableType subst)

/// The members of an interface and of the interfaces it inherits, each with the full name of
/// the interface that declares it (type arguments of an inherited generic interface are put in).
let rec allInterfaceMembers
    (com: Compiler)
    (ent: Fable.Entity)
    (subst: Map<string, Fable.Type>)
    : (string * string * Fable.Type list * Fable.Type) list
    =
    let sub = substFableType subst

    let own =
        interfaceMembers ent
        |> List.map (fun (n, args, ret) -> ent.FullName, n, List.map sub args, sub ret)

    let inherited =
        ent.DeclaredInterfaces
        |> Seq.toList
        |> List.collect (fun d ->
            match com.TryGetEntity d.Entity with
            | Some b ->
                let m =
                    List.zip (b.GenericParameters |> List.map (fun g -> g.Name)) (d.GenericArgs |> List.map sub)
                    |> Map.ofList

                allInterfaceMembers com b m
            | None -> []
        )

    own @ inherited |> List.distinctBy (fun (_, n, _, _) -> n)

/// Does a record or union contain itself, directly or through other records and unions?
/// With `throughUnions = false` the search stops at unions.
let reachesSelf (com: Compiler) (throughUnions: bool) (start: Fable.Entity) : bool =
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
            (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
            |> List.map (fun f -> f.FieldType)

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
let settleManaged (state: FileState) =
    let mutable changed = true

    while changed do
        changed <- false

        for e in state.Ents.Values do
            let m =
                e.Kind = KHeapUnion
                || e.Kind = KRefRecord
                || e.Kind = KIface
                || e.Hooks.IsSome
                || e.Cases |> List.exists (fun (_, fs) -> fs |> List.exists (snd >> isManagedDecl))
                // (a record of the library whose fields this file does not know, as `RegexOf`:
                // counted, as libRecordEnt says; the runtime's dup and drop go by its real type)
                || (e.Ref.FullName.StartsWith("Fable.Library.Zig.", System.StringComparison.Ordinal)
                    && e.Cases |> List.forall (fun (_, fs) -> fs.IsEmpty))

            if m <> e.Managed then
                e.Managed <- m
                changed <- true

            // (a resource without Dup is move-only, and so is what holds one)
            let c =
                (match e.Hooks with
                 | Some(_, None) -> false
                 | _ -> true)
                && e.Cases |> List.forall (fun (_, fs) -> fs |> List.forall (snd >> isCopyable))

            if c <> e.Copyable then
                e.Copyable <- c
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
let internal isMutableRuntimeCellName (name: string) =
    name = "fable_rt.Array"
    || name = "fable_rt.ResizeArray"
    || name = "fable_rt.Dictionary"
    || name = "fable_rt.HashSet"
    || name = "fable_rt.Lazy"

let settleCyclic (state: FileState) =
    let isCell (e: Ent) =
        e.Kind = KHeapUnion || e.Kind = KRefRecord

    let isAssignableCell (e: Ent) =
        isCell e && (not e.MutableFields.IsEmpty || isMutableRuntimeCellName e.Name)

    let cells = state.Ents.Values |> Seq.filter isCell |> List.ofSeq

    /// the cell types a value of this type refers to directly (looking through plain values),
    /// each with whether the reference is one that can be assigned later (what an array or a
    /// ref cell holds), and whether the value holds a function value or an exception
    let rec targets (seen: HashSet<Ent>) (t: Ty) : (Ent * bool) list * bool =
        let all (parts: ((Ent * bool) list * bool) list) =
            parts |> List.collect fst, parts |> List.exists snd

        match t with
        | TFn _
        | TPrim "fable_rt.Exn"
        | TPrim "fable_rt.Obj" -> [], true
        | TEnt(e, _) when e.Kind = KIface -> [], true
        | TEnt(e, args) ->
            let own =
                if isCell e then
                    [ e, false ], false
                elif seen.Add e then
                    e.Cases |> List.collect snd |> List.map (snd >> targets seen) |> all
                else
                    [], false

            // (the type arguments of a cell with assignable fields are what those fields hold)
            let assignable = isAssignableCell e

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
        if
            e.Name = "fable_rt.Lazy"
            || e.Name = "fable_rt.Dictionary"
            || e.Name = "fable_rt.HashSet"
        then
            reachesAny.Add e |> ignore

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
let settleCycles (state: FileState) =
    let rec reachesOpaque (t: Ty) : bool =
        match t with
        | TFn _
        | TPrim "fable_rt.Exn"
        | TPrim "fable_rt.Obj" -> true
        | TEnt(e, args) ->
            e.Kind = KIface
            || List.exists reachesOpaque args
            || (if e.Kind = KHeapUnion || e.Kind = KRefRecord then
                    e.ReachesOpaque
                else
                    e.Cases
                    |> List.exists (fun (c, _) -> caseFields t c |> List.exists (snd >> reachesOpaque)))
        | TOpt t -> reachesOpaque t
        | TTuple ts -> List.exists reachesOpaque ts
        | _ -> false

    let reachesAssignable (t: Ty) : bool =
        let seen = HashSet<Ent>()

        let rec go (t: Ty) : bool =
            match t with
            | TEnt(e, args) ->
                ((e.Kind = KHeapUnion || e.Kind = KRefRecord)
                 && (not e.MutableFields.IsEmpty || isMutableRuntimeCellName e.Name)
                 && reachesOpaque t)
                || List.exists go args
                || (if seen.Add e then
                        e.Cases |> List.exists (fun (c, _) -> caseFields t c |> List.exists (snd >> go))
                    else
                        false)
            | TOpt t -> go t
            | TTuple ts -> List.exists go ts
            | _ -> false

        go t

    let rec chainFields (t: Ty) =
        match t with
        | TEnt(e, _) when e.Name.EndsWith("__chain", System.StringComparison.Ordinal) ->
            caseFields t "" |> List.collect (snd >> chainFields)
        | TEnt(e, _) when e.Name.EndsWith("__part", System.StringComparison.Ordinal) -> caseFields t "" |> List.map snd
        | _ -> []

    let mutable holds = false
    let mutable generic = false
    let mutable instantiated = false
    let mutable captures = false
    let mutable capGeneric = false
    let mutable capInstantiated = false

    let checkOpaquePayload (t: Ty) =
        if reachesAssignable t then
            captures <- true

        if not (freeGens [ t ]).IsEmpty then
            capGeneric <- true

    let checkField (fieldTy: Ty) =
        if reachesOpaque fieldTy then
            holds <- true

        if not (freeGens [ fieldTy ]).IsEmpty then
            generic <- true

        checkOpaquePayload fieldTy

    let look (e: Expr) =
        match e with
        | ECon(TEnt({ Kind = KRefRecord } as ent, _) as t, _, _, _) ->
            for (f, fieldTy) in caseFields t "" do
                if List.contains f ent.MutableFields then
                    if reachesOpaque fieldTy then
                        holds <- true

                    if not (freeGens [ fieldTy ]).IsEmpty then
                        generic <- true
        | EExnNew(ent, args) ->
            for a in args do
                checkOpaquePayload (typeOf a)

            for (_, fields) in ent.Cases do
                for (_, fieldTy) in fields do
                    checkOpaquePayload fieldTy
        | EEmit(m, args, t)
        | ERt(m, args, t) ->
            match t with
            | TPrim "fable_rt.Obj" when m.StartsWith("fable_rt.objNew(", System.StringComparison.Ordinal) ->
                for a in args do
                    for fieldTy in chainFields (typeOf a) do
                        checkField fieldTy
            | TEnt(ent, itemArgs) when isMutableRuntimeCellName ent.Name ->
                if
                    List.exists reachesOpaque itemArgs
                    || (ent.Name = "fable_rt.Lazy" && m.Contains("lazyNew"))
                    || m.Contains("htNewWith")
                then
                    holds <- true

                if not (freeGens itemArgs).IsEmpty then
                    generic <- true
            | _ -> ()

            if m.StartsWith("fable_rt.box(", System.StringComparison.Ordinal) then
                for a in args do
                    checkOpaquePayload (typeOf a)
        | EClosure(_, typeArgs, caps, _) ->
            if List.exists reachesOpaque typeArgs then
                instantiated <- true

            if List.exists reachesAssignable typeArgs then
                capInstantiated <- true

            for c in caps do
                checkOpaquePayload (typeOf c)
        | EIface(ty, src, _) ->
            let typeArgs =
                match ty with
                | TEnt(_, args) -> args
                | _ -> []

            if List.exists reachesOpaque typeArgs then
                instantiated <- true

            if List.exists reachesAssignable typeArgs then
                capInstantiated <- true

            match src with
            | ISrcCaptures caps ->
                for c in caps do
                    checkOpaquePayload (typeOf c)
            | ISrcValue v
            | ISrcUpcast v -> checkOpaquePayload (typeOf v)
        | ECall(_, typeArgs, _, _) ->
            if List.exists reachesOpaque typeArgs then
                instantiated <- true

            if List.exists reachesAssignable typeArgs then
                capInstantiated <- true
        | _ -> ()

        false

    for fn in state.Fns do
        exists look fn.Body |> ignore

    for chainTy in state.AllocChains do
        for fieldTy in chainFields chainTy do
            checkField fieldTy

    state.Cycles <-
        {
            Holds = holds
            Generic = generic
            Instantiated = instantiated
            Captures = captures
            CapGeneric = capGeneric
            CapInstantiated = capInstantiated
        }

let listName = "Microsoft.FSharp.Collections.FSharpList`1"

/// F#'s list: a generic recursive union that the runtime library declares.
let listEnt (state: FileState) : Ent =
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
                Hooks = None
                Overrides = []
            }

        e.Cases <- [ "Empty", []; "Cons", [ "Head", TGen "T"; "Tail", TEnt(e, [ TGen "T" ]) ] ]
        state.Ents[listName] <- e
        e

let refName = "Microsoft.FSharp.Core.FSharpRef`1"

/// Is `refT` the type of the self reference F# gives a class of `type C() as this`: a field of
/// type `C ref` in C, null until the object is made?
let isSelfRefType (owner: Fable.Type) (refT: Fable.Type) =
    match owner, refT with
    | Fable.DeclaredType(c, _), Fable.DeclaredType(r, [ Fable.DeclaredType(c2, _) ]) ->
        r.FullName = refName && c.FullName = c2.FullName
    | _ -> false

/// The self reference as it is kept here: a `C option ref` (None until the object is made)
let selfRefType (refT: Fable.Type) =
    match refT with
    | Fable.DeclaredType(r, [ c ]) -> Fable.DeclaredType(r, [ Fable.Option(c, false) ])
    | t -> t

/// The type a field of the entity `owner` is kept as
let fieldTypeIn (owner: Fable.EntityRef) (f: Fable.Field) : Fable.Type =
    let ownerT = Fable.DeclaredType(owner, [])

    if isSelfRefType ownerT f.FieldType then
        selfRefType f.FieldType
    else
        f.FieldType

/// The .NET exception classes that the runtime library declares: each holds a message.
let dotnetExceptions =
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
        "AggregateException"
        "InvalidCastException"
        "TimeoutException"
        "UnauthorizedAccessException"
        "ObjectDisposedException"
        "OperationCanceledException"
        "ApplicationException"
        "OutOfMemoryException"
        "NotFiniteNumberException"
        "RankException"
        "ArrayTypeMismatchException"
        "MissingMethodException"
        "UriFormatException"
    ]
    |> List.map (fun name -> "System." + name, "fable_rt." + name)
    |> List.append
        [
            "System.Exception", "fable_rt.Failure"
            "System.Collections.Generic.KeyNotFoundException", "fable_rt.KeyNotFoundException"
            "Microsoft.FSharp.Core.MatchFailureException", "fable_rt.MatchFailureException"
            "System.IO.IOException", "fable_rt.IOException"
            "System.IO.FileNotFoundException", "fable_rt.FileNotFoundException"
            "System.IO.DirectoryNotFoundException", "fable_rt.DirectoryNotFoundException"
            "System.Threading.Tasks.TaskCanceledException", "fable_rt.TaskCanceledException"
            "System.Threading.ThreadStateException", "fable_rt.ThreadStateException"
        ]
    |> Map.ofList

/// The message .NET gives an exception of a class made without one.
let defaultExnMessages =
    Map.ofList
        [
            "System.Exception", "Exception of type 'System.Exception' was thrown."
            "System.SystemException", "System error."
            "System.ArgumentException", "Value does not fall within the expected range."
            "System.ArgumentNullException", "Value cannot be null."
            "System.ArgumentOutOfRangeException", "Specified argument was out of the range of valid values."
            "System.InvalidOperationException", "Operation is not valid due to the current state of the object."
            "System.NotSupportedException", "Specified method is not supported."
            "System.NotImplementedException", "The method or operation is not implemented."
            "System.IndexOutOfRangeException", "Index was outside the bounds of the array."
            "System.DivideByZeroException", "Attempted to divide by zero."
            "System.OverflowException", "Arithmetic operation resulted in an overflow."
            "System.FormatException", "One of the identified items was in an invalid format."
            "System.ArithmeticException", "Overflow or underflow in the arithmetic operation."
            "System.NullReferenceException", "Object reference not set to an instance of an object."
            "System.AggregateException", "One or more errors occurred."
            "System.InvalidCastException", "Specified cast is not valid."
            "System.TimeoutException", "The operation has timed out."
            "System.UriFormatException", "Invalid URI: The format of the URI could not be determined."
            "System.UnauthorizedAccessException", "Attempted to perform an unauthorized operation."
            "System.OperationCanceledException", "The operation was canceled."
            "System.ApplicationException", "Error in the application."
            "System.OutOfMemoryException", "Insufficient memory to continue the execution of the program."
            "System.NotFiniteNumberException", "Number encountered was not a finite quantity."
            "System.RankException", "Attempted to operate on an array with the incorrect number of dimensions."
            "System.ArrayTypeMismatchException", "Attempted to access an element as a type incompatible with the array."
            "System.MissingMethodException", "Attempted to access a missing method."
            "System.Collections.Generic.KeyNotFoundException", "The given key was not present in the dictionary."
            "System.IO.IOException", "I/O error occurred."
            "System.IO.FileNotFoundException", "Unable to find the specified file."
            "System.IO.DirectoryNotFoundException", "Attempted to access a path that is not on the disk."
            "System.Threading.Tasks.TaskCanceledException", "A task was canceled."
            "System.Threading.ThreadStateException", "Thread was in an invalid state for the operation being executed."
        ]

/// A .NET exception class that the runtime library declares (`System.Exception` is what
/// `failwith` raises). Its one field is the message.
let dotnetExnEntIn (state: FileState) (fullName: string) : Ent =
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
                Cases =
                    if fullName = "Microsoft.FSharp.Core.MatchFailureException" then
                        [ "", [ "Data0", tStr; "Data1", tI32; "Data2", tI32 ] ]
                    else
                        [ "", [ "Message", tStr ] ]
                MutableFields = []
                Managed = false
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        state.Ents[key] <- e
        state.UsesRuntime <- true
        e

/// F#'s `ref` cell: a generic reference record that the runtime library declares.
/// (the type this target gives what the task builder makes of a body: Fable gives none)
let taskCodeName = "Fable.Library.Zig.Task.TaskCode`1"

let resultName = "Microsoft.FSharp.Core.FSharpResult`2"
let mapName = "Microsoft.FSharp.Collections.FSharpMap`2"
let setName = "Microsoft.FSharp.Collections.FSharpSet`1"

/// F#'s `Result`: a union of the runtime library.
let resultEnt (state: FileState) : Ent =
    match state.Ents.TryGetValue resultName with
    | true, e -> e
    | _ ->
        let e =
            {
                Name = "fable_rt.Result"
                Ref =
                    {
                        FullName = resultName
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KValueUnion
                TypeParams = [ "T"; "TError" ]
                Cases = [ "Ok", [ "ResultValue", TGen "T" ]; "Error", [ "ErrorValue", TGen "TError" ] ]
                MutableFields = []
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        state.Ents[resultName] <- e
        state.UsesRuntime <- true
        e

/// F#'s `Choice<..>` (what a multi-case active pattern gives): a union of the runtime library.
let choiceEnt (state: FileState) (fullName: string) : Ent =
    match state.Ents.TryGetValue fullName with
    | true, e -> e
    | _ ->
        let n = int (fullName.Substring(fullName.IndexOf '`' + 1))
        let typeParams = List.init n (fun i -> $"T%d{i + 1}")

        let e =
            {
                Name = $"fable_rt.Choice%d{n}"
                Ref =
                    {
                        FullName = fullName
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KValueUnion
                TypeParams = typeParams
                Cases =
                    typeParams
                    |> List.mapi (fun i p -> $"Choice%d{i + 1}Of%d{n}", [ "Item", TGen p ])
                MutableFields = []
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        state.Ents[fullName] <- e
        state.UsesRuntime <- true
        e

/// F#'s array: a cell of the runtime library whose items can be assigned.
let arrayEnt (state: FileState) : Ent =
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
                Hooks = None
                Overrides = []
            }

        state.Ents["$array"] <- e
        state.UsesRuntime <- true
        e

/// .NET's mutable collections, cells of the runtime library whose contents can be assigned:
/// `List<T>` (ResizeArray), `Dictionary<K, V>`, `HashSet<T>`.
let netEnt (state: FileState) (name: string) : Ent =
    let key = "$net:" + name

    match state.Ents.TryGetValue key with
    | true, e -> e
    | _ ->
        let typeParams, fields =
            match name with
            | "Dictionary" -> [ "K"; "V" ], [ "key", TGen "K"; "value", TGen "V" ]
            | "HashSet" -> [ "T" ], [ "key", TGen "T" ]
            | "StringBuilder"
            | "Random" -> [], []
            // (a weak reference holds nothing that keeps its target alive)
            | "Weak" -> [ "T" ], []
            | _ -> [ "T" ], [ "items", TGen "T" ]

        let e =
            {
                Name = "fable_rt." + name
                Ref =
                    {
                        FullName =
                            (if name = "StringBuilder" then
                                 "System.Text."
                             elif name = "Random" then
                                 "System."
                             else
                                 "System.Collections.Generic.")
                            + name
                        Path = Fable.CoreAssemblyName "System.Runtime"
                    }
                Kind = KRefRecord
                TypeParams = typeParams
                Cases = [ "", fields ]
                MutableFields = fields |> List.map fst
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        state.Ents[key] <- e
        state.UsesRuntime <- true
        e

/// An anonymous record: a struct of the runtime library, one type per shape (the names of the
/// fields, which F# sorts), whichever file makes it.
let anonEnt (state: FileState) (names: string[]) : Ent =
    let key = "$anon:" + String.concat "," names

    match state.Ents.TryGetValue key with
    | true, e -> e
    | _ ->
        let typeParams = names |> Array.mapi (fun i _ -> $"A%d{i}") |> List.ofArray

        let e =
            {
                // (a name of the file, declared at its top as the runtime's type of this shape)
                Name = "fable_anon_" + String.concat "_" names + ".of"
                Ref =
                    {
                        FullName = key
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KRecord
                TypeParams = typeParams
                Cases = [ "", List.zip (List.ofArray names) (typeParams |> List.map TGen) ]
                MutableFields = []
                Managed = false
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        state.Ents[key] <- e
        state.UsesRuntime <- true
        e

/// A .NET interface type of known member names, emitted as `fable_rt.Iface(fable_iface_<N>(...))`.
let ifaceAnonEnt (state: FileState) (names: string[]) : Ent =
    let key = "$iface:" + String.concat "," names

    match state.Ents.TryGetValue key with
    | true, e -> e
    | false, _ ->
        let safeNames = names |> Array.map cleanIdent

        let alias =
            if safeNames.Length = 0 then
                "fable_iface_0"
            else
                "fable_iface_" + String.concat "_" safeNames

        let typeParams = Array.init names.Length (fun i -> "T" + string i) |> List.ofArray

        let e =
            {
                // (`Emit.zigType` turns `fable_iface_<name>.of` into `fable_rt.Iface(fable_iface_<name>.of(...))`)
                Name = alias + ".of"
                Ref =
                    {
                        FullName = key
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KIface
                TypeParams = typeParams
                Cases = [ "", List.zip (List.ofArray names) (typeParams |> List.map TGen) ]
                MutableFields = []
                Managed = true
                Cyclic = false
                ReachesOpaque = true
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        state.Ents[key] <- e
        state.UsesRuntime <- true
        e

/// `lazy`: a cell of the runtime library that holds the code, then the value.
let lazyEnt (state: FileState) : Ent =
    match state.Ents.TryGetValue "$lazy" with
    | true, e -> e
    | _ ->
        let e =
            {
                Name = "fable_rt.Lazy"
                Ref =
                    {
                        FullName = "System.Lazy`1"
                        Path = Fable.CoreAssemblyName "System.Runtime"
                    }
                Kind = KRefRecord
                TypeParams = [ "T" ]
                Cases = [ "", [ "value", TGen "T"; "thunk", TFn([ tVoid ], TGen "T") ] ]
                MutableFields = [ "value"; "thunk" ]
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        state.Ents["$lazy"] <- e
        state.UsesRuntime <- true
        e

let isArrayTy (t: Ty) =
    match t with
    | TEnt({ Name = "fable_rt.Array" }, _) -> true
    | _ -> false

let refEnt (state: FileState) : Ent =
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
                Hooks = None
                Overrides = []
            }

        state.Ents[refName] <- e
        e

/// A class that takes part in inheritance: its objects are `fable_rt.Obj` (see the runtime).
type ObjInfo =
    {
        Ref: Fable.EntityRef
        FullName: string
        /// `Circle`, or `alias.Circle` for a class another file declares
        Prefix: string
        /// how many classes are above it (0: it derives from System.Object)
        Depth: int
        Parent: ObjInfo option
        /// the struct of the fields the class itself declares
        Part: Ent
        /// the struct of the fields of the whole chain: `base` (the parent's chain) and `own`
        Chain: Ent
        /// the virtual members it introduces: compiled name and the type of the function value
        Slots: (string * Ty) list
        /// the struct of function values that holds the members above
        Table: Ent option
        IsAbstract: bool
        IsLocal: bool
        /// the class's type parameters (its structs and its object type are generic in them)
        Gens: string list
        /// the type arguments it gives its base class, in terms of its own type parameters
        ParentArgs: Fable.Type list
    }

let tObj = TPrim "fable_rt.Obj"
/// `obj`: an object (of a class, or a boxed value), or null
let tAny = TOpt tObj

/// An object of a class where it is used (a member called, a field read): checked for null,
/// which raises .NET's NullReferenceException; an object known to be one (`this`) as it is
let asObj (x: Expr) : Expr =
    match typeOf x with
    | TOpt t when t = tObj -> ERt("fable_rt.objNonNull($0)", [ x ], tObj)
    | _ -> x

/// Is the expression an object made right there (never null)?
let isMadeObject (e: Fable.Expr) : bool =
    match e with
    | Fable.Call(_, { MemberRef = Some(Fable.MemberRef(_, m)) }, _, _) -> m.CompiledName = ".ctor"
    | Fable.ObjectExpr _ -> true
    | _ -> false

/// `asObj` of what `x` lowered to: no check where `x` is known not to be null (an object made
/// there, or a variable bound to one: `Ctx.NonNull`), only the object read out of the option
let asObjOf (ctx: Ctx) (x: Fable.Expr) (ir: Expr) : Expr =
    let known =
        match x with
        | Fable.IdentExpr i -> ctx.NonNull.Contains i.Name
        | _ -> isMadeObject x

    match typeOf ir with
    | TOpt t when t = tObj && known -> EGet(ir, PSome, tObj)
    | _ -> asObj ir

/// Check `ir` (the lowered receiver of `x`) for null when needed and project its `Obj` as a
/// borrow without `dup`/`drop`. Binds non-variable optionals first so literal `null` never
/// produces comptime `(@as(?Obj, null)).?` in Zig.
let withBorrowedObj (ctx: Ctx) (x: Fable.Expr) (ir: Expr) (k: Expr -> Expr) : Expr =
    let known =
        match x with
        | Fable.IdentExpr i -> ctx.NonNull.Contains i.Name
        | _ -> isMadeObject x

    match typeOf ir with
    | TOpt t when t = tObj ->
        let step (vExpr: Expr) =
            let proj = EGet(vExpr, PSome, tObj)

            if known then
                k proj
            else
                ctx.State.UsesRuntime <- true
                ESeq(ERt("fable_rt.checkNonNull($0)", [ vExpr ], tVoid), k proj)

        match ir with
        | EVar _ -> step ir
        | _ ->
            let v = ctx.State.NewVar("obj", typeOf ir, VLocal, false)
            ELet(v, ir, step (EVar v))
    | _ -> k ir

let isFatIfaceTy (ty: Ty) : bool =
    match ty with
    | TEnt({ Kind = KIface }, _)
    | TOpt(TEnt({ Kind = KIface }, _)) -> true
    | _ -> false

/// Check `ir` (the lowered fat-pointer interface receiver of `x`) for null when needed and
/// project its `fable_rt.Iface(Vt)` as a borrow without `dup`/`drop`.
let withBorrowedIface (ctx: Ctx) (x: Fable.Expr) (ir: Expr) (k: Expr -> Expr) : Expr =
    let known =
        match x with
        | Fable.IdentExpr i -> ctx.NonNull.Contains i.Name
        | _ -> isMadeObject x

    match typeOf ir with
    | TOpt(TEnt({ Kind = KIface }, _) as ifaceTy) ->
        let step (vExpr: Expr) =
            let proj = EGet(vExpr, PSome, ifaceTy)

            if known then
                k proj
            else
                ctx.State.UsesRuntime <- true
                ESeq(ERt("fable_rt.checkNonNull($0)", [ vExpr ], tVoid), k proj)

        match ir with
        | EVar _ -> step ir
        | _ ->
            let v = ctx.State.NewVar("iface", typeOf ir, VLocal, false)
            ELet(v, ir, step (EVar v))
    | _ -> k ir

/// The names that `e` reads. (Not those read only by a binding of a read that is itself never
/// read: such bindings are left out.) One walk of `e`.
let rec namesRead (e: Fable.Expr) : Set<string> =
    match e with
    | Fable.IdentExpr i -> Set.singleton i.Name
    | Fable.Let(other, (Fable.Get(Fable.IdentExpr _, _, _, _) | Fable.IdentExpr _ as value), body) when
        not other.IsMutable
        ->
        let inBody = namesRead body

        if inBody.Contains other.Name then
            Set.union (inBody.Remove other.Name) (namesRead value)
        else
            inBody
    | _ ->
        AST.getSubExpressions e
        |> List.fold (fun acc x -> Set.union acc (namesRead x)) Set.empty

let liveUse (name: string) (e: Fable.Expr) : bool = (namesRead e).Contains name

/// The targets of a decision tree, where each that several leaves reach and that is not small
/// is a call of a function of its own: otherwise its code would be written out once per leaf,
/// and a target that holds the rest of a match (as a `when` that fails goes on to) would
/// multiply with each.
let internal sharedTargetCount =
    new System.Threading.ThreadLocal<int ref>(fun () -> ref 0)

let sharedTargets
    (targets: (Fable.Ident list * Fable.Expr) list)
    (expr: Fable.Expr)
    : (Fable.Ident * Fable.Expr) list * (Fable.Ident list * Fable.Expr) list
    =
    let uses = Array.zeroCreate (List.length targets)

    let rec count (e: Fable.Expr) =
        match e with
        | Fable.DecisionTreeSuccess(i, values, _) ->
            if i < uses.Length then
                uses[i] <- uses[i] + 1

            values |> List.iter count
        // (a tree inside has targets of its own)
        | Fable.DecisionTree _ -> ()
        | _ -> AST.getSubExpressions e |> List.iter count

    count expr

    let rec size (limit: int) (e: Fable.Expr) : int =
        if limit <= 0 then
            0
        else
            AST.getSubExpressions e
            |> List.fold
                (fun acc x ->
                    if acc >= limit then
                        acc
                    else
                        acc + size (limit - acc) x
                )
                1

    let fns = List<Fable.Ident * Fable.Expr>()

    let small =
        targets
        |> List.mapi (fun i (ids, body) ->
            if uses[i] > 1 && size 40 body >= 40 then
                sharedTargetCount.Value.Value <- sharedTargetCount.Value.Value + 1

                let unitArg = AST.makeTypedIdent Fable.Unit "unitVar"

                let args =
                    if ids.IsEmpty then
                        [ unitArg ]
                    else
                        ids

                let fnId =
                    AST.makeTypedIdent
                        (Fable.DelegateType(args |> List.map (fun a -> a.Type), body.Type))
                        $"match_target_%d{sharedTargetCount.Value.Value}"

                let call =
                    Fable.CurriedApply(
                        Fable.IdentExpr fnId,
                        (if ids.IsEmpty then
                             [ Fable.Value(Fable.UnitConstant, None) ]
                         else
                             ids |> List.map Fable.IdentExpr),
                        body.Type,
                        None
                    )

                fns.Add((fnId, Fable.Delegate(args, body, None, [])))
                ids, call
            else
                ids, body
        )

    List.ofSeq fns, small

/// The .NET members of the Fable2Zig.Dotnet.*.fs files, which come after this file, by the name
/// of their block: set by Fable2Zig.fs. Each gives the lowered call, or null when the member is
/// not one of its own; `dotnetCall` asks each where its cases were among its own.
let mutable domainCalls
    : string -> Ctx -> SourceLocation option -> string -> string -> Fable.CallInfo -> Fable.Type -> Expr =
    fun _ _ _ _ _ _ _ -> Unchecked.defaultof<Expr>

let (|DomainCall|_|)
    (domain: string)
    (ctx: Ctx)
    (r: SourceLocation option)
    (info: Fable.CallInfo)
    (t: Fable.Type)
    (entity: string, name: string, _: Fable.Expr list)
    : Expr option
    =
    let lowered = domainCalls domain ctx r entity name info t

    if obj.ReferenceEquals(lowered, null) then
        None
    else
        Some lowered

/// Is the function bound to `name` only given as a value in `e`, never called there? Then it is
/// one value, made once (a delegate given to `AddHandler` and then to `RemoveHandler` is the
/// same delegate, as on .NET), rather than a function of the file made into a value at each use.
let onlyAsValue (name: string) (e: Fable.Expr) : bool =
    let mutable called = false
    let mutable used = false

    let rec walk (e: Fable.Expr) =
        match e with
        | Fable.Call(Fable.IdentExpr i, info, _, _) when i.Name = name ->
            called <- true
            info.Args |> List.iter walk
        | Fable.CurriedApply(Fable.IdentExpr i, args, _, _) when i.Name = name ->
            called <- true
            args |> List.iter walk
        | Fable.IdentExpr i when i.Name = name -> used <- true
        | _ -> AST.getSubExpressions e |> List.iter walk

    walk e
    used && not called

/// A dictionary: .NET's, or what F#'s `dict` and `readOnlyDict` give
let isDictionaryName (name: string) =
    name = "System.Collections.Generic.Dictionary`2"
    || name = "System.Collections.Generic.IDictionary`2"
    || name = "System.Collections.Generic.IReadOnlyDictionary`2"


let isClassEntity (ent: Fable.Entity) =
    not (
        ent.IsFSharpRecord
        || ent.IsFSharpUnion
        || ent.IsInterface
        || ent.IsFSharpModule
        || ent.IsFSharpExceptionDeclaration
        || ent.IsValueType
    )

/// A class of the program that derives from .NET's `Dictionary` or `HashSet` and adds only
/// members (no fields, no overrides): the collection it is, here, as its base type with the
/// class's type arguments put in
let collectionBase (com: Compiler) (t: Fable.Type) : Fable.Type option =
    match t with
    | Fable.DeclaredType(entRef, genArgs) ->
        match entRef.Path with
        | Fable.SourcePath _ ->
            match com.TryGetEntity entRef with
            | Some ent when isClassEntity ent ->
                match ent.BaseType with
                | Some bt when
                    (bt.Entity.FullName = "System.Collections.Generic.Dictionary`2"
                     || bt.Entity.FullName = "System.Collections.Generic.HashSet`1")
                    && ent.FSharpFields |> List.forall (fun f -> f.IsStatic)
                    && not (
                        ent.MembersFunctionsAndValues
                        |> Seq.exists (fun m -> m.IsOverrideOrExplicitInterfaceImplementation)
                    )
                    ->
                    let subst =
                        List.zip (ent.GenericParameters |> List.map (fun g -> g.Name)) genArgs
                        |> Map.ofList

                    let rec put (t: Fable.Type) =
                        match t with
                        | Fable.GenericParam(name, _, _) when subst.ContainsKey name -> subst[name]
                        | Fable.Array(item, kind) -> Fable.Array(put item, kind)
                        | Fable.List item -> Fable.List(put item)
                        | Fable.Option(item, isStruct) -> Fable.Option(put item, isStruct)
                        | Fable.Tuple(items, isStruct) -> Fable.Tuple(List.map put items, isStruct)
                        | Fable.DeclaredType(e, args) -> Fable.DeclaredType(e, List.map put args)
                        | Fable.LambdaType(a, b) -> Fable.LambdaType(put a, put b)
                        | other -> other

                    if ent.GenericParameters.Length = genArgs.Length then
                        Some(Fable.DeclaredType(bt.Entity, List.map put bt.GenericArgs))
                    else
                        None
                | _ -> None
            | _ -> None
        | _ -> None
    | _ -> None

/// A class that derives from `System.Exception` (`inherit exn(message)`): an exception here,
/// whose payload is its message and its fields
let isExceptionClass (ent: Fable.Entity) =
    isClassEntity ent
    && (
        match ent.BaseType with
        | Some bt -> bt.Entity.FullName = "System.Exception"
        | None -> false
    )

/// .NET's name of a type: `Probe+Circle` for a class in module `Probe`.
let rec dotnetTypeName (com: Compiler) (ent: Fable.Entity) : string =
    match ent.DeclaringEntity with
    | Some d ->
        match com.TryGetEntity d with
        // (a namespace is not a type: the name is the namespace's, then a dot)
        | Some outer when outer.IsNamespace -> ent.FullName
        | Some outer -> dotnetTypeName com outer + "+" + ent.CompiledName
        | None -> ent.FullName
    | None -> ent.FullName

/// .NET's value types that are records of the library (as the library's file and record): their
/// `%A` and `%O` are their `ToString`
let libraryValueTypes =
    dict
        [
            "System.Uri", ("Uri", "UriOf")
            "System.Guid", ("Guid", "GuidOf")
            "System.TimeSpan", ("TimeSpan", "TimeSpanOf")
            "System.DateTime", ("DateTime", "DateTimeOf")
            "System.DateTimeOffset", ("DateTimeOffset", "DateTimeOffsetOf")
            "System.DateOnly", ("DateOnly", "DateOnlyOf")
            "System.TimeOnly", ("DateOnly", "TimeOnlyOf")
        ]

/// A class of the program with no constructor, fields or instance members (as the witness types
/// of SRTP, `type Parse = static member ...`): its only value is null, which nothing can use;
/// it is `void` here
let isWitnessClass (ctx: Ctx) (entRef: Fable.EntityRef) : bool =
    match entRef.Path with
    | Fable.SourcePath _ ->
        match ctx.Com.TryGetEntity entRef with
        | Some ent ->
            not ent.IsInterface
            && not ent.IsFSharpRecord
            && not ent.IsFSharpUnion
            && not ent.IsFSharpModule
            && not ent.IsValueType
            && not ent.IsFSharpExceptionDeclaration
            && ent.BaseType.IsNone
            && ent.FSharpFields.IsEmpty
            && Seq.isEmpty ent.DeclaredInterfaces
            && ent.MembersFunctionsAndValues
               |> Seq.forall (fun m -> not m.IsInstance && not m.IsConstructor)
        | None -> false
    | _ -> false

/// .NET's types of regular expressions, as the records of the library's Regex.fs
let regexTypes =
    dict
        [
            "System.Text.RegularExpressions.Regex", "RegexOf"
            "System.Text.RegularExpressions.Match", "MatchOf"
            "System.Text.RegularExpressions.Group", "GroupOf"
            "System.Text.RegularExpressions.Capture", "GroupOf"
            "System.Text.RegularExpressions.MatchCollection", "MatchCollectionOf"
            "System.Text.RegularExpressions.GroupCollection", "GroupCollectionOf"
        ]
