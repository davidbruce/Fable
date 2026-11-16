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

let private paramTypesOf (m: Fable.MemberFunctionOrValue) =
    m.CurriedParameterGroups |> List.concat |> List.map (fun p -> p.Type)

/// The dispatch slots of an interface (a property is there as itself and as its getter)
let private dispatchSlots (ent: Fable.Entity) =
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

let interfaceMembers (ent: Fable.Entity) : (string * Fable.Type list * Fable.Type) list =
    dispatchSlots ent
    |> Seq.distinctBy (fun m -> slotKey ent m.CompiledName (paramTypesOf m))
    // (a generic member, `abstract eval<'a>: ...`, is no field of the struct: a function value
    // has one type; calls of it are refused)
    |> Seq.filter (fun m ->
        let own = ent.GenericParameters |> List.map (fun g -> g.Name) |> set

        let rec foreign (t: Fable.Type) =
            match t with
            | Fable.GenericParam(name, _, _) -> not (own.Contains name)
            | t -> t.Generics |> List.exists foreign

        let types =
            m.ReturnParameter.Type
            :: (m.CurriedParameterGroups |> List.concat |> List.map (fun p -> p.Type))

        not (List.exists foreign types)
    )
    |> Seq.map (fun m ->
        let args =
            match m.CurriedParameterGroups |> List.concat |> List.map (fun p -> p.Type) with
            | [] -> [ Fable.Unit ]
            | ts -> ts

        slotKey ent m.CompiledName (paramTypesOf m), args, m.ReturnParameter.Type
    )
    |> List.ofSeq

/// Substitute type parameters in a Fable AST type using `subst`.
/// The constructors of the classes of the file being compiled: their declaration's name, their
/// member, and the types of their parameters, by the class's full name (see `lowerFile`)
/// (Fable compiles files at once on several threads, each file whole on a thread of its own, see
/// Fable2Zig.transformFile: what belongs to the file being compiled is kept per thread)
let private fileCtorsHere =
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
let private isMutableRuntimeCellName (name: string) =
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
let private sharedTargetCount =
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

/// Unwrap F# 9 nullness (`T | null` = `Fable.Nullable(t, false)`), leaving `System.Nullable<T>` untouched.
let rec unwrapNullness (t: Fable.Type) : Fable.Type =
    match t with
    | Fable.Nullable(inner, false) -> unwrapNullness inner
    | _ -> t

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
        // (Zig's u16 is a char here: a uint16 is a type of its own of the same size)
        | UInt16 -> TPrim "c_ushort"
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
        | BigInt -> TPrim "fable_rt.BigInt"
        | Decimal -> TPrim "fable_rt.NetDecimal"
    | Fable.String -> tStr
    // (a unit argument stays, as `void`: a function value has one shape whatever its type
    // parameters stand for)
    | Fable.LambdaType(arg, ret) -> TFn([ mapType ctx r arg ], mapType ctx r ret)
    // (a delegate of no parameters, `delegate of unit -> int`: as a function value here, it takes
    // the unit)
    | Fable.DelegateType([], ret) -> TFn([ tVoid ], mapType ctx r ret)
    | Fable.DelegateType(args, ret) -> TFn(args |> List.map (mapType ctx r), mapType ctx r ret)
    | Fable.Tuple(ts, _) -> TTuple(ts |> List.map (mapType ctx r))
    // (`Tuple<'T>`, which F# does not write as a tuple)
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "System.Tuple`1" || ent.FullName = "System.ValueTuple`1" ->
        TTuple [ mapType ctx r t ]
    // (`None` and `[]` whose item type F# leaves as `obj` are of `obj` here too)
    | Fable.Option(t, _) -> TOpt(mapType ctx r t)
    // (`Nullable<T>`: an option; `T | null`: the same Zig type when already nullable here)
    | Fable.Nullable(t, false) ->
        let inner = mapType ctx r t

        match t with
        | Fable.String
        | Fable.Any
        | Fable.MetaType -> inner
        | Fable.Array(_, (Fable.MutableArray | Fable.ImmutableArray)) -> inner
        | _ when (objOfType ctx r t).IsSome -> inner
        | Fable.DeclaredType(ent, _) when
            (match ctx.Com.TryGetEntity ent with
             | Some e -> e.IsInterface
             | None -> false)
            && (
                match inner with
                | TOpt _ -> true
                | _ -> false
            )
            ->
            inner
        | _ -> TOpt inner
    | Fable.Nullable(t, true) -> TOpt(mapType ctx r t)
    // (reflection: the runtime's fable_reflect.zig)
    | Fable.MetaType -> TPrim "fable_rt.reflect.Type"
    // (quotations and their variables: objects of the library's Quotation.fs; a method by its name)
    | Fable.DeclaredType(ent, _) when
        ent.FullName = "Microsoft.FSharp.Quotations.FSharpExpr"
        || ent.FullName = "Microsoft.FSharp.Quotations.FSharpExpr`1"
        || ent.FullName = "Microsoft.FSharp.Quotations.FSharpVar"
        ->
        tAny
    | Fable.DeclaredType(ent, []) when
        ent.FullName = "System.Reflection.MethodInfo"
        || ent.FullName = "System.Reflection.MethodBase"
        ->
        tStr
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Type" -> TPrim "fable_rt.reflect.Type"
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Reflection.PropertyInfo" ->
        TPrim "fable_rt.reflect.Property"
    | Fable.DeclaredType(ent, []) when ent.FullName = "Microsoft.FSharp.Reflection.UnionCaseInfo" ->
        TPrim "fable_rt.reflect.UnionCase"
    | Fable.List t -> TEnt(listEnt ctx.State, [ mapType ctx r t ])
    | Fable.Array(t, Fable.ResizeArray) -> TEnt(netEnt ctx.State "ResizeArray", [ mapType ctx r t ])
    | Fable.AnonymousRecordType(names, genArgs, _) ->
        TEnt(anonEnt ctx.State names, genArgs |> List.map (FableTransforms.uncurryType >> mapTypeArg ctx r))
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "System.Lazy`1" -> TEnt(lazyEnt ctx.State, [ mapType ctx r t ])
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "System.WeakReference`1" ->
        TEnt(netEnt ctx.State "Weak", [ mapType ctx r t ])
    // a byref: a pointer (`inref` to what cannot be assigned)
    | Fable.DeclaredType(ent, [ t; kind ]) when ent.FullName = "Microsoft.FSharp.Core.byref`2" ->
        let isIn =
            match kind with
            | Fable.DeclaredType(k, _) -> k.FullName.EndsWith(".In", System.StringComparison.Ordinal)
            | _ -> false

        TPtr(mapType ctx r t, isIn)
    // a native pointer (`NativePtr.stackalloc`): a many-item pointer; `voidptr`: an opaque one
    | Fable.DeclaredType(ent, [ t ]) when
        ent.FullName = "nativeptr`1"
        || ent.FullName = "Microsoft.FSharp.Core.nativeptr`1"
        ->
        TPrim("[*]" + zigType (mapType ctx r t))
    | Fable.DeclaredType(ent, []) when ent.FullName = "voidptr" || ent.FullName = "System.Void*" -> TPrim "*anyopaque"
    // a span: a slice of what it views
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "System.Span`1" || ent.FullName = "System.ReadOnlySpan`1" ->
        TSlice(mapType ctx r t, ent.FullName = "System.ReadOnlySpan`1")
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Text.StringBuilder" ->
        TEnt(netEnt ctx.State "StringBuilder", [])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Random" -> TEnt(netEnt ctx.State "Random", [])
    | Fable.Array(t, _) -> TEnt(arrayEnt ctx.State, [ mapType ctx r t ])
    | Fable.DeclaredType(ent, [ k; v ]) when isDictionaryName ent.FullName ->
        TEnt(netEnt ctx.State "Dictionary", [ mapType ctx r k; mapType ctx r v ])
    // (`d.Keys` and `d.Values`: the list of them)
    | Fable.DeclaredType(ent, [ k; _ ]) when ent.FullName = "System.Collections.Generic.Dictionary`2.KeyCollection" ->
        TEnt(listEnt ctx.State, [ mapType ctx r k ])
    | Fable.DeclaredType(ent, [ _; v ]) when ent.FullName = "System.Collections.Generic.Dictionary`2.ValueCollection" ->
        TEnt(listEnt ctx.State, [ mapType ctx r v ])
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "System.Collections.Generic.HashSet`1" ->
        TEnt(netEnt ctx.State "HashSet", [ mapType ctx r t ])
    | Fable.GenericParam(name = name) -> TGen name
    | Fable.DeclaredType(ent, _) when dotnetExceptions.ContainsKey ent.FullName -> tExn
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = refName -> TEnt(refEnt ctx.State, [ mapType ctx r t ])
    | Fable.DeclaredType(ent, _) when (tryExnEnt ctx r ent).IsSome -> tExn
    // (a class whose only value is null: nothing)
    | Fable.DeclaredType(ent, _) when isWitnessClass ctx ent -> tVoid
    // (an object of a class: null or the object, as on .NET)
    | Fable.DeclaredType(ent, _) when (objInfo ctx r ent).IsSome -> TOpt tObj
    // an async computation: the record of the library's Async.fs; the builder has no state
    // (F#'s `Event<'T>`: the record of the library's Event.fs)
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpEvent`1" ->
        TEnt(libRecordEnt ctx "Event" "EventOf_1", [ mapType ctx r item ])
    // (`Event<'Delegate, 'Args>`: of a delegate of the sender and the arguments)
    | Fable.DeclaredType(ent, [ _; args ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpEvent`2" ->
        TEnt(libRecordEnt ctx "Event" "DelegateEventOf_1", [ mapType ctx r args ])
    // (a unit of measure given as a type argument: nothing here; the numbers it marks are
    // plain numbers)
    | Fable.Measure _ -> tVoid
    | Fable.DeclaredType(ent, _) when
        ent.FullName.StartsWith("Microsoft.FSharp.Core.CompilerServices.Measure", System.StringComparison.Ordinal)
        ->
        tVoid
    // (.NET's `Uri`, `Guid`, `TimeSpan`, the dates and times: records of the library)
    | Fable.DeclaredType(ent, []) when libraryValueTypes.ContainsKey ent.FullName ->
        let file, record = libraryValueTypes[ent.FullName]
        TEnt(libRecordEnt ctx file record, [])
    // (.NET's stack and queue: records of the library's Stack.fs and Queue.fs)
    // (.NET's regular expressions: records of the library's Regex.fs)
    | Fable.Regex -> TEnt(libRecordEnt ctx "Regex" "RegexOf", [])
    | Fable.DeclaredType(ent, []) when regexTypes.ContainsKey ent.FullName ->
        TEnt(libRecordEnt ctx "Regex" regexTypes[ent.FullName], [])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.IO.DirectoryInfo" ->
        TEnt(libRecordEnt ctx "Path" "DirectoryInfoOf", [])
    // (what `Parallel.For` gives: nothing here)
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.Tasks.ParallelLoopResult" -> tVoid
    // (`Comparer<'T>`, as `Comparer<'T>.Default` gives it: the IComparer it is used as)
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.Comparer`1" ->
        mapType
            ctx
            r
            (Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IComparer`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ item ]
            ))
    // (.NET's text encodings: the runtime's TextEncoding, UTF-8 or UTF-16)
    | Fable.DeclaredType(ent, []) when
        ent.FullName = "System.Text.Encoding"
        || ent.FullName = "System.Text.UTF8Encoding"
        || ent.FullName = "System.Text.UnicodeEncoding"
        ->
        TPrim "fable_rt.TextEncoding"
    // (`IList<'T>`, as an array is seen through it: the array; `System.Array`: an array of objects)
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.IList`1" ->
        mapType ctx r (Fable.Array(item, Fable.MutableArray))
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Array" ->
        mapType ctx r (Fable.Array(Fable.Any, Fable.MutableArray))
    // (`IComparable`, as F# types a key whose type it leaves open (`Map []`): an object, as on
    // .NET, which compares by what it holds)
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.IComparable" -> tAny
    // (.NET's threads: the runtime's ThreadOf)
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.Thread" -> TPrim "fable_rt.ThreadOf"
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Diagnostics.Stopwatch" ->
        TEnt(libRecordEnt ctx "Stopwatch" "StopwatchOf", [])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.Stack`1" ->
        TEnt(libRecordEnt ctx "Stack" "StackOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ k; v ]) when ent.FullName = "System.Runtime.CompilerServices.ConditionalWeakTable`2" ->
        TEnt(libRecordEnt ctx "ConditionalWeakTable" "ConditionalWeakTableOf_2", [ mapType ctx r k; mapType ctx r v ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Core.CompilerServices.ListCollector`1" ->
        TEnt(libRecordEnt ctx "ListCollector" "ListCollectorOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.Queue`1" ->
        TEnt(libRecordEnt ctx "Queue" "QueueOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpAsync`1" ->
        TEnt(libRecordEnt ctx "Async" "AsyncOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, []) when ent.FullName = "Microsoft.FSharp.Control.FSharpAsyncBuilder" -> tVoid
    // (.NET's cancellation: records of the library's Async.fs; a registration is what disposes it)
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.CancellationTokenSource" ->
        TEnt(libRecordEnt ctx "Async" "CancellationSource", [])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.CancellationToken" ->
        TEnt(libRecordEnt ctx "Async" "CancellationTokenOf", [])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.CancellationTokenRegistration" ->
        mapType
            ctx
            r
            (Fable.DeclaredType(
                {
                    FullName = "System.IDisposable"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                []
            ))
    // a task and what the builder makes of `task { }`: records of the library's Task.fs; the
    // builder has no state
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Threading.Tasks.Task`1" ->
        TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.Tasks.Task" ->
        TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ tVoid ])
    // (a task's awaiter is the task itself)
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Runtime.CompilerServices.TaskAwaiter`1" ->
        TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Runtime.CompilerServices.TaskAwaiter" ->
        TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ tVoid ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpMailboxProcessor`1" ->
        TEnt(libRecordEnt ctx "Async" "MailboxOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpAsyncReplyChannel`1" ->
        TEnt(libRecordEnt ctx "Async" "ReplyChannelOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Threading.Tasks.TaskCompletionSource`1" ->
        TEnt(libRecordEnt ctx "Task" "TaskSourceOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = taskCodeName ->
        TEnt(libRecordEnt ctx "Task" "TaskCode_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, []) when ent.FullName = "Microsoft.FSharp.Control.TaskBuilder" -> tVoid
    // a sequence: the record of the library's Seq.fs
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.IEnumerable`1" ->
        TEnt(seqEnt ctx, [ mapTypeArg ctx r item ])
    // (an entry of a map, as a `for ... in` loop over the map gives it: a pair here)
    | Fable.DeclaredType(ent, [ k; v ]) when ent.FullName = "System.Collections.Generic.KeyValuePair`2" ->
        TTuple [ mapType ctx r k; mapType ctx r v ]
    // (what `Map.keys` and `Map.values` give: a list here, which is what they hold, in order)
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.ICollection`1" ->
        TEnt(listEnt ctx.State, [ mapType ctx r item ])
    | Fable.DeclaredType(ent, genArgs) when ent.FullName = mapName || ent.FullName = setName ->
        TEnt(treeEnt ctx (ent.FullName = mapName), genArgs |> List.map (mapTypeArg ctx r))
    // (an interface of .NET's, `IDisposable`: a struct of function values as the program's own
    // interfaces are, of the runtime's type for its member names, so that it is one type in
    // every file)
    | Fable.DeclaredType(ent, genArgs) when
        (match ent.Path with
         | Fable.SourcePath _ -> false
         | _ -> true)
        && (
            match ctx.Com.TryGetEntity ent with
            | Some e -> e.IsInterface
            | None -> false
        )
        ->
        let e = ctx.Com.GetEntity ent

        let subst =
            List.zip (e.GenericParameters |> List.map (fun g -> g.Name)) genArgs
            |> Map.ofList

        let members =
            allInterfaceMembers ctx.Com e subst |> List.sortBy (fun (_, n, _, _) -> n)

        TOpt(
            TEnt(
                ifaceAnonEnt ctx.State (members |> List.map (fun (_, n, _, _) -> n) |> Array.ofList),
                // (functions in the signatures as values have them: uncurried)
                members
                |> List.map (fun (_, _, args, ret) ->
                    TSlot(
                        args |> List.map (FableTransforms.uncurryType >> mapType ctx r),
                        mapType ctx r (FableTransforms.uncurryType ret)
                    )
                )
            )
        )
    | Fable.DeclaredType(ent, genArgs) ->
        let ty = TEnt(entOf ctx r ent, genArgs |> List.map (mapTypeArg ctx r))

        match ctx.Com.TryGetEntity ent with
        | Some e when e.IsInterface -> TOpt ty
        | _ -> ty
    | Fable.Any -> tAny

/// A type argument (`obj`, as for the item type of something empty, is `obj` here too).
and mapTypeArg (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : Ty =
    match t with
    | Fable.Any -> tAny
    | _ -> mapType ctx r t

/// The record or union behind an entity reference. Immutable, non-recursive records and
/// unions are plain Zig values: a `struct`, or a `union(enum)` with one payload per case.
/// A union that contains itself is a handle: a `union(enum)` whose cases with fields point to
/// reference-counted cells. (A record that reaches itself only through such unions is still a
/// plain value.)
and entOf (ctx: Ctx) (r: SourceLocation option) (entRef: Fable.EntityRef) : Ent =
    match ctx.State.Ents.TryGetValue entRef.FullName with
    | true, e -> e
    | _ when entRef.FullName = resultName -> resultEnt ctx.State
    | _ when entRef.FullName.StartsWith("Microsoft.FSharp.Core.FSharpChoice`", System.StringComparison.Ordinal) ->
        choiceEnt ctx.State entRef.FullName
    | _ ->
        let ent =
            match ctx.Com.TryGetEntity entRef with
            | Some e -> e
            | None -> fail r "the Zig target cannot find the type %s" entRef.FullName

        let isStruct =
            ent.IsValueType
            && not (ent.IsFSharpRecord || ent.IsFSharpUnion || ent.IsInterface || ent.IsFSharpModule)

        if not (ent.IsFSharpRecord || ent.IsFSharpUnion || ent.IsInterface || isStruct) then
            fail r "the Zig target does not support the type %s yet" entRef.FullName

        let recursive = reachesSelf ctx.Com true ent

        // (a record or union compared by reference, `[<ReferenceEquality>]` or `[<NoEquality>]`
        // without an `Equals` of its own: its values are cells, so that each has an identity)
        let byReference =
            (ent.IsFSharpRecord || ent.IsFSharpUnion)
            && not ent.IsValueType
            && (ent.Attributes
                |> Seq.exists (fun a -> a.Entity.FullName = "Microsoft.FSharp.Core.ReferenceEqualityAttribute")
                || ent.Attributes
                   |> Seq.exists (fun a -> a.Entity.FullName = "Microsoft.FSharp.Core.NoEqualityAttribute")
                   && not (
                       ent.MembersFunctionsAndValues
                       |> Seq.exists (fun m ->
                           m.IsOverrideOrExplicitInterfaceImplementation && m.CompiledName = "Equals"
                       )
                   ))

        // A record that can be assigned to (and is not a struct), or that contains itself, is a
        // reference: a pointer to a counted cell.
        let isReference =
            ent.IsFSharpRecord
            && (byReference
                || (recursive && reachesSelf ctx.Com false ent)
                || (not ent.IsValueType
                    && (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                       |> List.exists (fun f -> f.IsMutable)))

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
                    if ent.IsInterface then
                        KIface
                    elif isReference then
                        KRefRecord
                    elif not ent.IsFSharpUnion then
                        KRecord
                    elif recursive || byReference then
                        KHeapUnion
                    else
                        KValueUnion
                TypeParams = ent.GenericParameters |> List.map (fun g -> g.Name)
                Cases = []
                MutableFields =
                    if ent.IsFSharpRecord || isStruct then
                        (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                        |> List.filter (fun f -> f.IsMutable)
                        |> List.map (fun f -> f.Name)
                    else
                        []
                Managed = ent.IsInterface
                Cyclic = false
                ReachesOpaque = ent.IsInterface
                Copyable = true
                IsLocal = isLocal
                Hooks = None
                Overrides = []
            }

        if ent.IsInterface then
            ctx.State.UsesRuntime <- true

        // a resource: `IResource<'T>` (destroyed after its last use, move-only) or
        // `ISharedResource<'T>` (copies share it)
        let resourceKind =
            if ent.IsInterface then
                Seq.empty
            else
                ent.DeclaredInterfaces
            |> Seq.map (fun i -> i.Entity.FullName)
            |> Seq.fold
                (fun acc n ->
                    if n.EndsWith("ISharedResource`1", System.StringComparison.Ordinal) then
                        Some true
                    elif n.EndsWith("IResource`1", System.StringComparison.Ordinal) && acc.IsNone then
                        Some false
                    else
                        acc
                )
                None

        match resourceKind with
        | Some shared ->
            if e.Kind = KHeapUnion || e.Kind = KRefRecord then
                fail
                    r
                    "%s: a record that can be assigned or a type that contains itself is already a counted reference; IResource is for values that stand for something outside the program"
                    entRef.FullName

            if not ent.GenericParameters.IsEmpty then
                fail r "the Zig target does not support generic resources yet (%s)" entRef.FullName

            let hook (member': string) =
                ent.MembersFunctionsAndValues
                |> Seq.tryFind (fun m ->
                    m.CompiledName.IndexOf("Resource<", System.StringComparison.Ordinal) >= 0
                    && m.CompiledName.EndsWith("." + member', System.StringComparison.Ordinal)
                )
                |> Option.map (fun m -> implName name m.CompiledName)

            let destroy =
                match hook "Destroy" with
                | Some d -> d
                | None -> fail r "%s: a resource needs its static member Destroy" entRef.FullName

            e.Hooks <-
                Some(
                    destroy,
                    if shared then
                        hook "Dup"
                    else
                        None
                )

            e.Copyable <- shared
        | None -> ()

        // the `Equals`, `GetHashCode` and `IComparable.CompareTo` of its own, which `=`, `hash`
        // and `compare` call (F#'s own for a record or a union unless it says otherwise)
        let hasAttr (name: string) =
            ent.Attributes |> Seq.exists (fun a -> a.Entity.FullName = name)

        let ownEquality =
            not (ent.IsFSharpRecord || ent.IsFSharpUnion)
            || hasAttr "Microsoft.FSharp.Core.CustomEqualityAttribute"
            || hasAttr "Microsoft.FSharp.Core.NoEqualityAttribute"

        let ownComparison =
            not (ent.IsFSharpRecord || ent.IsFSharpUnion)
            || hasAttr "Microsoft.FSharp.Core.CustomComparisonAttribute"
            || hasAttr "Microsoft.FSharp.Core.NoComparisonAttribute"

        let declares (compiled: string) =
            ent.MembersFunctionsAndValues
            |> Seq.exists (fun m ->
                m.IsInstance
                && m.IsOverrideOrExplicitInterfaceImplementation
                && m.CompiledName = compiled
            )

        if isLocal && not ent.IsInterface then
            e.Overrides <-
                [
                    if byReference then
                        "fable_reference_equality", ""
                    if declares "ToString" && (ent.IsFSharpRecord || ent.IsFSharpUnion) then
                        "fable_to_string", name + "__ToString"
                    if ownEquality && declares "Equals" then
                        "fable_equals", name + "__Equals"
                    if ownEquality && declares "GetHashCode" then
                        "fable_hash", name + "__GetHashCode"
                    if ownComparison && declares "System.IComparable.CompareTo" then
                        "fable_compare", implName name "System.IComparable.CompareTo"
                ]

            if not e.Overrides.IsEmpty && not ent.GenericParameters.IsEmpty then
                fail
                    r
                    "the Zig target does not support Equals, GetHashCode or CompareTo of a generic type yet (%s)"
                    entRef.FullName

        ctx.State.Ents[entRef.FullName] <- e
        ctx.State.EntDepth <- ctx.State.EntDepth + 1

        try
            e.Cases <-
                if ent.IsInterface then
                    [
                        "",
                        allInterfaceMembers ctx.Com ent Map.empty
                        |> List.map (fun (_, name, args, ret) ->
                            // (functions in the signatures as values have them: uncurried)
                            name,
                            TSlot(
                                args |> List.map (FableTransforms.uncurryType >> mapType ctx r),
                                mapType ctx r (FableTransforms.uncurryType ret)
                            )
                        )
                    ]
                elif ent.IsFSharpUnion then
                    ent.UnionCases
                    |> List.map (fun c ->
                        c.Name,
                        c.UnionCaseFields
                        |> List.map (fun f -> f.Name, mapType ctx r (FableTransforms.uncurryType f.FieldType))
                    )
                else
                    [
                        "",
                        (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                        |> List.map (fun f ->
                            f.Name, mapType ctx r (FableTransforms.uncurryType (fieldTypeIn entRef f))
                        )
                    ]
        with _ ->
            ctx.State.EntDepth <- ctx.State.EntDepth - 1
            ctx.State.Ents.Remove entRef.FullName |> ignore
            reraise ()

        ctx.State.EntDepth <- ctx.State.EntDepth - 1

        if isLocal then
            ctx.State.LocalEnts.Add e

            // (what reflection says of it: .NET's name, and what it is)
            if ent.IsFSharpRecord || ent.IsFSharpUnion then
                ctx.State.NetTypes[e.Name] <-
                    (dotnetTypeName ctx.Com ent,
                     if ent.IsFSharpRecord then
                         "record"
                     else
                         "union")

        // (the types this one refers to are all known once the outermost one is finished)
        if ctx.State.EntDepth = 0 then
            settleManaged ctx.State

        e

/// The F# `exception` declaration behind an entity reference, if it is one. Its values have
/// the type `exn`; the declaration says what fields they have.
/// What is known of a class that takes part in inheritance: one that is abstract, derives from
/// a class, has virtual members, or that a class of the project derives from. (None for every
/// other type.)
and objInfo (ctx: Ctx) (r: SourceLocation option) (entRef: Fable.EntityRef) : ObjInfo option =
    match ctx.State.ObjInfos.TryGetValue entRef.FullName with
    | true, o when isNull o -> None
    | true, o -> Some(o :?> ObjInfo)
    | _ ->
        let found =
            match entRef.Path with
            | Fable.SourcePath _ ->
                match ctx.Com.TryGetEntity entRef with
                // (a struct is a value, not an object; a class deriving from System.Exception is
                // an exception)
                | Some ent when isClassEntity ent && not ent.IsValueType && not (isExceptionClass ent) -> Some ent
                | _ -> None
            | _ -> None

        match found with
        | None ->
            ctx.State.ObjInfos[entRef.FullName] <- null
            None
        | Some ent ->
            let gens = ent.GenericParameters |> List.map (fun g -> g.Name)

            let parentArgs =
                match ent.BaseType with
                | Some bt when bt.Entity.FullName <> "System.Object" -> bt.GenericArgs
                | _ -> []

            let parent =
                match ent.BaseType with
                | Some bt when bt.Entity.FullName <> "System.Object" ->
                    match objInfo ctx r bt.Entity with
                    | Some p -> Some p
                    | None -> fail r "the Zig target does not support deriving from %s yet" bt.Entity.FullName
                | _ -> None

            let name, isLocal =
                match FSharp2Fable.Util.entityIdent ctx.Com entRef with
                | Fable.IdentExpr id -> id.Name, true
                | Fable.Import(imp, _, _) -> importAlias ctx imp.Path + "." + imp.Selector, false
                | _ -> fail r "the Zig target cannot reference the type %s" entRef.FullName

            let synth (suffix: string) : Ent =
                {
                    Name = name + "__" + suffix
                    Ref =
                        {
                            FullName = entRef.FullName + "$" + suffix
                            Path = entRef.Path
                        }
                    Kind = KRecord
                    TypeParams = gens
                    Cases = []
                    MutableFields = []
                    Managed = false
                    Cyclic = false
                    ReachesOpaque = false
                    Copyable = true
                    IsLocal = isLocal
                    Hooks = None
                    Overrides = []
                }

            let part = synth "part"
            let chain = synth "chain"

            // (a property is there as itself and as its accessors: the accessors are the slots)
            let dispatch =
                ent.MembersFunctionsAndValues
                |> Seq.filter (fun m -> m.IsDispatchSlot && not m.IsProperty)
                |> List.ofSeq

            let table =
                if dispatch.IsEmpty then
                    None
                else
                    Some(synth "vt")

            let info =
                {
                    Ref = entRef
                    FullName = entRef.FullName
                    Prefix = name
                    Depth =
                        match parent with
                        | Some p -> p.Depth + 1
                        | None -> 0
                    Parent = parent
                    Part = part
                    Chain = chain
                    Slots = []
                    Table = table
                    IsAbstract = ent.IsAbstractClass
                    IsLocal = isLocal
                    Gens = gens
                    ParentArgs = parentArgs
                }

            // (registered before its fields are mapped: they may mention the class)
            ctx.State.ObjInfos[entRef.FullName] <- box info

            let fields =
                (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                |> List.map (fun f -> f.Name, mapType ctx r (FableTransforms.uncurryType (fieldTypeIn entRef f)))

            part.Cases <- [ "", fields ]
            part.MutableFields <- fields |> List.map fst

            chain.Cases <-
                [
                    "",
                    (match parent with
                     | Some p -> [ "base", TEnt(p.Chain, parentArgs |> List.map (mapTypeArg ctx r)) ]
                     | None -> [])
                    @ [ "own", TEnt(part, gens |> List.map TGen) ]
                ]

            let slots =
                dispatch
                |> List.map (fun m ->
                    let ps =
                        m.CurriedParameterGroups
                        |> List.concat
                        |> List.map (fun p -> mapType ctx r p.Type)

                    let ps =
                        if ps.IsEmpty then
                            [ tVoid ]
                        else
                            ps

                    m.CompiledName, TFn(tObj :: ps, mapType ctx r m.ReturnParameter.Type)
                )

            if (slots |> List.map fst |> List.distinct).Length <> slots.Length then
                fail r "the Zig target does not support overloaded virtual members yet (%s)" entRef.FullName

            match table with
            | Some vt -> vt.Cases <- [ "", slots ]
            | None -> ()

            let info = { info with Slots = slots }
            ctx.State.ObjInfos[entRef.FullName] <- box info

            for e in [ Some part; Some chain; table ] |> List.choose id do
                ctx.State.Ents[e.Ref.FullName] <- e

                if isLocal then
                    ctx.State.LocalEnts.Add e

            if ctx.State.EntDepth = 0 then
                settleManaged ctx.State

            Some info

/// The class of an object, if its type is one that takes part in inheritance.
and objOfType (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : ObjInfo option =
    match unwrapNullness t with
    | Fable.DeclaredType(e, _) -> objInfo ctx r e
    | _ -> None

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
        | Some ent when ent.IsFSharpExceptionDeclaration || isExceptionClass ent ->
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
                    Hooks = None
                    Overrides = []
                }

            ctx.State.Ents[entRef.FullName] <- e

            try
                let fields =
                    (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                    |> List.map (fun f -> f.Name, mapType ctx r (FableTransforms.uncurryType f.FieldType))

                // (a class: its message first, which its base constructor was given)
                e.Cases <-
                    [
                        "",
                        if isExceptionClass ent then
                            ("fable_message", tStr) :: fields
                        else
                            fields
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

/// F#'s `seq`: the record of the library's Seq.fs, around the function that starts a walk.
and seqEnt (ctx: Ctx) : Ent =
    match ctx.State.Ents.TryGetValue "$seq" with
    | true, e -> e
    | _ ->
        let e =
            {
                Name = libraryTarget ctx "Seq" "SeqOf_1"
                Ref =
                    {
                        FullName = "Fable.Library.Zig.Seq.SeqOf`1"
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KRecord
                TypeParams = [ "T" ]
                Cases = [ "", [ "fable_seq", TFn([ tVoid ], TEnt(walkEnt ctx, [ TGen "T" ])) ] ]
                MutableFields = []
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        ctx.State.Ents["$seq"] <- e
        e

/// A record of the library's (`AsyncOf_1` of Async.fs, `Cont_1`): what a program sees of it
/// is its type; its fields are the library's own business.
and libRecordEnt (ctx: Ctx) (file: string) (name: string) : Ent =
    let key = $"$lib:%s{file}.%s{name}"

    match ctx.State.Ents.TryGetValue key with
    | true, e -> e
    | _ ->
        let contTy () =
            TEnt(libRecordEnt ctx "Async" "Cont_1", [ TGen "T" ])

        let fields =
            match name with
            | "AsyncOf_1" -> [ "fable_async", TFn([ contTy () ], tVoid) ]
            | "Cont_1" ->
                [
                    "ok", TFn([ TGen "T" ], tVoid)
                    "fail", TFn([ tExn ], tVoid)
                    "cancel", TFn([ tExn ], tVoid)
                    "token", TEnt(libRecordEnt ctx "Async" "CancellationTokenOf", [])
                    "handOver", TOpt(TEnt(libRecordEnt ctx "Async" "HandOver", []))
                ]
            | "HandOver" -> [ "handedOver", tBool ]
            | "Timer" ->
                [
                    "due", TPrim "i64"
                    "order", tI32
                    "action", TFn([ tVoid ], tVoid)
                    "live", tBool
                ]
            | "CancellationSource" ->
                [
                    "cancelled", tBool
                    "handlers", TEnt(netEnt ctx.State "ResizeArray", [ TOpt(TFn([ tVoid ], tVoid)) ])
                    "disposed", tBool
                ]
            | "CancellationTokenOf" -> [ "source", TEnt(libRecordEnt ctx "Async" "CancellationSource", []) ]
            | "TaskOf_1" ->
                [
                    "fable_task", TOpt(TEnt(resultEnt ctx.State, [ TGen "T"; tExn ]))
                    "fable_thread", TOpt(TPrim "fable_rt.ThreadOf")
                ]
            | "TaskSourceOf_1" -> [ "task", TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ TGen "T" ]) ]
            | "ReplyChannelOf_1" -> [ "reply", TFn([ TGen "T" ], tVoid) ]
            // (its body takes the mailbox itself: what a program sees of it is a cell)
            | "MailboxOf_1" ->
                [
                    "queue", TEnt(netEnt ctx.State "ResizeArray", [ TGen "T" ])
                    "waiting", TOpt(TFn([ TGen "T" ], tVoid))
                    "started", tBool
                    "begun", tBool
                    "running", tBool
                    "turnToken", tI32
                ]
            | "TaskCode_1" -> [ "code", TFn([ tVoid ], TGen "T") ]
            | "StackOf_1" -> [ "items", TEnt(netEnt ctx.State "ResizeArray", [ TGen "T" ]) ]
            | "QueueOf_1" ->
                [
                    "items", TEnt(netEnt ctx.State "ResizeArray", [ TGen "T" ])
                    "head", TPrim "i32"
                ]
            | "EventOf_1" ->
                [
                    "handlers", TEnt(netEnt ctx.State "ResizeArray", [ TFn([ tAny; TGen "T" ], tVoid) ])
                ]
            | "DelegateEventOf_1" ->
                [
                    "dhandlers", TEnt(netEnt ctx.State "ResizeArray", [ TFn([ tAny; TGen "T" ], tVoid) ])
                ]
            | "TimeSpanOf" -> [ "ticks", TPrim "i64" ]
            | "DateTimeOf" -> [ "ticks", TPrim "i64"; "kind", TPrim "i32" ]
            | "DateOnlyOf" -> [ "dayNumber", TPrim "i32" ]
            | "DateTimeOffsetOf" -> [ "utcTicks", TPrim "i64"; "offsetMinutes", TPrim "i32" ]
            | "TimeOnlyOf" -> [ "timeTicks", TPrim "i64" ]
            | "StopwatchOf" -> [ "elapsed", TPrim "i64"; "startedAt", TPrim "i64"; "running", tBool ]
            | "DirectoryInfoOf" -> [ "fullName", tStr ]
            | "GuidOf" -> [ "a", TPrim "u32"; "b", tI32; "c", tI32; "rest", TPrim "u64" ]
            | "UriOf" ->
                [
                    "original", tStr
                    "isAbsolute", tBool
                    "scheme", tStr
                    "host", tStr
                    "port", tI32
                    "path", tStr
                    "query", tStr
                    "fragment", tStr
                ]
            | _ -> []

        // (records with fields that can be assigned are counted cells, as the library declares them)
        let mutableFields =
            match name with
            | "StackOf_1" -> [ "items" ]
            | "QueueOf_1" -> [ "items"; "head" ]
            | "EventOf_1" -> [ "handlers" ]
            | "DelegateEventOf_1" -> [ "dhandlers" ]
            | "CancellationSource" -> [ "cancelled"; "handlers"; "disposed" ]
            | "HandOver" -> [ "handedOver" ]
            | "Timer" -> [ "live" ]
            | "StopwatchOf" -> [ "elapsed"; "startedAt"; "running" ]
            | "TaskOf_1" -> [ "fable_task"; "fable_thread" ]
            | "MailboxOf_1" -> [ "waiting"; "started"; "begun"; "running"; "turnToken" ]
            | _ -> []

        let e =
            {
                Name = libraryTarget ctx file name
                Ref =
                    {
                        FullName = $"Fable.Library.Zig.%s{file}.%s{name.Replace('_', '`')}"
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind =
                    (if mutableFields.IsEmpty then
                         KRecord
                     else
                         KRefRecord)
                // (`AsyncOf_1` and the others of one type parameter; `UriOf` of none)
                TypeParams =
                    (if name.EndsWith("_1", System.StringComparison.Ordinal) then
                         [ "T" ]
                     else
                         [])
                Cases = [ "", fields ]
                MutableFields = mutableFields
                // (as the library's own declaration has it: a record of numbers only, as `GuidOf`,
                // is a plain value)
                Managed =
                    not mutableFields.IsEmpty
                    || fields.IsEmpty
                    || fields |> List.exists (snd >> isManaged)
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        ctx.State.Ents[key] <- e
        e

/// A walk of a sequence (Seq.fs): the record of the function that gives the next item.
and walkEnt (ctx: Ctx) : Ent =
    match ctx.State.Ents.TryGetValue "$walk" with
    | true, e -> e
    | _ ->
        let e =
            {
                Name = libraryTarget ctx "Seq" "Walk_1"
                Ref =
                    {
                        FullName = "Fable.Library.Zig.Seq.Walk`1"
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KRecord
                TypeParams = [ "T" ]
                Cases =
                    [
                        "", [ "next", TFn([ tVoid ], TOpt(TGen "T")); "close", TFn([ tVoid ], tVoid) ]
                    ]
                MutableFields = []
                Managed = true
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = false
                Hooks = None
                Overrides = []
            }

        ctx.State.Ents["$walk"] <- e
        e

/// A function of the part of the library written in F#: `m_Seq.toList`, or `toList` inside
/// Seq.fs itself.
and libraryTarget (ctx: Ctx) (file: string) (fn: string) : string =
    if System.IO.Path.GetFileNameWithoutExtension(ctx.Com.CurrentFile) = file then
        fn
    else
        importAlias ctx (Fable.Transforms.AST.getLibPath ctx.Com file) + "." + fn

/// F#'s `Map` and `Set`: the trees of the part of the runtime library written in F#
/// (`Map.fs`, `Set.fs`).
and treeEnt (ctx: Ctx) (isMap: bool) : Ent =
    let key =
        if isMap then
            "$map"
        else
            "$set"

    match ctx.State.Ents.TryGetValue key with
    | true, e -> e
    | _ ->
        // (the names Fable gives the declarations of the library's files)
        let file, typeName =
            if isMap then
                "Map", "MapTree_2"
            else
                "Set", "SetTree_1"

        let pre =
            if isMap then
                "Map"
            else
                "Set"

        let e =
            {
                Name = importAlias ctx (Fable.Transforms.AST.getLibPath ctx.Com file) + "." + typeName
                Ref =
                    {
                        FullName = $"Fable.Library.Zig.%s{file}.%s{typeName.Replace('_', '`')}"
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KHeapUnion
                TypeParams =
                    if isMap then
                        [ "Key"; "Value" ]
                    else
                        [ "T" ]
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

        let self = TEnt(e, e.TypeParams |> List.map TGen)

        e.Cases <-
            [
                pre + "Empty", []
                pre + "Node",
                [
                    "key", TGen e.TypeParams.Head
                    if isMap then
                        "value", TGen "Value"
                    "left", self
                    "right", self
                    "height", tI32
                ]
            ]

        ctx.State.Ents[key] <- e
        e

let isUnit (t: Fable.Type) =
    match t with
    | Fable.Unit -> true
    | _ -> false

let floatLit (ty: string) (x: float) =
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

let numberLit (r: SourceLocation option) (v: Fable.NumberValue) : string * Ty =
    match v with
    | Fable.NumberValue.Int8 x -> string<sbyte> x, TPrim "i8"
    | Fable.NumberValue.UInt8 x -> string<byte> x, TPrim "u8"
    | Fable.NumberValue.Int16 x -> string<int16> x, TPrim "i16"
    | Fable.NumberValue.UInt16 x -> string<uint16> x, TPrim "c_ushort"
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
                | ECallVt _
                | ECallIface _
                | EClosure _
                | EIface _
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
                // (a unit made by statements, a loop: run before, the unit given)
                elif i <= last && not (isFlat ir) && isVoid (typeOf ir) then
                    let v = ctx.State.NewVar("unitArg", tVoid, VLocal, false)
                    binds.Add((v, ir))
                    EUnit
                else
                    ir
            )

        List.foldBack (fun (v, ir) acc -> ELet(v, ir, acc)) (List.ofSeq binds) (k (List.ofArray outs))

let bindArgs (ctx: Ctx) (irs: Expr list) (k: Expr list -> Expr) : Expr = bindArgsIn false ctx irs k

/// The surrounding variables that `bodies` use, in the order they are first used. A use of a
/// function declared in the surroundings counts as a use of what that function captures.
let freeNames (ctx: Ctx) (bodies: (Fable.Ident list * Fable.Expr) list) : string list =
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

/// Can a `with` handler catch OutOfMemoryException? It catches everything unless it raises again
/// what it caught (F# makes `| :? T -> ...` a handler that tests and re-raises the rest); then
/// only if it tests for a type of which OutOfMemoryException is one, or tests in a way not known
/// here.
let handlerMayCatchOom (caught: Fable.Ident) (handler: Fable.Expr) : bool =
    let mutable reraises = false
    let mutable catches = false

    let rec isCaught (e: Fable.Expr) =
        match e with
        | Fable.IdentExpr i -> i.Name = caught.Name
        | Fable.TypeCast(x, _) -> isCaught x
        | _ -> false

    let rec walk (e: Fable.Expr) =
        match e with
        | Fable.Extended(Fable.Throw(None, _), _) -> reraises <- true
        | Fable.Extended(Fable.Throw(Some x, _), _) when isCaught x -> reraises <- true
        | Fable.Test(x, Fable.TypeTest(Fable.DeclaredType(ent, _)), _) when isCaught x ->
            match ent.FullName with
            | "System.Exception"
            | "System.SystemException"
            | "System.OutOfMemoryException" -> catches <- true
            | _ -> ()
        | Fable.Test(x, _, _) when isCaught x -> catches <- true
        | _ -> ()

        AST.getSubExpressions e |> List.iter walk

    walk handler
    not reraises || catches

let uniqueName (ctx: Ctx) (wanted: string) =
    let mutable name = wanted
    let mutable i = 1

    while not (ctx.Reserved.Add name) do
        name <- $"%s{wanted}_%d{i}"
        i <- i + 1

    name

let captureExprs (ctx: Ctx) (r: SourceLocation option) (names: string list) : Expr list =
    names
    |> List.map (fun n ->
        match ctx.Vars.TryGetValue n with
        | true, v -> EVar v
        | _ -> fail r "internal: the captured variable `%s` is not in scope" n
    )

/// What `e` is, if it names a function: one declared inside the function being lowered, one of
/// this file, or one of another file.
let tryCallable (ctx: Ctx) (e: Fable.Expr) : Callable option =
    match e with
    | Fable.IdentExpr id when not (ctx.Vars.ContainsKey id.Name) ->
        match ctx.LocalFns.TryGetValue id.Name with
        // (a generic value is not called by name: its value is, see `lw`)
        | true, fn when ctx.State.GenericValues.Contains fn.FnName -> None
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
                let ctorSelf =
                    if m.IsConstructor then
                        m.DeclaringEntity
                        |> Option.bind (fun entRef ->
                            objInfo ctx None entRef
                            |> Option.map (fun _ ->
                                let gs =
                                    match ctx.Com.TryGetEntity entRef with
                                    | Some ent ->
                                        ent.GenericParameters
                                        |> List.map (fun g -> Fable.GenericParam(g.Name, false, []))
                                    | None -> []

                                Fable.DeclaredType(entRef, gs)
                            )
                        )
                    else
                        None

                let ps = m.CurriedParameterGroups |> List.concat |> List.map (fun p -> p.Type)

                let argTypes =
                    match ctorSelf with
                    | Some selfTy -> selfTy :: ps
                    | None ->
                        match ps with
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
                        Ret =
                            if ctorSelf.IsSome then
                                Fable.Unit
                            else
                                m.ReturnParameter.Type
                    }
            | _ -> None
        | _ -> None
    | _ -> None

/// A module-level value of another file: its name there, and whether it can be assigned.
let importedValue (ctx: Ctx) (imp: Fable.ImportInfo) : (string * bool) option =
    match imp.Kind with
    | Fable.MemberImport memberRef ->
        match ctx.Com.TryGetMember memberRef with
        | Some m when m.IsValue -> Some(importAlias ctx imp.Path + "." + imp.Selector, m.IsMutable)
        | _ -> None
    | _ -> None

/// What the type parameters of `pattern` stand for, if `actual` is an instance of it.
let rec unify (found: Dictionary<string, Fable.Type>) (pattern: Fable.Type) (actual: Fable.Type) : unit =
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
let zigQuoted (text: string) : string option =
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
let stringLiteral (text: string) : string =
    match zigQuoted text with
    | Some quoted -> $"fable_rt.str(%s{quoted})"
    | None ->
        let units = text |> Seq.map (fun c -> string<int>(int c)) |> String.concat ", "
        $"fable_rt.strOf(&[_]u16{{ %s{units} }})"

/// One part of an F# format string: literal text, or a specifier that takes a value.
type FormatPart =
    | Text of string
    /// flags, width, precision, the letter, and the .NET format of a hole (`{x:N2}`)
    | Spec of string * int * int option * char * string

/// "%5d items%%" -> [ Spec("", 5, None, 'd'); Text " items%" ]. In an interpolated string every
/// hole is `%P()`, after a specifier of its own if it has one (`%d%P()`).
let parseFormat (r: SourceLocation option) (fmt: string) : FormatPart list =
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
let (|PrintfCall|_|) (e: Fable.Expr) : (string * string * Fable.Expr list) option =
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

/// `kprintf cont fmt args` as `cont (sprintf fmt args)`.
let kprintf
    (imp: Fable.ImportInfo)
    (info: Fable.CallInfo)
    (args: Fable.Expr list)
    (t: Fable.Type)
    (r: SourceLocation option)
    : Fable.Expr
    =
    let cont, fmtArg =
        match info.Args with
        | [ cont; fmtArg ] -> Some cont, fmtArg
        | [ fmtArg ] -> None, fmtArg
        | _ -> raise (ZigError("the Zig target does not support this kind of printf yet", r))

    let toString =
        Fable.Call(
            Fable.Import(
                { imp with
                    Selector = "PrintFormatToString"
                    Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.ExtraTopLevelOperators"
                },
                Fable.Any,
                None
            ),
            { info with Args = [ fmtArg ] },
            Fable.String,
            r
        )

    let text =
        if args.IsEmpty then
            toString
        else
            Fable.CurriedApply(toString, args, Fable.String, r)

    match cont with
    | Some cont -> Fable.CurriedApply(cont, [ text ], t, r)
    | None -> text

/// (for the names of the operands of `Math.DivRem`)
let private divRemTemps = new System.Threading.ThreadLocal<int ref>(fun () -> ref 0)

/// Is this a culture or a format provider given to a .NET method (`CultureInfo.InvariantCulture`)?
let isCulture (x: Fable.Expr) =
    match unwrapNullness x.Type with
    | Fable.DeclaredType(e, _) ->
        e.FullName = "System.Globalization.CultureInfo"
        || e.FullName = "System.IFormatProvider"
    | _ -> false

/// (for the names of the values of a printf that is used as a function)
let private printfValues =
    new System.Threading.ThreadLocal<int ref>(fun () -> ref 0)

/// A printf that has not been given all the values its format takes: the printf, and the
/// values it has.
let (|PrintfPartial|_|) (e: Fable.Expr) : (Fable.Expr * Fable.Expr list) option =
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
let rec (|Uncast|) (e: Fable.Expr) : Fable.Expr =
    match e with
    | Fable.TypeCast(Uncast inner, _) -> inner
    | _ -> e

/// The item type of what is a list here: a list, or a collection that `Map.keys` gives.
let listItem (t: Fable.Type) : Fable.Type option =
    match t with
    | Fable.List item -> Some item
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.ICollection`1" -> Some item
    | _ -> None

/// The functions of FSharp.Core that the part of the runtime library written in F# has: the
/// file, and the name there (the name FSharp.Core compiles the function to).
let libraryFunction (entity: string) (name: string) : (string * string) option =
    let has (names: string) =
        names.Split([| ' '; '\n' |], System.StringSplitOptions.RemoveEmptyEntries)
        |> Array.contains name

    // (the library names its functions as FSharp.Core compiles them, with a small first letter:
    // a name like `Map` is one that Fable would not leave alone)
    let small (s: string) =
        s.Substring(0, 1).ToLowerInvariant() + s.Substring(1)

    match entity with
    | "Microsoft.FSharp.Collections.ListModule" when
        has
            "Length Head Tail TryHead Last TryLast TryItem Item Singleton Reverse Append Concat Map MapIndexed Map2
             Iterate IterateIndexed Fold FoldBack Reduce Filter Choose Collect Exists ForAll Contains TryFind Find
             TryFindIndex FindIndex TryPick Pick Initialize Replicate Zip Unzip Take Truncate Skip TakeWhile SkipWhile
             Partition Indexed Pairwise Distinct ExactlyOne OfArray ToArray SortWith Sort SortBy SortDescending
             SortByDescending Max Min MaxBy MinBy DistinctBy GroupBy CountBy Except Scan SplitAt ChunkBySize
             Windowed Iterate2 ForAll2 Exists2 Fold2 Map3 Zip3 Head Permute AllPairs TryExactlyOne Where Get
             Cons Empty IsEmpty Transpose InsertAt RemoveAt UpdateAt MapFold MapFoldBack Unzip3 Unfold TryFindIndexBack
             TryFindBack FindIndexBack FindBack SplitInto ScanBack ReduceBack MapIndexed2 IterateIndexed2 FoldBack2
             InsertManyAt RemoveManyAt"
        ->
        Some("List", small name)
    // (the List module's random functions are in Array.fs, which can use both)
    | "Microsoft.FSharp.Collections.ListModule" when name.StartsWith("Random", System.StringComparison.Ordinal) ->
        Some("Array", "list" + name)
    // (a value option is an option here: its module is the same functions)
    | "Microsoft.FSharp.Collections.FSharpList`1" when name = "GetSlice" -> Some("List", "getSlice")
    | "Microsoft.FSharp.Collections.FSharpList`1" when name = "Cons" -> Some("List", "cons")
    | "Microsoft.FSharp.Collections.ListModule" when name = "ToSeq" -> Some("Seq", "ofList")
    | "Microsoft.FSharp.Collections.ArrayModule" when name = "ToSeq" -> Some("Seq", "ofArray")
    | "Microsoft.FSharp.Collections.MapModule" when name = "ToSeq" -> Some("Map", "toSeq")
    | "Microsoft.FSharp.Collections.SetModule" when name = "ToSeq" -> Some("Set", "toSeq")
    | "Microsoft.FSharp.Collections.SetModule" when name = "IntersectMany" -> Some("Set", "intersectMany")
    | "Microsoft.FSharp.Collections.ArrayModule" when name = "OfSeq" -> Some("Seq", "toArray")
    | "Microsoft.FSharp.Collections.SeqModule" when name = "Tail" -> Some("Seq", "tail")
    | "Microsoft.FSharp.Control.ObservableModule" -> Some("Observable", small name)
    | "Microsoft.FSharp.Control.EventModule" -> Some("Event", small name)
    | "Microsoft.FSharp.Collections.SeqModule" when name.StartsWith("Random", System.StringComparison.Ordinal) ->
        Some("Seq", small name)
    // (what `while`, `try ... finally` and `try ... with` in `seq { }` are)
    | "Microsoft.FSharp.Core.CompilerServices.RuntimeHelpers" when
        name = "EnumerateWhile"
        || name = "EnumerateThenFinally"
        || name = "EnumerateTryWith"
        ->
        Some("Seq", small name)
    | "Microsoft.FSharp.Core.OptionModule"
    | "Microsoft.FSharp.Core.ValueOption" when
        has
            "Map Bind DefaultValue DefaultWith IsSome IsNone GetValue Iterate Filter Exists ForAll Fold OrElse
             OrElseWith ToList ToArray Count Contains Flatten Map2 FoldBack Map3 OfValueOption ToValueOption"
        ->
        Some("Option", small name)
    | "Microsoft.FSharp.Core.ValueOption" when name = "ToOption" -> Some("Option", "ofValueOption")
    | "Microsoft.FSharp.Core.ValueOption" when name = "OfOption" -> Some("Option", "toValueOption")
    | "Microsoft.FSharp.Core.Operators" when name = "DefaultArg" || name = "DefaultValueArg" ->
        Some("Option", "defaultArg")
    | ("Microsoft.FSharp.Core.FSharpOption`1" | "Microsoft.FSharp.Core.FSharpValueOption`1") when name = "get_IsSome" ->
        Some("Option", "isSome")
    | ("Microsoft.FSharp.Core.FSharpOption`1" | "Microsoft.FSharp.Core.FSharpValueOption`1") when name = "get_IsNone" ->
        Some("Option", "isNone")
    | ("Microsoft.FSharp.Core.FSharpOption`1" | "Microsoft.FSharp.Core.FSharpValueOption`1") when name = "get_Value" ->
        Some("Option", "memberValue")
    | "Microsoft.FSharp.Core.ResultModule" when
        has
            "Map Bind MapError IsOk IsError Contains Count DefaultValue DefaultWith Exists ForAll Fold FoldBack
             Iterate ToArray ToList ToOption ToValueOption"
        ->
        Some("Result", small name)
    | "Microsoft.FSharp.Collections.MapModule" when
        has
            "Empty IsEmpty Add Find TryFind ContainsKey Remove Change Iterate Fold FoldBack ToList ToArray OfList OfArray
             OfSeq Count Exists ForAll Filter Partition Map TryPick Pick TryFindKey FindKey Keys Values MinKeyValue
             MaxKeyValue"
        ->
        Some(
            "Map",
            (if name = "OfSeq" then
                 "ofList"
             else
                 small name)
        )
    | "Microsoft.FSharp.Collections.FSharpMap`2" ->
        match name with
        | "get_Item" -> Some("Map", "getItem")
        | "Add"
        | "Remove"
        | "ContainsKey"
        | "TryFind"
        | "Change" -> Some("Map", "member" + name)
        | "get_Count" -> Some("Map", "memberCount")
        | "get_IsEmpty" -> Some("Map", "memberIsEmpty")
        // `Map [ (k, v); ... ]`
        | ".ctor" -> Some("Map", "ofList")
        | _ -> None
    | "Microsoft.FSharp.Collections.SetModule" when
        has
            "Empty IsEmpty Add Singleton Contains Remove Iterate Fold FoldBack ToList ToArray OfList OfArray OfSeq Count
             Exists ForAll Filter Partition Map Union UnionMany Intersect Difference IsSubset IsSuperset IsProperSubset
             IsProperSuperset MinElement MaxElement"
        ->
        Some(
            "Set",
            (if name = "OfSeq" then
                 "ofList"
             else
                 small name)
        )
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators" when name = "CreateSet" -> Some("Set", "ofList")
    | "Microsoft.FSharp.Collections.ListModule" when name = "OfSeq" -> Some("List", "ofSeq")
    | "Microsoft.FSharp.Collections.ArrayModule" when
        has
            "Singleton Replicate Head TryHead Last TryLast Item TryItem ExactlyOne TryFindIndex FindIndex TryFind Find
             TryFindBack TryPick Pick Choose Collect Concat FoldBack Reduce Scan Max Min MaxBy MinBy SortWith Sort SortBy
             SortDescending SortByDescending SortInPlaceWith SortInPlace SortInPlaceBy Distinct DistinctBy GroupBy
             CountBy Indexed Zip Unzip Map2 Iterate2 Fold2 Exists2 ForAll2 Partition Take Truncate Skip TakeWhile
             SkipWhile SplitAt ChunkBySize Windowed Pairwise AllPairs Except CopyTo InsertAt InsertManyAt RemoveAt
             RemoveManyAt UpdateAt Where Tail TryExactlyOne TryFindIndexBack FindIndexBack FindBack ReduceBack ScanBack
             MapFold MapFoldBack Map3 MapIndexed2 IterateIndexed2 FoldBack2 Zip3 Unzip3 Transpose SplitInto Permute
             CompareWith RandomShuffle RandomShuffleWith RandomShuffleBy RandomChoice RandomChoiceWith RandomChoiceBy RandomChoices RandomChoicesWith RandomChoicesBy RandomSample RandomSampleWith RandomSampleBy RandomShuffleInPlace RandomShuffleInPlaceWith RandomShuffleInPlaceBy"
        ->
        Some(
            "Array",
            (if name = "CopyTo" then
                 "blit"
             else
                 small name)
        )
    | "Microsoft.FSharp.Collections.SeqModule" when
        has
            "Empty Singleton Delay OfList OfArray Append Map MapIndexed Filter Where Choose Collect Concat Initialize InitializeInfinite Unfold Take Truncate Skip TakeWhile SkipWhile Zip Indexed Pairwise Iterate IterateIndexed Fold ToList ToArray Length IsEmpty TryHead Head TryLast Last TryItem Item TryFind Find TryPick Pick Exists ForAll Contains Reduce Reverse Sort SortBy SortWith SortDescending Distinct Max Min MaxBy MinBy GroupBy CountBy Cache
             Map2 Zip3 Scan Replicate DistinctBy Except Windowed ChunkBySize Cast ReadOnly Iterate2 Fold2 Exists2 ForAll2
             CompareWith TryFindIndex FindIndex TryFindBack FindBack TryFindIndexBack FindIndexBack FoldBack FoldBack2
             ExactlyOne TryExactlyOne ReduceBack SortByDescending SplitInto Permute MapFold MapFoldBack AllPairs
             InsertAt InsertManyAt RemoveAt RemoveManyAt UpdateAt Transpose"
        ->
        Some("Seq", small name)
    | "Microsoft.FSharp.Core.Operators" when name = "CreateSequence" -> Some("Seq", "createSequence")
    | "Microsoft.FSharp.Control.FSharpAsyncBuilder" when
        has "Return ReturnFrom Zero Delay Bind Combine TryWith TryFinally While For"
        ->
        Some("Async", "builder" + name)
    | "Microsoft.FSharp.Control.FSharpAsync" ->
        match name with
        | "RunSynchronously" -> Some("Async", "runSynchronously")
        | "StartImmediate" -> Some("Async", "startImmediate")
        | "Start" -> Some("Async", "startAsync")
        | "Sleep" -> Some("Async", "sleep")
        | "Ignore" -> Some("Async", "ignoreAsync")
        | "Catch" -> Some("Async", "catch")
        | "Parallel" -> Some("Async", "parallelAll")
        | _ -> None
    | "Microsoft.FSharp.Collections.FSharpSet`1" ->
        match name with
        | ".ctor" -> Some("Set", "ofList")
        | "Add"
        | "Remove"
        | "Contains" -> Some("Set", "member" + name)
        | "get_Count"
        | "get_IsEmpty"
        | "get_MinimumElement"
        | "get_MaximumElement" -> Some("Set", "member" + name.Substring 4)
        | "IsSubsetOf"
        | "IsSupersetOf"
        | "IsProperSubsetOf"
        | "IsProperSupersetOf" -> Some("Set", "member" + name)
        | "op_Addition" -> Some("Set", "opAddition")
        | "op_Subtraction" -> Some("Set", "opSubtraction")
        | _ -> None
    | "Microsoft.FSharp.Collections.FSharpList`1" when name = "get_Item" -> Some("List", "getItem")
    | "Microsoft.FSharp.Collections.FSharpList`1" when name = "get_Length" -> Some("List", "length")
    | "Microsoft.FSharp.Core.Operators" when name = "op_Append" -> Some("List", "append")
    | _ -> None

/// The type a byref points at; any other type as it is.
let unByref (t: Fable.Type) : Fable.Type =
    match t with
    | Fable.DeclaredType(ent, [ inner; _ ]) when ent.FullName = "Microsoft.FSharp.Core.byref`2" -> inner
    | _ -> t

/// A read of what a byref points at, typed as that: `string s.[i]`, `%d` of it.
let readByref (e: Fable.Expr) : Fable.Expr =
    match e.Type with
    | Fable.DeclaredType(ent, [ inner; _ ]) when ent.FullName = "Microsoft.FSharp.Core.byref`2" ->
        Fable.TypeCast(e, inner)
    | _ -> e

/// Pull a pointer (`byref`) out of a dereference or variable, keeping any enclosing bindings.
let rec tryAddress (ir: Expr) : Expr option =
    match ir with
    | EDeref(p, _) -> Some p
    | _ when
        (match typeOf ir with
         | TPtr _ -> true
         | _ -> false)
        ->
        Some ir
    | EVar v -> Some(EAddr(EVar v, not v.FMutable))
    // (a field of a reference record that holds a plain value, as `&counter.contents` for
    // `Interlocked`: what is written through it needs no count)
    | EGet(EVar _ as cell, PField f, ty) when
        not (isManaged ty)
        && (
            match typeOf cell with
            | TEnt({ Kind = KRefRecord }, _) -> true
            | _ -> false
        )
        ->
        Some(EAddr(EGet(cell, PField f, ty), false))
    // (a module-level mutable value, read: its own place)
    | EEmit("fable_rt.dup($0)", [ EVar v ], _) when v.Kind = VGlobal -> Some(EAddr(EVar v, not v.FMutable))
    | ELet(v, rhs, body) -> tryAddress body |> Option.map (fun b -> ELet(v, rhs, b))
    | ESeq(s, body) -> tryAddress body |> Option.map (fun b -> ESeq(s, b))
    | _ -> None

/// The expression under the casts and unboxing that F# puts around `x` in `use x = ...`.
let rec (|Unboxed|) (e: Fable.Expr) : Fable.Expr =
    match e with
    | Fable.TypeCast(Unboxed inner, _) -> inner
    | Fable.Call(Fable.Import(imp, _, _), info, _, _) when
        (imp.Selector = "UnboxGeneric" || imp.Selector = "UnboxFast")
        && info.Args.Length = 1
        ->
        let (Unboxed inner) = info.Args.Head
        inner
    | _ -> e

let rec (|UnboxedOrBox|) (e: Fable.Expr) : Fable.Expr =
    match e with
    | Fable.TypeCast(UnboxedOrBox inner, _) -> inner
    | Fable.Call(Fable.Import(imp, _, _), info, _, _) when
        (imp.Selector = "UnboxGeneric"
         || imp.Selector = "UnboxFast"
         || imp.Selector = "Box")
        && info.Args.Length = 1
        ->
        let (UnboxedOrBox inner) = info.Args.Head
        inner
    | _ -> e

/// Does a declared type (not an interface) implement the interface? None when that is not
/// known here.
let implements (com: Compiler) (t: Fable.Type) (ifaceFullName: string) : bool option =
    match unwrapNullness t with
    | Fable.DeclaredType(entRef, _) ->
        match com.TryGetEntity entRef with
        | Some ent when not ent.IsInterface ->
            Some(ent.AllInterfaces |> Seq.exists (fun i -> i.Entity.FullName = ifaceFullName))
        | _ -> None
    | _ -> None

let implementsType (com: Compiler) (t: Fable.Type) (ifaceType: Fable.Type) : bool option =
    let rec hasGenParam (ty: Fable.Type) =
        match ty with
        | Fable.GenericParam _ -> true
        | _ -> ty.Generics |> List.exists hasGenParam

    match unwrapNullness t, unwrapNullness ifaceType with
    | Fable.DeclaredType(entRef, typeArgs), Fable.DeclaredType(ifaceRef, ifaceArgs) ->
        match com.TryGetEntity entRef with
        | Some ent when not ent.IsInterface ->
            let subst =
                if ent.GenericParameters.Length = typeArgs.Length then
                    List.zip (ent.GenericParameters |> List.map (fun g -> g.Name)) typeArgs
                    |> Map.ofList
                else
                    Map.empty

            let candidates =
                ent.AllInterfaces
                |> Seq.filter (fun i -> i.Entity.FullName = ifaceRef.FullName)
                |> Seq.map (fun i -> i.GenericArgs |> List.map (substFableType subst))
                |> Seq.toList

            if candidates.IsEmpty then
                Some false
            elif ifaceArgs.IsEmpty then
                Some true
            elif
                ifaceArgs |> List.exists hasGenParam
                || candidates |> List.exists (List.exists hasGenParam)
            then
                if candidates |> List.contains ifaceArgs then
                    Some true
                else
                    None
            else
                Some(candidates |> List.contains ifaceArgs)
        | Some ent when ent.IsInterface ->
            let subst =
                if ent.GenericParameters.Length = typeArgs.Length then
                    List.zip (ent.GenericParameters |> List.map (fun g -> g.Name)) typeArgs
                    |> Map.ofList
                else
                    Map.empty

            if
                entRef.FullName = ifaceRef.FullName
                && (ifaceArgs.IsEmpty || typeArgs = ifaceArgs)
            then
                Some true
            else
                let hasBase =
                    ent.AllInterfaces
                    |> Seq.exists (fun i ->
                        i.Entity.FullName = ifaceRef.FullName
                        && (ifaceArgs.IsEmpty
                            || (i.GenericArgs |> List.map (substFableType subst)) = ifaceArgs)
                    )

                if hasBase then
                    Some true
                else
                    None
        | _ -> None
    | _ -> None

/// The entity of `seq<'T>`.
let seqEntRef: Fable.EntityRef =
    {
        FullName = "System.Collections.Generic.IEnumerable`1"
        Path = Fable.CoreAssemblyName "System.Runtime"
    }


let taskCodeOf (t: Fable.Type) : Fable.Type =
    Fable.DeclaredType(
        {
            FullName = taskCodeName
            Path = Fable.CoreAssemblyName "FSharp.Core"
        },
        [ t ]
    )

/// F#'s resumable code (`TaskCode`): a delegate of a byref to a state machine.
let rec isResumableCode (t: Fable.Type) : bool =
    match t with
    | Fable.DelegateType(args, _) ->
        args
        |> List.exists (fun a ->
            match a with
            | Fable.DeclaredType(_, [ Fable.DeclaredType(sm, _); _ ]) ->
                sm.FullName.StartsWith(
                    "Microsoft.FSharp.Core.CompilerServices.ResumableStateMachine",
                    System.StringComparison.Ordinal
                )
            | _ -> false
        )
    | Fable.DeclaredType(ent, _) ->
        ent.FullName.StartsWith("Microsoft.FSharp.Control.TaskCode", System.StringComparison.Ordinal)
    | _ -> false

/// The calls of `task { }` have no type in what Fable gives (`Any`): the type of each is found
/// here from its arguments, from the inside out.
let typeTaskBuilders (body: Fable.Expr) : Fable.Expr =
    let itemOf (t: Fable.Type) =
        match t with
        | Fable.DeclaredType(_, [ item ]) -> item
        | _ -> Fable.Any

    let retOf (t: Fable.Type) =
        match t with
        | Fable.LambdaType(_, ret) -> ret
        | Fable.DelegateType(_, ret) -> ret
        | _ -> Fable.Any

    body
    |> AST.visitFromInsideOut (fun e ->
        match e with
        | Fable.Call(Fable.Import(imp, it, ir) as callee, info, callTy, r) when
            imp.Path.StartsWith(
                Replacements.DotnetPrefix + "Microsoft.FSharp.Control.TaskBuilder",
                System.StringComparison.Ordinal
            )
            && (callTy = Fable.Any || isResumableCode callTy)
            ->
            let name = imp.Selector.Substring(imp.Selector.LastIndexOf '.' + 1)

            let t =
                match name, info.Args with
                | "Return", [ x ] -> taskCodeOf x.Type
                | "Zero", _ -> taskCodeOf Fable.Unit
                | "Delay", [ f ] -> retOf f.Type
                | "Bind", [ _; cont ] -> retOf cont.Type
                | "ReturnFrom", [ task ] -> taskCodeOf (itemOf task.Type)
                | "Combine", [ _; second ] -> second.Type
                | ("While" | "For"), _ -> taskCodeOf Fable.Unit
                | ("TryWith" | "TryFinally"), b :: _ -> b.Type
                | "Using", [ _; binder ] -> retOf binder.Type
                | _ -> Fable.Any

            Fable.Call(callee, info, t, r)
        | _ -> e
    )

/// Is this F#'s `seq<'T>`?
let isSeqType (t: Fable.Type) : bool =
    match t with
    | Fable.DeclaredType(ent, [ _ ]) -> ent.FullName = "System.Collections.Generic.IEnumerable`1"
    | _ -> false

/// Is this the type of an interface?
let isInterfaceType (com: Compiler) (t: Fable.Type) : bool =
    match unwrapNullness t with
    | Fable.DeclaredType(entRef, _) ->
        match com.TryGetEntity entRef with
        | Some ent -> ent.IsInterface
        | None -> false
    | _ -> false

/// A class's constructor as a function that makes the object: the fields are computed in
/// order, as locals, and the object is made of them at the end. (`this` cannot be used before
/// all its fields are there.)
/// The class and its ancestors, the class first.
let rec ancestors (o: ObjInfo) : ObjInfo list =
    o
    :: (
        match o.Parent with
        | Some p -> ancestors p
        | None -> []
    )

let chainType (o: ObjInfo) : Fable.Type = Fable.DeclaredType(o.Chain.Ref, [])

/// A class's own type parameters, as F# types (the arguments of its structs within its code)
let ownArgs (o: ObjInfo) : Fable.Type list =
    o.Gens |> List.map (fun g -> Fable.GenericParam(g, false, []))

/// The type of the chain of a class of these type arguments
let chainTypeOf (o: ObjInfo) (genArgs: Fable.Type list) : Fable.Type =
    Fable.DeclaredType(
        o.Chain.Ref,
        (if o.Gens.IsEmpty then
             []
         else
             genArgs)
    )

/// The Zig name of a class's type (`Circle__type`).
let objTypeName (o: ObjInfo) : string = callTarget (o.Prefix + "__type")

/// The structs of fields of a class and the classes above it, the root's first, as Zig text.
let partNames (o: ObjInfo) : string =
    ancestors o
    |> List.rev
    |> List.map (fun k -> callTarget k.Part.Name)
    |> String.concat ", "

/// Each class of an object's chain with its type arguments, the object's class first: `args` are
/// the class's own; a base class's are what the class gives it.
let levelArgs (ctx: Ctx) (r: SourceLocation option) (o: ObjInfo) (args: Ty list) : (ObjInfo * Ty list) list =
    let rec go (k: ObjInfo) (kargs: Ty list) =
        (k, kargs)
        :: (
            match k.Parent with
            | Some p ->
                let subst =
                    if k.Gens.Length = kargs.Length then
                        List.zip k.Gens kargs |> Map.ofList
                    else
                        Map.empty

                go p (k.ParentArgs |> List.map (mapTypeArg ctx r >> substTy subst))
            | None -> []
        )

    go o args

/// The type arguments of an object's class, from its F# type
let objArgs (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : Ty list =
    match t with
    | Fable.DeclaredType(_, gs) -> gs |> List.map (mapTypeArg ctx r)
    | _ -> []

/// The type arguments of the level `level` of the chain of an object of type `t`
let argsOfLevel (ctx: Ctx) (r: SourceLocation option) (o: ObjInfo) (t: Fable.Type) (level: ObjInfo) : Ty list =
    levelArgs ctx r o (objArgs ctx r t)
    |> List.tryFind (fun (k, _) -> k.FullName = level.FullName)
    |> Option.map snd
    |> Option.defaultValue []

/// A pointer to a class's object type, of these type arguments (`&Circle__type`, or
/// `Box__type(i32)` for a generic class)
let objTypeRef (o: ObjInfo) (args: Ty list) : string =
    if o.Gens.IsEmpty then
        "&" + objTypeName o
    else
        objTypeName o + "(" + (args |> List.map zigType |> String.concat ", ") + ")"

/// `partNames` of a chain of type arguments
let partNamesOf (ctx: Ctx) (r: SourceLocation option) (o: ObjInfo) (args: Ty list) : string =
    levelArgs ctx r o args
    |> List.rev
    |> List.map (fun (k, kargs) -> zigType (TEnt(k.Part, kargs)))
    |> String.concat ", "

/// The class of the chain that declares a field.
let fieldOwner (o: ObjInfo) (field: string) : ObjInfo option =
    ancestors o
    |> List.tryFind (fun k -> caseFields (TEnt(k.Part, [])) "" |> List.exists (fun (f, _) -> f = field))

/// The class that introduced a virtual member, and the type of its function value.
let virtualSlot (o: ObjInfo) (slot: string) : (ObjInfo * Ty) option =
    ancestors o
    |> List.tryPick (fun k ->
        k.Slots
        |> List.tryFind (fun (s, _) -> s = slot)
        |> Option.map (fun (_, ty) -> k, ty)
    )

/// Does the class itself implement the virtual member (`override`, or `default` in the class that
/// introduces it)?
let classImplements (com: Compiler) (k: ObjInfo) (slot: string) : bool =
    match com.TryGetEntity k.Ref with
    | Some ent ->
        ent.MembersFunctionsAndValues
        |> Seq.exists (fun m ->
            m.IsOverrideOrExplicitInterfaceImplementation
            && not m.IsDispatchSlot
            && m.CompiledName = slot
        )
    | None -> false

/// The function that implements a virtual member for objects of class `o`: the one of the most
/// derived class of its chain that has one.
let implementationOf (com: Compiler) (r: SourceLocation option) (o: ObjInfo) (slot: string) : string =
    match ancestors o |> List.tryFind (fun k -> classImplements com k slot) with
    | Some k -> implName k.Prefix slot
    | None -> fail r "the Zig target finds no implementation of %s for %s" slot o.FullName

/// The compiled name of the member a call goes to.
let slotName (com: Compiler) (call: Fable.CallInfo) (fieldName: string) : string =
    match call.MemberRef |> Option.bind com.TryGetMember with
    | Some m ->
        // (an overload of an interface's member: its field says which)
        match m.DeclaringEntity |> Option.bind com.TryGetEntity with
        | Some owner when owner.IsInterface && m.IsDispatchSlot -> slotKey owner m.CompiledName (paramTypesOf m)
        | _ -> m.CompiledName
    | None -> fieldName.Substring(fieldName.LastIndexOf '.' + 1)

/// The field of an interface's struct that a member implements (an object expression's, or a
/// class's `interface ... with`)
let implementedSlot (com: Compiler) (m: Fable.MemberFunctionOrValue) : string =
    let compiled = m.CompiledName.Substring(m.CompiledName.LastIndexOf '.' + 1)

    // (some members cannot say what they implement: those of .NET's own interfaces)
    let signature =
        try
            m.ImplementedAbstractSignatures |> Seq.tryHead
        with _ ->
            None

    match signature with
    | Some sg ->
        match sg.DeclaringType with
        | Fable.DeclaredType(i, _) ->
            match com.TryGetEntity i with
            | Some owner when owner.IsInterface -> slotKey owner compiled (paramTypesOf m)
            | _ -> compiled
        | _ -> compiled
    | None -> compiled

/// The compiled name an implementation's function is named by: an overload's with its slot
let implFnName (com: Compiler) (m: Fable.MemberFunctionOrValue) : string =
    let slot = implementedSlot com m

    if slot.Contains "$" then
        m.CompiledName.Substring(0, m.CompiledName.LastIndexOf '.' + 1) + slot
    else
        m.CompiledName


let isConstructorCall (com: Compiler) (call: Fable.CallInfo) : bool =
    match call.MemberRef |> Option.bind com.TryGetMember with
    | Some m -> m.IsConstructor
    | None -> false

/// The prefix of the functions of a class's members: for an object, of the class of its chain
/// that implements `iface` when one is given.
let classPrefixWith
    (com: Compiler)
    (objOf: Fable.EntityRef -> ObjInfo option)
    (entName: Fable.EntityRef -> string)
    (classRef: Fable.EntityRef)
    (iface: string option)
    : string
    =
    match objOf classRef with
    | Some o ->
        match iface with
        | Some i ->
            ancestors o
            |> List.tryFind (fun k ->
                match com.TryGetEntity k.Ref with
                | Some ent -> ent.DeclaredInterfaces |> Seq.exists (fun d -> d.Entity.FullName = i)
                | None -> false
            )
            |> Option.defaultValue o
            |> fun k -> k.Prefix
        | None -> o.Prefix
    | None -> entName classRef

let classPrefix (ctx: Ctx) (r: SourceLocation option) (classRef: Fable.EntityRef) (iface: string option) : string =
    classPrefixWith ctx.Com (objInfo ctx r) (fun c -> (entOf ctx r c).Name) classRef iface

/// The function that implements member `name` of interface `iface` for a class: the class's
/// own, or the one of the nearest class above it that has one. (A member is implemented under
/// the name of the interface written in `interface X with`, which may inherit `iface`.)
let interfaceImpl
    (ctx: Ctx)
    (r: SourceLocation option)
    (classRef: Fable.EntityRef)
    (iface: string)
    (name: string)
    : string
    =
    let classes =
        match objInfo ctx r classRef with
        | Some o -> ancestors o |> List.map (fun k -> k.Ref, k.Prefix)
        | None -> [ classRef, (entOf ctx r classRef).Name ]

    let found =
        classes
        |> List.tryPick (fun (ref, prefix) ->
            match ctx.Com.TryGetEntity ref with
            | Some ent ->
                ent.MembersFunctionsAndValues
                |> Seq.tryFind (fun m ->
                    m.IsOverrideOrExplicitInterfaceImplementation
                    && (if name.Contains "$" then
                            implementedSlot ctx.Com m = name
                        else
                            m.CompiledName.EndsWith("." + name, System.StringComparison.Ordinal))
                )
                |> Option.map (fun m -> implName prefix (implFnName ctx.Com m))
            | None -> None
        )

    match found with
    | Some f -> f
    | None -> implName (classPrefix ctx r classRef (Some iface)) (iface + "." + name)

/// Like `interfaceImpl`, paired with the implementing ancestor's type arguments for `srcType`.
let interfaceImplSlot
    (ctx: Ctx)
    (r: SourceLocation option)
    (srcType: Fable.Type)
    (classRef: Fable.EntityRef)
    (iface: string)
    (name: string)
    : string * Ty list
    =
    match objInfo ctx r classRef with
    | Some o ->
        let found =
            ancestors o
            |> List.tryPick (fun k ->
                match ctx.Com.TryGetEntity k.Ref with
                | Some ent ->
                    ent.MembersFunctionsAndValues
                    |> Seq.tryFind (fun m ->
                        m.IsOverrideOrExplicitInterfaceImplementation
                        && (if name.Contains "$" then
                                implementedSlot ctx.Com m = name
                            else
                                m.CompiledName.EndsWith("." + name, System.StringComparison.Ordinal))
                    )
                    |> Option.map (fun m -> implName k.Prefix (implFnName ctx.Com m), argsOfLevel ctx r o srcType k)
                | None -> None
            )

        match found with
        | Some res -> res
        | None ->
            let owner =
                ancestors o
                |> List.tryFind (fun k ->
                    match ctx.Com.TryGetEntity k.Ref with
                    | Some ent -> ent.DeclaredInterfaces |> Seq.exists (fun d -> d.Entity.FullName = iface)
                    | None -> false
                )
                |> Option.defaultValue o

            implName owner.Prefix (iface + "." + name), argsOfLevel ctx r o srcType owner
    | None ->
        let typeArgs =
            match srcType with
            | Fable.DeclaredType(_, gs) -> gs |> List.map (mapTypeArg ctx r)
            | _ -> []

        interfaceImpl ctx r classRef iface name, typeArgs

/// What the file emits for a class that takes part in inheritance that it declares.
let objDecl (ctx: Ctx) (r: SourceLocation option) (o: ObjInfo) (dotnetName: string) : ObjDecl =
    let com = ctx.Com
    // (each class of the chain with its type arguments, in terms of this class's own)
    let levels = levelArgs ctx r o (o.Gens |> List.map TGen)

    let argsOf (k: ObjInfo) =
        levels
        |> List.tryFind (fun (x, _) -> x.FullName = k.FullName)
        |> Option.map snd
        |> Option.defaultValue []

    // (the class of the chain whose member fills a slot)
    let implementer (slot: string) =
        match ancestors o |> List.tryFind (fun k -> classImplements com k slot) with
        | Some k -> k
        | None -> fail r "the Zig target finds no implementation of %s for %s" slot o.FullName

    let tables =
        levels
        |> List.rev
        |> List.map (fun (level, largs) ->
            match level.Table with
            | Some vt when not o.IsAbstract ->
                let subst =
                    if level.Gens.Length = largs.Length then
                        List.zip level.Gens largs |> Map.ofList
                    else
                        Map.empty

                let entries =
                    level.Slots
                    |> List.map (fun (slot, slotTy) ->
                        let k = implementer slot
                        slot, implName k.Prefix slot, argsOf k, substTy subst slotTy
                    )

                Some(TEnt(vt, largs), entries)
            | _ -> None
        )

    // (the interfaces of the class, with the tables a value of each made of its object has)
    let ifaces =
        if o.IsAbstract then
            []
        else
            match com.TryGetEntity o.Ref with
            | Some ent ->
                let srcType =
                    Fable.DeclaredType(o.Ref, o.Gens |> List.map (fun g -> Fable.GenericParam(g, false, [])))

                ent.AllInterfaces
                |> Seq.toList
                // (the interfaces of the program: .NET's have tables of their own here)
                |> List.filter (fun i ->
                    match i.Entity.Path with
                    | Fable.SourcePath _
                    | Fable.PrecompiledLib _ -> true
                    | _ -> false
                )
                |> List.choose (fun i ->
                    let ifaceType = Fable.DeclaredType(i.Entity, i.GenericArgs)

                    try
                        if not (isInterfaceType com ifaceType) then
                            None
                        else
                            match mapType ctx r ifaceType with
                            | TOpt(TEnt(e, _) as s)
                            | (TEnt(e, _) as s) when e.Kind = KIface ->
                                let slots =
                                    caseFields s ""
                                    |> List.map (fun (f, _) ->
                                        f, interfaceImplSlot ctx r srcType o.Ref i.Entity.FullName f
                                    )

                                Some(s, slots)
                            | _ -> None
                    with _ ->
                        None
                )
            | None -> []

    {
        Ifaces = ifaces
        TypeName = o.Prefix + "__type"
        TypeParams = o.Gens
        Chain = TEnt(o.Chain, o.Gens |> List.map TGen)
        DotnetName = dotnetName
        Parent = o.Parent |> Option.map (fun p -> objTypeRef p (argsOf p))
        Tables = tables
        ToString =
            ancestors o
            |> List.tryFind (fun k -> classImplements com k "ToString")
            |> Option.map (fun k -> k.Prefix + "__ToString", argsOf k)
        Thunks = []
        Overrides =
            [
                "equals", "Equals"
                "hash", "GetHashCode"
                "compare", "System.IComparable.CompareTo"
            ]
            |> List.choose (fun (hook, slot) ->
                ancestors o
                |> List.tryFind (fun k -> classImplements com k slot)
                |> Option.map (fun k -> hook, implName k.Prefix slot)
            )
    }

/// A constructor as a function that computes the fields in order and ends with `finish` of
/// their values.
let constructorBodyWith
    (fieldNames: string list)
    (defaults: string -> Fable.Expr option)
    (finish: Fable.Expr list -> Fable.Expr)
    (body: Fable.Expr)
    : Fable.Expr
    =
    let fieldIdent (name: string) (t: Fable.Type) : Fable.Ident =
        {
            Name = "field_" + name
            Type = t
            IsMutable = false
            IsThisArgument = false
            IsCompilerGenerated = true
            Range = None
            IsInlineIfLambda = false
        }

    let set = Dictionary<string, Fable.Ident>()
    /// the field of the self reference, when the constructor fills it with the object
    let mutable selfField: (string * Fable.Type) option = None

    let rec usesThis (e: Fable.Expr) =
        match e with
        | Fable.Value(Fable.ThisValue _, _) -> true
        | _ -> getSubExpressions e |> List.exists usesThis

    let rec fieldsOf (e: Fable.Expr) : Fable.Expr =
        match e with
        // (the object read through its self reference before it is made: .NET's error)
        | Fable.Get(Fable.Get(Fable.Value(Fable.ThisValue owner, _), Fable.FieldGet _, refT, _), Fable.FieldGet ci, t, r) when
            ci.Name = "contents" && isSelfRefType owner refT
            ->
            Fable.Call(
                Fable.Import(
                    {
                        Selector = "FailInit"
                        Path =
                            Replacements.DotnetPrefix
                            + "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(),
                t,
                r
            )
        | Fable.Get(Fable.Value(Fable.ThisValue _, _), Fable.FieldGet info, t, _) when set.ContainsKey info.Name ->
            Fable.IdentExpr set[info.Name]
        | _ ->
            match e with
            | Fable.Value(Fable.ThisValue _, r) ->
                raise (ZigError("the Zig target does not support using `this` in a constructor yet", r))
            | _ -> e |> AST.visit fieldsOf

    let rec build (stmts: Fable.Expr list) : Fable.Expr =
        match stmts with
        | [] ->
            let values =
                fieldNames
                |> List.map (fun f ->
                    match set.TryGetValue f, defaults f with
                    | (true, id), _ -> Fable.IdentExpr id
                    // (`[<DefaultValue>] val mutable`: the default of its type)
                    | _, Some d -> d
                    | _ ->
                        raise (
                            ZigError(
                                $"the Zig target needs every field of a class to be given a value in its constructor (`%s{f}`)",
                                None
                            )
                        )
                )

            match selfField with
            | None -> finish values
            | Some(name, refT) ->
                // the object, then its self reference filled with it
                let made = finish values

                match made.Type with
                // (a class in a hierarchy: its constructor gives the chain of fields, and where the
                // object is made of it, the self reference is filled; see the constructor call)
                | Fable.DeclaredType(e, _) when e.FullName.EndsWith("$chain", System.StringComparison.Ordinal) -> made
                | _ ->

                    let obj = AST.makeTypedIdent made.Type "made"

                    let optT =
                        match refT with
                        | Fable.DeclaredType(_, [ o ]) -> o
                        | _ -> raise (ZigError("internal: a self reference", None))

                    let fieldInfo: Fable.FieldInfo =
                        {
                            Name = name
                            FieldType = Some refT
                            IsMutable = true
                            MaybeCalculated = false
                            Tags = []
                        }

                    let cell =
                        Fable.Get(Fable.IdentExpr obj, Fable.GetKind.FieldGet fieldInfo, refT, None)

                    Fable.Let(
                        obj,
                        made,
                        Fable.Sequential
                            [
                                Fable.Set(
                                    cell,
                                    Fable.FieldSet "contents",
                                    optT,
                                    Fable.Value(Fable.NewOption(Some(Fable.IdentExpr obj), made.Type, false), None),
                                    None
                                )
                                Fable.IdentExpr obj
                            ]
                    )
        | stmt :: rest ->
            match stmt with
            | Fable.Sequential xs -> build (xs @ rest)
            | Fable.Value(Fable.UnitConstant, _) -> build rest
            // (the constructor of System.Object)
            | Fable.Call(Fable.Import(imp, _, _), _, _, _) when
                imp.Selector = ".ctor" && imp.Path.EndsWith "System.Object"
                ->
                build rest
            // (`type C() as this`: the self reference starts empty)
            | Fable.Set(Fable.Value(Fable.ThisValue owner, _), Fable.FieldSet name, t, _, _) when isSelfRefType owner t ->
                let kept = selfRefType t

                let empty =
                    match kept with
                    | Fable.DeclaredType(refEntRef, [ Fable.Option(c, _) as optT ]) ->
                        Fable.Value(
                            Fable.NewRecord([ Fable.Value(Fable.NewOption(None, c, false), None) ], refEntRef, [ optT ]),
                            None
                        )
                    | _ -> raise (ZigError("internal: a self reference", None))

                let id = fieldIdent name kept
                set[name] <- id
                Fable.Let(id, empty, build rest)
            // (and is filled with the object once it is made: see `finish`)
            | Fable.Set(Fable.Get(Fable.Value(Fable.ThisValue owner, _), Fable.FieldGet fi, refT, _),
                        Fable.FieldSet "contents",
                        _,
                        Fable.Value(Fable.ThisValue _, _),
                        _) when isSelfRefType owner refT ->
                selfField <- Some(fi.Name, selfRefType refT)
                build rest
            | Fable.Set(Fable.Value(Fable.ThisValue _, _), Fable.FieldSet name, t, value, _) ->
                let id = fieldIdent name t
                let value = fieldsOf value
                set[name] <- id
                Fable.Let(id, value, build rest)
            | Fable.Let(id, value, body) -> Fable.Let(id, fieldsOf value, build (body :: rest))
            | other -> Fable.Sequential [ fieldsOf other; build rest ]

    build [ body ]

let constructorBody
    (classRef: Fable.EntityRef)
    (genArgs: Fable.Type list)
    (fieldNames: string list)
    (defaults: string -> Fable.Expr option)
    (body: Fable.Expr)
    : Fable.Expr
    =
    constructorBodyWith
        fieldNames
        defaults
        (fun values -> Fable.Value(Fable.NewRecord(values, classRef, genArgs), None))
        body

/// Build the self identifier parameter for an object-first constructor of class `o`.
let objSelfIdent (o: ObjInfo) : Fable.Ident =
    let genArgs = o.Gens |> List.map (fun g -> Fable.GenericParam(g, false, []))

    {
        Name = "self_obj"
        Type = Fable.DeclaredType(o.Ref, genArgs)
        IsMutable = false
        IsThisArgument = true
        IsCompilerGenerated = true
        Range = None
        IsInlineIfLambda = false
    }

/// The constructor of an object class (`objAlloc` allocates `selfId` first; the base constructor
/// runs with the same `selfId`, then the fields, `init@`, and `do` statements execute in order
/// directly against the live heap object).
let objConstructorBody
    (o: ObjInfo)
    (selfId: Fable.Ident)
    (defaults: string -> Fable.Expr option)
    (baseCall: Fable.Expr option)
    (body: Fable.Expr)
    : Fable.Expr
    =
    let fields = caseFields (TEnt(o.Part, [])) "" |> List.map fst
    let assigned = HashSet<string>()
    let typedThisAliases = HashSet<string>()

    let rec rewriteCtor (e: Fable.Expr) : Fable.Expr =
        match e with
        // (the constructor of System.Object)
        | Fable.Call(Fable.Import(imp, _, _), _, _, _) when imp.Selector = ".ctor" && imp.Path.EndsWith "System.Object" ->
            Fable.Value(Fable.UnitConstant, None)
        // (`FSharp2Fable` binds `_this: Any = ThisValue Any` around object expressions inside an
        // implicit constructor; give `_this` the class type so member/field lookups recognize it)
        | Fable.Let(id, Fable.Value(Fable.ThisValue _, r), body) when id.Type = Fable.Any ->
            typedThisAliases.Add id.Name |> ignore

            let id =
                { id with
                    Type = selfId.Type
                    IsThisArgument = true
                }

            Fable.Let(id, Fable.IdentExpr { selfId with Range = r }, rewriteCtor body)
        | Fable.IdentExpr id when typedThisAliases.Contains id.Name && id.Type = Fable.Any ->
            Fable.IdentExpr
                { id with
                    Type = selfId.Type
                    IsThisArgument = true
                }
        // (`type C() as this`: the self reference starts empty)
        | Fable.Set(Fable.Value(Fable.ThisValue owner, _), Fable.FieldSet name, t, _, r) when isSelfRefType owner t ->
            assigned.Add name |> ignore
            let kept = selfRefType t

            let empty =
                match kept with
                | Fable.DeclaredType(refEntRef, [ Fable.Option(c, _) as optT ]) ->
                    Fable.Value(
                        Fable.NewRecord([ Fable.Value(Fable.NewOption(None, c, false), None) ], refEntRef, [ optT ]),
                        None
                    )
                | _ -> raise (ZigError("internal: a self reference", r))

            Fable.Set(Fable.IdentExpr selfId, Fable.FieldSet name, kept, empty, r)
        // (and is filled with `Some self_obj` right where F# puts the store)
        | Fable.Set(Fable.Get(Fable.Value(Fable.ThisValue owner, _), Fable.FieldGet fi, refT, r1),
                    Fable.FieldSet "contents",
                    _,
                    Fable.Value(Fable.ThisValue _, _),
                    r2) when isSelfRefType owner refT ->
            let kept = selfRefType refT

            let optT, itemT =
                match kept with
                | Fable.DeclaredType(_, [ Fable.Option(c, _) as optT ]) -> optT, c
                | _ -> raise (ZigError("internal: a self reference", r2))

            let cell =
                Fable.Get(Fable.IdentExpr selfId, Fable.FieldGet { fi with FieldType = Some kept }, kept, r1)

            Fable.Set(
                cell,
                Fable.FieldSet "contents",
                optT,
                Fable.Value(Fable.NewOption(Some(Fable.IdentExpr selfId), itemT, false), r2),
                r2
            )
        | Fable.Set(Fable.Value(Fable.ThisValue _, _), Fable.FieldSet name, t, value, r) ->
            assigned.Add name |> ignore
            Fable.Set(Fable.IdentExpr selfId, Fable.FieldSet name, t, rewriteCtor value, r)
        | Fable.Value(Fable.ThisValue _, r) -> Fable.IdentExpr { selfId with Range = r }
        | _ -> e |> AST.visit rewriteCtor

    let rewritten = rewriteCtor body

    let missingDefaults =
        fields
        |> List.choose (fun f ->
            if assigned.Contains f then
                None
            else
                match defaults f with
                | Some d -> Some(Fable.Set(Fable.IdentExpr selfId, Fable.FieldSet f, d.Type, d, None))
                | None ->
                    raise (
                        ZigError(
                            $"the Zig target needs every field of a class to be given a value in its constructor (`%s{f}`)",
                            None
                        )
                    )
        )

    let baseStep =
        match o.Parent, baseCall with
        | Some p, Some(Fable.Call(callee, info, retTy, r)) ->
            let pArgs =
                match retTy with
                | Fable.DeclaredType(_, gs) when not gs.IsEmpty -> gs
                | _ -> o.ParentArgs

            let call =
                Fable.Call(
                    callee,
                    { info with
                        ThisArg = Some(Fable.IdentExpr selfId)
                        GenericArgs =
                            if info.GenericArgs.IsEmpty then
                                pArgs
                            else
                                info.GenericArgs
                    },
                    Fable.Unit,
                    r
                )

            [ call ]
        | Some _, _ ->
            raise (
                ZigError(
                    $"the Zig target does not support this call of the base constructor of %s{o.FullName} yet",
                    None
                )
            )
        | None, _ -> []

    Fable.Sequential(
        baseStep
        @ missingDefaults
        @ [ rewritten; Fable.Value(Fable.UnitConstant, None) ]
    )

/// A module-level value, of this file or (`alias.name`) of another.
let globalVar (name: string) (ty: Ty) (isMutable: bool) : Expr =
    EVar
        {
            Id = 0
            Base = name
            Ty = ty
            Kind = VGlobal
            FMutable = isMutable
        }

/// Is the variable used inside a function that is declared in `e`?
let usedInFunction (name: string) (e: Fable.Expr) : bool =
    let rec go (inside: bool) (e: Fable.Expr) : bool =
        match e with
        | Fable.IdentExpr id -> inside && id.Name = name
        | Fable.Lambda(_, body, _)
        | Fable.Delegate(_, body, _, _) -> go true body
        | Fable.ObjectExpr(members, _, _) -> members |> List.exists (fun m -> go true m.Body)
        | _ -> getSubExpressions e |> List.exists (go inside)

    go false e

let hasAddressOfIdent (name: string) (e: Fable.Expr) : bool =
    let rec go e =
        match e with
        | Fable.Operation(Fable.Unary(UnaryAddressOf, Uncast(Fable.IdentExpr id)), _, _, _) when id.Name = name -> true
        | _ -> getSubExpressions e |> List.exists go

    go e

let mutatedIdentsIn (e: Fable.Expr) : HashSet<string> =
    let acc = HashSet<string>()

    let rec go e =
        match e with
        | Fable.Set(Fable.IdentExpr id, Fable.ValueSet, _, value, _) ->
            acc.Add id.Name |> ignore
            go value
        | _ -> getSubExpressions e |> List.iter go

    go e
    acc

/// A string that is certainly not null: its length needs no test.
let rec neverNull (e: Fable.Expr) : bool =
    match e with
    | Fable.Value(Fable.StringConstant _, _) -> true
    | Fable.TypeCast(x, _) -> neverNull x
    | PrintfCall("PrintFormatToString", _, _)
    | Fable.CurriedApply(PrintfCall("PrintFormatToString", _, _), _, _, _) -> true
    | Fable.Call(Fable.Import(imp, _, _), _, Fable.String, _) ->
        imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.StringModule"
        || (imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
            && (imp.Selector = "op_Addition" || imp.Selector = "ToString"))
        // (.NET's string methods that give a string never give null)
        || (imp.Path = Replacements.DotnetPrefix + "System.String"
            && (
                match imp.Selector with
                | "Substring"
                | "Trim"
                | "TrimStart"
                | "TrimEnd"
                | "Replace"
                | "ToUpper"
                | "ToLower"
                | "ToUpperInvariant"
                | "ToLowerInvariant"
                | "PadLeft"
                | "PadRight"
                | "Insert"
                | "Remove"
                | "Concat"
                | "Format"
                | "Join"
                | "ToString" -> true
                | _ -> false
            ))
    | Fable.Value(Fable.StringTemplate _, _) -> true
    | _ -> false

/// What a condition tells, from what its leaves tell (`atom`): the variables (immutable) of
/// which something is known where it is true, and where it is false; through `not`, `&&` and
/// `||` (also as F# compiles them: `if a then true else b`, `if a then b else false`)
let rec factsOf (atom: Fable.Expr -> string list * string list) (cond: Fable.Expr) : string list * string list =
    match cond with
    | Fable.Operation(Fable.Unary(UnaryNot, x), _, _, _) ->
        let t, f = factsOf atom x
        f, t
    | Fable.Operation(Fable.Logical(LogicalAnd, a, b), _, _, _)
    | Fable.IfThenElse(a, b, Fable.Value(Fable.BoolConstant false, _), _) ->
        let ta, _ = factsOf atom a
        let tb, _ = factsOf atom b
        ta @ tb, []
    | Fable.Operation(Fable.Logical(LogicalOr, a, b), _, _, _)
    | Fable.IfThenElse(a, Fable.Value(Fable.BoolConstant true, _), b, _) ->
        let _, fa = factsOf atom a
        let _, fb = factsOf atom b
        [], fa @ fb
    | _ -> atom cond

let private namedImmutable (e: Fable.Expr) =
    match e with
    | Fable.IdentExpr i when not i.IsMutable -> Some i.Name
    | _ -> None

/// What a condition tells of nulls: the variables known not to be null where it is true, and
/// where it is false. `isNull x`, `x = null`, `x <> null`, `String.IsNullOrEmpty x`
let nullFacts (cond: Fable.Expr) : string list * string list =
    let isNullValue (e: Fable.Expr) =
        match e with
        | Fable.Value(Fable.Null _, _) -> true
        | Fable.Call(Fable.Import(imp, _, _), info, _, _) -> imp.Selector = "DefaultOf" && info.Args.IsEmpty
        | _ -> false

    let named = namedImmutable

    factsOf
        (fun cond ->
            match cond with
            | Fable.Call(Fable.Import(imp, _, _), info, _, _) ->
                match imp.Selector, info.Args with
                | ("IsNull" | "IsNullOrEmpty" | "IsNullOrWhiteSpace"), [ x ] -> [], Option.toList (named x)
                | "ReferenceEquals", [ x; n ] when isNullValue n -> [], Option.toList (named x)
                | "ReferenceEquals", [ n; x ] when isNullValue n -> [], Option.toList (named x)
                | ("NonNull" | "NonNullQuickPattern"), [ x ] -> Option.toList (named x), []
                | "op_Equality", [ x; n ] when isNullValue n -> [], Option.toList (named x)
                | "op_Equality", [ n; x ] when isNullValue n -> [], Option.toList (named x)
                | "op_Inequality", [ x; n ] when isNullValue n -> Option.toList (named x), []
                | "op_Inequality", [ n; x ] when isNullValue n -> Option.toList (named x), []
                | _ -> [], []
            | Fable.Operation(Fable.Binary(BinaryEqual, x, n), _, _, _) when isNullValue n ->
                [], Option.toList (named x)
            | Fable.Operation(Fable.Binary(BinaryUnequal, x, n), _, _, _) when isNullValue n ->
                Option.toList (named x), []
            | _ -> [], []
        )
        cond

/// What a condition tells of whole numbers: the variables known to be greater than zero (a
/// divisor that is neither zero nor -1) where it is true, and where it is false. `x > 0`,
/// `x >= 1`, `0 < x`, `x <= 0`, `x < 1`, and of an unsigned `x`, `x <> 0` and `x = 0`
let positiveFacts (cond: Fable.Expr) : string list * string list =
    let constOf (e: Fable.Expr) : int64 option =
        match e with
        | Fable.Value(Fable.NumberConstant(v, _), _) ->
            match v with
            | Fable.NumberValue.Int8 n -> Some(int64 n)
            | Fable.NumberValue.Int16 n -> Some(int64 n)
            | Fable.NumberValue.Int32 n -> Some(int64 n)
            | Fable.NumberValue.Int64 n -> Some n
            | Fable.NumberValue.UInt8 n -> Some(int64 n)
            | Fable.NumberValue.UInt16 n -> Some(int64 n)
            | Fable.NumberValue.UInt32 n -> Some(int64 n)
            | Fable.NumberValue.UInt64 n when n <= uint64 System.Int64.MaxValue -> Some(int64 n)
            | _ -> None
        | _ -> None

    let isUnsigned (t: Fable.Type) =
        match t with
        | Fable.Number((UInt8 | UInt16 | UInt32 | UInt64), _) -> true
        | _ -> false

    let named (e: Fable.Expr) =
        match e with
        | Fable.IdentExpr i when not i.IsMutable ->
            match i.Type with
            | Fable.Number((Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64), _) -> Some i.Name
            | _ -> None
        | _ -> None

    let leaf (op: BinaryOperator) (x: Fable.Expr) (c: int64) : string list * string list =
        match named x with
        | None -> [], []
        | Some n ->
            match op with
            | BinaryGreater when c >= 0L -> [ n ], []
            | BinaryGreaterOrEqual when c >= 1L -> [ n ], []
            | BinaryLessOrEqual when c >= 0L -> [], [ n ]
            | BinaryLess when c >= 1L -> [], [ n ]
            | BinaryUnequal when c = 0L && isUnsigned x.Type -> [ n ], []
            | BinaryEqual when c = 0L && isUnsigned x.Type -> [], [ n ]
            | _ -> [], []

    let flip (op: BinaryOperator) =
        match op with
        | BinaryGreater -> BinaryLess
        | BinaryGreaterOrEqual -> BinaryLessOrEqual
        | BinaryLess -> BinaryGreater
        | BinaryLessOrEqual -> BinaryGreaterOrEqual
        | o -> o

    factsOf
        (fun cond ->
            match cond with
            | Fable.Operation(Fable.Binary(op, x, k), _, _, _) ->
                match constOf k, constOf x with
                | Some c, _ -> leaf op x c
                | None, Some c -> leaf (flip op) k c
                | _ -> [], []
            | _ -> [], []
        )
        cond

/// What a condition tells of whole numbers: the variables known to be non-negative (`>= 0`)
/// where it is true, and where it is false.
let nonNegFacts (cond: Fable.Expr) : string list * string list =
    let constOf (e: Fable.Expr) : int64 option =
        match e with
        | Fable.Value(Fable.NumberConstant(v, _), _) ->
            match v with
            | Fable.NumberValue.Int8 n -> Some(int64 n)
            | Fable.NumberValue.Int16 n -> Some(int64 n)
            | Fable.NumberValue.Int32 n -> Some(int64 n)
            | Fable.NumberValue.Int64 n -> Some n
            | Fable.NumberValue.UInt8 n -> Some(int64 n)
            | Fable.NumberValue.UInt16 n -> Some(int64 n)
            | Fable.NumberValue.UInt32 n -> Some(int64 n)
            | Fable.NumberValue.UInt64 n when n <= uint64 System.Int64.MaxValue -> Some(int64 n)
            | _ -> None
        | _ -> None

    let named (e: Fable.Expr) =
        match e with
        | Fable.IdentExpr i when not i.IsMutable ->
            match i.Type with
            | Fable.Number((Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64), _) -> Some i.Name
            | _ -> None
        | _ -> None

    let leaf (op: BinaryOperator) (x: Fable.Expr) (c: int64) : string list * string list =
        match named x with
        | None -> [], []
        | Some n ->
            match op with
            | BinaryGreaterOrEqual when c >= 0L -> [ n ], []
            | BinaryGreater when c >= -1L -> [ n ], []
            | BinaryLess when c >= 0L && c <= 0L -> [], [ n ]
            | BinaryLessOrEqual when c >= -1L && c <= -1L -> [], [ n ]
            | _ -> [], []

    let flip (op: BinaryOperator) =
        match op with
        | BinaryGreater -> BinaryLess
        | BinaryGreaterOrEqual -> BinaryLessOrEqual
        | BinaryLess -> BinaryGreater
        | BinaryLessOrEqual -> BinaryGreaterOrEqual
        | o -> o

    factsOf
        (fun cond ->
            match cond with
            | Fable.Operation(Fable.Binary(op, x, k), _, _, _) ->
                match constOf k, constOf x with
                | Some c, _ -> leaf op x c
                | None, Some c -> leaf (flip op) k c
                | _ -> [], []
            | _ -> [], []
        )
        cond

/// Does this always raise (`raise`, `failwith`, `nullArg`, `invalidArg`, `invalidOp`)?
let rec alwaysRaises (e: Fable.Expr) : bool =
    match e with
    | Fable.Extended(Fable.Throw _, _) -> true
    | Fable.Call(Fable.Import(imp, _, _), _, _, _) ->
        imp.Path.EndsWith("Microsoft.FSharp.Core.Operators", System.StringComparison.Ordinal)
        && (
            match imp.Selector with
            | "Raise"
            | "FailWith"
            | "InvalidArg"
            | "InvalidOp"
            | "NullArg" -> true
            | _ -> false
        )
    | Fable.Sequential es -> not es.IsEmpty && alwaysRaises (List.last es)
    | Fable.Let(_, _, body) -> alwaysRaises body
    | Fable.IfThenElse(_, a, b, _) -> alwaysRaises a && alwaysRaises b
    | Fable.TypeCast(x, _) -> alwaysRaises x
    | _ -> false

/// What a statement leaves known for what follows it (by `facts`): a guard whose other branch
/// always raises (`if isNull s then nullArg "s"`, `if n <= 0 then invalidArg ...`)
let factsAfter (facts: Fable.Expr -> string list * string list) (stmt: Fable.Expr) : string list =
    match stmt with
    | Fable.IfThenElse(guard, thenExpr, elseExpr, _) ->
        let whenTrue, whenFalse = facts guard

        (if alwaysRaises thenExpr then
             whenFalse
         else
             [])
        @ (if alwaysRaises elseExpr then
               whenTrue
           else
               [])
    | _ -> []

/// `f ()` with these names in `set` (what is known of them) while it runs
let withFacts (set: HashSet<string>) (names: string list) (f: unit -> 'a) : 'a =
    let added = names |> List.filter (fun n -> set.Add n)

    try
        f ()
    finally
        for n in added do
            set.Remove n |> ignore

/// `f ()` with these variables known not to be null, and these known positive
let withKnown (ctx: Ctx) (nonNull: string list) (positive: string list) (f: unit -> 'a) : 'a =
    withFacts ctx.NonNull nonNull (fun () -> withFacts ctx.Positive positive f)

/// `f ()` with these variables known non-null, positive, and non-negative
let withKnownFacts
    (ctx: Ctx)
    (nonNull: string list)
    (positive: string list)
    (nonNeg: string list)
    (f: unit -> 'a)
    : 'a
    =
    withFacts ctx.NonNull nonNull (fun () -> withFacts ctx.Positive positive (fun () -> withFacts ctx.NonNeg nonNeg f))

let clearIdentFacts (ctx: Ctx) (name: string) : unit =
    ctx.NonNull.Remove name |> ignore
    ctx.Positive.Remove name |> ignore
    ctx.NonNeg.Remove name |> ignore
    ctx.BoundedBelowMax.Remove name |> ignore
    ctx.Lengths.Remove name |> ignore

    let depKeys =
        ctx.Lengths
        |> Seq.choose (fun kv ->
            if fst kv.Value = name then
                Some kv.Key
            else
                None
        )
        |> List.ofSeq

    for k in depKeys do
        ctx.Lengths.Remove k |> ignore

    ctx.ConstLen.Remove name |> ignore
    ctx.KnownTypes.Remove name |> ignore

    ctx.InBounds.RemoveWhere(fun k ->
        k.StartsWith(name + "|", System.StringComparison.Ordinal)
        || k.EndsWith("|" + name, System.StringComparison.Ordinal)
    )
    |> ignore

let withScopedIdent (ctx: Ctx) (id: Fable.Ident) (f: unit -> 'a) : 'a =
    let name = id.Name

    let savedVar =
        match ctx.Vars.TryGetValue name with
        | true, v -> Some v
        | _ -> None

    let savedBoxed = ctx.Boxed.Contains name
    let savedNonNull = ctx.NonNull.Contains name
    let savedPositive = ctx.Positive.Contains name
    let savedNonNeg = ctx.NonNeg.Contains name
    let savedBounded = ctx.BoundedBelowMax.Contains name

    let savedLenKey =
        match ctx.Lengths.TryGetValue name with
        | true, v -> Some v
        | _ -> None

    let savedLenVals =
        ctx.Lengths
        |> Seq.choose (fun kv ->
            if fst kv.Value = name then
                Some(kv.Key, kv.Value)
            else
                None
        )
        |> List.ofSeq

    let savedConstLen =
        match ctx.ConstLen.TryGetValue name with
        | true, n -> Some n
        | _ -> None

    let savedKnownType =
        match ctx.KnownTypes.TryGetValue name with
        | true, t -> Some t
        | _ -> None

    let savedBounds =
        ctx.InBounds
        |> Seq.filter (fun k ->
            k.StartsWith(name + "|", System.StringComparison.Ordinal)
            || k.EndsWith("|" + name, System.StringComparison.Ordinal)
        )
        |> List.ofSeq

    ctx.Vars.Remove name |> ignore
    ctx.Boxed.Remove name |> ignore
    clearIdentFacts ctx name

    try
        f ()
    finally
        ctx.Vars.Remove name |> ignore
        ctx.Boxed.Remove name |> ignore
        clearIdentFacts ctx name

        match savedVar with
        | Some v -> ctx.Vars[name] <- v
        | None -> ()

        if savedBoxed then
            ctx.Boxed.Add name |> ignore

        if savedNonNull then
            ctx.NonNull.Add name |> ignore

        if savedPositive then
            ctx.Positive.Add name |> ignore

        if savedNonNeg then
            ctx.NonNeg.Add name |> ignore

        if savedBounded then
            ctx.BoundedBelowMax.Add name |> ignore

        match savedLenKey with
        | Some v -> ctx.Lengths[name] <- v
        | None -> ()

        for (k, v) in savedLenVals do
            ctx.Lengths[k] <- v

        match savedConstLen with
        | Some n -> ctx.ConstLen[name] <- n
        | None -> ()

        match savedKnownType with
        | Some t -> ctx.KnownTypes[name] <- t
        | None -> ()

        for k in savedBounds do
            ctx.InBounds.Add k |> ignore

let tryLengthTarget (ctx: Ctx) (e: Fable.Expr) : (string * Fable.Type) option =
    let ofArgs (info: Fable.CallInfo) =
        match info.ThisArg, info.Args with
        | Some(Fable.IdentExpr c), []
        | None, [ Fable.IdentExpr c ] when not c.IsMutable -> Some(c.Name, c.Type)
        | _ -> None

    match e with
    | Fable.Call(Fable.Import(imp, _, _), info, _, _) when imp.Selector = "get_Length" || imp.Selector = "Length" ->
        ofArgs info
    | Fable.IdentExpr n when not n.IsMutable ->
        match ctx.Lengths.TryGetValue n.Name with
        | true, (cName, cTy) when ctx.Vars.ContainsKey cName -> Some(cName, cTy)
        | _ -> None
    | _ -> None

let tryConstArrayLen (e: Fable.Expr) : int option =
    match e with
    | Fable.Value(Fable.NewArray(Fable.ArrayValues vs, _, _), _) -> Some vs.Length
    | Fable.Value(Fable.NewArray(Fable.ArrayAlloc(Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 k, _), _)),
                                 _,
                                 _),
                  _) when k >= 0 -> Some k
    | Fable.Call(Fable.Import(imp, _, _),
                 {
                     ThisArg = None
                     Args = [ Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 k, _), _) ]
                 },
                 _,
                 _) when
        (imp.Selector = "ZeroCreate" || imp.Selector = "Create")
        && imp.Path.EndsWith("ArrayModule", System.StringComparison.Ordinal)
        && k >= 0
        ->
        Some k
    | _ -> None

let isKnownPosExpr (ctx: Ctx) (e: Fable.Expr) : bool =
    match e with
    | Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 k, _), _) -> k > 0
    | Fable.IdentExpr id -> ctx.Positive.Contains id.Name
    | _ -> false

let isKnownNonNegExpr (ctx: Ctx) (e: Fable.Expr) : bool =
    match e with
    | Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 k, _), _) -> k >= 0
    | Fable.IdentExpr id -> ctx.NonNeg.Contains id.Name || ctx.Positive.Contains id.Name
    | _ when (tryLengthTarget ctx e).IsSome -> true
    | Fable.Operation(Fable.Binary(BinaryPlus,
                                   Fable.IdentExpr v,
                                   Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 1, _), _)),
                      _,
                      _,
                      _)
    | Fable.Operation(Fable.Binary(BinaryPlus,
                                   Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 1, _), _),
                                   Fable.IdentExpr v),
                      _,
                      _,
                      _) when ctx.BoundedBelowMax.Contains v.Name -> true
    | _ -> false

let isArrayIndexInBounds (ctx: Ctx) (a: Fable.Expr) (i: Fable.Expr) : bool =
    match a, i with
    | Fable.IdentExpr ai, Fable.IdentExpr ii -> ctx.InBounds.Contains(ai.Name + "|" + ii.Name)
    | Fable.IdentExpr ai, Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 k, _), _) when k >= 0 ->
        match ctx.ConstLen.TryGetValue ai.Name with
        | true, len -> k < len
        | _ -> false
    | _ -> false

/// The type a `Type` value stands for, where it is known here: `typeof<T>`, `typedefof<T>`, a
/// `MakeGenericType` of known types, a variable bound to one (what an ahead-of-time compiler can
/// see, as .NET's NativeAOT does)
let rec staticTypeOf (ctx: Ctx) (e: Fable.Expr) : Fable.Type option =
    match e with
    | Fable.IdentExpr i when not i.IsMutable ->
        match ctx.KnownTypes.TryGetValue i.Name with
        | true, t -> Some t
        | _ -> None
    | Fable.Value(Fable.TypeInfo(t, _), _) -> Some t
    | Fable.Call(Fable.Import(imp, _, _), info, _, _) when
        (imp.Selector = "TypeOf" || imp.Selector = "TypeDefOf") && info.Args.IsEmpty
        ->
        List.tryHead info.GenericArgs
    | Fable.Call(Fable.Import(imp, _, _), ({ ThisArg = Some def } as info), _, _) when imp.Selector = "MakeGenericType" ->
        let typeArgs =
            match info.Args with
            | [ Fable.Value(Fable.NewArray(Fable.ArrayValues ts, _, _), _) ] -> ts
            | ts -> ts

        match staticTypeOf ctx def with
        | Some(Fable.DeclaredType(ent, gs)) when gs.Length = typeArgs.Length ->
            let known = typeArgs |> List.map (staticTypeOf ctx)

            if known |> List.forall Option.isSome then
                Some(Fable.DeclaredType(ent, known |> List.map Option.get))
            else
                None
        | _ -> None
    | Fable.TypeCast(x, _) -> staticTypeOf ctx x
    | _ -> None

/// `neverNull`, or a variable bound to such a string and never assigned (`Ctx.NonNull`)
let neverNullIn (ctx: Ctx) (e: Fable.Expr) : bool =
    match e with
    | Fable.IdentExpr i -> ctx.NonNull.Contains i.Name
    | _ -> neverNull e

/// Has this type a default value here (what .NET's is: zero, false, null of a string, None)?
let rec hasDefault (ctx: Ctx) (t: Fable.Type) : bool =
    match t with
    | Fable.Number _
    | Fable.Char
    | Fable.Boolean
    | Fable.String
    | Fable.Unit
    | Fable.Any
    | Fable.MetaType
    | Fable.Option _
    | Fable.Nullable _ -> true
    | Fable.Array(_, (Fable.MutableArray | Fable.ImmutableArray)) -> true
    // (a function: one that raises NullReferenceException, see fable_rt.nullOf)
    | Fable.LambdaType _
    | Fable.DelegateType _ -> true
    | Fable.Tuple(ts, _) -> List.forall (hasDefault ctx) ts
    | Fable.DeclaredType(entRef, _) when
        entRef.FullName = "System.Span`1"
        || entRef.FullName = "System.ReadOnlySpan`1"
        || entRef.FullName = "System.DateOnly"
        || entRef.FullName = "System.TimeOnly"
        || entRef.FullName = "System.DateTimeOffset"
        || entRef.FullName = "System.DateTime"
        || entRef.FullName = "System.TimeSpan"
        || entRef.FullName = "System.Guid"
        || entRef.FullName = "System.Uri"
        ->
        true
    | Fable.DeclaredType(entRef, _) when (objInfo ctx None entRef).IsSome -> true
    | Fable.DeclaredType _ when
        isInterfaceType ctx.Com t
        && (
            match mapType ctx None t with
            | TOpt _ -> true
            | _ -> false
        )
        ->
        true
    | Fable.DeclaredType(entRef, genArgs) ->
        match ctx.Com.TryGetEntity entRef with
        | Some ent when
            ent.IsFSharpUnion
            && ent.UnionCases.Length = 1
            && ent.UnionCases.Head.UnionCaseFields.IsEmpty
            ->
            true
        | Some ent when
            ent.IsValueType
            && not ent.IsFSharpUnion
            && not ent.IsInterface
            && (
                match entRef.Path with
                | Fable.SourcePath _ -> true
                | _ -> false
            )
            ->
            let sub =
                if ent.GenericParameters.Length = genArgs.Length then
                    List.zip (ent.GenericParameters |> List.map (fun g -> g.Name)) genArgs
                    |> Map.ofList
                else
                    Map.empty

            ent.FSharpFields
            |> List.filter (fun f -> not f.IsStatic)
            |> List.forall (fun f -> hasDefault ctx (substFableType sub f.FieldType))
        | _ -> isWitnessClass ctx entRef
    | _ -> false

/// Adapt a lowered IR expression between `T` and `T | null` when their Zig types differ
/// (wrapping `T` into `Some` for `?T`, or unwrapping generic `?inner` to nullable `inner`).
let rec coerceTy (ctx: Ctx) (expectedTy: Ty) (expr: Expr) : Expr =
    let actualTy = typeOf expr

    if actualTy = expectedTy then
        expr
    else
        match expr with
        | ERaise(ex, _) -> ERaise(ex, expectedTy)
        | ESeq(s, last) -> ESeq(s, coerceTy ctx expectedTy last)
        | _ ->
            match actualTy, expectedTy with
            | _, TOpt inner when inner = actualTy ->
                bindArgsIn true ctx [ expr ] (fun xs -> ECon(expectedTy, "Some", xs, None))
            | TOpt inner, _ when inner = expectedTy ->
                let nullVal =
                    match expectedTy with
                    | TOpt _ -> Some(ECon(expectedTy, "None", [], None))
                    | TPrim "fable_rt.String" -> Some(ELit("@as(fable_rt.String, null)", expectedTy))
                    | TPrim "fable_rt.reflect.Type" ->
                        ctx.State.UsesRuntime <- true
                        Some(EEmit("fable_rt.reflect.nullType()", [], expectedTy))
                    | TEnt({ Name = "fable_rt.Array" }, _) ->
                        ctx.State.UsesRuntime <- true
                        Some(EEmit("fable_rt.arrayNull($R)", [], expectedTy))
                    | _ -> None

                match nullVal with
                | Some nv ->
                    bindArgs
                        ctx
                        [ expr ]
                        (fun xs ->
                            EIf(ETest(xs.Head, "None", actualTy), nv, EGet(xs.Head, PSome, expectedTy), expectedTy)
                        )
                | None -> expr
            | _ -> expr

/// Unwrap an interface struct option, raising NullReferenceException when null.
let unwrapIface (ctx: Ctx) (x: Expr) : Expr =
    match typeOf x with
    | TOpt innerTy ->
        ctx.State.UsesRuntime <- true
        ERt("fable_rt.nonNullUnwrap($0)", [ x ], innerTy)
    | _ -> x

/// The default value of a class's field the constructor does not set (`[<DefaultValue>] val
/// mutable`), if its type has one
let fieldDefaults (ctx: Ctx) (ent: Fable.Entity) (name: string) : Fable.Expr option =
    ent.FSharpFields
    |> List.tryFind (fun f -> f.Name = name && not f.IsStatic && hasDefault ctx f.FieldType)
    |> Option.map (fun f ->
        // (a function field is kept uncurried: its null is made at that shape, not adapted to it)
        let ty =
            match f.FieldType with
            | Fable.LambdaType _ -> FableTransforms.uncurryType f.FieldType
            | t -> t

        Fable.Call(
            Fable.Import(
                {
                    Selector = "DefaultOf"
                    Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators.Unchecked"
                    Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                },
                Fable.Any,
                None
            ),
            Fable.CallInfo.Create(genArgs = [ ty ]),
            ty,
            None
        )
    )

/// The item type of `IEnumerator<T>`.
let enumeratorItem (t: Fable.Type) : Fable.Type =
    match t with
    | Fable.DeclaredType(_, [ item ]) -> item
    | _ -> Fable.Any

/// What Fable makes of `for x in s do body` after `let enumerator = s.GetEnumerator()`:
/// `try (while enumerator.MoveNext() do body) finally enumerator.Dispose()`, perhaps followed
/// by more code. The body of the loop, and what follows the loop.
let forInLoop (enumerator: string) (rest: Fable.Expr) : (Fable.Expr * Fable.Expr option) option =
    let isMoveNext (c: Fable.Expr) =
        match c with
        | Fable.Call(Fable.Import(imp, _, _), info, _, _) when imp.Selector = "MoveNext" ->
            match info.ThisArg with
            | Some(Fable.IdentExpr e) -> e.Name = enumerator
            | _ -> false
        | _ -> false

    let rec loopOf (e: Fable.Expr) =
        match e with
        | Fable.WhileLoop(c, body, _) when isMoveNext c -> Some body
        | Fable.TryCatch(body, None, Some _, _) -> loopOf body
        | _ -> None

    match rest with
    | Fable.Sequential(first :: next) when (loopOf first).IsSome ->
        Some(
            (loopOf first).Value,
            (if next.IsEmpty then
                 None
             else
                 Some(Fable.Sequential next))
        )
    | _ -> loopOf rest |> Option.map (fun body -> body, None)

/// A delegate's body that applies an expression to the delegate's own parameters, in order and
/// nothing else, when that expression is a computation (not a variable, a function or an
/// import): the expression, and the body with another in its place
let etaHead (args: Fable.Ident list) (body: Fable.Expr) : (Fable.Expr * (Fable.Expr -> Fable.Expr)) option =
    let names = args |> List.map (fun a -> a.Name)

    let isParams (xs: Fable.Expr list) =
        xs.Length = names.Length
        && List.forall2
            (fun (x: Fable.Expr) n ->
                match x with
                | Fable.IdentExpr i -> i.Name = n
                | _ -> false
            )
            xs
            names

    // (the applications from the outside in, until those peeled give exactly the parameters)
    let rec peel (e: Fable.Expr) (given: Fable.Expr list) : (Fable.Expr * (Fable.Expr -> Fable.Expr)) option =
        if not given.IsEmpty && isParams given then
            Some(e, id)
        elif given.Length >= names.Length then
            None
        else
            match e with
            // (an application of more than the parameters: the arguments before them are applied
            // once, `f x` of `f x a b`)
            | Fable.CurriedApply(f, xs, t, r) when
                (xs @ given).Length > names.Length
                && isParams (List.skip ((xs @ given).Length - names.Length) (xs @ given))
                ->
                let inXs = names.Length - given.Length
                let before = List.take (xs.Length - inXs) xs
                let after = List.skip (xs.Length - inXs) xs

                // (the type of `f` with `before` applied)
                let rec drop (n: int) (ty: Fable.Type) =
                    if n = 0 then
                        ty
                    else
                        match ty with
                        | Fable.LambdaType(_, ret) -> drop (n - 1) ret
                        | other -> other

                let head = Fable.CurriedApply(f, before, drop before.Length f.Type, r)
                Some(head, (fun h -> Fable.CurriedApply(h, after, t, r)))
            | Fable.CurriedApply(f, xs, t, r) ->
                peel f (xs @ given)
                |> Option.map (fun (head, rebuild) -> head, (fun h -> Fable.CurriedApply(rebuild h, xs, t, r)))
            | _ -> None

    match peel body [] with
    | Some(head, rebuild) ->
        let isComputation =
            match head with
            | Fable.IdentExpr _
            | Fable.Import _
            | Fable.Lambda _
            | Fable.Delegate _
            | Fable.Value _ -> false
            | _ -> true

        let rec uses (e: Fable.Expr) =
            match e with
            | Fable.IdentExpr i -> List.contains i.Name names
            | _ -> AST.getSubExpressions e |> List.exists uses

        if isComputation && not (uses head) then
            Some(head, rebuild)
        else
            None
    | None -> None

/// Whether a type still has type parameters in it
let rec hasTypeParams (t: Fable.Type) : bool =
    match t with
    | Fable.GenericParam _ -> true
    | _ -> t.Generics |> List.exists hasTypeParams

/// The names of the type parameters a type mentions
let rec typeParamNames (t: Fable.Type) : string list =
    match t with
    | Fable.GenericParam(name, _, _) -> [ name ]
    | _ -> t.Generics |> List.collect typeParamNames

/// Whether a type is another with obj in some of its places
let rec moreGeneral (t: Fable.Type) (wanted: Fable.Type) : bool =
    match t, wanted with
    | Fable.Any, _ -> true
    | Fable.LambdaType(a, r), Fable.LambdaType(a2, r2) -> moreGeneral a a2 && moreGeneral r r2
    | _ -> t = wanted

/// Propagates an outer `T | null` type into inner `DefaultOf` (`null` literal) expressions.
let rec wrapNullCast (wanted: Fable.Type) (e: Fable.Expr) : Fable.Expr =
    match wanted with
    | Fable.Nullable(inner, false) ->
        match e with
        | Fable.Call(Fable.Import(imp, ct, cr), info, t, r) when
            imp.Selector = "DefaultOf" && unwrapNullness inner = unwrapNullness t
            ->
            Fable.Call(Fable.Import(imp, ct, cr), { info with GenericArgs = [ wanted ] }, wanted, r)
        | Fable.TypeCast(Fable.Call(Fable.Import(imp, ct, cr), info, t, r), _) when
            imp.Selector = "DefaultOf" && unwrapNullness inner = unwrapNullness t
            ->
            Fable.Call(Fable.Import(imp, ct, cr), { info with GenericArgs = [ wanted ] }, wanted, r)
        | Fable.TypeCast(x, _) ->
            let x' = wrapNullCast wanted x

            if x'.Type = wanted then
                x'
            else
                Fable.TypeCast(x', wanted)
        | Fable.IfThenElse(g, a, b, r) ->
            let ifE = Fable.IfThenElse(g, wrapNullCast wanted a, wrapNullCast wanted b, r)

            if ifE.Type = wanted then
                ifE
            else
                Fable.TypeCast(ifE, wanted)
        | Fable.Let(id, v, body) -> Fable.Let(id, v, wrapNullCast wanted body)
        | Fable.Sequential es when not es.IsEmpty ->
            let rev = List.rev es
            Fable.Sequential(List.rev (wrapNullCast wanted rev.Head :: rev.Tail))
        | Fable.DecisionTree(expr, targets) ->
            let targets' =
                targets |> List.map (fun (ids, body) -> ids, wrapNullCast wanted body)

            let dt = Fable.DecisionTree(expr, targets')

            if dt.Type = wanted then
                dt
            else
                Fable.TypeCast(dt, wanted)
        | _ -> e
    | _ -> e

let rec wrapFnNullCast (fnTy: Fable.Type) (fnExpr: Fable.Expr) : Fable.Expr =
    let rec peel (n: int) (t: Fable.Type) =
        match n, t with
        | 0, _ -> Some t
        | n, Fable.LambdaType(_, r) when n > 0 -> peel (n - 1) r
        | _, Fable.DelegateType(_, r) -> Some r
        | _ -> None

    match fnExpr, fnTy with
    | Fable.Lambda(arg, body, name), Fable.LambdaType(_, rest) -> Fable.Lambda(arg, wrapFnNullCast rest body, name)
    | Fable.Delegate(args, body, name, tags), _ ->
        match peel args.Length fnTy with
        | Some ret -> Fable.Delegate(args, wrapNullCast ret body, name, tags)
        | None -> fnExpr
    | _ -> wrapNullCast fnTy fnExpr

/// A value made at a more general type than the variable it is bound to has: F# generalizes
/// `let a = Ok string`, and where Fable puts the value in at its use, its type parameters are obj
/// (`Ok (fun (v: obj) -> string v)`) though the use is at `Result<int -> string, _>`. The value,
/// fitted to the type wanted: a function taking obj where a value of a type is given takes that
/// value and boxes it, as .NET's generic code would see it as that type.
let rec adaptTo (com: Compiler) (wanted: Fable.Type) (e: Fable.Expr) : Fable.Expr =
    if e.Type = wanted then
        e
    else
        match e, wanted with
        // (a function: applied in the body, so it keeps its type there)
        | Fable.Lambda(arg, body, name), Fable.LambdaType((Fable.LambdaType _ as ta), tr) when
            arg.Type <> ta && moreGeneral arg.Type ta
            ->
            let typed = { arg with Type = ta }

            let body =
                body
                |> AST.visitFromInsideOut (fun x ->
                    match x with
                    | Fable.IdentExpr i when i.Name = arg.Name -> Fable.IdentExpr typed
                    | Fable.CurriedApply(Fable.IdentExpr i, args, Fable.Any, r) when i.Name = arg.Name ->
                        let ret =
                            List.fold
                                (fun t _ ->
                                    match t with
                                    | Fable.LambdaType(_, r) -> r
                                    | _ -> t
                                )
                                ta
                                args

                        // (each argument as the parameter's type wants it)
                        let args =
                            List.fold
                                (fun (t, acc) (a: Fable.Expr) ->
                                    match t with
                                    | Fable.LambdaType(p, rest) -> rest, adaptTo com p a :: acc
                                    | _ -> t, a :: acc
                                )
                                (ta, [])
                                args
                            |> snd
                            |> List.rev

                        Fable.TypeCast(Fable.CurriedApply(Fable.IdentExpr typed, args, ret, r), Fable.Any)
                    | _ -> x
                )

            Fable.Lambda(typed, adaptTo com tr body, name)
        | Fable.Lambda(arg, body, name), Fable.LambdaType(ta, tr) when arg.Type = Fable.Any && ta <> Fable.Any ->
            let typed =
                { arg with
                    Name = arg.Name + "_typed"
                    Type = ta
                }

            Fable.Lambda(
                typed,
                Fable.Let(arg, Fable.TypeCast(Fable.IdentExpr typed, Fable.Any), adaptTo com tr body),
                name
            )
        | Fable.Lambda(arg, body, name), Fable.LambdaType(ta, tr) when arg.Type = ta ->
            Fable.Lambda(arg, adaptTo com tr body, name)
        | Fable.Value(Fable.NewUnion(values, tag, ent, genArgs), r), Fable.DeclaredType(ent2, targs) when
            ent.FullName = ent2.FullName && genArgs.Length = targs.Length
            ->
            match com.TryGetEntity ent with
            | Some entity when tag < entity.UnionCases.Length ->
                let subst =
                    List.zip (entity.GenericParameters |> List.map (fun g -> g.Name)) targs
                    |> Map.ofList

                let fields =
                    entity.UnionCases[tag].UnionCaseFields
                    |> List.map (fun f -> substFableType subst f.FieldType)

                if fields.Length = values.Length then
                    Fable.Value(Fable.NewUnion(List.map2 (adaptTo com) fields values, tag, ent, targs), r)
                else
                    e
            | _ -> e
        | Fable.Value(Fable.NewOption(Some v, _, isStruct), r), Fable.Option(item, _) ->
            Fable.Value(Fable.NewOption(Some(adaptTo com item v), item, isStruct), r)
        | Fable.Value(Fable.NewTuple(values, isStruct), r), Fable.Tuple(ts, _) when ts.Length = values.Length ->
            Fable.Value(Fable.NewTuple(List.map2 (adaptTo com) ts values, isStruct), r)
        | _, Fable.Nullable(inner, false) ->
            let e = wrapNullCast wanted e

            if e.Type = wanted then
                e
            else
                let adapted = adaptTo com inner e

                if adapted.Type = wanted then
                    adapted
                else
                    Fable.TypeCast(adapted, wanted)
        // (a value boxed and unboxed again)
        | Fable.TypeCast(inner, Fable.Any), _ when inner.Type = wanted -> inner
        // (an object where a value of a type is wanted: unboxed)
        | _, _ when
            unwrapNullness e.Type = Fable.Any
            && not (hasTypeParams wanted)
            && unwrapNullness wanted <> Fable.Any
            ->
            match wanted with
            | Fable.LambdaType _
            | Fable.DelegateType _ -> e
            | _ -> Fable.TypeCast(e, wanted)
        | _ -> e

/// What the shared QuotationEmitter makes of a quotation, with the plain values it gives where
/// the library takes objects boxed (a value, the items of an array of objects)
let boxQuotationArgs (e: Fable.Expr) : Fable.Expr =
    let asObj (x: Fable.Expr) =
        if x.Type = Fable.Any then
            x
        else
            Fable.TypeCast(x, Fable.Any)

    let rec go (x: Fable.Expr) =
        match x with
        | Fable.Call(Fable.Import(imp, it, ir), info, t, r) when imp.Selector = "mkValue" ->
            let args =
                match info.Args |> List.map go with
                | v :: rest -> asObj v :: rest
                | [] -> []

            Fable.Call(Fable.Import(imp, it, ir), { info with Args = args }, t, r)
        | Fable.Value(Fable.NewArray(Fable.ArrayValues items, Fable.Any, kind), r) ->
            Fable.Value(Fable.NewArray(Fable.ArrayValues(items |> List.map (go >> asObj)), Fable.Any, kind), r)
        | _ -> AST.visit go x

    go e

/// The names an expression reads that it does not bind itself (over-approximated where a decision
/// tree binds them: that only makes a caller more careful)
let rec freeNamesOf (e: Fable.Expr) : Set<string> =
    match e with
    | Fable.IdentExpr i -> Set.singleton i.Name
    | Fable.Lambda(a, b, _) -> (freeNamesOf b).Remove a.Name
    | Fable.Delegate(ps, b, _, _) -> ps |> List.fold (fun (acc: Set<string>) p -> acc.Remove p.Name) (freeNamesOf b)
    | Fable.Let(id, v, b) -> Set.union (freeNamesOf v) ((freeNamesOf b).Remove id.Name)
    | _ ->
        AST.getSubExpressions e
        |> List.fold (fun acc x -> Set.union acc (freeNamesOf x)) Set.empty

/// How many arguments a function value really takes before it gives a function of the rest:
/// its lambdas' parameters, or a known function's (0 when not known)
let rec stageArityOf (ctx: Ctx) (g: Fable.Expr) : int =
    match g with
    | Fable.Lambda(_, (Fable.Lambda _ as inner), _) -> 1 + stageArityOf ctx inner
    | Fable.Lambda _ -> 1
    | Fable.Delegate(ps, _, _, _) -> ps.Length
    // (a variable that holds a function value: what its type takes at once)
    | Fable.IdentExpr i when ctx.Vars.ContainsKey i.Name ->
        match ctx.Vars[i.Name].Ty with
        | TFn(ps, _) -> ps.Length
        | _ -> 0
    | Fable.IdentExpr _ ->
        match tryCallable ctx g with
        | Some c -> c.Arity
        | None -> 0
    | _ -> 0

/// The type of what a function value gives after `k` of its arguments
let rec peelArgs (t: Fable.Type) (k: int) : Fable.Type =
    if k <= 0 then
        t
    else
        match t with
        | Fable.LambdaType(_, ret) -> peelArgs ret (k - 1)
        | Fable.DelegateType(ps, ret) when ps.Length <= k -> peelArgs ret (k - ps.Length)
        | _ -> t

/// Resolve an interface member access/call against a `KIface` vtable struct: returns
/// `(directSlot, getterSlot)` where `directSlot` matches a callable slot (or indexed getter)
/// and `getterSlot` matches a 0-arg `"get_..."` property slot (e.g. a property returning a function).
let resolveIfaceSlot
    (ctx: Ctx)
    (xType: Fable.Type)
    (ifaceStructTy: Ty)
    (infoName: string)
    (argCount: int option)
    : (string * Ty list * Ty) option * (string * Ty) option
    =
    let fields = caseFields ifaceStructTy ""
    // (a mangled interface's member is named in full: `Ns.IFoo.get_Bar`)
    let short = infoName.Substring(infoName.LastIndexOf '.' + 1)

    // (and its overload's hash, `SumZ35CD86D0`)
    let name =
        if fields |> List.exists (fun (f, _) -> f = short || f = "get_" + short) then
            short
        else
            System.Text.RegularExpressions.Regex.Replace(short, "Z?[0-9A-F]{8}$", "")

    // (an overload: the one whose hash Fable gave the name, `get_ItemZ524259A4`)
    let name =
        if fields |> List.exists (fun (f, _) -> f = name || f = "get_" + name) then
            name
        else
            match unwrapNullness xType with
            | Fable.DeclaredType(iref, _) ->
                match ctx.Com.TryGetEntity iref with
                | Some ient ->
                    let genParams = ient.GenericParameters |> List.map (fun g -> g.Name)

                    ient.MembersFunctionsAndValues
                    |> Seq.filter (fun m -> m.IsDispatchSlot && m.CompiledName = name)
                    |> Seq.tryFind (fun m ->
                        let groups = m.CurriedParameterGroups |> List.map (List.map (fun p -> p.Type))

                        short = name + OverloadSuffix.getHash genParams groups
                    )
                    |> Option.map (fun m -> slotKey ient m.CompiledName (paramTypesOf m))
                    |> Option.defaultValue name
                | None -> name
            | _ -> name

    let directSlot =
        fields
        |> List.tryPick (fun (f, fty) ->
            match fty with
            | TSlot(ptys, ret) when
                (f = name
                 || (argCount.IsSome
                     && f = "get_" + name
                     && not (ptys.Length = 1 && isVoid ptys.Head)))
                && (
                    match argCount with
                    | Some n -> ptys.Length = n
                    | None -> true
                )
                ->
                Some(f, ptys, ret)
            | _ -> None
        )

    let getterSlot =
        fields
        |> List.tryPick (fun (f, fty) ->
            match fty with
            | TSlot([ p ], ret) when isVoid p && (f = "get_" + name || f = name) -> Some(f, ret)
            | _ -> None
        )

    directSlot, getterSlot

let rec lw (ctx: Ctx) (e: Fable.Expr) : Expr =
    match e with
    // (a unit that does something, the one argument of a call (`box (ignore (f ()))`): it is done,
    // then the call made of `()`)
    | Fable.Call(callee,
                 ({
                      Args = [ x ]
                      ThisArg = None
                  } as info),
                 t,
                 r) when
        x.Type = Fable.Unit
        && (
            match x with
            | Fable.Value(Fable.UnitConstant, _) -> false
            | _ -> true
        )
        ->
        lw
            ctx
            (Fable.Sequential
                [
                    x
                    Fable.Call(callee, { info with Args = [ Fable.Value(Fable.UnitConstant, None) ] }, t, r)
                ])
    // (a function cast to a type that is not a function and then applied, as the inliner
    // leaves an SRTP operator's result (Aether's `(Set ^= optic) value`): the function applied)
    | Fable.CurriedApply(Fable.TypeCast(f, castTo), args, t, r) when
        (match f.Type, castTo with
         | (Fable.LambdaType _ | Fable.DelegateType _), (Fable.LambdaType _ | Fable.DelegateType _ | Fable.Any) -> false
         | (Fable.LambdaType _ | Fable.DelegateType _), _ -> true
         | _ -> false)
        ->
        lw ctx (Fable.CurriedApply(f, args, t, r))
    // a quotation: what the shared emitter makes of it, nodes of the library's Quotation.fs
    | Fable.Quote(body, _, _) -> lw ctx (boxQuotationArgs (QuotationEmitter.emitQuotedExpr ctx.Com body))
    // ---- objects of classes that take part in inheritance ----
    // `base`: the object itself, seen as its parent class
    | Fable.Value(Fable.BaseValue(Some id, _), _) -> lw ctx (Fable.IdentExpr id)
    // `Circle 1.0`: allocate the object first, then run its constructor on it.
    | Fable.Call(callee, info, Fable.DeclaredType(cls, clsArgs), r) when
        isConstructorCall ctx.Com info && (objInfo ctx r cls).IsSome
        ->
        let o = (objInfo ctx r cls).Value

        if o.IsAbstract then
            fail r "the abstract class %s cannot be made" o.FullName

        let targs = clsArgs |> List.map (mapTypeArg ctx r)
        let chainTy = TEnt(o.Chain, targs)
        ctx.State.AllocChains.Add chainTy
        let typeRef = objTypeRef o targs
        let v = ctx.State.NewVar("made", tObj, VLocal, false)

        let madeId =
            { AST.makeTypedIdent (Fable.DeclaredType(cls, clsArgs)) $"__made_%d{v.Id}" with IsThisArgument = true }

        ctx.Vars[madeId.Name] <- v
        let alloc = EEmit($"fable_rt.objAlloc(%s{zigType chainTy}, %s{typeRef})", [], tObj)

        let ctorCall =
            Fable.Call(
                callee,
                { info with
                    ThisArg = Some(Fable.IdentExpr madeId)
                    GenericArgs =
                        if info.GenericArgs.IsEmpty then
                            clsArgs
                        else
                            info.GenericArgs
                },
                Fable.Unit,
                r
            )

        ELet(v, alloc, ESeq(lwStmt ctx ctorCall, EVar v))
    // `base.Describe()`: the implementation its parent class has, called directly
    | Fable.Call(Fable.Get(Fable.Value(Fable.BaseValue(Some id, baseTy), _), Fable.FieldGet field, _, _), call, t, r) when
        (objOfType ctx r baseTy).IsSome
        ->
        let o = (objOfType ctx r baseTy).Value
        let slot = slotName ctx.Com call field.Name
        let target = implementationOf ctx.Com r o slot

        // (the implementing class's type arguments, as the base gives them)
        let typeArgs =
            match ancestors o |> List.tryFind (fun k -> classImplements ctx.Com k slot) with
            | Some k -> argsOfLevel ctx r o baseTy k
            | None -> []

        let args =
            match call.Args with
            | [] -> [ EUnit ]
            | given -> given |> List.map (lw ctx)

        bindArgs ctx (lw ctx (Fable.IdentExpr id) :: args) (fun xs -> ECall(target, typeArgs, xs, mapType ctx r t))
    // `shape.Area()`: through the table of the class that introduced the member
    | Fable.Call(Fable.Get(x, Fable.FieldGet field, _, _), call, t, r) when
        (match objOfType ctx r x.Type with
         | Some o -> (virtualSlot o (slotName ctx.Com call field.Name)).IsSome
         | None -> false)
        ->
        let o = (objOfType ctx r x.Type).Value
        let slot = slotName ctx.Com call field.Name
        let level, slotTy = (virtualSlot o slot).Value
        let largs = argsOfLevel ctx r o x.Type level

        let slotTy =
            substTy
                (if level.Gens.Length = largs.Length then
                     List.zip level.Gens largs |> Map.ofList
                 else
                     Map.empty)
                slotTy

        let args =
            match call.Args with
            | [] -> [ EUnit ]
            | given -> given |> List.map (lw ctx)

        let table = TPtr(TEnt(level.Table.Value, largs), true)

        bindArgs
            ctx
            (lw ctx x :: args)
            (fun given ->
                // (the object: checked for null and borrowed)
                withBorrowedObj
                    ctx
                    x
                    given.Head
                    (fun o ->
                        let fn =
                            EGet(EEmit($"fable_rt.objVt($R, $0, %d{level.Depth})", [ o ], table), PField slot, slotTy)

                        ECallVt(fn, o, given.Tail, mapType ctx r t)
                    )
            )
    // an abstract property read: its getter, through the table
    | Fable.Get(x, Fable.FieldGet field, t, r) when
        (match objOfType ctx r x.Type with
         | Some o -> (virtualSlot o ("get_" + field.Name.Substring(field.Name.LastIndexOf '.' + 1))).IsSome
         | None -> false)
        ->
        let o = (objOfType ctx r x.Type).Value
        let slot = "get_" + field.Name.Substring(field.Name.LastIndexOf '.' + 1)
        let level, slotTy = (virtualSlot o slot).Value
        let largs = argsOfLevel ctx r o x.Type level

        let slotTy =
            substTy
                (if level.Gens.Length = largs.Length then
                     List.zip level.Gens largs |> Map.ofList
                 else
                     Map.empty)
                slotTy

        let table = TPtr(TEnt(level.Table.Value, largs), true)

        bindArgs
            ctx
            [ lw ctx x ]
            (fun given ->
                // (the object: checked for null and borrowed)
                withBorrowedObj
                    ctx
                    x
                    given.Head
                    (fun o ->
                        let fn =
                            EGet(EEmit($"fable_rt.objVt($R, $0, %d{level.Depth})", [ o ], table), PField slot, slotTy)

                        let retTy =
                            match slotTy with
                            | TFn(_, ret) -> ret
                            | _ -> mapType ctx r t

                        ECallVt(fn, o, [ EUnit ], retTy)
                    )
            )
    // a field of an object: in the part of the chain of the class that declares it
    | Fable.Get(x, Fable.FieldGet field, _, r) when
        (match objOfType ctx r x.Type with
         | Some o -> (fieldOwner o field.Name).IsSome
         | None -> false)
        ->
        let o = (objOfType ctx r x.Type).Value
        let level = (fieldOwner o field.Name).Value
        let largs = argsOfLevel ctx r o x.Type level
        let part = TEnt(level.Part, largs)
        let fty = caseFields part "" |> List.find (fun (f, _) -> f = field.Name) |> snd
        let parts = partNamesOf ctx r level largs

        bindArgs
            ctx
            [ lw ctx x ]
            (fun given ->
                // (the object: checked for null and borrowed)
                withBorrowedObj
                    ctx
                    x
                    given.Head
                    (fun o ->
                        EGet(
                            EEmit($"fable_rt.objPart($R, &[_]type{{ %s{parts} }}, $0)", [ o ], TPtr(part, false)),
                            PField field.Name,
                            fty
                        )
                    )
            )
    | Fable.Set(x, Fable.FieldSet name, _, value, r) when
        (match objOfType ctx r x.Type with
         | Some o -> (fieldOwner o name).IsSome
         | None -> false)
        ->
        let o = (objOfType ctx r x.Type).Value
        let level = (fieldOwner o name).Value
        let largs = argsOfLevel ctx r o x.Type level
        let part = TEnt(level.Part, largs)
        let fields = caseFields part ""
        let fieldIdx = fields |> List.findIndex (fun (f, _) -> f = name)
        let fty = snd fields[fieldIdx]
        let parts = partNamesOf ctx r level largs

        bindArgs
            ctx
            [ lw ctx x; lw ctx value ]
            (fun given ->
                // (the object: checked for null and borrowed)
                withBorrowedObj
                    ctx
                    x
                    given[0]
                    (fun o ->
                        let place =
                            if ctx.InCtor then
                                EGet(
                                    EEmit($"objInit:%d{fieldIdx}:%s{parts}", [ o ], TPtr(part, false)),
                                    PField name,
                                    fty
                                )
                            else
                                EGet(
                                    EEmit(
                                        $"fable_rt.objPart($R, &[_]type{{ %s{parts} }}, $0)",
                                        [ o ],
                                        TPtr(part, false)
                                    ),
                                    PField name,
                                    fty
                                )

                        EStore(place, given[1])
                    )
            )
    // (what Fable's curry and uncurry of an option of functions call: `Option.map`)
    | Fable.Call(Fable.Import(imp, _, _), info, t, r) when
        imp.Selector = "map"
        && imp.Path.EndsWith("/Option.zig", System.StringComparison.Ordinal)
        ->
        match info.Args, t with
        | [ fn; source ], Fable.Option(outItem, _) ->
            // (the function's parameter says what the option holds: uncurried or not)
            let inItem =
                match fn, source.Type with
                | Fable.Delegate([ p ], _, _, _), _ -> p.Type
                | _, Fable.Option(item, _) -> item
                | _ -> Fable.Any

            lw
                ctx
                (Fable.Call(
                    Fable.Import(
                        {
                            Selector = "Map"
                            Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.OptionModule"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                        },
                        Fable.Any,
                        None
                    ),
                    { info with GenericArgs = [ inItem; outItem ] },
                    t,
                    r
                ))
        | _ -> fail r "internal: Option.map"
    // a static field of a type of this file: a module-level value
    | Fable.Get(Fable.IdentExpr id, Fable.FieldGet info, t, r) when
        ctx.State.StaticFields.ContainsKey(id.Name + "." + info.Name)
        ->
        lw
            ctx
            (Fable.IdentExpr
                { id with
                    Name = ctx.State.StaticFields[id.Name + "." + info.Name]
                    Type = t
                })
    | Fable.Set(Fable.IdentExpr id, Fable.FieldSet name, t, value, r) when
        ctx.State.StaticFields.ContainsKey(id.Name + "." + name)
        ->
        lw
            ctx
            (Fable.Set(
                Fable.IdentExpr
                    { id with
                        Name = ctx.State.StaticFields[id.Name + "." + name]
                        Type = t
                        IsMutable = true
                    },
                Fable.ValueSet,
                t,
                value,
                r
            ))
    // `x :? IDisposable` where the type of x is known (what `use` asks), and interface / fat-pointer type tests
    | Fable.Test(UnboxedOrBox inner, Fable.TypeTest t, _) when
        (match unwrapNullness t, unwrapNullness inner.Type with
         | Fable.DeclaredType(ifaceRef, _), Fable.DeclaredType(e, _) ->
             ifaceRef.FullName = "System.IDisposable"
             && e.FullName = "System.Collections.Generic.IEnumerator`1"
         | _ -> false)
        ->
        ESeq(lwStmt ctx inner, ELit("true", tBool))
    | Fable.Test(UnboxedOrBox inner, Fable.TypeTest t, _) when
        isInterfaceType ctx.Com (unwrapNullness t)
        && (implementsType ctx.Com inner.Type t).IsSome
        ->
        let impl = (implementsType ctx.Com inner.Type t).Value

        bindArgs
            ctx
            [ lw ctx inner ]
            (fun xs ->
                if not impl then
                    ELit("false", tBool)
                else
                    match typeOf xs.Head with
                    | TOpt _ -> EPrim("not", [ ETest(xs.Head, "None", typeOf xs.Head) ], tBool)
                    | _ -> ELit("true", tBool)
            )
    | Fable.Test(UnboxedOrBox inner, Fable.TypeTest t, r) when
        isInterfaceType ctx.Com inner.Type && isFatIfaceTy (mapType ctx r inner.Type)
        ->
        ifaceTypeTest ctx r inner t
    // `o :? T` of an `obj` (not one F# made by boxing a value of a known type, as `use` does)
    | Fable.Test(x, Fable.TypeTest t, r) when
        unwrapNullness x.Type = Fable.Any
        && (let (Unboxed inner) = x in unwrapNullness inner.Type = Fable.Any)
        ->
        match unwrapNullness t with
        // (`o :? System.Array`: any array)
        | Fable.DeclaredType(cls, []) when cls.FullName = "System.Array" ->
            ctx.State.UsesRuntime <- true
            bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.isArray($0)", xs, tBool))
        | Fable.DeclaredType(cls, gs) when (objInfo ctx r cls).IsSome ->
            let o = (objInfo ctx r cls).Value
            ctx.State.UsesRuntime <- true
            let typeRef = objTypeRef o (gs |> List.map (mapTypeArg ctx r))
            bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.anyIsClass($0, %s{typeRef})", xs, tBool))
        | _ ->
            let ty = mapType ctx r t
            let found = ctx.State.NewVar("unboxed", TOpt ty, VLocal, false)

            bindArgs
                ctx
                [ lw ctx x ]
                (fun xs ->
                    ELet(
                        found,
                        EEmit("fable_rt.tryUnbox($R, $0)", xs, TOpt ty),
                        EPrim("not", [ ETest(EVar found, "None", found.Ty) ], tBool)
                    )
                )
    // `x :? Circle`
    | Fable.Test(x, Fable.TypeTest(Fable.DeclaredType(cls, gs)), r) when
        (objInfo ctx r cls).IsSome && (objOfType ctx r x.Type).IsSome
        ->
        let o = (objInfo ctx r cls).Value
        let typeRef = objTypeRef o (gs |> List.map (mapTypeArg ctx r))
        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.objIs($0, %s{typeRef})", xs, tBool))
    | Fable.Value(kind, r) ->
        match kind with
        | Fable.UnitConstant -> EUnit
        // `null`: of a string and of `obj` (other types have no null here)
        | Fable.Null(Fable.Nullable(inner, false) as t) ->
            match mapType ctx r t with
            | TOpt _ as optTy -> ECon(optTy, "None", [], None)
            | _ -> lw ctx (Fable.Value(Fable.Null inner, r))
        | Fable.Null Fable.String -> ELit("@as(fable_rt.String, null)", tStr)
        | Fable.Null Fable.Any ->
            ctx.State.UsesRuntime <- true
            ELit("@as(fable_rt.Any, null)", tAny)
        | Fable.Null Fable.MetaType ->
            ctx.State.UsesRuntime <- true
            EEmit("fable_rt.reflect.nullType()", [], TPrim "fable_rt.reflect.Type")
        // (of an array: the array's null, see fable_array.zig)
        | Fable.Null(Fable.Array(_, (Fable.MutableArray | Fable.ImmutableArray)) as t) ->
            ctx.State.UsesRuntime <- true
            let ty = mapType ctx r t
            EEmit("fable_rt.arrayNull($R)", [], ty)
        // (of a class: no object)
        | Fable.Null t when (objOfType ctx r t).IsSome ->
            ctx.State.UsesRuntime <- true
            ELit("@as(fable_rt.Any, null)", tAny)
        | Fable.Null t ->
            match mapType ctx r t with
            | TOpt _ as optTy -> ECon(optTy, "None", [], None)
            | _ -> fail r "the Zig target does not support null of this type (%A)" t
        | Fable.BoolConstant b ->
            ELit(
                (if b then
                     "true"
                 else
                     "false"),
                tBool
            )
        | Fable.NumberConstant(Fable.NumberValue.BigInt x, _) ->
            ctx.State.UsesRuntime <- true
            EEmit("fable_rt.bigLit(\"" + string x + "\")", [], TPrim "fable_rt.BigInt")
        | Fable.NumberConstant(Fable.NumberValue.Decimal x, _) ->
            ctx.State.UsesRuntime <- true
            let bits = System.Decimal.GetBits x
            let scale = (bits[3] >>> 16) &&& 0xFF

            let m =
                (bigint (uint32 bits[2]) <<< 64)
                + (bigint (uint32 bits[1]) <<< 32)
                + bigint (uint32 bits[0])

            let m =
                if bits[3] < 0 then
                    -m
                else
                    m

            ELit($"fable_rt.decLit(%s{string m}, %d{scale})", TPrim "fable_rt.NetDecimal")
        | Fable.NumberConstant(v, _) -> ELit(numberLit r v)
        | Fable.CharConstant c -> ELit(string<int>(int c), TPrim "u16")
        | Fable.StringConstant text -> ELit(stringLiteral text, tStr)
        // (what a match without a case raises, when F# writes it out: its file, line and column
        // are not kept, its message is)
        | Fable.NewRecord(values, entRef, _) when entRef.FullName = "Microsoft.FSharp.Core.MatchFailureException" ->
            match values with
            | [ _; _; _ ] ->
                bindArgsIn
                    true
                    ctx
                    (values |> List.map (lw ctx))
                    (fun xs -> EExnNew(dotnetExnEnt ctx entRef.FullName, xs))
            | _ -> EExnNew(dotnetExnEnt ctx entRef.FullName, matchLocation ctx r)
        | Fable.NewRecord(values, entRef, _) when (tryExnEnt ctx r entRef).IsSome ->
            let ent = (tryExnEnt ctx r entRef).Value
            bindArgsIn true ctx (values |> List.map (lw ctx)) (fun xs -> EExnNew(ent, xs))
        | Fable.NewRecord(values, entRef, genArgs) ->
            let ty = TEnt(entOf ctx r entRef, genArgs |> List.map (mapTypeArg ctx r))
            let fieldTys = caseFields ty "" |> List.map snd

            let values =
                match ctx.Com.TryGetEntity entRef with
                | Some fEnt when fEnt.FSharpFields.Length = values.Length ->
                    let subst =
                        if fEnt.GenericParameters.Length = genArgs.Length then
                            List.zip (fEnt.GenericParameters |> List.map (fun g -> g.Name)) genArgs
                            |> Map.ofList
                        else
                            Map.empty

                    List.map2
                        (fun (f: Fable.Field) v -> wrapNullCast (substFableType subst f.FieldType) v)
                        fEnt.FSharpFields
                        values
                | _ -> values

            let irs =
                if fieldTys.Length = values.Length then
                    List.map2 (fun fty v -> coerceTy ctx fty (lw ctx v)) fieldTys values
                else
                    values |> List.map (lw ctx)

            bindArgsIn true ctx irs (fun xs -> ECon(ty, "", xs, None))
        | Fable.NewUnion(values, tag, entRef, genArgs) ->
            let ent = entOf ctx r entRef
            let ty = TEnt(ent, genArgs |> List.map (mapTypeArg ctx r))
            let case = fst (List.item tag ent.Cases)
            let fieldTys = caseFields ty case |> List.map snd

            let values =
                match ctx.Com.TryGetEntity entRef with
                | Some fEnt when tag < fEnt.UnionCases.Length ->
                    let fields = fEnt.UnionCases[tag].UnionCaseFields

                    if fields.Length = values.Length then
                        let subst =
                            if fEnt.GenericParameters.Length = genArgs.Length then
                                List.zip (fEnt.GenericParameters |> List.map (fun g -> g.Name)) genArgs
                                |> Map.ofList
                            else
                                Map.empty

                        List.map2
                            (fun (f: Fable.Field) v -> wrapNullCast (substFableType subst f.FieldType) v)
                            fields
                            values
                    else
                        values
                | _ -> values

            let irs =
                if fieldTys.Length = values.Length then
                    List.map2 (fun fty v -> coerceTy ctx fty (lw ctx v)) fieldTys values
                else
                    values |> List.map (lw ctx)

            bindArgsIn true ctx irs (fun xs -> ECon(ty, case, xs, None))
        | Fable.NewTuple(values, _) ->
            let values =
                match e.Type with
                | Fable.Tuple(ts, _) when ts.Length = values.Length -> List.map2 wrapNullCast ts values
                | _ -> values

            bindArgsIn
                true
                ctx
                (values |> List.map (lw ctx))
                (fun xs -> ECon(TTuple(xs |> List.map typeOf), "", xs, None))
        | Fable.NewAnonymousRecord(values, names, genArgs, _) ->
            // (Fable's uncurrying makes the record again with the types of the signature it is
            // given to, which can name its type parameters: the values' own types then)
            let rec hasGeneric (t: Fable.Type) =
                match t with
                | Fable.GenericParam _ -> true
                | t -> t.Generics |> List.exists hasGeneric

            let fieldTys =
                if genArgs.Length = values.Length then
                    List.map2
                        (fun (g: Fable.Type) (v: Fable.Expr) ->
                            if hasGeneric g && not (hasGeneric v.Type) then
                                mapTypeArg ctx r v.Type
                            else
                                mapTypeArg ctx r (FableTransforms.uncurryType g)
                        )
                        genArgs
                        values
                else
                    genArgs |> List.map (FableTransforms.uncurryType >> mapTypeArg ctx r)

            let ty = TEnt(anonEnt ctx.State names, fieldTys)

            let values =
                if genArgs.Length = values.Length then
                    List.map2 wrapNullCast genArgs values
                else
                    values

            bindArgsIn true ctx (values |> List.map (lw ctx)) (fun xs -> ECon(ty, "", xs, None))
        // `[| a; b |]`, and an array of a given length
        | Fable.NewArray(Fable.ArrayValues values, t, _) ->
            let itemTy = mapType ctx r t
            let ty = TEnt(arrayEnt ctx.State, [ mapTypeArg ctx r t ])
            let holes = values |> List.mapi (fun i _ -> $"$%d{i}") |> String.concat ", "

            bindArgs
                ctx
                (values |> List.map (wrapNullCast t >> lw ctx >> coerceTy ctx itemTy))
                (fun xs -> EEmit($"fable_rt.arrayOf($R, .{{ %s{holes} }})", xs, ty))
        | Fable.NewArray(Fable.ArrayAlloc size, t, _) ->
            let ty = TEnt(arrayEnt ctx.State, [ mapTypeArg ctx r t ])
            bindArgs ctx [ lw ctx size ] (fun xs -> ERt("fable_rt.arrayZero($R, $0)", xs, ty))
        | Fable.NewArray(Fable.ArrayFrom(Uncast source), t, _) when source.Type = Fable.List t ->
            let ty = TEnt(arrayEnt ctx.State, [ mapTypeArg ctx r t ])
            bindArgs ctx [ lw ctx source ] (fun xs -> EEmit("fable_rt.arrayOfList($R, $0)", xs, ty))
        | Fable.NewList(headAndTail, t) ->
            let itemTy = mapType ctx r t
            let ty = mapType ctx r (Fable.List t)

            match headAndTail with
            | Some(head, tail) ->
                bindArgsIn
                    true
                    ctx
                    [
                        coerceTy ctx itemTy (lw ctx (wrapNullCast t head))
                        coerceTy ctx ty (lw ctx tail)
                    ]
                    (fun xs -> ECon(ty, "Cons", xs, None))
            | None -> ECon(ty, "Empty", [], None)
        // (a `None` whose item type Fable lost: Zig's `null` fits the option it is given to)
        | Fable.NewOption(None, Fable.Any, _) -> ELit("null", TOpt tVoid)
        | Fable.NewOption(value, t, isStruct) ->
            let itemTy = mapType ctx r t
            let ty = mapType ctx r (Fable.Option(t, isStruct))

            match value with
            | Some v ->
                bindArgsIn
                    true
                    ctx
                    [ coerceTy ctx itemTy (lw ctx (wrapNullCast t v)) ]
                    (fun xs -> ECon(ty, "Some", xs, None))
            | None -> ECon(ty, "None", [], None)
        | _ -> fail r "the Zig target does not support %s yet" (exprKind e)

    // (unit has one value: a variable of that type is never read)
    | Fable.IdentExpr id when isUnit id.Type -> EUnit

    | Fable.IdentExpr id when ctx.Boxed.Contains id.Name && ctx.Vars.ContainsKey id.Name ->
        EGet(EVar ctx.Vars[id.Name], PField "contents", mapType ctx id.Range id.Type)

    | Fable.IdentExpr id ->
        match ctx.Vars.TryGetValue id.Name with
        | true, ({ Ty = TPtr(t, _) } as v) -> EDeref(EVar v, t)
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
            // (what a module-level value that can be assigned holds now, as a reference of its own)
            | true, MValue ty ->
                ctx.State.UsesRuntime <- true
                EEmit("fable_rt.dup($0)", [ globalVar id.Name ty true ], ty)
            | _ ->
                match ctx.LocalFns.TryGetValue id.Name with
                | true, fn when ctx.State.GenericValues.Contains fn.FnName ->
                    let c =
                        {
                            Target = fn.FnName
                            Captures = captureExprs ctx id.Range fn.CaptureNames
                            OuterTypeArgs = fn.OuterTypeParams |> List.map TGen
                            TypeParams = fn.TypeParams
                            ArgTypes = []
                            Ret = fn.Ret
                        }

                    let typeArgs, _ = typeArgsOf ctx id.Range c None [] (Some id.Type)
                    ECall(c.Target, typeArgs, c.Captures, mapType ctx id.Range id.Type)
                | _ ->

                    match tryCallable ctx e with
                    | Some c -> fnValue ctx id.Range e c id.Type
                    | None -> fail id.Range "the Zig target cannot resolve `%s` yet" id.Name

    // a function of another file, as a value
    | Fable.Import(_, t, r) when (tryCallable ctx e).IsSome -> fnValue ctx r e (tryCallable ctx e).Value t

    // a module-level value of another file
    | Fable.Import(imp, t, r) when (importedValue ctx imp).IsSome ->
        let ty = mapType ctx r t
        let name, isMutable = (importedValue ctx imp).Value

        if isVoid ty then
            EUnit
        elif isMutable then
            ctx.State.UsesRuntime <- true
            EEmit("fable_rt.dup($0)", [ globalVar name ty true ], ty)
        else
            globalVar name ty false

    // A function declared inside this one becomes a function of the file (see `LocalFn`).
    | Fable.Let(id, (Fable.Lambda _ | Fable.Delegate _ as fnExpr), body) when
        not id.IsMutable
        && (not (onlyAsValue id.Name body && not ((namesRead fnExpr).Contains id.Name))
            // (a generic function, which F# generalizes: a function of the file whose uses give
            // its type arguments; a value of it could not be generic)
            || freeGens [ mapType ctx id.Range id.Type ]
               |> List.exists (fun g -> not (List.contains g ctx.TypeParams)))
        ->
        liftGroup ctx id.Range [ Some id.Name, id.Name, wrapFnNullCast id.Type fnExpr ]
        |> ignore

        lw ctx body

    // A generic value (F# generalizes `let fOpt = Some f` when its expression can be): a
    // function of the file without parameters, which each use calls at its own types, as .NET
    // compiles it to a generic method (its expression is made again at each use)
    | Fable.Let(id, value, body) when
        not id.IsMutable
        && (
            match value with
            | Fable.Lambda _
            | Fable.Delegate _
            // (an alias of a function: see the case of aliases)
            | Fable.IdentExpr _ -> false
            | _ -> true
        )
        && typeParamNames id.Type
           |> List.exists (fun g -> not (List.contains g ctx.TypeParams))
        && freeGens [ mapType ctx id.Range id.Type ]
           |> List.exists (fun g -> not (List.contains g ctx.TypeParams))
        ->
        let fn =
            liftGroup ctx id.Range [ Some id.Name, id.Name, Fable.Delegate([], value, None, []) ]
            |> List.head

        ctx.State.GenericValues.Add fn.FnName |> ignore
        lw ctx body

    | Fable.LetRec(bindings, body) ->
        for (id, value) in bindings do
            match value with
            | Fable.Lambda _
            | Fable.Delegate _ -> ()
            | _ -> fail id.Range "the Zig target does not support recursive values yet (`%s`)" id.Name

        liftGroup
            ctx
            e.Range
            (bindings
             |> List.map (fun (id, value) -> Some id.Name, id.Name, wrapFnNullCast id.Type value))
        |> ignore

        lw ctx body

    // (a function value that applies the null of a function, as F# fills a function field that a
    // constructor leaves to its default: the null of the function at this shape)
    | Fable.Delegate(args, Fable.CurriedApply(g, appArgs, _, _), _, _) when
        appArgs.Length = args.Length
        && (
            match g with
            | Fable.Call(Fable.Import(imp, _, _), _, _, _) -> imp.Selector = "DefaultOf"
            | Fable.Value(Fable.Null _, _) -> true
            | _ -> false
        )
        ->
        ctx.State.UsesRuntime <- true
        EEmit("fable_rt.nullOf($R)", [], mapType ctx e.Range e.Type)

    // A function value of several arguments made of a function of fewer (`doMap` of one,
    // given as `SetState -> 'model -> Dispatch -> unit`): it carries that first stage, which a
    // partial application of it calls once (see fable_rt.withStage)
    | Fable.Delegate(args, Fable.CurriedApply(g, appArgs, retTy, _), name, tags) when
        not (List.contains "nostage" tags)
        && args.Length >= 2
        && appArgs.Length = args.Length
        && List.forall2
            (fun (a: Fable.Ident) x ->
                match x with
                | Fable.IdentExpr i -> i.Name = a.Name
                | _ -> false
            )
            args
            appArgs
        && (let k = stageArityOf ctx g
            k >= 1 && k < args.Length)
        ->
        let k = stageArityOf ctx g
        let fresh (i: Fable.Ident) = { i with Name = i.Name + "_stage" }
        let first, rest = List.splitAt k args
        let firstS = first |> List.map fresh
        let restS = rest |> List.map fresh
        let rTy = peelArgs g.Type k
        let staged = AST.makeTypedIdent rTy "staged"

        let stage =
            Fable.Delegate(
                firstS,
                Fable.Let(
                    staged,
                    Fable.CurriedApply(g, firstS |> List.map Fable.IdentExpr, rTy, None),
                    Fable.Delegate(
                        restS,
                        Fable.CurriedApply(Fable.IdentExpr staged, restS |> List.map Fable.IdentExpr, retTy, None),
                        None,
                        [ "nostage" ]
                    )
                ),
                None,
                [ "nostage" ]
            )

        let inner =
            Fable.Delegate(args, Fable.CurriedApply(g, appArgs, retTy, None), name, "nostage" :: tags)

        bindArgs
            ctx
            [ lw ctx inner; lw ctx stage ]
            (fun xs -> EEmit($"fable_rt.withStage($0, %d{k}, $1)", xs, typeOf xs.Head))

    // (the same of a function value that is an expression, `fun a b -> (g y)(x, a, b)`: the
    // value is computed once, when the partial application is made, as F# computes it)
    | Fable.Delegate(rest, Fable.CurriedApply(fexpr, args, t, r), name, tags) when
        not (List.contains "nostage" tags)
        && not rest.IsEmpty
        && args.Length > rest.Length
        && (
            match fexpr with
            | Fable.IdentExpr _ -> false
            | Fable.Lambda _
            | Fable.Delegate _ -> false
            | _ -> true
        )
        && rest |> List.forall (fun p -> not ((freeNamesOf fexpr).Contains p.Name))
        && List.forall2
            (fun (p: Fable.Ident) x ->
                match x with
                | Fable.IdentExpr i -> i.Name = p.Name
                | _ -> false
            )
            rest
            (List.skip (args.Length - rest.Length) args)
        && List.take (args.Length - rest.Length) args
           |> List.forall (fun x -> rest |> List.forall (fun p -> not ((freeNamesOf x).Contains p.Name)))
        ->
        let fixedArgs = List.take (args.Length - rest.Length) args
        let restArgs = List.skip fixedArgs.Length args
        let fIr = lw ctx fexpr
        let v = ctx.State.NewVar("partial", typeOf fIr, VLocal, false)
        let fv = AST.makeTypedIdent fexpr.Type $"partial$%d{v.Id}"
        ctx.Vars[fv.Name] <- v

        let body =
            match v.Ty with
            // (it takes all the arguments at once: a partial application of it, which may use
            // its first stage)
            | TFn(ps, _) when ps.Length = args.Length ->
                Fable.Delegate(
                    rest,
                    Fable.Call(Fable.IdentExpr fv, Fable.CallInfo.Create(args = args), t, r),
                    name,
                    tags
                )
            // (it takes the fixed arguments first: applied to them once, and the result to the
            // rest at each call)
            | TFn(ps, _) when ps.Length <= fixedArgs.Length ->
                let fixedTy = peelArgs fexpr.Type fixedArgs.Length
                let applied = AST.makeTypedIdent fixedTy $"applied$%d{v.Id}"

                Fable.Let(
                    applied,
                    Fable.CurriedApply(Fable.IdentExpr fv, fixedArgs, fixedTy, r),
                    Fable.Delegate(
                        rest,
                        Fable.CurriedApply(Fable.IdentExpr applied, restArgs, t, r),
                        name,
                        "nostage" :: tags
                    )
                )
            | _ -> Fable.Delegate(rest, Fable.CurriedApply(Fable.IdentExpr fv, args, t, r), name, "nostage" :: tags)

        ELet(v, fIr, lw ctx body)

    // An adapter that calls a function value in another shape (`fun b0 b1 -> fun a0 ->
    // f(b0, b1, a0)`, as Fable passes a function of three arguments where one of two that gives
    // a function is wanted): it carries the value's first stage, seen in its own shape
    | Fable.Delegate(args, body, name, tags) when
        not (List.contains "nostage" tags)
        && args.Length >= 2
        && (let rec peel (e: Fable.Expr) acc =
                match e with
                | Fable.Lambda(p, b, _) -> peel b (p :: acc)
                | _ -> List.rev acc, e

            match peel body [] with
            | extra, Fable.Call(Fable.IdentExpr f, info, _, _) when
                info.ThisArg.IsNone
                && ctx.Vars.ContainsKey f.Name
                && not (ctx.LocalFns.ContainsKey f.Name)
                && info.Args.Length = args.Length + extra.Length
                ->
                List.forall2
                    (fun (p: Fable.Ident) x ->
                        match x with
                        | Fable.IdentExpr i -> i.Name = p.Name
                        | _ -> false
                    )
                    (args @ extra)
                    info.Args
            | _ -> false)
        ->
        let rec peel (e: Fable.Expr) acc =
            match e with
            | Fable.Lambda(p, b, _) -> peel b (p :: acc)
            | _ -> List.rev acc, e

        let extra, call = peel body []

        let f, retTy =
            match call with
            | Fable.Call(Fable.IdentExpr f, _, t, _) -> f, t
            | _ -> failwith "unreachable"

        let n = ctx.State.NewVar("adapted", tVoid, VLocal, false).Id
        let fresh (i: Fable.Ident) = { i with Name = $"%s{i.Name}$a%d{n}" }
        let x1 = fresh args.Head

        let restAll =
            (args.Tail @ extra)
            |> List.map (fun i -> { fresh i with Name = (fresh i).Name + "r" })

        let consumer =
            Fable.Delegate(
                restAll,
                Fable.Call(
                    Fable.IdentExpr f,
                    Fable.CallInfo.Create(args = (Fable.IdentExpr x1 :: (restAll |> List.map Fable.IdentExpr))),
                    retTy,
                    None
                ),
                None,
                []
            )

        let rTy = Fable.DelegateType(restAll |> List.map (fun i -> i.Type), retTy)
        let rId = AST.makeTypedIdent rTy $"adaptedRest$%d{n}"

        let tailArgs =
            args.Tail |> List.map (fun i -> { fresh i with Name = (fresh i).Name + "t" })

        let extraArgs =
            extra |> List.map (fun i -> { fresh i with Name = (fresh i).Name + "e" })

        let restCall =
            Fable.Call(
                Fable.IdentExpr rId,
                Fable.CallInfo.Create(args = ((tailArgs @ extraArgs) |> List.map Fable.IdentExpr)),
                retTy,
                None
            )

        let restView =
            Fable.Delegate(
                tailArgs,
                List.foldBack (fun i b -> Fable.Lambda(i, b, None)) extraArgs restCall,
                None,
                [ "nostage" ]
            )

        let stage =
            Fable.Delegate([ x1 ], Fable.Let(rId, Fable.TypeCast(consumer, rTy), restView), None, [ "nostage" ])

        let adapter = Fable.Delegate(args, body, name, "nostage" :: tags)

        bindArgs
            ctx
            [ lw ctx (Fable.IdentExpr f); lw ctx adapter; lw ctx stage ]
            (fun xs -> EEmit("fable_rt.withStageIf($0, $1, 1, $2)", xs, typeOf xs[1]))

    // A partial application of a function value to its first arguments, as Fable writes it
    // (`fun a b -> f(x, a, b)`): the value's first stage, if it carries one of these arguments,
    // called once; otherwise a function that calls the value with all of them
    | Fable.Delegate(rest, Fable.Call(Fable.IdentExpr f, info, t, r), name, tags) when
        not (List.contains "nostage" tags)
        && info.ThisArg.IsNone
        && ctx.Vars.ContainsKey f.Name
        && not (ctx.LocalFns.ContainsKey f.Name)
        && not rest.IsEmpty
        && info.Args.Length > rest.Length
        && List.forall2
            (fun (p: Fable.Ident) x ->
                match x with
                | Fable.IdentExpr i -> i.Name = p.Name
                | _ -> false
            )
            rest
            (List.skip (info.Args.Length - rest.Length) info.Args)
        && List.take (info.Args.Length - rest.Length) info.Args
           |> List.forall (fun x -> rest |> List.forall (fun p -> not ((freeNamesOf x).Contains p.Name)))
        ->
        let k = info.Args.Length - rest.Length
        let fixedArgs = List.take k info.Args
        let restFnTy = mapType ctx r e.Type

        // (the fixed arguments, computed once, under names of their own)
        let bound =
            fixedArgs
            |> List.map (fun x ->
                let ir = lw ctx x
                let v = ctx.State.NewVar("fixed", typeOf ir, VLocal, false)
                let id = AST.makeTypedIdent x.Type $"fixed$%d{v.Id}"
                ctx.Vars[id.Name] <- v
                id, v, ir
            )

        let fixedIds = bound |> List.map (fun (id, _, _) -> Fable.IdentExpr id)
        let fixedVars = bound |> List.map (fun (_, v, _) -> EVar v)
        let sTy = TFn(bound |> List.map (fun (_, v, _) -> v.Ty), restFnTy)
        let sv = ctx.State.NewVar("stage", TOpt sTy, VLocal, false)

        let fallback =
            lw
                ctx
                (Fable.Delegate(
                    rest,
                    Fable.Call(
                        Fable.IdentExpr f,
                        { info with Args = fixedIds @ (rest |> List.map Fable.IdentExpr) },
                        t,
                        r
                    ),
                    name,
                    "nostage" :: tags
                ))

        let body =
            bindArgs
                ctx
                [ lw ctx (Fable.IdentExpr f) ]
                (fun xs ->
                    ELet(
                        sv,
                        EEmit($"fable_rt.stageOf($R, $0, %d{k})", xs, TOpt sTy),
                        EIf(
                            EPrim("not", [ ETest(EVar sv, "None", TOpt sTy) ], tBool),
                            ECallClo(EGet(EVar sv, PSome, sTy), fixedVars, restFnTy),
                            fallback,
                            restFnTy
                        )
                    )
                )

        List.foldBack (fun (_, v, ir) acc -> ELet(v, ir, acc)) bound body

    // (a function value made of the partial application of another, `fun a b -> (f x) a b`, as
    // Fable writes it to keep the value uncurried: `f x` is computed once, when the value is
    // made, as F# computes it)
    | Fable.Delegate(args, body, name, tags) when (etaHead args body).IsSome ->
        let head, rebuild = (etaHead args body).Value
        let held = AST.makeTypedIdent head.Type "applied"
        lw ctx (Fable.Let(held, head, Fable.Delegate(args, rebuild (Fable.IdentExpr held), name, tags)))
    // (a delegate of no parameters takes the unit here, as its type says)
    | Fable.Delegate([], body, name, tags) ->
        lw ctx (Fable.Delegate([ AST.makeTypedIdent Fable.Unit "unitVar" ], body, name, tags))
    | Fable.Lambda(a1, (Fable.Lambda(a2, innerBody, _) | Fable.Delegate([ a2 ], innerBody, _, _)), _)
    | Fable.Delegate([ a1 ], (Fable.Lambda(a2, innerBody, _) | Fable.Delegate([ a2 ], innerBody, _, _)), _, _) when
        not a1.IsThisArgument
        && not a2.IsThisArgument
        && (
            match mapType ctx e.Range e.Type with
            | TFn([ _ ], TFn([ _ ], _)) -> true
            | _ -> false
        )
        && (
            match e with
            | Fable.Delegate(args, body, _, _) -> (etaHead args body).IsNone
            | _ -> true
        )
        ->
        let a1For2 =
            if a1.Name = a2.Name then
                let suffix = ctx.State.NewVar("outer", tVoid, VLocal, false).Id
                { a1 with Name = $"%s{a1.Name}$outer%d{suffix}" }
            else
                a1

        let fns =
            liftGroup
                ctx
                e.Range
                [
                    None, "lambda", e
                    None, "lambda2", Fable.Delegate([ a1For2; a2 ], innerBody, None, [])
                ]

        let fn = fns.Head
        let fn2 = fns[1]
        ctx.State.Curried2[fn.FnName] <- fn2.FnName
        let ty = mapType ctx e.Range e.Type
        EClosure(fn.FnName, ctx.TypeParams |> List.map TGen, captureExprs ctx e.Range fn.CaptureNames, ty)
    | Fable.Lambda _
    | Fable.Delegate _ ->
        let fn = liftGroup ctx e.Range [ None, "lambda", e ] |> List.head

        // (a member's object, which is not null: see liftGroup)
        let ty =
            match e, mapType ctx e.Range e.Type with
            | Fable.Delegate(this :: _, _, _, _), TFn(TOpt t :: rest, ret) when this.IsThisArgument && t = tObj ->
                TFn(tObj :: rest, ret)
            | _, ty -> ty

        EClosure(fn.FnName, ctx.TypeParams |> List.map TGen, captureExprs ctx e.Range fn.CaptureNames, ty)

    // a match that no case covers
    | Fable.Extended(Fable.Throw(Some(Fable.Value(Fable.StringConstant text, _)), t), r) when
        text.StartsWith("Match failure", System.StringComparison.Ordinal)
        ->
        let failure =
            EExnNew(dotnetExnEnt ctx "Microsoft.FSharp.Core.MatchFailureException", matchLocation ctx r)

        // (Fable gives the raise no type: where it stands, nothing is expected of it)
        ERaise(
            failure,
            match t with
            | Fable.Any -> tVoid
            | _ -> mapType ctx r t
        )

    // (F#'s own `raise` of an exception value, as a `with` that does not match passes it on)
    | Fable.Extended(Fable.Throw(Some x, t), _) ->
        bindArgs ctx [ lw ctx x ] (fun xs -> ERaise(xs.Head, mapType ctx e.Range t))
    | Fable.Extended(Fable.Throw(None, t), r) ->
        match ctx.CaughtExn with
        | Some exV -> ERaise(EVar exV, mapType ctx r t)
        | None -> fail r "`reraise ()` is only possible inside a `with` handler"
    // a function with several arguments that is used one argument at a time
    // (a function value of several arguments made curried: one argument, then the partial
    // application of the value to it, curried in turn, so that a first stage the value carries
    // is used, see fable_rt.withStage)
    | Fable.Extended(Fable.Curry(f, arity), r) when
        arity >= 2
        && (tryCallable ctx f).IsNone
        && (
            match f.Type, f with
            | Fable.DelegateType(ps, _), _ -> ps.Length = arity
            // (a variable typed curried that holds a function of all the arguments at once)
            | Fable.LambdaType _, Fable.IdentExpr i when ctx.Vars.ContainsKey i.Name ->
                match ctx.Vars[i.Name].Ty with
                | TFn(zps, _) -> zps.Length = arity
                | _ -> false
            | _ -> false
        )
        ->
        let ps, ret =
            match f.Type with
            | Fable.DelegateType(ps, ret) -> ps, ret
            | t ->
                let rec peel (t: Fable.Type) k acc =
                    match t with
                    | Fable.LambdaType(a, r) when k > 0 -> peel r (k - 1) (a :: acc)
                    | _ -> List.rev acc, t

                peel t arity []

        // (the value under the type of what it is: a function of all the arguments)
        let f =
            match f with
            | Fable.IdentExpr i -> Fable.IdentExpr { i with Type = Fable.DelegateType(ps, ret) }
            | _ -> f

        let n = ctx.State.NewVar("curried", tVoid, VLocal, false).Id
        let fv = AST.makeTypedIdent (Fable.DelegateType(ps, ret)) $"curried$%d{n}"
        let a1 = AST.makeTypedIdent ps.Head $"curriedArg$%d{n}"

        let restIds =
            ps.Tail
            |> List.mapi (fun i t -> AST.makeTypedIdent t $"curriedArg$%d{n}$%d{i + 1}")

        let inner =
            Fable.Delegate(
                restIds,
                Fable.Call(
                    Fable.IdentExpr fv,
                    Fable.CallInfo.Create(args = (Fable.IdentExpr a1 :: (restIds |> List.map Fable.IdentExpr))),
                    ret,
                    r
                ),
                None,
                []
            )

        // (after the first argument: the partial application, made once, then the others one at
        // a time)
        let innerCurried =
            if restIds.Length >= 2 then
                let restTy = Fable.DelegateType(ps.Tail, ret)
                let g = AST.makeTypedIdent restTy $"curriedRest$%d{n}"
                let nextIds = restIds |> List.map (fun i -> { i with Name = i.Name + "_c" })

                let call =
                    Fable.Call(
                        Fable.IdentExpr g,
                        Fable.CallInfo.Create(args = (nextIds |> List.map Fable.IdentExpr)),
                        ret,
                        r
                    )

                // (bound as a value, made once for this first argument: a `let` of a lambda would
                // be a function of the file instead)
                Fable.Let(
                    g,
                    Fable.TypeCast(inner, restTy),
                    List.foldBack (fun i body -> Fable.Lambda(i, body, None)) nextIds call
                )
            else
                inner

        lw ctx (Fable.Let(fv, f, Fable.Lambda(a1, innerCurried, None)))
    | Fable.Extended(Fable.Curry(f, arity), _) -> lw ctx (Replacements.Api.curryExprAtRuntime ctx.Com arity f)

    // `match w.TryGetTarget() with | true, x -> ...` where x's type has no default value (null on
    // .NET): the pair is an option here, which the pattern reads
    | Fable.Let(pair,
                Fable.Let(out,
                          Fable.Call(Fable.Import(defaultOf, _, _), _, _, _),
                          Fable.Value(Fable.NewTuple([ tryCall; Fable.IdentExpr outRef ], _), _)),
                body) when
        defaultOf.Selector = "DefaultOf"
        && outRef.Name = out.Name
        && not (hasDefault ctx out.Type)
        ->
        let valueTy = mapType ctx e.Range out.Type
        let found = ctx.State.NewVar("found", TOpt valueTy, VLocal, false)

        let tryIr =
            match tryCall with
            | Fable.Call(Fable.Import(imp, _, _), info, _, r) ->
                let target = Option.toList info.ThisArg @ info.Args
                let source = target.Head

                match imp.Selector with
                | "TryGetTarget" ->
                    bindArgs ctx [ lw ctx source ] (fun xs -> EEmit("fable_rt.weakTryGet($0)", xs, TOpt valueTy))
                | "TryGetValue" ->
                    bindArgs
                        ctx
                        [ lw ctx source; lw ctx target[1] ]
                        (fun xs -> EEmit("fable_rt.dictTryGet($0, $1)", xs, TOpt valueTy))
                // (`Uri.TryCreate(s, kind, &uri)` and `Uri.TryCreate(baseUri, relative, &uri)`)
                // (`DateTimeOffset.TryParse(s[, culture[, styles]], &d)`)
                | "TryParse" when imp.Path.EndsWith("System.DateTimeOffset", System.StringComparison.Ordinal) ->
                    libraryCall
                        ctx
                        r
                        "DateTimeOffset"
                        "tryParseOption"
                        { info with ThisArg = None }
                        [ info.Args.Head ]
                        (Fable.Option(out.Type, false))
                // (`DateTime.TryParse(s[, culture[, styles]], &d)`)
                | "TryParse" when imp.Path.EndsWith("System.DateTime", System.StringComparison.Ordinal) ->
                    libraryCall
                        ctx
                        r
                        "DateTime"
                        "tryParseOption"
                        { info with ThisArg = None }
                        [ info.Args.Head ]
                        (Fable.Option(out.Type, false))
                // (`TimeSpan.TryParse(s[, culture], &t)`)
                | "TryParse" when imp.Path.EndsWith("System.TimeSpan", System.StringComparison.Ordinal) ->
                    libraryCall
                        ctx
                        r
                        "TimeSpan"
                        "tryParseOption"
                        { info with ThisArg = None }
                        [ info.Args.Head ]
                        (Fable.Option(out.Type, false))
                // (`Guid.TryParse(s, &g)`)
                | "TryParse" when imp.Path.EndsWith("System.Guid", System.StringComparison.Ordinal) ->
                    libraryCall
                        ctx
                        r
                        "Guid"
                        "tryParseOption"
                        { info with ThisArg = None }
                        [ info.Args.Head ]
                        (Fable.Option(out.Type, false))
                | "TryCreate" when imp.Path.EndsWith("System.Uri", System.StringComparison.Ordinal) ->
                    let args = info.Args |> List.take (info.Args.Length - 1)

                    let fn =
                        if args.Head.Type = Fable.String then
                            "tryCreateOption"
                        else
                            "tryCreateFromBaseOption"

                    libraryCall ctx r "Uri" fn { info with ThisArg = None } args (Fable.Option(out.Type, false))
                | other -> fail r "the Zig target does not support %s with a value of this type yet" other
            | _ -> fail e.Range "internal: not a call"

        ctx.State.UsesRuntime <- true
        ctx.OutTuples[pair.Name] <- found
        ELet(found, tryIr, lw ctx body)

    | Fable.Get(Fable.IdentExpr pair, Fable.TupleIndex i, t, r) when ctx.OutTuples.ContainsKey pair.Name ->
        let found = ctx.OutTuples[pair.Name]

        if i = 0 then
            EPrim("not", [ ETest(EVar found, "None", found.Ty) ], tBool)
        else
            EGet(EVar found, PSome, mapType ctx r t)

    // `for x in source do body`: Fable gives an enumerator and a `while` over `MoveNext`. Here
    // it is a loop of the source's own: down a list, along a string by index. A set or a map is
    // walked as the list of what it holds, in order.
    | Fable.Let(enumerator, Fable.Call(Fable.Import(getEnum, _, _), getInfo, _, r), rest) when
        getEnum.Selector = "GetEnumerator"
        && getInfo.ThisArg.IsSome
        && (forInSource ctx getInfo.ThisArg.Value).IsSome
        && (forInLoop enumerator.Name rest).IsSome
        ->
        let loopBody, finalizer = (forInLoop enumerator.Name rest).Value
        let source, kind = (forInSource ctx getInfo.ThisArg.Value).Value
        // (the item type is the source's: an enumerator of a .NET collection has a type of its own)
        let itemTy =
            match kind with
            | "string" -> TPrim "u16"
            | _ -> itemOf source

        // (a sequence's walk is a call; the source is named so that the walk starts once)

        let cur = ctx.State.NewVar("item", itemTy, VLocal, false)
        ctx.Enumerators[enumerator.Name] <- cur

        let loop =
            match kind with
            | "list" ->
                let listTy = typeOf source
                let restV = ctx.State.NewVar("rest", listTy, VLocal, true)
                let nextRest = ctx.State.NewVar("next_rest", listTy, VLocal, false)

                ELet(
                    restV,
                    source,
                    EWhile(
                        EPrim("not", [ ETest(EVar restV, "Empty", listTy) ], tBool),
                        ELet(
                            cur,
                            EGet(EVar restV, PCase("Cons", "Head"), itemTy),
                            ELet(
                                nextRest,
                                EGet(EVar restV, PCase("Cons", "Tail"), listTy),
                                ESeq(EAssign(restV, EVar nextRest), lwStmt ctx loopBody)
                            )
                        )
                    )
                )
            | "array" ->
                let arrTy = typeOf source
                let arrV = ctx.State.NewVar("arr", arrTy, VLocal, false)
                let lenV = ctx.State.NewVar("len", tI32, VLocal, false)
                let iV = ctx.State.NewVar("i", tI32, VLocal, true)
                ctx.State.UsesRuntime <- true

                ELet(
                    arrV,
                    source,
                    ELet(
                        lenV,
                        EEmit("fable_rt.arrayLen($0)", [ EVar arrV ], tI32),
                        ELet(
                            iV,
                            ELit("0", tI32),
                            EWhile(
                                EPrim("lt", [ EVar iV; EVar lenV ], tBool),
                                ELet(
                                    cur,
                                    EEmit(
                                        "fable_rt.arrayItemAt($0, @as(usize, @intCast($1)))",
                                        [ EVar arrV; EVar iV ],
                                        itemTy
                                    ),
                                    ESeq(
                                        EAssign(iV, EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32)),
                                        lwStmt ctx loopBody
                                    )
                                )
                            )
                        )
                    )
                )
            | "seq" ->
                // a sequence: start a walk, ask it for each item until it has none, and close on exit
                let walkTy = TEnt(walkEnt ctx, [ itemTy ])
                let nextTy = TFn([ tVoid ], TOpt itemTy)
                let closeTy = TFn([ tVoid ], tVoid)
                let walk = ctx.State.NewVar("walk", walkTy, VLocal, false)
                let go = ctx.State.NewVar("go", tBool, VLocal, true)
                let next = ctx.State.NewVar("next", TOpt itemTy, VLocal, false)
                let exV = ctx.State.NewVar("exn", tExn, VLocal, false)

                let closeWalk () =
                    ECallClo(EGet(EVar walk, PField "close", closeTy), [ EUnit ], tVoid)

                let loop =
                    ELet(
                        go,
                        ELit("true", tBool),
                        EWhile(
                            EVar go,
                            ELet(
                                next,
                                ECallClo(EGet(EVar walk, PField "next", nextTy), [ EUnit ], TOpt itemTy),
                                EIf(
                                    ETest(EVar next, "None", TOpt itemTy),
                                    EAssign(go, ELit("false", tBool)),
                                    ELet(cur, EGet(EVar next, PSome, itemTy), lwStmt ctx loopBody),
                                    tVoid
                                )
                            )
                        )
                    )

                let onRaise = ESeq(closeWalk (), ERaise(EVar exV, tVoid))

                ELet(
                    walk,
                    ECallClo(EGet(source, PField "fable_seq", TFn([ tVoid ], walkTy)), [ EUnit ], walkTy),
                    ESeq(ETry(loop, exV, onRaise, tVoid), closeWalk ())
                )
            | _ ->
                // a string, by index
                let s = ctx.State.NewVar("text", tStr, VLocal, false)
                let i = ctx.State.NewVar("i", tI32, VLocal, true)
                ctx.State.UsesRuntime <- true

                let bodyIr =
                    match getInfo.ThisArg.Value with
                    | Uncast(Fable.IdentExpr si) when not si.IsMutable ->
                        withKnown ctx [ si.Name ] [] (fun () -> lwStmt ctx loopBody)
                    | _ -> lwStmt ctx loopBody

                ELet(
                    s,
                    source,
                    ELet(
                        i,
                        ELit("0", tI32),
                        EWhile(
                            EPrim("lt", [ EVar i; EEmit("fable_rt.strLength($0)", [ EVar s ], tI32) ], tBool),
                            ELet(
                                cur,
                                EEmit("fable_rt.unitsOf($0)[@intCast($1)]", [ EVar s; EVar i ], itemTy),
                                ESeq(EAssign(i, EPrim("add", [ EVar i; ELit("1", tI32) ], tI32)), bodyIr)
                            )
                        )
                    )
                )

        let after =
            match finalizer with
            | Some next -> lw ctx next
            | None -> EUnit

        ESeq(loop, after)

    // A `let mutable` that a function inside this one uses is a ref cell, which the function
    // and its surroundings share: that is what F# makes of it on .NET.
    | Fable.Let(id, value, body) when id.IsMutable && not (isUnit id.Type) && usedInFunction id.Name body ->
        let cellTy = TEnt(refEnt ctx.State, [ mapType ctx id.Range id.Type ])
        ctx.State.UsesRuntime <- true
        let v = ctx.State.NewVar(id.Name, cellTy, VLocal, false)

        let rhs =
            bindArgsIn true ctx [ lw ctx value ] (fun xs -> ECon(cellTy, "", xs, None))

        withScopedIdent
            ctx
            id
            (fun () ->
                ctx.Vars[id.Name] <- v
                ctx.Boxed.Add id.Name |> ignore
                ELet(v, rhs, lw ctx body)
            )

    // a byref variable bound to a place: the pointer to it
    | Fable.Let(id, value, body) when
        (match id.Type with
         | Fable.DeclaredType(ent, _) -> ent.FullName = "Microsoft.FSharp.Core.byref`2"
         | _ -> false)
        ->
        let place =
            match tryAddress (lw ctx value) with
            | Some p -> p
            | None -> fail id.Range "the Zig target cannot take the address of this yet"

        // (the address of what cannot be assigned, as F# takes to copy a struct record with
        // some fields changed, only reads)
        let ty =
            match mapType ctx id.Range id.Type, typeOf place with
            | TPtr(t, false), (TPtr(t2, true) as actual) when t = t2 -> actual
            | ty, _ -> ty

        let v = ctx.State.NewVar(id.Name, ty, VLocal, false)

        withScopedIdent
            ctx
            id
            (fun () ->
                ctx.Vars[id.Name] <- v
                ELet(v, place, lw ctx body)
            )

    // another name of a function of this function (`let alias = f`): the same function, so a
    // generic one stays generic, each use giving its type arguments
    | Fable.Let(id, Fable.IdentExpr other, body) when
        not id.IsMutable
        && not (ctx.Vars.ContainsKey other.Name)
        && ctx.LocalFns.ContainsKey other.Name
        ->
        ctx.LocalFns[id.Name] <- ctx.LocalFns[other.Name]
        lw ctx body

    // (a part of a value that a pattern names and nothing uses: Zig rejects a constant that is
    // never read)
    | Fable.Let(id, (Fable.Get(Fable.IdentExpr _, _, _, _) | Fable.IdentExpr _), body) when
        not id.IsMutable && not (liveUse id.Name body)
        ->
        lw ctx body
    | Fable.Let(id, value, body) ->
        let isValNonNull =
            not id.IsMutable
            && (isMadeObject value
                || (id.Type = Fable.String && neverNullIn ctx value)
                || (unwrapNullness id.Type = Fable.String && neverNullIn ctx value)
                || (
                    match value with
                    | Uncast(Fable.IdentExpr s) -> ctx.NonNull.Contains s.Name
                    | _ -> false
                ))

        let isValPos = not id.IsMutable && isKnownPosExpr ctx value

        let canTrackMutNonNeg =
            id.IsMutable
            && not (usedInFunction id.Name body)
            && not (hasAddressOfIdent id.Name body)

        let isValNonNeg =
            (not id.IsMutable || canTrackMutNonNeg)
            && (isValPos || isKnownNonNegExpr ctx value)

        let lenTarget =
            if not id.IsMutable then
                tryLengthTarget ctx value
            else
                None

        let strOwnerNonNull =
            match value, lenTarget with
            | Fable.Call(Fable.Import(imp, _, _), _, _, _), Some(cName, cTy) when
                imp.Selector = "get_Length" && unwrapNullness cTy = Fable.String
                ->
                [ cName ]
            | _ -> []

        let constLen =
            if not id.IsMutable then
                tryConstArrayLen value
            else
                None

        let stOpt =
            if id.IsMutable then
                None
            else
                staticTypeOf ctx value

        let rhs = lw ctx (adaptTo ctx.Com id.Type value)
        let ty = mapType ctx id.Range id.Type

        // (a function of several arguments read from a field is uncurried there, as Fable keeps
        // it, though the variable's type says it is curried)
        let ty =
            match ty, typeOf rhs with
            | (TFn _ | TOpt(TFn _)), (TFn _ | TOpt(TFn _) as actual) when
                actual <> ty
                && actual = mapType ctx id.Range (FableTransforms.uncurryType id.Type)
                ->
                actual
            // (the address of what cannot be assigned, which F# takes to copy a struct record
            // with some fields changed: a pointer that only reads)
            | TPtr(t, false), (TPtr(t2, true) as actual) when t = t2 -> actual
            | _ -> ty

        withScopedIdent
            ctx
            id
            (fun () ->
                if isValNonNull then
                    ctx.NonNull.Add id.Name |> ignore

                if isValPos then
                    ctx.Positive.Add id.Name |> ignore

                if isValNonNeg then
                    ctx.NonNeg.Add id.Name |> ignore

                match lenTarget with
                | Some lt -> ctx.Lengths[id.Name] <- lt
                | None -> ()

                match constLen with
                | Some n -> ctx.ConstLen[id.Name] <- n
                | None -> ()

                match stOpt with
                | Some st when unwrapNullness id.Type = Fable.MetaType -> ctx.KnownTypes[id.Name] <- st
                | _ -> ()

                let lowerBody () =
                    if strOwnerNonNull.IsEmpty then
                        lw ctx body
                    else
                        withFacts ctx.NonNull strOwnerNonNull (fun () -> lw ctx body)

                if isVoid ty then
                    ESeq(asStmt ctx rhs, lowerBody ())
                else
                    let rhs = coerceTy ctx ty rhs

                    match rhs with
                    // an immutable name for an immutable variable is that variable
                    | EVar x when not id.IsMutable && not x.FMutable && x.Kind <> VGlobal ->
                        ctx.Vars[id.Name] <- x
                        lowerBody ()
                    | _ ->
                        let v = ctx.State.NewVar(id.Name, ty, VLocal, id.IsMutable)
                        ctx.Vars[id.Name] <- v
                        ELet(v, rhs, lowerBody ())
            )

    // (`ExceptionDispatchInfo.Capture(e).Throw()`, as F# rethrows in an `async` handler, then a
    // placeholder value never reached: the rethrow, of the sequence's type)
    | Fable.Sequential es when
        es
        |> List.exists (fun x ->
            match x with
            | Fable.Call(Fable.Import(imp, _, _), _, _, _) ->
                imp.Selector = "Throw"
                && imp.Path =
                    Replacements.DotnetPrefix
                    + "System.Runtime.ExceptionServices.ExceptionDispatchInfo"
            | _ -> false
        )
        ->
        let isThrow (x: Fable.Expr) =
            match x with
            | Fable.Call(Fable.Import(imp, _, _), _, _, _) ->
                imp.Selector = "Throw"
                && imp.Path =
                    Replacements.DotnetPrefix
                    + "System.Runtime.ExceptionServices.ExceptionDispatchInfo"
            | _ -> false

        let before = es |> List.takeWhile (isThrow >> not)

        let thrown =
            match es |> List.find isThrow with
            | Fable.Call(_, info, _, _) ->
                match info.ThisArg with
                | Some edi -> edi
                | None -> fail e.Range "internal: ExceptionDispatchInfo.Throw without its object"
            | _ -> fail e.Range "internal: not a call"

        let raiseIr =
            bindArgs ctx [ lw ctx thrown ] (fun xs -> ERaise(xs.Head, mapType ctx e.Range e.Type))

        before |> List.rev |> List.fold (fun acc s -> ESeq(lwStmt ctx s, acc)) raiseIr
    // (a guard that raises when something is null: it is not null in what follows)
    | Fable.Sequential es when
        es
        |> List.exists (fun x ->
            not (factsAfter nullFacts x).IsEmpty
            || not (factsAfter positiveFacts x).IsEmpty
            || not (factsAfter nonNegFacts x).IsEmpty
        )
        ->
        let rec go (stmts: Fable.Expr list) : Expr =
            match stmts with
            | [] -> EUnit
            | [ last ] -> lw ctx last
            | x :: rest ->
                let ir = lwStmt ctx x

                ESeq(
                    ir,
                    withKnownFacts
                        ctx
                        (factsAfter nullFacts x)
                        (factsAfter positiveFacts x)
                        (factsAfter nonNegFacts x)
                        (fun () -> go rest)
                )

        go es
    | Fable.Sequential es ->
        match List.rev es with
        | [] -> EUnit
        | last :: restRev ->
            let lastIr = lw ctx last
            restRev |> List.fold (fun acc s -> ESeq(lwStmt ctx s, acc)) lastIr

    | Fable.IfThenElse(guard, thenExpr, elseExpr, r) ->
        let merged =
            match e.Type, elseExpr.Type with
            | Fable.Nullable(_, false), _ -> e.Type
            | _, (Fable.Nullable(_, false) as n) when unwrapNullness n = unwrapNullness e.Type -> n
            | _ -> e.Type

        let ty = mapType ctx r merged
        let thenExpr = wrapNullCast merged thenExpr
        let elseExpr = wrapNullCast merged elseExpr

        // (what the guard tells of nulls and ints holds in its branches)
        let whenTrue, whenFalse = nullFacts guard
        let posTrue, posFalse = positiveFacts guard
        let nonNegTrue, nonNegFalse = nonNegFacts guard

        bindArgs
            ctx
            [ lw ctx guard ]
            (fun xs ->
                EIf(
                    xs.Head,
                    coerceTy ctx ty (withKnownFacts ctx whenTrue posTrue nonNegTrue (fun () -> lw ctx thenExpr)),
                    coerceTy ctx ty (withKnownFacts ctx whenFalse posFalse nonNegFalse (fun () -> lw ctx elseExpr)),
                    ty
                )
            )

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
            | UnaryAddressOf ->
                match tryAddress ir with
                // (a byref passed on is the pointer it is)
                | Some p -> p
                | None -> fail r "the Zig target can only take the address of a variable (`&x`)"
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
                // (a variable a guard has shown to be greater than zero)
                | Fable.IdentExpr i -> ctx.Positive.Contains i.Name
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
    // `Printf.kprintf cont fmt a b` and `ksprintf`: `cont (sprintf fmt a b)` (`Printf.sprintf`
    // is `ksprintf id`)
    | Fable.CurriedApply(Fable.Call(Fable.Import(imp, _, _), info, _, _), args, t, r) when
        imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.PrintfModule"
        && (imp.Selector = "PrintFormatThen" || imp.Selector = "PrintFormatToStringThen")
        ->
        lw ctx (kprintf imp info args t r)
    | Fable.Call(Fable.Import(imp, _, _), info, t, r) when
        imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.PrintfModule"
        && (imp.Selector = "PrintFormatThen" || imp.Selector = "PrintFormatToStringThen")
        ->
        lw ctx (kprintf imp info [] t r)
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
        let n = printfValues.Value.Value + 1
        printfValues.Value.Value <- n

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

    // (`Dispose` of an enumerator, as `use e = s.GetEnumerator()` calls it through an unboxing
    // to `IDisposable`: the enumerator's own)
    | Fable.Call(Fable.Import(imp, it, ir), info, t, r) when
        imp.Selector = "Dispose"
        && imp.Path = Replacements.DotnetPrefix + "System.IDisposable"
        && (
            match info.ThisArg with
            | Some(Fable.Call _ as unboxing) ->
                let (Unboxed inner) = unboxing

                match inner.Type with
                | Fable.DeclaredType(e, _) -> e.FullName = "System.Collections.Generic.IEnumerator`1"
                | _ -> false
            | _ -> false
        )
        ->
        let (Unboxed inner) = info.ThisArg.Value
        lw ctx (Fable.Call(Fable.Import(imp, it, ir), { info with ThisArg = Some inner }, t, r))

    // (`Dispose` of a cancellation source, as `use` calls it: the library's Async.fs)
    | Fable.Call(Fable.Import(imp, _, _), info, t, r) when
        imp.Selector = "Dispose"
        && imp.Path = Replacements.DotnetPrefix + "System.IDisposable"
        && (
            match info.ThisArg with
            | Some(Unboxed inner) ->
                match inner.Type with
                | Fable.DeclaredType(e, _) -> e.FullName = "System.Threading.CancellationTokenSource"
                | _ -> false
            | _ -> false
        )
        ->
        let (Unboxed inner) = info.ThisArg.Value
        libraryCall ctx r "Async" "sourceDispose" (Fable.CallInfo.Create(args = [ inner ])) [ inner ] t
    // a member of an interface called on a value whose type is known: the type's own function
    | Fable.Call(Fable.Import(imp, _, _), info, t, r) when
        imp.Path.StartsWith(Replacements.DotnetPrefix, System.StringComparison.Ordinal)
        && info.ThisArg.IsSome
        && (
            match info.ThisArg.Value with
            | Unboxed inner ->
                // (a type of the program's: those of .NET and FSharp.Core are the runtime's)
                (match inner.Type with
                 | Fable.DeclaredType({ Path = Fable.SourcePath _ }, _) -> true
                 | _ -> false)
                && (implements ctx.Com inner.Type (imp.Path.Substring Replacements.DotnetPrefix.Length)) = Some true
        )
        ->
        let (Unboxed inner) = info.ThisArg.Value
        let iface = imp.Path.Substring Replacements.DotnetPrefix.Length

        match inner.Type with
        | Fable.DeclaredType(typeRef, genArgs) ->
            let target = interfaceImpl ctx r typeRef iface imp.Selector

            let args =
                match info.Args |> List.filter (fun a -> not (isUnit a.Type)) with
                | [] -> [ EUnit ]
                | given -> given |> List.map (lw ctx)

            bindArgs
                ctx
                (lw ctx inner :: args)
                (fun xs ->
                    // (the object: checked for null and borrowed)
                    withBorrowedObj
                        ctx
                        inner
                        xs.Head
                        (fun o -> ECall(target, genArgs |> List.map (mapTypeArg ctx r), o :: xs.Tail, mapType ctx r t))
                )
        | _ -> fail r "internal: not a declared type"

    // A call that the replacements kept under its .NET name.
    | Fable.Call(Fable.Import(imp, _, _), info, t, r) when
        imp.Path.StartsWith(Replacements.DotnetPrefix, System.StringComparison.Ordinal)
        ->
        let info =
            if info.SignatureArgTypes.Length = info.Args.Length then
                { info with Args = List.map2 wrapNullCast info.SignatureArgTypes info.Args }
            else
                info

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

        // (`[<Emit("try f($0)")>]`: a call that may raise, whose exception goes on as F#'s does)
        if info.Macro.StartsWith("try ", System.StringComparison.Ordinal) then
            bindArgs ctx args (fun xs -> ERt(info.Macro.Substring 4, xs, ty))
        else
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

    // (`type C() as this`: the object read through its self reference; before the constructor
    // made it, the error .NET gives)
    | Fable.Get(Fable.Get(x, Fable.FieldGet fi, refT, r1), Fable.FieldGet ci, t, r) when
        ci.Name = "contents" && isSelfRefType x.Type refT
        ->
        let kept = selfRefType refT

        let optT =
            match kept with
            | Fable.DeclaredType(_, [ o ]) -> o
            | _ -> fail r "internal: a self reference"

        let cell = Fable.Get(x, Fable.FieldGet { fi with FieldType = Some kept }, kept, r1)

        let v = AST.makeTypedIdent optT "self"

        let failInit =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = "FailInit"
                        Path =
                            Replacements.DotnetPrefix
                            + "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(),
                t,
                r
            )

        lw
            ctx
            (Fable.Let(
                v,
                Fable.Get(cell, Fable.FieldGet { ci with FieldType = Some optT }, optT, r),
                Fable.IfThenElse(
                    Fable.Test(Fable.IdentExpr v, Fable.OptionTest true, r),
                    Fable.Get(Fable.IdentExpr v, Fable.OptionValue, t, r),
                    failInit,
                    r
                )
            ))
    // calling a member of a fat-pointer interface directly through its vtable slot
    | Fable.Call(Fable.Get(x, Fable.FieldGet info, _, _), call, t, r) when
        isInterfaceType ctx.Com x.Type && isFatIfaceTy (mapType ctx r x.Type)
        ->
        let ifaceTy = mapType ctx r x.Type

        let ifaceStructTy =
            match ifaceTy with
            | TOpt s -> s
            | s -> s

        let rawArgs =
            match call.Args with
            | [ a ] when isUnit a.Type -> []
            | xs -> xs

        let argCount =
            if rawArgs.IsEmpty then
                1
            else
                rawArgs.Length

        let wrappedRawArgs =
            if not rawArgs.IsEmpty && call.SignatureArgTypes.Length = rawArgs.Length then
                List.map2 wrapNullCast call.SignatureArgTypes rawArgs
            else
                rawArgs

        match resolveIfaceSlot ctx x.Type ifaceStructTy info.Name (Some argCount) with
        | Some(f, ptys, ret), _ ->
            let args =
                if rawArgs.IsEmpty then
                    [ EUnit ]
                else
                    let lowered = wrappedRawArgs |> List.map (lw ctx)

                    if ptys.Length = lowered.Length then
                        List.map2 (coerceTy ctx) ptys lowered
                    else
                        lowered

            bindArgs
                ctx
                (lw ctx x :: args)
                (fun given ->
                    withBorrowedIface
                        ctx
                        x
                        given.Head
                        (fun iface -> coerceTy ctx (mapType ctx r t) (ECallIface(iface, f, given.Tail, ret)))
                )
        | None, Some(f, fnTy) ->
            let args =
                if rawArgs.IsEmpty then
                    [ EUnit ]
                else
                    let lowered = wrappedRawArgs |> List.map (lw ctx)

                    match fnTy with
                    | TFn(ptys, _) when ptys.Length = lowered.Length -> List.map2 (coerceTy ctx) ptys lowered
                    | _ -> lowered

            bindArgs
                ctx
                (lw ctx x :: args)
                (fun given ->
                    withBorrowedIface
                        ctx
                        x
                        given.Head
                        (fun iface ->
                            bindArgs
                                ctx
                                [ ECallIface(iface, f, [ EUnit ], fnTy) ]
                                (fun cs ->
                                    coerceTy ctx (mapType ctx r t) (ECallClo(cs.Head, given.Tail, mapType ctx r t))
                                )
                        )
                )
        | None, None -> fail r "the Zig target cannot find the member %s of this interface (%A)" info.Name t
    // a member of a fat-pointer interface: a property getter calls its slot; a method as value
    // binds the interface into a closure with `fable_rt.ifaceMethod`
    | Fable.Get(x, Fable.FieldGet info, t, r) when isInterfaceType ctx.Com x.Type && isFatIfaceTy (mapType ctx r x.Type) ->
        let ifaceTy = mapType ctx r x.Type

        let ifaceStructTy =
            match ifaceTy with
            | TOpt s -> s
            | s -> s

        let targetTy = mapType ctx r t

        bindArgs
            ctx
            [ lw ctx x ]
            (fun given ->
                withBorrowedIface
                    ctx
                    x
                    given.Head
                    (fun iface ->
                        match resolveIfaceSlot ctx x.Type ifaceStructTy info.Name None with
                        | Some(f, [ p ], ret), _ when
                            isVoid p
                            && f.StartsWith("get_", System.StringComparison.Ordinal)
                            && targetTy <> TFn([ tVoid ], ret)
                            ->
                            coerceTy ctx targetTy (ECallIface(iface, f, [ EUnit ], ret))
                        | Some(f, ptys, ret), _ ->
                            ctx.State.UsesRuntime <- true
                            EEmit($"fable_rt.ifaceMethod($R, $0, \"%s{cleanIdent f}\")", [ iface ], TFn(ptys, ret))
                        | None, Some(f, ret) -> coerceTy ctx targetTy (ECallIface(iface, f, [ EUnit ], ret))
                        | None, None ->
                            fail r "the Zig target cannot find the member %s of this interface (%A)" info.Name t
                    )
            )

    // (an F# map seen as a sequence: of its entries, in order, as Map.toSeq gives them)
    | Fable.TypeCast(m, (Fable.DeclaredType(target, [ _ ]) as targetType)) when
        target.FullName = "System.Collections.Generic.IEnumerable`1"
        && (
            match m.Type with
            | Fable.DeclaredType(ent, [ _; _ ]) -> ent.FullName = "Microsoft.FSharp.Collections.FSharpMap`2"
            | _ -> false
        )
        ->
        let k, v =
            match m.Type with
            | Fable.DeclaredType(_, [ k; v ]) -> k, v
            | _ -> Fable.Any, Fable.Any

        lw
            ctx
            (Fable.Call(
                Fable.Import(
                    {
                        Selector = "ToSeq"
                        Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Collections.MapModule"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(args = [ m ], genArgs = [ k; v ]),
                targetType,
                e.Range
            ))

    // (an F# map seen as `IDictionary` or `IReadOnlyDictionary`: a read-only dictionary of its
    // entries, in its order, as `dict` makes; the map cannot change, so neither can it)
    | Fable.TypeCast(m, (Fable.DeclaredType(target, _) as targetType)) when
        isDictionaryName target.FullName
        && (
            match m.Type with
            | Fable.DeclaredType(ent, [ _; _ ]) -> ent.FullName = "Microsoft.FSharp.Collections.FSharpMap`2"
            | _ -> false
        )
        ->
        let k, v =
            match m.Type with
            | Fable.DeclaredType(_, [ k; v ]) -> k, v
            | _ -> Fable.Any, Fable.Any

        let import entity selector =
            Fable.Import(
                {
                    Selector = selector
                    Path = Replacements.DotnetPrefix + entity
                    Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                },
                Fable.Any,
                None
            )

        let pairs =
            Fable.Call(
                import "Microsoft.FSharp.Collections.MapModule" "ToList",
                Fable.CallInfo.Create(args = [ m ], genArgs = [ k; v ]),
                Fable.List(Fable.Tuple([ k; v ], false)),
                None
            )

        lw
            ctx
            (Fable.Call(
                import "Microsoft.FSharp.Core.ExtraTopLevelOperators" "CreateReadOnlyDictionary",
                Fable.CallInfo.Create(args = [ pairs ], genArgs = [ k; v ]),
                targetType,
                e.Range
            ))

    // (a dictionary seen as `IDictionary` or `IReadOnlyDictionary`: the same here)
    | Fable.TypeCast(x, Fable.DeclaredType(target, _)) when
        isDictionaryName target.FullName
        && (
            match x.Type with
            | Fable.DeclaredType(ent, _) -> isDictionaryName ent.FullName
            | _ -> false
        )
        ->
        match x with
        // (`upcast Dictionary()`: the new dictionary is of the type it is cast to, whose type
        // arguments F# knows)
        | Fable.Call(callee, info, _, cr) -> lw ctx (Fable.Call(callee, info, e.Type, cr))
        | _ -> lw ctx x
    // a collection given where a sequence is expected: a sequence that walks it
    | Fable.TypeCast(x, Fable.DeclaredType(seqRef, [ item ])) when
        seqRef.FullName = "System.Collections.Generic.IEnumerable`1"
        && not (isSeqType x.Type)
        ->
        let itemTy = mapTypeArg ctx e.Range item
        let seqTy = TEnt(seqEnt ctx, [ itemTy ])

        match x.Type with
        | Fable.Array(_, Fable.MutableArray)
        | Fable.Array(_, Fable.ImmutableArray) ->
            bindArgs ctx [ lw ctx x ] (fun xs -> ECall(libraryTarget ctx "Seq" "ofArray", [ itemTy ], xs, seqTy))
        // (an object of the program's that implements `IEnumerable<'T>`: what its
        // `GetEnumerator` gives)
        | Fable.DeclaredType({ Path = Fable.SourcePath _ }, _) when
            implements ctx.Com x.Type "System.Collections.Generic.IEnumerable`1" = Some true
            ->
            let obj = AST.makeTypedIdent x.Type "enumerable"

            let getEnumerator =
                Fable.Call(
                    Fable.Import(
                        {
                            Selector = "GetEnumerator"
                            Path = Replacements.DotnetPrefix + "System.Collections.Generic.IEnumerable`1"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = true))
                        },
                        Fable.Any,
                        None
                    ),
                    Fable.CallInfo.Create(thisArg = Fable.IdentExpr obj),
                    Fable.DeclaredType(
                        {
                            FullName = "System.Collections.Generic.IEnumerator`1"
                            Path = Fable.CoreAssemblyName "System.Runtime"
                        },
                        [ item ]
                    ),
                    e.Range
                )

            let v = ctx.State.NewVar("enumerable", mapType ctx e.Range x.Type, VLocal, false)
            ctx.Vars[obj.Name] <- v
            ELet(v, lw ctx x, lowerSeqOfGetEnumerator ctx e.Range item getEnumerator)
        // (an `IList<'T>`: the array it is here)
        | Fable.DeclaredType(il, [ item ]) when il.FullName = "System.Collections.Generic.IList`1" ->
            lw ctx (Fable.TypeCast(Fable.TypeCast(x, Fable.Array(item, Fable.MutableArray)), e.Type))
        // (a `System.Array`: an array of objects here)
        | Fable.DeclaredType(arr, []) when arr.FullName = "System.Array" ->
            lw ctx (Fable.TypeCast(Fable.TypeCast(x, Fable.Array(Fable.Any, Fable.MutableArray)), e.Type))
        // (the matches and the groups of a regular expression)
        | Fable.DeclaredType(coll, []) when
            coll.FullName = "System.Text.RegularExpressions.MatchCollection"
            || coll.FullName = "System.Text.RegularExpressions.GroupCollection"
            ->
            libraryCall
                ctx
                e.Range
                "Regex"
                (if coll.FullName.EndsWith("MatchCollection", System.StringComparison.Ordinal) then
                     "matchesToSeq"
                 else
                     "groupsToSeq")
                (Fable.CallInfo.Create(args = [ x ]))
                [ x ]
                e.Type
        // (a string: its chars)
        | Fable.String ->
            let chars = TEnt(arrayEnt ctx.State, [ TPrim "u16" ])
            ctx.State.UsesRuntime <- true

            bindArgs
                ctx
                [ lw ctx x ]
                (fun xs ->
                    bindArgs
                        ctx
                        [ ERt("fable_rt.strToChars($0)", xs, chars) ]
                        (fun cs -> ECall(libraryTarget ctx "Seq" "ofArray", [ itemTy ], cs, seqTy))
                )
        | _ ->
            match forInSource ctx x with
            | Some(listExpr, "list") ->
                bindArgs ctx [ listExpr ] (fun xs -> ECall(libraryTarget ctx "Seq" "ofList", [ itemTy ], xs, seqTy))
            | _ ->
                match x.Type with
                // (a value of a type parameter constrained to a sequence: what it is, Zig knows
                // when it instantiates the function)
                | Fable.GenericParam _ ->
                    let seqModule =
                        if System.IO.Path.GetFileNameWithoutExtension(ctx.Com.CurrentFile) = "Seq" then
                            "@This()"
                        else
                            importAlias ctx (Fable.Transforms.AST.getLibPath ctx.Com "Seq")

                    ctx.State.UsesRuntime <- true
                    bindArgs ctx [ lw ctx x ] (fun xs -> ERt($"fable_rt.flexSeq($R, $0, %s{seqModule})", xs, seqTy))
                | _ -> fail e.Range "the Zig target cannot use a value of this type as a sequence yet (%A)" x.Type

    // (a cancellation source given as an `IDisposable`: what the library's Async.fs makes of it)
    | Fable.TypeCast(x, Fable.DeclaredType(target, _)) when
        target.FullName = "System.IDisposable"
        && (
            match x.Type with
            | Fable.DeclaredType(e, _) -> e.FullName = "System.Threading.CancellationTokenSource"
            | _ -> false
        )
        ->
        libraryCall ctx e.Range "Async" "sourceAsDisposable" (Fable.CallInfo.Create(args = [ x ])) [ x ] e.Type
    // an interface given where an interface it inherits is expected: fat-pointer upcast preserving
    // underlying identity and sub-interface type for round-trip casts
    | Fable.TypeCast(x, (Fable.DeclaredType _ as ifaceType)) when
        isInterfaceType ctx.Com ifaceType
        && isInterfaceType ctx.Com x.Type
        && isFatIfaceTy (mapType ctx e.Range ifaceType)
        && isFatIfaceTy (mapType ctx e.Range x.Type)
        && mapType ctx e.Range ifaceType <> mapType ctx e.Range x.Type
        ->
        match x with
        | Fable.TypeCast(inner, _) when not (isInterfaceType ctx.Com inner.Type) ->
            lw ctx (Fable.TypeCast(inner, ifaceType))
        | _ ->
            let ifaceTy = mapType ctx e.Range ifaceType

            let ifaceStructTy =
                match ifaceTy with
                | TOpt s -> s
                | _ -> ifaceTy

            let srcTy = mapType ctx e.Range x.Type

            let srcStructTy =
                match srcTy with
                | TOpt s -> s
                | _ -> srcTy

            let srcFields = caseFields srcStructTy "" |> List.map fst |> Set.ofList
            let targetFields = caseFields ifaceStructTy ""

            for (f, _) in targetFields do
                if not (srcFields.Contains f) then
                    fail e.Range "the Zig target cannot see %A as %A yet" x.Type ifaceType

            let slots = targetFields |> List.map (fun (f, _) -> f, (f, []))

            bindArgs
                ctx
                [ lw ctx x ]
                (fun xs ->
                    let buildFrom (src: Expr) =
                        let built = EIface(ifaceStructTy, ISrcUpcast src, slots)

                        match ifaceTy with
                        | TOpt _ -> ECon(ifaceTy, "Some", [ built ], None)
                        | _ -> built

                    match typeOf xs.Head with
                    | TOpt _ ->
                        EIf(
                            ETest(xs.Head, "None", typeOf xs.Head),
                            ECon(ifaceTy, "None", [], None),
                            bindArgs ctx [ EGet(xs.Head, PSome, srcStructTy) ] (fun ys -> buildFrom ys.Head),
                            ifaceTy
                        )
                    | _ -> buildFrom xs.Head
                )

    // (a `System.Array` or an `IList<'T>` seen as something else, a sequence: as the array it is
    // here)
    | Fable.TypeCast(x, target) when
        (match x.Type, target with
         | Fable.DeclaredType(a, []), Fable.DeclaredType(b, _) when a.FullName = "System.Array" ->
             b.FullName <> "System.Array"
         | Fable.DeclaredType(a, [ _ ]), Fable.DeclaredType(b, _) when a.FullName = "System.Collections.Generic.IList`1" ->
             b.FullName <> "System.Collections.Generic.IList`1"
         | _ -> false)
        ->
        let asArray =
            match x.Type with
            | Fable.DeclaredType(_, [ item ]) -> Fable.Array(item, Fable.MutableArray)
            | _ -> Fable.Array(Fable.Any, Fable.MutableArray)

        // (the non-generic IEnumerable, as `Seq.cast` takes it: a sequence of objects)
        let target =
            match target with
            | Fable.DeclaredType(e, []) when e.FullName = "System.Collections.IEnumerable" ->
                Fable.DeclaredType(
                    {
                        FullName = "System.Collections.Generic.IEnumerable`1"
                        Path = Fable.CoreAssemblyName "System.Runtime"
                    },
                    [ Fable.Any ]
                )
            | t -> t

        lw ctx (Fable.TypeCast(Fable.TypeCast(x, asArray), target))
    // (an array seen as `IList<'T>`: the same array)
    | Fable.TypeCast(x, Fable.DeclaredType(i, [ _ ])) when
        i.FullName = "System.Collections.Generic.IList`1"
        && (
            match x.Type with
            | Fable.Array(_, (Fable.MutableArray | Fable.ImmutableArray)) -> true
            | _ -> false
        )
        ->
        lw ctx x
    // (an array seen as `System.Array`: its items as objects)
    | Fable.TypeCast(x, Fable.DeclaredType(i, [])) when
        i.FullName = "System.Array"
        && (
            match x.Type with
            | Fable.Array(item, (Fable.MutableArray | Fable.ImmutableArray)) -> item <> Fable.Any
            | _ -> false
        )
        ->
        ctx.State.UsesRuntime <- true

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                EEmit("fable_rt.arrayBoxAll($0)", xs, mapType ctx e.Range (Fable.Array(Fable.Any, Fable.MutableArray)))
            )
    // (a value seen as `IComparable`: the object of it)
    | Fable.TypeCast(x, Fable.DeclaredType(i, [])) when i.FullName = "System.IComparable" && x.Type <> Fable.Any ->
        boxed ctx x
    // (`Comparer<'T>` where its IComparer is expected: the same value here)
    | Fable.TypeCast(x, ifaceTarget) when
        (match x.Type, unwrapNullness ifaceTarget with
         | Fable.DeclaredType(c, [ _ ]), Fable.DeclaredType(i, [ _ ]) ->
             c.FullName = "System.Collections.Generic.Comparer`1"
             && i.FullName = "System.Collections.Generic.IComparer`1"
         | _ -> false)
        ->
        lw ctx x
    // a value given where an interface is expected: fat-pointer `{ data, vt }` built from static
    // vtable slots (zero allocation for class objects; boxed for value types/records)
    // (a map seen as the collection of its entries: the list of its pairs, as `ICollection` is a
    // list here and an entry a pair)
    | Fable.TypeCast(x, Fable.DeclaredType(c, [ _ ])) when
        (c.FullName = "System.Collections.Generic.ICollection`1"
         || c.FullName = "System.Collections.Generic.IReadOnlyCollection`1")
        && (
            match x.Type with
            | Fable.DeclaredType(m, [ _; _ ]) -> m.FullName = mapName
            | _ -> false
        )
        ->
        let k, v =
            match x.Type with
            | Fable.DeclaredType(_, [ k; v ]) -> mapTypeArg ctx e.Range k, mapTypeArg ctx e.Range v
            | _ -> failwith "unreachable"

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                ECall(libraryTarget ctx "Map" "toList", [ k; v ], xs, TEnt(listEnt ctx.State, [ TTuple [ k; v ] ]))
            )
    | Fable.TypeCast(x, ifaceTarget) when isInterfaceType ctx.Com ifaceTarget && not (isInterfaceType ctx.Com x.Type) ->
        let ifaceRef, _ =
            match unwrapNullness ifaceTarget with
            | Fable.DeclaredType(r, _) as t -> r, t
            | _ -> fail e.Range "internal: not an interface type"

        let ifaceTy = mapType ctx e.Range ifaceTarget

        let ifaceStructTy =
            match ifaceTy with
            | TOpt s -> s
            | _ -> ifaceTy

        let innerSrcType = unwrapNullness x.Type

        let classRef =
            match innerSrcType with
            | Fable.DeclaredType(classRef, _) -> classRef
            | other -> fail e.Range "the Zig target cannot make an interface of a value of this type yet (%A)" other

        let slots =
            caseFields ifaceStructTy ""
            |> List.map (fun (f, _) ->
                let fn, targs =
                    interfaceImplSlot ctx e.Range innerSrcType classRef ifaceRef.FullName f

                f, (fn, targs)
            )

        bindArgs
            ctx
            [ lw ctx x ]
            (fun objs ->
                let buildWith (xs: Expr list) =
                    let built = EIface(ifaceStructTy, ISrcValue xs.Head, slots)

                    match ifaceTy with
                    | TOpt _ -> ECon(ifaceTy, "Some", [ built ], None)
                    | _ -> built

                match typeOf objs.Head with
                | TOpt innerTy ->
                    EIf(
                        ETest(objs.Head, "None", typeOf objs.Head),
                        ECon(ifaceTy, "None", [], None),
                        bindArgs ctx [ EGet(objs.Head, PSome, innerTy) ] buildWith,
                        ifaceTy
                    )
                | _ -> bindArgs ctx [ objs.Head ] buildWith
            )

    // `{ new IShape with ... }`: each member, a function value of its own
    // `{ new Shape("x") with member _.Area() = ... }`: an object of a class of its own that
    // derives from Shape. Its fields are the function values of its members (which hold what
    // they capture); its table calls them.
    | Fable.ObjectExpr(members, Fable.DeclaredType(baseRef, baseGenArgs), Some(Fable.Call(callee, call, _, cr))) when
        (objInfo ctx e.Range baseRef).IsSome
        ->
        let parent = (objInfo ctx e.Range baseRef).Value
        let n = ctx.State.ObjInfos.Count
        let prefix = $"%s{cleanIdent ctx.FnBase}__obj%d{n}"

        // (enclosing type parameters used by the base class arguments or overridden members)
        let gens =
            if ctx.TypeParams.IsEmpty then
                []
            else
                let used = HashSet<string>()

                let rec collect (t: Fable.Type) =
                    match t with
                    | Fable.GenericParam(name, _, _) -> used.Add name |> ignore
                    | Fable.Option(i, _)
                    | Fable.Nullable(i, _)
                    | Fable.Array(i, _)
                    | Fable.List i -> collect i
                    | Fable.Tuple(ts, _)
                    | Fable.AnonymousRecordType(_, ts, _) -> List.iter collect ts
                    | Fable.LambdaType(a, r) ->
                        collect a
                        collect r
                    | Fable.DelegateType(args, r) ->
                        List.iter collect args
                        collect r
                    | Fable.DeclaredType(_, gs) -> List.iter collect gs
                    | _ -> ()

                List.iter collect baseGenArgs

                for m in members do
                    collect m.Body.Type

                    for a in m.Args do
                        collect a.Type

                for a in call.Args do
                    collect a.Type

                ctx.TypeParams |> List.filter used.Contains

        let genTys = gens |> List.map TGen
        let fableGenArgs = gens |> List.map (fun g -> Fable.GenericParam(g, false, []))

        let parentChainArgs =
            if parent.Gens.IsEmpty then
                []
            else
                baseGenArgs

        let parentLevels =
            levelArgs ctx e.Range parent (parentChainArgs |> List.map (mapTypeArg ctx e.Range))

        let parentArgsOf (k: ObjInfo) =
            parentLevels
            |> List.tryFind (fun (x, _) -> x.FullName = k.FullName)
            |> Option.map snd
            |> Option.defaultValue []

        let slots =
            members
            |> List.map (fun m ->
                let slot =
                    match ctx.Com.TryGetMember m.MemberRef with
                    | Some info -> info.CompiledName
                    | None -> m.Name

                if slot = "ToString" then
                    "ToString", TFn([ tObj; tVoid ], tStr), m
                else
                    match virtualSlot parent slot with
                    | Some(declarer, ty) ->
                        let dArgs = parentArgsOf declarer

                        let subst =
                            if declarer.Gens.Length = dArgs.Length then
                                List.zip declarer.Gens dArgs |> Map.ofList
                            else
                                Map.empty

                        slot, substTy subst ty, m
                    | None -> fail e.Range "the Zig target does not support %s in this object expression yet" slot
            )

        let synth (suffix: string) (cases: (string * Ty) list) : Ent =
            {
                Name = prefix + "__" + suffix
                Ref =
                    {
                        FullName = parent.FullName + "$" + prefix + "$" + suffix
                        Path = baseRef.Path
                    }
                Kind = KRecord
                TypeParams = gens
                Cases = [ "", cases ]
                MutableFields = []
                Managed = false
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = true
                Hooks = None
                Overrides = []
            }

        let part = synth "part" (slots |> List.map (fun (slot, ty, _) -> slot, ty))

        let chain =
            synth
                "chain"
                [
                    "base", TEnt(parent.Chain, parentChainArgs |> List.map (mapTypeArg ctx e.Range))
                    "own", TEnt(part, genTys)
                ]

        for ent in [ part; chain ] do
            ctx.State.Ents[ent.Ref.FullName] <- ent
            ctx.State.LocalEnts.Add ent

        if ctx.State.EntDepth = 0 then
            settleManaged ctx.State

        let info =
            {
                Ref =
                    {
                        FullName = parent.FullName + "$" + prefix
                        Path = baseRef.Path
                    }
                FullName = parent.FullName + "$" + prefix
                Prefix = prefix
                Depth = parent.Depth + 1
                Parent = Some parent
                Part = part
                Chain = chain
                Slots = []
                Table = None
                IsAbstract = false
                IsLocal = true
                Gens = gens
                ParentArgs = parentChainArgs
            }

        ctx.State.ObjInfos[info.FullName] <- box info
        let overridden = slots |> List.map (fun (slot, _, _) -> slot) |> set

        let tables =
            (None
             :: (parentLevels
                 |> List.map (fun (level, largs) ->
                     match level.Table with
                     | Some vt ->
                         let subst =
                             if level.Gens.Length = largs.Length then
                                 List.zip level.Gens largs |> Map.ofList
                             else
                                 Map.empty

                         let entries =
                             level.Slots
                             |> List.map (fun (slot, slotTy) ->
                                 if overridden.Contains slot then
                                     slot, "@raw:" + prefix + "__" + slot, genTys, substTy subst slotTy
                                 else
                                     let impl =
                                         match
                                             ancestors parent
                                             |> List.tryFind (fun k -> classImplements ctx.Com k slot)
                                         with
                                         | Some k -> k
                                         | None ->
                                             fail
                                                 e.Range
                                                 "the Zig target finds no implementation of %s for %s"
                                                 slot
                                                 parent.FullName

                                     slot, implName impl.Prefix slot, parentArgsOf impl, substTy subst slotTy
                             )

                         Some(TEnt(vt, largs), entries)
                     | None -> None
                 )))
            |> List.rev

        ctx.State.Objs.Add
            {
                TypeName = prefix + "__type"
                TypeParams = gens
                Chain = TEnt(chain, genTys)
                DotnetName = parent.FullName.Substring(parent.FullName.LastIndexOf '.' + 1) + "@" + string n
                Parent = Some(objTypeRef parent (parentArgsOf parent))
                Tables = tables
                ToString =
                    if overridden.Contains "ToString" then
                        Some("@raw:" + prefix + "__ToString", ([]: Ty list))
                    else
                        ancestors parent
                        |> List.tryFind (fun k -> classImplements ctx.Com k "ToString")
                        |> Option.map (fun k -> k.Prefix + "__ToString", parentArgsOf k)
                Overrides =
                    [
                        "equals", "Equals"
                        "hash", "GetHashCode"
                        "compare", "System.IComparable.CompareTo"
                    ]
                    |> List.choose (fun (hook, slot) ->
                        ancestors parent
                        |> List.tryFind (fun k -> classImplements ctx.Com k slot)
                        |> Option.map (fun k -> hook, implName k.Prefix slot)
                    )
                Ifaces = []
                Thunks =
                    slots
                    |> List.map (fun (slot, ty, _) ->
                        prefix + "__" + slot,
                        TPtr(TEnt(part, genTys), false),
                        partNamesOf ctx e.Range info genTys,
                        slot,
                        ty
                    )
            }

        let chainTy = TEnt(chain, genTys)
        ctx.State.AllocChains.Add chainTy
        let v = ctx.State.NewVar("made", tObj, VLocal, false)

        let madeId =
            { AST.makeTypedIdent (Fable.DeclaredType(info.Ref, fableGenArgs)) $"__made_%d{v.Id}" with
                IsThisArgument = true
            }

        ctx.Vars[madeId.Name] <- v

        let alloc =
            EEmit($"fable_rt.objAlloc(%s{zigType chainTy}, %s{objTypeRef info genTys})", [], tObj)

        // (a member's first argument is the object, which the call checks is not null; store the
        // object expression's method closures into its part before calling the base constructor, so
        // virtual calls inside the base constructor find them ready)
        let partSets =
            slots
            |> List.map (fun (slot, _, m) ->
                let args =
                    match m.Args with
                    | [ this ] when slot = "ToString" ->
                        [ { this with IsThisArgument = true }; AST.makeTypedIdent Fable.Unit "unitArg" ]
                    | this :: rest -> { this with IsThisArgument = true } :: rest
                    | [] -> []

                let closure = Fable.Delegate(args, m.Body, None, [])
                Fable.Set(Fable.IdentExpr madeId, Fable.FieldSet slot, closure.Type, closure, e.Range)
            )

        let baseCallExpr =
            Fable.Call(
                callee,
                { call with
                    ThisArg = Some(Fable.IdentExpr madeId)
                    GenericArgs =
                        if call.GenericArgs.IsEmpty then
                            parentChainArgs
                        else
                            call.GenericArgs
                },
                Fable.Unit,
                cr
            )

        ELet(v, alloc, ESeq(lwStmt { ctx with InCtor = true } (Fable.Sequential(partSets @ [ baseCallExpr ])), EVar v))

    // an object expression of `IEnumerable<'T>`: a sequence of its `GetEnumerator`
    | Fable.ObjectExpr(members, Fable.DeclaredType(seqRef, [ item ]), None) when
        seqRef.FullName = "System.Collections.Generic.IEnumerable`1"
        ->
        let getEnumerator =
            members
            |> List.tryFind (fun m ->
                match m.Body.Type with
                | Fable.DeclaredType(e, [ _ ]) -> e.FullName = "System.Collections.Generic.IEnumerator`1"
                | _ -> false
            )

        match getEnumerator with
        | Some m ->
            let body =
                match m.Args with
                | this :: _ when liveUse this.Name m.Body ->
                    fail e.Range "the Zig target does not support `this` in an object expression yet"
                | _ -> m.Body

            lowerSeqOfGetEnumerator ctx e.Range item body
        | None -> fail e.Range "the Zig target cannot find GetEnumerator in this object expression"
    // an object expression whose members use the object itself (`member x.Test i = x.Value - i`):
    // they read it from a cell, which is filled with it once it is made
    | Fable.ObjectExpr(members, ifaceType, None) when
        isInterfaceType ctx.Com ifaceType
        && members
           |> List.exists (fun m ->
               match m.Args with
               | this :: _ -> liveUse this.Name m.Body
               | [] -> false
           )
        ->
        let optT = Fable.Option(ifaceType, false)

        let refRef: Fable.EntityRef =
            {
                FullName = refName
                Path = Fable.CoreAssemblyName "FSharp.Core"
            }

        let cellT = Fable.DeclaredType(refRef, [ optT ])
        let cell = AST.makeTypedIdent cellT "objectSelf"
        let obj = AST.makeTypedIdent ifaceType "objectMade"

        // (a ref cell, as F# makes one: `ref x`, `r.Value`, `r.Value <- x`)
        let refCall
            (selector: string)
            (path: string)
            (thisArg: Fable.Expr option)
            (args: Fable.Expr list)
            (t: Fable.Type)
            =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = selector
                        Path = Replacements.DotnetPrefix + path
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = thisArg.IsSome))
                    },
                    Fable.Any,
                    None
                ),
                { Fable.CallInfo.Create(?thisArg = thisArg, args = args) with GenericArgs = [ optT ] },
                t,
                None
            )

        let self =
            Fable.Get(
                refCall "get_Value" refName (Some(Fable.IdentExpr cell)) [ Fable.Value(Fable.UnitConstant, None) ] optT,
                Fable.OptionValue,
                ifaceType,
                None
            )

        let members =
            members
            |> List.map (fun m ->
                match m.Args with
                | this :: _ ->
                    let rec subst (x: Fable.Expr) =
                        match x with
                        | Fable.IdentExpr i when i.Name = this.Name -> self
                        | _ -> AST.visit subst x

                    { m with Body = subst m.Body }
                | [] -> m
            )

        lw
            ctx
            (Fable.Let(
                cell,
                refCall
                    "Ref"
                    "Microsoft.FSharp.Core.Operators"
                    None
                    [ Fable.Value(Fable.NewOption(None, ifaceType, false), None) ]
                    cellT,
                Fable.Let(
                    obj,
                    Fable.ObjectExpr(members, ifaceType, None),
                    Fable.Sequential
                        [
                            refCall
                                "set_Value"
                                refName
                                (Some(Fable.IdentExpr cell))
                                [
                                    Fable.Value(Fable.NewOption(Some(Fable.IdentExpr obj), ifaceType, false), None)
                                ]
                                Fable.Unit
                            Fable.IdentExpr obj
                        ]
                )
            ))
    | Fable.ObjectExpr(members, ifaceType, None) when isInterfaceType ctx.Com ifaceType ->
        // (`fun a b -> (f x) a b`: compute partial applications once when the object is made)
        let mutable preBindings = []

        let hoistedMembers =
            members
            |> List.map (fun m ->
                match m.Args with
                | this :: rawArgs when not rawArgs.IsEmpty ->
                    match etaHead rawArgs m.Body with
                    | Some(head, rebuild) ->
                        let held = AST.makeTypedIdent head.Type "applied"
                        preBindings <- (held, head) :: preBindings
                        { m with Body = rebuild (Fable.IdentExpr held) }
                    | None -> m
                | _ -> m
            )

        if not preBindings.IsEmpty then
            let expr =
                List.fold
                    (fun body (id, v) -> Fable.Let(id, v, body))
                    (Fable.ObjectExpr(hoistedMembers, ifaceType, None))
                    preBindings

            lw ctx expr
        else
            let ifaceTy = mapType ctx e.Range ifaceType

            let ifaceStructTy =
                match ifaceTy with
                | TOpt s -> s
                | _ -> ifaceTy

            let rec usesIdent (name: string) (e: Fable.Expr) =
                match e with
                | Fable.IdentExpr id -> id.Name = name
                | _ -> getSubExpressions e |> List.exists (usesIdent name)

            // (two members of one name, as `IEnumerator<'T>.Current` and `IEnumerator.Current`: the one
            // whose result is the type the struct keeps)
            let candidates =
                hoistedMembers
                |> List.map (fun m ->
                    let compiled =
                        match ctx.Com.TryGetMember m.MemberRef with
                        | Some info ->
                            let slot = implementedSlot ctx.Com info

                            // (the field of the struct: the slot, when the member says which)
                            if slot.Contains "$" then
                                slot
                            else
                                info.CompiledName
                        | None -> m.Name

                    compiled, m
                )

            let pick (f: string) (fty: Ty) =
                match candidates |> List.filter (fun (n, _) -> n = f) with
                | [] -> None
                | [ (_, m) ] -> Some m
                | several ->
                    let returns (m: Fable.ObjectExprMember) =
                        match fty with
                        | TSlot(_, ret)
                        | TFn(_, ret) -> mapType ctx e.Range m.Body.Type = ret
                        | _ -> false

                    let notObj (m: Fable.ObjectExprMember) = m.Body.Type <> Fable.Any

                    several
                    |> List.tryFind (snd >> returns)
                    |> Option.orElse (several |> List.tryFind (snd >> notObj))
                    |> Option.defaultValue several.Head
                    |> snd
                    |> Some

            let slotDelegates =
                caseFields ifaceStructTy ""
                |> List.map (fun (f, fty) ->
                    match pick f fty with
                    | Some m ->
                        match m.Args with
                        | this :: rawArgs ->
                            if usesIdent this.Name m.Body then
                                fail e.Range "the Zig target does not support `this` in an object expression yet"

                            let body =
                                match ctx.Com.TryGetMember m.MemberRef with
                                | Some info -> wrapNullCast info.ReturnParameter.Type m.Body
                                | None -> m.Body

                            let args =
                                if rawArgs.IsEmpty then
                                    [ AST.makeTypedIdent Fable.Unit "unitVar" ]
                                else
                                    rawArgs

                            f, Fable.Delegate(args, body, None, [])
                        | [] -> fail e.Range "internal: a member without its object"
                    // (a `[<CLIEvent>]` member: the object expression has its add_ and remove_; its
                    // getter is the event F# makes of them, `RuntimeHelpers.CreateEvent`)
                    | None when
                        f.StartsWith("get_", System.StringComparison.Ordinal)
                        && (pick ("add_" + f.Substring 4) fty).IsSome
                        && (pick ("remove_" + f.Substring 4) fty).IsSome
                        ->
                        let name = f.Substring 4
                        let addM = (pick ("add_" + name) fty).Value
                        let removeM = (pick ("remove_" + name) fty).Value

                        let handlerOf (m: Fable.ObjectExprMember) =
                            match m.Args with
                            | _ :: h :: _ -> Fable.Lambda(h, m.Body, None), h.Type
                            | _ -> fail e.Range "internal: an event's add or remove without its handler"

                        let addF, delTy = handlerOf addM
                        let removeF, _ = handlerOf removeM

                        let argTy =
                            match delTy with
                            | Fable.DelegateType([ _; a ], _) -> a
                            | Fable.DeclaredType(_, [ _; a ]) -> a
                            | _ -> Fable.Any

                        let fId =
                            AST.makeTypedIdent
                                (Fable.LambdaType(Fable.Any, Fable.LambdaType(argTy, Fable.Unit)))
                                "handler"

                        let sId = AST.makeTypedIdent Fable.Any "sender"
                        let aId = AST.makeTypedIdent argTy "args"

                        let createF =
                            Fable.Lambda(
                                fId,
                                Fable.Delegate(
                                    [ sId; aId ],
                                    Fable.CurriedApply(
                                        Fable.IdentExpr fId,
                                        [ Fable.IdentExpr sId; Fable.IdentExpr aId ],
                                        Fable.Unit,
                                        None
                                    ),
                                    None,
                                    []
                                ),
                                None
                            )

                        let eventTy =
                            Fable.DeclaredType(
                                {
                                    FullName = "Microsoft.FSharp.Control.IEvent`2"
                                    Path = Fable.CoreAssemblyName "FSharp.Core"
                                },
                                [ delTy; argTy ]
                            )

                        let create =
                            Fable.Call(
                                Fable.Import(
                                    {
                                        Selector = "CreateEvent"
                                        Path =
                                            Replacements.DotnetPrefix
                                            + "Microsoft.FSharp.Core.CompilerServices.RuntimeHelpers"
                                        Kind =
                                            Fable.LibraryImport(
                                                Fable.LibraryImportInfo.Create(isInstanceMember = false)
                                            )
                                    },
                                    Fable.Any,
                                    None
                                ),
                                Fable.CallInfo.Create(args = [ addF; removeF; createF ], genArgs = [ delTy; argTy ]),
                                eventTy,
                                e.Range
                            )

                        f, Fable.Delegate([ AST.makeTypedIdent Fable.Unit "unitVar" ], create, None, [])
                    | None ->
                        fail
                            e.Range
                            "the Zig target cannot find the member %s in this object expression (it has %s)"
                            f
                            (candidates |> List.map fst |> String.concat ", ")
                )

            let lifted =
                liftGroup ctx e.Range (slotDelegates |> List.map (fun (f, fnExpr) -> None, cleanIdent f, fnExpr))

            let captureNames =
                match lifted with
                | fn :: _ -> fn.CaptureNames
                | [] -> []

            let capExprs = captureExprs ctx e.Range captureNames
            let typeArgs = ctx.TypeParams |> List.map TGen

            let slots =
                List.zip (slotDelegates |> List.map fst) lifted
                |> List.map (fun (f, fn) -> f, (fn.FnName, typeArgs))

            bindArgsIn
                true
                ctx
                capExprs
                (fun caps ->
                    let built = EIface(ifaceStructTy, ISrcCaptures caps, slots)

                    match ifaceTy with
                    | TOpt _ -> ECon(ifaceTy, "Some", [ built ], None)
                    | _ -> built
                )

    | Fable.Get(x, kind, t, r) ->
        let ty = mapType ctx r t

        let getFrom (v: Expr) =
            // (a function of several arguments is kept uncurried in a field, as Fable has it:
            // the field's own type says how)
            let stored (case: string) (field: string) =
                match ty with
                | TFn _
                | TOpt(TFn _) ->
                    match caseFields (typeOf v) case |> List.tryFind (fun (f, _) -> f = field) with
                    | Some(_, (TFn _ | TOpt(TFn _) as fty)) -> fty
                    | _ -> ty
                | _ -> ty

            match kind, typeOf v with
            | Fable.FieldGet info, TEnt(ent, _) when ent.Kind = KRecord || ent.Kind = KRefRecord ->
                EGet(v, PField info.Name, stored "" info.Name)
            | Fable.TupleIndex i, TTuple _ -> EGet(v, PItem i, ty)
            | Fable.UnionField info, TEnt(ent, _) ->
                let case, fields = List.item info.CaseIndex ent.Cases
                let field = fst (List.item info.FieldIndex fields)
                EGet(v, PCase(case, field), stored case field)
            | Fable.UnionTag, TEnt _ -> EPrim("tag", [ v ], tI32)
            | Fable.ListHead, TEnt _ -> EGet(v, PCase("Cons", "Head"), ty)
            | Fable.ListTail, TEnt _ -> EGet(v, PCase("Cons", "Tail"), ty)
            | Fable.OptionValue, TOpt(TFn _ as inner) when
                (match ty with
                 | TFn _ -> true
                 | _ -> false)
                ->
                EGet(v, PSome, inner)
            | Fable.OptionValue, TOpt _ -> EGet(v, PSome, ty)
            | _ -> fail r "the Zig target does not support %s yet" (exprKind e)

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                match kind, typeOf xs.Head with
                | Fable.OptionValue, _ -> getFrom xs.Head
                | _, TOpt _ -> bindArgs ctx [ unwrapIface ctx xs.Head ] (fun ys -> getFrom ys.Head)
                | _ -> getFrom xs.Head
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
                if not ctx.State.CatchesOom && handlerMayCatchOom id handler then
                    ctx.State.CatchesOom <- true

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
        let testOf (v: Expr) =
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

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                match kind, typeOf xs.Head with
                | Fable.OptionTest _, _ -> testOf xs.Head
                | _, TOpt _ -> bindArgs ctx [ unwrapIface ctx xs.Head ] (fun ys -> testOf ys.Head)
                | _ -> testOf xs.Head
            )

    // (a function of the quotations' library, as the shared mapping and emitter call it)
    | Fable.Call(Fable.Import(imp, _, _), info, t, r) when
        imp.Path.EndsWith("quotation.zig", System.StringComparison.OrdinalIgnoreCase)
        ->
        libraryCall ctx r "Quotation" imp.Selector info (Option.toList info.ThisArg @ info.Args) t
    | Fable.Call(callee, info, t, r) ->
        let ty = mapType ctx r t

        // (a member of a type is a function whose first argument is the object)
        let allArgs = Option.toList info.ThisArg @ info.Args

        // (a property read as a value, as `[<CLIEvent>]` makes it: the getter takes its unit, which
        // the call does not give; and the other way round)
        // (only for a function of this file: its parameters include the object; those that the
        // members of another file list do not)
        let allArgs =
            match
                (match callee with
                 | Fable.IdentExpr _ -> tryCallable ctx callee
                 | _ -> None)
            with
            | Some c when allArgs.Length + 1 = c.ArgTypes.Length && List.last c.ArgTypes = Fable.Unit ->
                allArgs @ [ Fable.Value(Fable.UnitConstant, None) ]
            | Some c when
                allArgs.Length = c.ArgTypes.Length + 1
                && (List.last allArgs).Type = Fable.Unit
                && not c.ArgTypes.IsEmpty
                ->
                List.take c.ArgTypes.Length allArgs
            | _ -> allArgs

        // (optional arguments left out at the end of the call, which Fable drops: `None`)
        let allArgs =
            match tryCallable ctx callee with
            | Some c when
                allArgs.Length < c.ArgTypes.Length
                && c.ArgTypes
                   |> List.skip allArgs.Length
                   |> List.forall (fun t ->
                       match t with
                       | Fable.Option(_, false) -> true
                       | _ -> false
                   )
                ->
                allArgs
                @ (c.ArgTypes
                   |> List.skip allArgs.Length
                   |> List.map (fun t -> Fable.Value(Fable.NewOption(None, t.Generics.Head, false), None)))
            | _ -> allArgs

        let allArgs =
            if info.SignatureArgTypes.Length = allArgs.Length then
                List.map2 wrapNullCast info.SignatureArgTypes allArgs
            elif info.ThisArg.IsSome && info.SignatureArgTypes.Length + 1 = allArgs.Length then
                allArgs.Head :: List.map2 wrapNullCast info.SignatureArgTypes allArgs.Tail
            else
                allArgs

        // (an argument made at a more general type than the parameter's, see adaptTo)
        let allArgs =
            match tryCallable ctx callee with
            | Some c when
                c.ArgTypes.Length = allArgs.Length
                && c.TypeParams.Length = info.GenericArgs.Length
                ->
                let subst = List.zip c.TypeParams info.GenericArgs |> Map.ofList

                if allArgs |> List.exists (fun a -> hasTypeParams a.Type |> not) then
                    List.map2
                        (fun (p: Fable.Type) (a: Fable.Expr) ->
                            let wanted = substFableType subst p

                            if hasTypeParams wanted then
                                wrapNullCast wanted a
                            else
                                adaptTo ctx.Com wanted a
                        )
                        c.ArgTypes
                        allArgs
                else
                    List.map2
                        (fun (p: Fable.Type) (a: Fable.Expr) -> wrapNullCast (substFableType subst p) a)
                        c.ArgTypes
                        allArgs
            | _ -> allArgs

        let args = allArgs |> List.map (lw ctx)

        // (the object a member of a class is called on: checked for null; named first, as it is
        // read twice)
        let args =
            match info.ThisArg, args with
            | Some x, first :: rest when
                (match x.Type with
                 | Fable.DeclaredType(e, _) -> (objInfo ctx r e).IsSome
                 | _ -> false)
                && (
                    match typeOf first with
                    | TOpt t -> t = tObj
                    | _ -> false
                )
                ->
                match first with
                | EVar _ -> asObjOf ctx x first :: rest
                | _ ->
                    let v = ctx.State.NewVar("obj", typeOf first, VLocal, false)
                    ELet(v, first, asObjOf ctx x (EVar v)) :: rest
            | _ -> args

        match tryCallable ctx callee, callee with
        | Some c, _ ->
            let typeArgs, subst =
                typeArgsOf ctx r c (Some info.GenericArgs) (allArgs |> List.map (fun a -> a.Type)) (Some t)

            // (F# gives a value, not its address, where an `inref` is expected)
            let isByref (t: Fable.Type) =
                match t with
                | Fable.DeclaredType(ent, _) -> ent.FullName = "Microsoft.FSharp.Core.byref`2"
                | _ -> false

            let args =
                if c.ArgTypes.Length = allArgs.Length then
                    List.map3
                        (fun (p: Fable.Type) (a: Fable.Expr) (argIr: Expr) ->
                            if isByref p && isByref a.Type then
                                defaultArg (tryAddress argIr) argIr
                            else
                                argIr
                        )
                        c.ArgTypes
                        allArgs
                        args
                else
                    args

            // (whether a value is given by its address, and whether the callee may change it
            // through it: `byref`, as the `this` of a struct with mutable fields, or `inref`)
            let wantsAddress =
                if c.ArgTypes.Length = allArgs.Length then
                    List.map2
                        (fun (p: Fable.Type) (a: Fable.Expr) ->
                            if isByref p && not (isByref a.Type) then
                                match mapType ctx r p with
                                | TPtr(_, isConst) -> Some isConst
                                | _ -> Some true
                            else
                                None
                        )
                        c.ArgTypes
                        allArgs
                else
                    allArgs |> List.map (fun _ -> None)

            bindArgs
                ctx
                args
                (fun xs ->
                    // (a value that is not in a variable is put in one, whose address is given)
                    let temps = List<Var * Expr>()

                    let xs =
                        List.map2
                            (fun x want ->
                                match x, want with
                                | EVar v, Some isConst -> EAddr(EVar v, isConst)
                                | EEmit("fable_rt.dup($0)", [ EVar v ], _), Some isConst when
                                    v.Kind = VGlobal && v.FMutable
                                    ->
                                    EAddr(EVar v, isConst)
                                | EAddr _, _
                                | _, None -> x
                                | _, Some isConst ->
                                    let v = ctx.State.NewVar("inref", typeOf x, VLocal, false)
                                    temps.Add((v, x))
                                    EAddr(EVar v, isConst)
                            )
                            xs
                            wantsAddress

                    let callRetTy =
                        if ty = tVoid then
                            tVoid
                        else
                            let instRet = substTy subst (mapType ctx r c.Ret)

                            if instRet = TOpt ty || ty = TOpt instRet then
                                instRet
                            else
                                ty

                    let callExpr =
                        Seq.foldBack
                            (fun (v, x) body -> ELet(v, x, body))
                            temps
                            (ECall(c.Target, typeArgs, c.Captures @ xs, callRetTy))

                    if ty = tVoid then
                        callExpr
                    else
                        coerceTy ctx ty callExpr
                )
        | None, Fable.Import(imp, _, _) ->
            fail r "the Zig target does not support this library call yet (%s from %s)" imp.Selector imp.Path
        // a function value: all its arguments at once
        | None, _ ->
            bindArgs
                ctx
                (lw ctx callee :: args)
                (fun xs ->
                    let callRetTy =
                        match typeOf xs.Head with
                        | TFn(ps, ret) when ps.Length = xs.Tail.Length -> ret
                        | _ -> ty

                    ECallClo(xs.Head, xs.Tail, callRetTy)
                )

    | Fable.CurriedApply(applied, args, t, r) ->
        let rec wrapApplyArgs (fnTy: Fable.Type) (xs: Fable.Expr list) =
            match fnTy, xs with
            | Fable.LambdaType(p, rest), a :: tail -> wrapNullCast p a :: wrapApplyArgs rest tail
            | Fable.DelegateType(ps, _), _ when ps.Length <= xs.Length ->
                let headArgs, tailArgs = List.splitAt ps.Length xs
                (List.map2 wrapNullCast ps headArgs) @ tailArgs
            | _ -> xs

        let args = wrapApplyArgs applied.Type args
        let targetTy = mapType ctx r t

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
                let callRetTy =
                    if targetTy = tVoid then
                        tVoid
                    else
                        let instRet = substTy subst (mapType ctx r c.Ret)

                        if instRet = TOpt targetTy || targetTy = TOpt instRet then
                            instRet
                        else
                            targetTy

                bindArgs
                    ctx
                    nowIr
                    (fun xs ->
                        let ce = ECall(c.Target, typeArgs, c.Captures @ xs, callRetTy)

                        if targetTy = tVoid then
                            ce
                        else
                            coerceTy ctx targetTy ce
                    )
            else
                // the function returns a function, which gets the other arguments
                let first =
                    bindArgs
                        ctx
                        nowIr
                        (fun xs -> ECall(c.Target, typeArgs, c.Captures @ xs, substTy subst (mapType ctx r c.Ret)))

                coerceTy ctx targetTy (applyValue ctx r subst first c.Ret rest t)
        | Some c ->
            coerceTy
                ctx
                targetTy
                (applyValue ctx r Map.empty (fnValue ctx r applied c applied.Type) applied.Type args t)
        | None -> coerceTy ctx targetTy (applyValue ctx r Map.empty (lw ctx applied) applied.Type args t)

    // `record.Field <- value`
    // (a property of an interface: by calling its setter slot on its vtable)
    | Fable.Set(x, Fable.FieldSet name, t, value, r) when
        isInterfaceType ctx.Com x.Type && isFatIfaceTy (mapType ctx r x.Type)
        ->
        let value = wrapNullCast t value

        let ifaceStructTy =
            match mapType ctx r x.Type with
            | TOpt s -> s
            | s -> s

        // (a mangled interface's member is named in full: `Ns.IFoo.set_Bar`)
        let short = name.Substring(name.LastIndexOf '.' + 1)

        let setter =
            if short.StartsWith("set_", System.StringComparison.Ordinal) then
                short
            else
                "set_" + short

        match caseFields ifaceStructTy "" |> List.tryFind (fun (f, _) -> f = setter) with
        | Some(f, fty) ->
            let valIr =
                match fty with
                | TSlot([ pty ], _)
                | TFn([ pty ], _) -> coerceTy ctx pty (lw ctx value)
                | _ -> lw ctx value

            bindArgs
                ctx
                [ lw ctx x; valIr ]
                (fun given -> withBorrowedIface ctx x given[0] (fun iface -> ECallIface(iface, f, [ given[1] ], tVoid)))
        | None -> fail r "the Zig target cannot find the setter of %s of this interface" name
    | Fable.Set(x, Fable.FieldSet name, t, value, r) ->
        let fieldFableTy =
            match unwrapNullness x.Type with
            | Fable.DeclaredType(entRef, genArgs) ->
                match ctx.Com.TryGetEntity entRef with
                | Some fEnt ->
                    let subst =
                        if fEnt.GenericParameters.Length = genArgs.Length then
                            List.zip (fEnt.GenericParameters |> List.map (fun g -> g.Name)) genArgs
                            |> Map.ofList
                        else
                            Map.empty

                    fEnt.FSharpFields
                    |> List.tryFind (fun f -> f.Name = name)
                    |> Option.map (fun f -> substFableType subst f.FieldType)
                    |> Option.defaultValue t
                | None -> t
            | _ -> t

        let value = wrapNullCast fieldFableTy value

        bindArgs
            ctx
            [ lw ctx x; lw ctx value ]
            (fun xs ->
                match typeOf xs[0] with
                | TEnt(ent, _) as recTy when List.contains name ent.MutableFields ->
                    let fieldTy =
                        caseFields recTy "" |> List.tryFind (fun (f, _) -> f = name) |> Option.map snd

                    let targetTy = defaultArg fieldTy (mapType ctx r t)
                    EStore(EGet(xs[0], PField name, targetTy), coerceTy ctx targetTy xs[1])
                | _ -> fail r "the Zig target does not support this kind of assignment yet"
            )

    | Fable.Set(Fable.IdentExpr id, Fable.ValueSet, _, value, r) when ctx.Boxed.Contains id.Name ->
        let value = wrapNullCast id.Type value
        let cellTy = mapType ctx r id.Type
        let cell = EGet(EVar ctx.Vars[id.Name], PField "contents", cellTy)
        bindArgs ctx [ coerceTy ctx cellTy (lw ctx value) ] (fun xs -> EStore(cell, xs.Head))

    | Fable.Set(Fable.IdentExpr id, Fable.ValueSet, _, value, r) ->
        let value = wrapNullCast id.Type value
        let nonNegAfter = isKnownNonNegExpr ctx value
        let valueIr = lw ctx value
        clearIdentFacts ctx id.Name

        if nonNegAfter && id.IsMutable then
            ctx.NonNeg.Add id.Name |> ignore

        match ctx.Vars.TryGetValue id.Name, ctx.Members.TryGetValue id.Name with
        | (true, ({ Ty = TPtr(t, _) } as v)), _ ->
            bindArgs ctx [ coerceTy ctx t valueIr ] (fun xs -> EStore(EDeref(EVar v, t), xs.Head))
        | (true, v), _ -> EAssign(v, coerceTy ctx v.Ty valueIr)
        // (a module-level value: what it held is given up once the new value is in place)
        | _, (true, MValue ty) ->
            ctx.State.UsesRuntime <- true

            bindArgs
                ctx
                [ coerceTy ctx ty valueIr ]
                (fun xs ->
                    EEmit("fable_rt.store(&$0, fable_rt.dup($1))", [ globalVar id.Name ty true; xs.Head ], tVoid)
                )
        | _ -> fail r "the Zig target cannot assign to `%s`" id.Name

    | Fable.Set(Fable.Import(imp, t, _), Fable.ValueSet, _, value, r) when (importedValue ctx imp).IsSome ->
        let value = wrapNullCast t value
        let name, _ = (importedValue ctx imp).Value
        let ty = mapType ctx r t
        ctx.State.UsesRuntime <- true

        bindArgs
            ctx
            [ lw ctx value ]
            (fun xs -> EEmit("fable_rt.store(&$0, fable_rt.dup($1))", [ globalVar name ty true; xs.Head ], tVoid))

    | Fable.WhileLoop(guard, body, r) ->
        let rec checkMonotonicStep (idxName: string) (inNestedLoop: bool) (e: Fable.Expr) : bool =
            match e with
            | Fable.Set(Fable.IdentExpr id, Fable.ValueSet, _, rhs, _) when id.Name = idxName ->
                if inNestedLoop then
                    false
                else
                    match rhs with
                    | Fable.Operation(Fable.Binary(BinaryPlus,
                                                   Fable.IdentExpr v,
                                                   Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 1, _), _)),
                                      _,
                                      _,
                                      _)
                    | Fable.Operation(Fable.Binary(BinaryPlus,
                                                   Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 1, _), _),
                                                   Fable.IdentExpr v),
                                      _,
                                      _,
                                      _) when v.Name = idxName -> true
                    | Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 k, _), _) when k >= 0 -> true
                    | _ -> false
            | Fable.WhileLoop(g, b, _) -> checkMonotonicStep idxName true g && checkMonotonicStep idxName true b
            | Fable.ForLoop(_, s, l, b, _, _) ->
                checkMonotonicStep idxName true s
                && checkMonotonicStep idxName true l
                && checkMonotonicStep idxName true b
            | Fable.Set(Fable.IdentExpr id, Fable.ValueSet, _, rhs, _) ->
                id.Name <> idxName && checkMonotonicStep idxName inNestedLoop rhs
            | _ -> getSubExpressions e |> List.forall (checkMonotonicStep idxName inNestedLoop)

        let mono =
            match guard with
            | Fable.Operation(Fable.Binary(BinaryLess, Fable.IdentExpr idx, len), _, _, _) when
                (match idx.Type with
                 | Fable.Number(Int32, _) -> true
                 | _ -> false)
                && (ctx.NonNeg.Contains idx.Name || ctx.Positive.Contains idx.Name)
                && not (usedInFunction idx.Name body)
                && not (hasAddressOfIdent idx.Name body)
                && checkMonotonicStep idx.Name false body
                ->
                match tryLengthTarget ctx len with
                | Some(cName, cTy) -> Some(idx, cName, cTy)
                | None -> None
            | _ -> None

        let mutated = mutatedIdentsIn body

        for m in mutated do
            let keepNonNeg =
                match mono with
                | Some(idx, _, _) -> m = idx.Name
                | None -> false

            if keepNonNeg then
                ctx.Positive.Remove m |> ignore
                ctx.BoundedBelowMax.Remove m |> ignore
                ctx.ConstLen.Remove m |> ignore
                ctx.Lengths.Remove m |> ignore
                ctx.KnownTypes.Remove m |> ignore

                ctx.InBounds.RemoveWhere(fun k ->
                    k.StartsWith(m + "|", System.StringComparison.Ordinal)
                    || k.EndsWith("|" + m, System.StringComparison.Ordinal)
                )
                |> ignore
            else
                clearIdentFacts ctx m

        let c = lw ctx guard

        let bIr =
            match mono with
            | Some(idx, cName, cTy) ->
                let nonNull =
                    if unwrapNullness cTy = Fable.String then
                        [ cName ]
                    else
                        []

                let ir =
                    withFacts
                        ctx.NonNull
                        nonNull
                        (fun () ->
                            withFacts
                                ctx.BoundedBelowMax
                                [ idx.Name ]
                                (fun () ->
                                    withFacts ctx.InBounds [ cName + "|" + idx.Name ] (fun () -> lwStmt ctx body)
                                )
                        )

                ctx.Positive.Remove idx.Name |> ignore
                ctx.BoundedBelowMax.Remove idx.Name |> ignore

                ctx.InBounds.RemoveWhere(fun k ->
                    k.StartsWith(idx.Name + "|", System.StringComparison.Ordinal)
                    || k.EndsWith("|" + idx.Name, System.StringComparison.Ordinal)
                )
                |> ignore

                ir
            | None -> lwStmt ctx body

        if isFlat c then
            EWhile(c, bIr)
        else
            // (a condition with control flow in it, like `a && b`, is tested inside the loop)
            let go = ctx.State.NewVar("go", tBool, VLocal, true)
            let stop = EAssign(go, ELit("false", tBool))
            let step = bindArgs ctx [ c ] (fun xs -> EIf(xs.Head, bIr, stop, tVoid))
            ELet(go, ELit("true", tBool), EWhile(EVar go, step))

    | Fable.ForLoop(id, start, limit, body, isUp, _) ->
        let startNonNeg = isKnownNonNegExpr ctx start
        let startIr = lw ctx start
        let limitIr = lw ctx limit
        let iv = ctx.State.NewVar(id.Name, mapType ctx id.Range id.Type, VLocal, false)

        // (`for i in 0 .. c.Length - 1`, `let n = c.Length` aliases, and constant-length bounds)
        let coveredLen =
            match limit with
            | Fable.Operation(Fable.Binary(BinaryMinus,
                                           len,
                                           Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 1, _), _)),
                              _,
                              _,
                              _) when isUp && not id.IsMutable && startNonNeg -> tryLengthTarget ctx len
            | _ -> None

        let coveredConstHi =
            match limit with
            | Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 hi, _), _) when
                isUp && not id.IsMutable && startNonNeg
                ->
                Some hi
            | _ -> None

        let bodyIr =
            withScopedIdent
                ctx
                id
                (fun () ->
                    ctx.Vars[id.Name] <- iv

                    if isUp && not id.IsMutable && startNonNeg then
                        ctx.NonNeg.Add id.Name |> ignore

                    match coveredLen with
                    | Some(cName, cTy) ->
                        ctx.InBounds.Add(cName + "|" + id.Name) |> ignore
                        ctx.BoundedBelowMax.Add id.Name |> ignore

                        if unwrapNullness cTy = Fable.String then
                            withKnown ctx [ cName ] [] (fun () -> lwStmt ctx body)
                        else
                            lwStmt ctx body
                    | None ->
                        match coveredConstHi with
                        | Some hi ->
                            if hi < System.Int32.MaxValue then
                                ctx.BoundedBelowMax.Add id.Name |> ignore

                            for kv in ctx.ConstLen do
                                if hi < kv.Value then
                                    ctx.InBounds.Add(kv.Key + "|" + id.Name) |> ignore
                        | None -> ()

                        lwStmt ctx body
                )

        // (the start is evaluated before the bound, as .NET does: the loop computes the bound
        // first, so a start with effects is bound before it)
        if isFlat startIr && not (isPure startIr) && not (isPure limitIr) then
            let sv = ctx.State.NewVar("start", typeOf startIr, VLocal, false)
            ELet(sv, startIr, bindArgs ctx [ limitIr ] (fun xs -> EFor(iv, EVar sv, xs[0], isUp, bodyIr)))
        else
            bindArgs ctx [ startIr; limitIr ] (fun xs -> EFor(iv, xs[0], xs[1], isUp, bodyIr))

    // (`box e.InnerException`: null when there is none)
    | Fable.TypeCast(Fable.Call(Fable.Import(imp, _, _), info, _, _), Fable.Any) when
        imp.Selector = "get_InnerException" && info.ThisArg.IsSome
        ->
        ctx.State.UsesRuntime <- true
        bindArgs ctx [ lw ctx info.ThisArg.Value ] (fun xs -> EEmit("fable_rt.exnInnerBoxed($0)", xs, tAny))
    // `x :> obj` and `box x`: an object holds it
    | Fable.TypeCast(x, t) when unwrapNullness t = Fable.Any && unwrapNullness x.Type <> Fable.Any ->
        match x with
        | Fable.Call(Fable.Import(imp, ct, cr), info, _, r) when
            imp.Selector = "DefaultOf" && not (hasDefault ctx x.Type)
            ->
            let nt = Fable.Nullable(x.Type, false)
            boxed ctx (Fable.Call(Fable.Import(imp, ct, cr), { info with GenericArgs = [ nt ] }, nt, r))
        | _ -> boxed ctx x
    // `o :?> T` of an `obj`
    | Fable.TypeCast(x, t) when unwrapNullness x.Type = Fable.Any && unwrapNullness t <> Fable.Any ->
        unboxed ctx e.Range x t
    | Fable.TypeCast(x, t) when
        isInterfaceType ctx.Com x.Type
        && isFatIfaceTy (mapType ctx e.Range x.Type)
        && unwrapNullness t <> Fable.Any
        && unwrapNullness x.Type <> unwrapNullness t
        ->
        ifaceDowncast ctx e.Range x t
    | Fable.TypeCast(Fable.IfThenElse(guard, thenExpr, elseExpr, r), (Fable.Nullable(_, false) as t)) ->
        let ty = mapType ctx r t

        bindArgs
            ctx
            [ lw ctx guard ]
            (fun xs ->
                EIf(
                    xs.Head,
                    coerceTy ctx ty (lw ctx (wrapNullCast t thenExpr)),
                    coerceTy ctx ty (lw ctx (wrapNullCast t elseExpr)),
                    ty
                )
            )
    | Fable.TypeCast(Fable.DecisionTree(expr, targets), (Fable.Nullable(_, false) as t)) ->
        let targets = targets |> List.map (fun (ids, body) -> ids, wrapNullCast t body)

        match sharedTargets targets expr with
        | [], _ -> coerceTy ctx (mapType ctx e.Range t) (lw { ctx with DecisionTargets = targets } expr)
        | fns, small ->
            coerceTy
                ctx
                (mapType ctx e.Range t)
                (lw
                    ctx
                    (List.foldBack
                        (fun (fnId, fn) rest -> Fable.Let(fnId, fn, rest))
                        fns
                        (Fable.DecisionTree(expr, small))))
    | Fable.TypeCast(x, t) ->
        let ir = lw ctx (wrapNullCast t x)
        let targetTy = mapType ctx e.Range t

        match typeOf ir, targetTy with
        | a, b when a = b -> ir
        // (an object known not to be null as an object of a class, which may be)
        | a, TOpt b when a = tObj && b = tObj -> ir
        | _, _ ->
            let coerced = coerceTy ctx targetTy ir

            if typeOf coerced = targetTy then
                coerced
            else
                fail e.Range "the Zig target does not support %s yet" (exprKind e)

    // Pattern matching arrives as a decision tree whose leaves name a target and the values
    // its variables are bound to. A target reached from several leaves is lowered once per leaf.
    | Fable.DecisionTree(expr, targets) ->
        let merged =
            match e.Type with
            | Fable.Nullable(_, false) -> e.Type
            | _ ->
                targets
                |> List.tryPick (fun (_, b) ->
                    match b.Type with
                    | Fable.Nullable(_, false) as n when unwrapNullness n = unwrapNullness e.Type -> Some n
                    | _ -> None
                )
                |> Option.defaultValue e.Type

        let targets =
            match merged with
            | Fable.Nullable(_, false) -> targets |> List.map (fun (ids, body) -> ids, wrapNullCast merged body)
            | _ -> targets

        match sharedTargets targets expr with
        | [], _ -> lw { ctx with DecisionTargets = targets } expr
        | fns, small ->
            // (the functions are declared before the tree: a target sees only what is outside it
            // and what its leaf binds)
            lw
                ctx
                (List.foldBack (fun (fnId, fn) rest -> Fable.Let(fnId, fn, rest)) fns (Fable.DecisionTree(expr, small)))

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
            | Some given when given.Length = c.TypeParams.Length -> given |> List.map (mapTypeArg ctx r)
            | _ ->
                let found = Dictionary<string, Fable.Type>()

                for (declared, actual) in
                    List.zip (List.truncate argTypes.Length c.ArgTypes) (List.truncate c.Arity argTypes) do
                    unify found declared actual

                resultType |> Option.iter (unify found c.Ret)

                c.TypeParams
                |> List.map (fun name ->
                    match found.TryGetValue name with
                    | true, t -> mapTypeArg ctx r t
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

/// What a `MatchFailureException` holds: the file, line and column of the match, as .NET has
/// them.
and matchLocation (ctx: Ctx) (r: SourceLocation option) : Expr list =
    let file, line, column =
        match r with
        | Some r ->
            let file =
                match r.identifierName with
                | Some n when n.Contains ";file:" -> n.Substring(n.IndexOf ";file:" + 6)
                | _ -> ctx.Com.CurrentFile

            file, r.start.line, r.start.column
        | None -> ctx.Com.CurrentFile, 0, 0

    [
        ELit(stringLiteral file, tStr)
        ELit(string line, tI32)
        ELit(string column, tI32)
    ]

/// Raise a .NET exception of the given class with the given message.
and raiseDotnet (ctx: Ctx) (r: SourceLocation option) (fullName: string) (message: Expr) (t: Fable.Type) : Expr =
    bindArgsIn true ctx [ message ] (fun xs -> ERaise(EExnNew(dotnetExnEnt ctx fullName, xs), mapType ctx r t))

/// Raise an ArgumentException (or one of its classes) about the parameter `parameter`: its message
/// names it, and so does its `ParamName`
and raiseArgument
    (ctx: Ctx)
    (r: SourceLocation option)
    (fullName: string)
    (message: Expr)
    (parameter: Fable.Expr)
    (t: Fable.Type)
    : Expr
    =
    bindArgsIn
        true
        ctx
        [ withParameter ctx message parameter; lw ctx parameter ]
        (fun xs ->
            withParamName
                ctx
                (EExnNew(dotnetExnEnt ctx fullName, [ xs.Head ]))
                xs.[1]
                (fun e -> ERaise(e, mapType ctx r t))
        )

/// The exception `made` with its `ParamName` (bound first: what is bound is given up after)
and withParamName (ctx: Ctx) (made: Expr) (name: Expr) (k: Expr -> Expr) : Expr =
    bindArgs ctx [ made; name ] (fun ys -> k (EEmit("fable_rt.exnWithParam($0, $1)", ys, tExn)))

/// "message (Parameter 'name')", as .NET puts the name of a parameter into a message
and withParameter (ctx: Ctx) (message: Expr) (parameter: Fable.Expr) : Expr =
    bindArgs
        ctx
        [ message; lw ctx parameter ]
        (fun xs -> EEmit("fable_rt.format(.{ $0, \" (Parameter '\", $1, \"')\" })", xs, tStr))

/// The function that is the `ToString` a record or a union declares for itself, if it does.
and ownToString (ctx: Ctx) (t: Fable.Type) : string option =
    match unwrapNullness t with
    | Fable.DeclaredType(entRef, _) ->
        match ctx.Com.TryGetEntity entRef with
        | Some ent when
            // (a record, a union, or a class that is not an object of a hierarchy: a struct, say;
            // an object's `ToString` is found through its class)
            (ent.IsFSharpRecord
             || ent.IsFSharpUnion
             || (not ent.IsInterface && (objInfo ctx None entRef).IsNone))
            && ent.MembersFunctionsAndValues
               |> Seq.exists (fun m -> m.CompiledName = "ToString" && m.IsOverrideOrExplicitInterfaceImplementation)
            ->
            match FSharp2Fable.Util.entityIdent ctx.Com entRef with
            | Fable.IdentExpr id -> Some(id.Name + "__ToString")
            | Fable.Import(imp, _, _) -> Some(importAlias ctx imp.Path + "." + imp.Selector + "__ToString")
            | _ -> None
        | _ -> None
    | _ -> None

/// `box x`: `x` in an object (an object of a class is one already). It borrows `x`.
and boxed (ctx: Ctx) (x: Fable.Expr) : Expr =
    ctx.State.UsesRuntime <- true
    let ir = lw ctx x

    match ir with
    // (a literal is given its type first: Zig's literals have none)
    | ELit(_, ty) ->
        let v = ctx.State.NewVar("boxed", ty, VLocal, false)
        ELet(v, ir, EEmit("fable_rt.box($0)", [ EVar v ], tAny))
    | _ -> bindArgs ctx [ ir ] (fun xs -> EEmit("fable_rt.box($0)", xs, tAny))

/// `unbox<T> o` and `o :?> T`: what the object holds, or InvalidCastException
and unboxed (ctx: Ctx) (r: SourceLocation option) (x: Fable.Expr) (t: Fable.Type) : Expr =
    ctx.State.UsesRuntime <- true

    match unwrapNullness t with
    | Fable.DeclaredType(cls, gs) when (objInfo ctx r cls).IsSome ->
        let o = (objInfo ctx r cls).Value
        let typeRef = objTypeRef o (gs |> List.map (mapTypeArg ctx r))
        bindArgs ctx [ lw ctx x ] (fun xs -> ERt($"fable_rt.anyToClass($0, %s{typeRef})", xs, tAny))
    // (an interface F# declares has no null, unless `[<AllowNullLiteral>]` or `I | null` says so:
    // null raises NullReferenceException, as F#'s UnboxGeneric does)
    | Fable.DeclaredType(i, _) when
        (match t with
         | Fable.Nullable _ -> false
         | _ -> true)
        && (
            match (i: Fable.EntityRef).Path with
            | Fable.SourcePath _
            | Fable.PrecompiledLib _ -> true
            | _ -> false
        )
        && (
            match ctx.Com.TryGetEntity i with
            | Some ent ->
                ent.IsInterface
                && not (
                    ent.Attributes
                    |> Seq.exists (fun a -> a.Entity.FullName = "Microsoft.FSharp.Core.AllowNullLiteralAttribute")
                )
            | None -> false
        )
        ->
        bindArgs ctx [ lw ctx x ] (fun xs -> ERt("fable_rt.unboxNonNull($R, $0)", xs, mapType ctx r t))
    | _ -> bindArgs ctx [ lw ctx x ] (fun xs -> ERt("fable_rt.unbox($R, $0)", xs, mapType ctx r t))

/// `x :? T` where `x` is a fat-pointer interface.
and ifaceTypeTest (ctx: Ctx) (r: SourceLocation option) (x: Fable.Expr) (t: Fable.Type) : Expr =
    ctx.State.UsesRuntime <- true

    match unwrapNullness t with
    | Fable.DeclaredType(cls, []) when cls.FullName = "System.Array" ->
        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.isArray(fable_rt.ifaceToAnyBorrow($0))", xs, tBool))
    | Fable.DeclaredType(cls, gs) when (objInfo ctx r cls).IsSome ->
        let o = (objInfo ctx r cls).Value
        let typeRef = objTypeRef o (gs |> List.map (mapTypeArg ctx r))
        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.ifaceIsClass($0, %s{typeRef})", xs, tBool))
    | _ ->
        let ty = mapType ctx r t
        let found = ctx.State.NewVar("unboxed", TOpt ty, VLocal, false)

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                ELet(
                    found,
                    EEmit("fable_rt.ifaceTryUnbox($R, $0)", xs, TOpt ty),
                    EPrim("not", [ ETest(EVar found, "None", found.Ty) ], tBool)
                )
            )

/// `x :?> T` and `unbox<T> x` where `x` is a fat-pointer interface.
and ifaceDowncast (ctx: Ctx) (r: SourceLocation option) (x: Fable.Expr) (t: Fable.Type) : Expr =
    ctx.State.UsesRuntime <- true

    match unwrapNullness t with
    | Fable.DeclaredType(cls, gs) when (objInfo ctx r cls).IsSome ->
        let o = (objInfo ctx r cls).Value
        let typeRef = objTypeRef o (gs |> List.map (mapTypeArg ctx r))
        bindArgs ctx [ lw ctx x ] (fun xs -> ERt($"fable_rt.ifaceCastClass($0, %s{typeRef})", xs, tAny))
    | _ -> bindArgs ctx [ lw ctx x ] (fun xs -> ERt("fable_rt.ifaceUnbox($R, $0)", xs, mapType ctx r t))

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

/// Can `%A` write a value of this type as F# does? `option` and `voption` are one type in Zig,
/// a struct tuple is a tuple, and a function
/// value has no name here: a type that mentions one of them is refused, so that what is
/// written is never different from .NET's.
and showShapeOf (ctx: Ctx) (r: SourceLocation option) (strict: bool) (root: Fable.Type) : string option =
    let substFor (ent: Fable.Entity) (genArgs: Fable.Type list) =
        if ent.GenericParameters.Length = genArgs.Length && not genArgs.IsEmpty then
            List.zip (ent.GenericParameters |> List.map (fun g -> g.Name)) genArgs
            |> Map.ofList
        else
            Map.empty

    let rec typeKey (t: Fable.Type) : string =
        match t with
        | Fable.Number(k, _) -> $"N(%A{k})"
        | Fable.Boolean -> "B"
        | Fable.Char -> "C"
        | Fable.String -> "S"
        | Fable.Unit -> "U"
        | Fable.GenericParam(n, _, _) -> $"'%s{n}"
        | Fable.Option(i, s) ->
            (if s then
                 "VO("
             else
                 "O(")
            + typeKey i
            + ")"
        | Fable.Array(i, k) -> $"A(%A{k}," + typeKey i + ")"
        | Fable.List i -> "L(" + typeKey i + ")"
        | Fable.Tuple(ts, s) ->
            (if s then
                 "ST("
             else
                 "T(")
            + (ts |> List.map typeKey |> String.concat ",")
            + ")"
        | Fable.AnonymousRecordType(ns, gs, _) ->
            "AR("
            + (ns |> String.concat ";")
            + "|"
            + (gs |> List.map typeKey |> String.concat ",")
            + ")"
        | Fable.LambdaType _
        | Fable.DelegateType _ -> "FN"
        | Fable.DeclaredType(ent, gs) -> ent.FullName + "<" + (gs |> List.map typeKey |> String.concat ",") + ">"
        | _ -> "X"

    let checkedSeen = HashSet<string>()

    let rec check (t: Fable.Type) =
        match t with
        | Fable.Number _
        | Fable.Boolean
        | Fable.Char
        | Fable.String
        | Fable.Unit
        | Fable.GenericParam _
        | Fable.LambdaType _
        | Fable.DelegateType _ -> ()
        | Fable.Option(inner, _)
        | Fable.Nullable(inner, _)
        | Fable.Array(inner, _)
        | Fable.List inner -> check inner
        | Fable.Tuple(ts, _) -> List.iter check ts
        | Fable.AnonymousRecordType(_, genArgs, _) -> List.iter check genArgs
        | Fable.DeclaredType(ent, [ inner ]) when ent.FullName = "System.Collections.Generic.IEnumerable`1" ->
            check inner
        | Fable.DeclaredType(ent, [ inner ]) when ent.FullName = "System.Lazy`1" -> check inner
        | Fable.DeclaredType(entRef, genArgs) ->
            List.iter check genArgs
            let key = typeKey t

            if
                not (dotnetExceptions.ContainsKey entRef.FullName)
                && entRef.FullName <> mapName
                && entRef.FullName <> setName
                && not (isDictionaryName entRef.FullName)
                && entRef.FullName <> "System.Collections.Generic.HashSet`1"
                // (a `Uri`, a `Guid`, a date... is written by its `ToString`)
                && not (libraryValueTypes.ContainsKey entRef.FullName)
                && checkedSeen.Add key
            then
                match ctx.Com.TryGetEntity entRef with
                | Some ent when ent.IsFSharpUnion ->
                    let sub = substFor ent genArgs

                    for case in ent.UnionCases do
                        for field in case.UnionCaseFields do
                            check (substFableType sub field.FieldType)
                | Some ent when ent.IsFSharpRecord || ent.IsFSharpExceptionDeclaration ->
                    let sub = substFor ent genArgs

                    for field in (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic)) do
                        check (substFableType sub field.FieldType)
                | _ when strict ->
                    fail r "the Zig target cannot write a value of the type %s with %%A yet" entRef.FullName
                | _ -> ()
        | other when strict -> fail r "the Zig target cannot write a value of this type with %%A yet (%A)" other
        | _ -> ()

    check root

    // (`needsShape` computes reachability of voption / struct tuple / uint16, keeping
    // shapes empty when comptime defaults already match .NET)
    let needsShape (start: Fable.Type) : bool =
        let visited = HashSet<string>()

        let rec go (t: Fable.Type) =
            match t with
            | Fable.Option(_, true)
            | Fable.Tuple(_, true)
            | Fable.Number(UInt16, _) -> true
            | Fable.Option(inner, false)
            | Fable.Nullable(inner, false)
            | Fable.Array(inner, _)
            | Fable.List inner -> go inner
            | Fable.Tuple(ts, false) -> List.exists go ts
            | Fable.AnonymousRecordType(_, genArgs, _) -> List.exists go genArgs
            | Fable.DeclaredType(ent, [ inner ]) when
                ent.FullName = "System.Collections.Generic.IEnumerable`1"
                || ent.FullName = "System.Lazy`1"
                || ent.FullName = setName
                || ent.FullName = "System.Collections.Generic.HashSet`1"
                ->
                go inner
            | Fable.DeclaredType(ent, [ k; v ]) when ent.FullName = mapName || isDictionaryName ent.FullName ->
                go k || go v
            | Fable.DeclaredType(entRef, genArgs) when not (dotnetExceptions.ContainsKey entRef.FullName) ->
                if List.exists go genArgs then
                    true
                else
                    let key = typeKey t

                    if not (visited.Add key) then
                        false
                    else
                        match ctx.Com.TryGetEntity entRef with
                        | Some ent when ent.IsFSharpUnion ->
                            let sub = substFor ent genArgs

                            ent.UnionCases
                            |> List.exists (fun c ->
                                c.UnionCaseFields |> List.exists (fun f -> go (substFableType sub f.FieldType))
                            )
                        | Some ent when ent.IsFSharpRecord || ent.IsFSharpExceptionDeclaration ->
                            let sub = substFor ent genArgs

                            ent.FSharpFields
                            |> List.filter (fun f -> not f.IsStatic)
                            |> List.exists (fun f -> go (substFableType sub f.FieldType))
                        | _ -> false
            | _ -> false

        go start

    if not (needsShape root) then
        None
    else
        let autoIdx = 0xFFFFus
        let nodes = ResizeArray<string>()
        let refs = ResizeArray<uint16>()
        let memo = Dictionary<string, uint16>()

        let addNode s =
            let idx = uint16 nodes.Count
            nodes.Add s
            idx

        let addRefs (rs: uint16 list) =
            let start = uint16 refs.Count
            refs.AddRange rs
            start

        let rec build (t: Fable.Type) : uint16 =
            if not (needsShape t) then
                autoIdx
            else
                match t with
                | Fable.Number(UInt16, _) -> addNode ".{ .kind = .u16_num }"
                | Fable.Option(inner, isStruct) ->
                    let idx = addNode ""
                    let child = build inner

                    let kind =
                        if isStruct then
                            ".vopt"
                        else
                            ".opt"

                    nodes[int idx] <- $".{{ .kind = %s{kind}, .a = %d{child} }}"
                    idx
                | Fable.Tuple(ts, isStruct) ->
                    let idx = addNode ""
                    let rs = ts |> List.map build
                    let start = addRefs rs

                    let kind =
                        if isStruct then
                            ".struct_tuple"
                        else
                            ".tuple"

                    nodes[int idx] <- $".{{ .kind = %s{kind}, .a = %d{start}, .b = %d{rs.Length} }}"
                    idx
                | Fable.Array(inner, _)
                | Fable.List inner ->
                    let idx = addNode ""
                    let child = build inner
                    nodes[int idx] <- $".{{ .kind = .seq, .a = %d{child} }}"
                    idx
                | Fable.AnonymousRecordType(_, genArgs, _) ->
                    let idx = addNode ""
                    let rs = genArgs |> List.map build
                    let start = addRefs rs
                    nodes[int idx] <- $".{{ .kind = .record, .a = %d{start}, .b = %d{rs.Length} }}"
                    idx
                | Fable.DeclaredType(ent, [ inner ]) when
                    ent.FullName = "System.Collections.Generic.IEnumerable`1"
                    || ent.FullName = "System.Lazy`1"
                    || ent.FullName = setName
                    || ent.FullName = "System.Collections.Generic.HashSet`1"
                    ->
                    let idx = addNode ""
                    let child = build inner
                    nodes[int idx] <- $".{{ .kind = .seq, .a = %d{child} }}"
                    idx
                | Fable.DeclaredType(ent, [ k; v ]) when ent.FullName = mapName || isDictionaryName ent.FullName ->
                    let idx = addNode ""
                    let kIdx = build k
                    let vIdx = build v
                    nodes[int idx] <- $".{{ .kind = .map, .a = %d{kIdx}, .b = %d{vIdx} }}"
                    idx
                | Fable.DeclaredType(entRef, genArgs) ->
                    let key = typeKey t

                    match memo.TryGetValue key with
                    | true, existing -> existing
                    | _ ->
                        match ctx.Com.TryGetEntity entRef with
                        | Some ent when ent.IsFSharpUnion ->
                            let sub = substFor ent genArgs
                            let idx = addNode ""
                            memo[key] <- idx

                            let caseRefs =
                                ent.UnionCases
                                |> List.map (fun c ->
                                    let fieldRefs =
                                        c.UnionCaseFields |> List.map (fun f -> build (substFableType sub f.FieldType))

                                    if List.forall ((=) autoIdx) fieldRefs then
                                        autoIdx
                                    else
                                        let start = addRefs fieldRefs
                                        addNode $".{{ .kind = .record, .a = %d{start}, .b = %d{fieldRefs.Length} }}"
                                )

                            let start = addRefs caseRefs
                            nodes[int idx] <- $".{{ .kind = .@\"union\", .a = %d{start}, .b = %d{caseRefs.Length} }}"
                            idx
                        | Some ent when ent.IsFSharpRecord || ent.IsFSharpExceptionDeclaration ->
                            let sub = substFor ent genArgs
                            let idx = addNode ""
                            memo[key] <- idx

                            let fieldRefs =
                                ent.FSharpFields
                                |> List.filter (fun f -> not f.IsStatic)
                                |> List.map (fun f -> build (substFableType sub f.FieldType))

                            let start = addRefs fieldRefs
                            nodes[int idx] <- $".{{ .kind = .record, .a = %d{start}, .b = %d{fieldRefs.Length} }}"
                            idx
                        | _ -> autoIdx
                | _ -> autoIdx

        ignore (build root)
        let nodesLit = nodes |> String.concat ", "

        if refs.Count = 0 then
            Some $".{{ .nodes = &.{{ %s{nodesLit} }} }}"
        else
            let refsLit =
                refs
                |> Seq.map (fun i ->
                    if i = autoIdx then
                        "0xFFFF"
                    else
                        $"%d{i}"
                )
                |> String.concat ", "

            Some $".{{ .nodes = &.{{ %s{nodesLit} }}, .refs = &.{{ %s{refsLit} }} }}"

/// Check that a value of type `t` can be written with `%A`.
and checkShowable (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : unit = ignore (showShapeOf ctx r true t)

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
    let values = args |> List.map readByref |> Array.ofList

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

                // (`{x}` and `%O` of a value whose type has a `ToString` of its own, or of an
                // option, a tuple, a list, a map or a set: .NET's ToString)
                let netToString =
                    match args[i].Type with
                    | Fable.Option _
                    | Fable.Tuple _
                    | Fable.List _ -> true
                    | Fable.DeclaredType(ent, _) ->
                        ent.FullName = mapName
                        || ent.FullName = setName
                        || ent.FullName = "System.Text.StringBuilder"
                    | _ -> false

                // (a `Uri`: its `ToString` also for `%A`, as F# writes a class)
                let uriText =
                    (letter = 'A' || letter = 'P' || letter = 'O')
                    && (
                        match args[i].Type with
                        | Fable.DeclaredType(ent, []) -> libraryValueTypes.ContainsKey ent.FullName
                        | _ -> false
                    )

                if
                    uriText
                    || (letter = 'P' || letter = 'O')
                       && ((ownToString ctx args[i].Type).IsSome || netToString)
                then
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
                        checkNetFormat r net

                        if isStandardNetFormat net && "DdXxBb".IndexOf(net[0]) >= 0 && not isWhole then
                            fail r "the .NET format `%s` is for whole numbers" net

                        zigEscape net
                    | Fable.String
                    | Fable.Char
                    | Fable.Boolean -> ""
                    | _ when net = "" -> ""
                    | other ->
                        fail r "the Zig target does not support a .NET format for this type of value yet (%A)" other

                // what the specifier means for the type of its value
                let kind =
                    match letter, value.Type with
                    | _ when uriText -> 's'
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
                    | ('f' | 'F' | 'e' | 'E' | 'g' | 'G'), Fable.Number((Float32 | Float64 | Decimal), _) -> letter
                    | 'M', Fable.Number(Decimal, _) -> 'M'
                    // (a value whose type is a type parameter: its `ToString`, known when the
                    // Zig is compiled)
                    | ('P' | 'O' | 's'), Fable.GenericParam _ -> 'T'
                    | 'A', _ -> 'A'
                    | _, (Fable.String | Fable.Char | Fable.Boolean | Fable.Number _) ->
                        fail r "the Zig target does not support the format %%%c for this type of value yet" letter
                    | _, other -> fail r "the Zig target cannot turn a value of this type into text yet (%A)" other

                if kind = 'A' then
                    // (F# ignores a width, flags and a precision on %A)
                    match showShapeOf ctx r true value.Type with
                    | Some shape -> $"fable_rt.arg(.{{ .kind = 'A', .shape = %s{shape} }}, %s{typedArg ctx r value i})"
                    | None -> $"fable_rt.arg(.{{ .kind = 'A' }}, %s{typedArg ctx r value i})"
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

/// `String.Format("{0} {1:N2}", a, b)`: the format is taken apart here, as an interpolated
/// string's is: `{i,width:format}` becomes `%widthP(format)` of the value i.
and compositeFormat
    (ctx: Ctx)
    (r: SourceLocation option)
    (fmt: string)
    (values: Fable.Expr list)
    (t: Fable.Type)
    : Expr
    =
    // (`String.Format(fmt, [| a; b |])`, or the values one by one)
    let values =
        match values with
        | [ Fable.Value(Fable.NewArray(Fable.ArrayValues vs, _, _), _) ] -> vs
        | _ -> values
        |> List.map (fun v ->
            match v with
            | Uncast inner -> inner
        )

    // each value is evaluated once, in order, whatever the format uses
    let temps =
        values
        |> List.mapi (fun i v ->
            let name = $"format_arg_%d{i}_%d{ctx.State.Vars.Count}"
            let var = ctx.State.NewVar(name, mapType ctx r v.Type, VLocal, false)

            let ident: Fable.Ident =
                {
                    Name = name
                    Type = v.Type
                    IsMutable = false
                    IsThisArgument = false
                    IsCompilerGenerated = true
                    Range = None
                    IsInlineIfLambda = false
                }

            ctx.Vars[name] <- var
            var, lw ctx v, ident
        )

    let text = System.Text.StringBuilder()
    let holes = List<Fable.Expr>()
    let mutable bad = false
    let mutable i = 0

    while i < fmt.Length do
        let c = fmt[i]

        if c = '{' && i + 1 < fmt.Length && fmt[i + 1] = '{' then
            text.Append('{') |> ignore
            i <- i + 2
        elif c = '}' && i + 1 < fmt.Length && fmt[i + 1] = '}' then
            text.Append('}') |> ignore
            i <- i + 2
        elif c = '{' then
            let close = fmt.IndexOf('}', i)

            if close < 0 then
                fail r "the format of String.Format is not well formed"

            let item = fmt.Substring(i + 1, close - i - 1)

            let head, format =
                match item.IndexOf ':' with
                | -1 -> item, ""
                | k -> item.Substring(0, k), item.Substring(k + 1)

            let index, width =
                match head.IndexOf ',' with
                | -1 -> int (head.Trim()), 0
                | k -> int (head.Substring(0, k).Trim()), int (head.Substring(k + 1).Trim())

            if index >= temps.Length then
                bad <- true
            else
                let _, _, ident = temps[index]
                holes.Add(Fable.IdentExpr ident)

                let flags =
                    if width < 0 then
                        "-"
                    else
                        ""

                let widthText =
                    if width <> 0 then
                        string (abs width)
                    else
                        ""

                text.Append($"%%%s{flags}%s{widthText}P(%s{format})") |> ignore

            i <- close + 1
        elif c = '%' then
            text.Append("%%") |> ignore
            i <- i + 1
        else
            text.Append(c) |> ignore
            i <- i + 1

    let body =
        if bad then
            let message =
                ELit(
                    stringLiteral
                        "Index (zero based) must be greater than or equal to zero and less than the size of the argument list.",
                    tStr
                )

            raiseDotnet ctx r "System.FormatException" message t
        else
            formatted ctx r "PrintFormatToString" (text.ToString()) (List.ofSeq holes) t

    List.foldBack (fun (var, ir, _) acc -> ELet(var, ir, acc)) temps body

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
        // (the Zig type of what the value returns, when Fable's type of it does not say)
        let take, ret, valueRet =
            match fTy, typeOf f with
            | Fable.LambdaType(_, Fable.LambdaType(_, ret2)), TFn([ _ ], TFn([ _ ], _)) when args.Length >= 2 ->
                2, ret2, None
            | Fable.LambdaType(_, ret), _ -> 1, ret, None
            | Fable.DelegateType(ts, ret), _ -> ts.Length, ret, None
            | _, other ->
                // (Fable does not always say what type an item of an array has: the value does,
                // a curried one taking its arguments in several steps)
                match other with
                | TFn(ps, _) when ps.Length = args.Length -> ps.Length, finalTy, None
                | TFn(ps, valueRet) when ps.Length < args.Length -> ps.Length, fTy, Some valueRet
                | other -> fail r "the Zig target cannot apply a value of this type (%A, %A)" fTy other

        if args.Length < take then
            fail r "the Zig target does not support applying a function to some of its arguments here yet"

        let now, rest = List.splitAt take args

        let resultTy =
            match rest.IsEmpty, valueRet with
            | true, _ -> mapType ctx r finalTy
            | false, Some t -> t
            | false, None -> substTy subst (mapType ctx r ret)

        let call =
            bindArgs ctx (f :: (now |> List.map (lw ctx))) (fun xs -> ECallClo(xs.Head, xs.Tail, resultTy))

        applyValue ctx r subst call ret rest finalTy

/// A function that is called by name, used as a value of type `valueTy`.
/// `Seq.ofGetEnumerator (fun () -> getEnumerator)`: a sequence that walks what an
/// `IEnumerable<'T>` of the program's gives
and lowerSeqOfGetEnumerator
    (ctx: Ctx)
    (r: SourceLocation option)
    (item: Fable.Type)
    (getEnumerator: Fable.Expr)
    : Expr
    =
    let unitArg = AST.makeTypedIdent Fable.Unit "unitVar"
    let itemTy = mapTypeArg ctx r item
    let seqTy = TEnt(seqEnt ctx, [ itemTy ])

    bindArgs
        ctx
        [ lw ctx (Fable.Delegate([ unitArg ], getEnumerator, None, [])) ]
        (fun xs -> ECall(libraryTarget ctx "Seq" "ofGetEnumerator", [ itemTy ], xs, seqTy))

and fnValue (ctx: Ctx) (r: SourceLocation option) (orig: Fable.Expr) (c: Callable) (valueTy: Fable.Type) : Expr =
    // (a function of several arguments given as a value is uncurried, as Fable passes it to
    // functions and keeps it in fields: `let sum a b = ...` given to `Seq.fold`)
    let valueTy =
        match valueTy with
        | Fable.LambdaType _ when c.Arity > 1 ->
            match FableTransforms.uncurryType valueTy with
            | Fable.DelegateType(ts, _) as uncurried when ts.Length = c.Arity -> uncurried
            | _ -> valueTy
        | _ -> valueTy

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
    // (a named function declared as `let f a b c = ...`, which F# gives as nested lambdas,
    // takes all its arguments at once, as a function of the module does: a call with all of
    // them is direct, and mutual tail calls between such functions can be fused)
    let rec curriedArgs (acc: Fable.Ident list) (e: Fable.Expr) =
        match e with
        | Fable.Lambda(arg, body, _) -> curriedArgs (arg :: acc) body
        | _ -> List.rev acc, e

    let parts =
        bindings
        |> List.map (fun (ident, hint, fnExpr) ->
            match fnExpr with
            | Fable.Lambda _ when ident.IsSome ->
                let args, body = curriedArgs [] fnExpr
                ident, hint, args, body
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
            let argTys =
                args
                |> List.map (fun a ->
                    // (the object a member is called on is not null: the call checks)
                    match mapType ctx a.Range a.Type with
                    | TOpt t when t = tObj && a.IsThisArgument -> tObj
                    | ty -> ty
                )

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
                NonNull = HashSet<string>(ctx.NonNull)
                Positive = HashSet<string>(ctx.Positive)
                NonNeg = HashSet<string>(ctx.NonNeg)
                BoundedBelowMax = HashSet<string>(ctx.BoundedBelowMax)
                Lengths = Dictionary<string, string * Fable.Type>(ctx.Lengths)
                ConstLen = Dictionary<string, int>(ctx.ConstLen)
                KnownTypes = Dictionary<string, Fable.Type>(ctx.KnownTypes)
                InBounds = HashSet<string>(ctx.InBounds)
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
                clearIdentFacts inner a.Name

                if a.IsThisArgument then
                    inner.NonNull.Add a.Name |> ignore

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
    let tF64 = TPrim "f64"

    // (the Zig name of a number type)
    let zigTypeName (ty: Ty) =
        match ty with
        | TPrim name -> name
        | _ -> fail r "internal: not a number type"

    // (an enum's value is not a number argument: `IndexOf(c, StringComparison.Ordinal)`)
    let isInt (x: Fable.Expr) =
        match x.Type with
        | Fable.Number(Int32, Fable.NumberInfo.IsEnum _) -> false
        | Fable.Number(Int32, _) -> true
        | _ -> false

    let tBig = TPrim "fable_rt.BigInt"
    let tDec = TPrim "fable_rt.NetDecimal"

    let isDec (x: Fable.Expr) =
        match x.Type with
        | Fable.Number(Decimal, _) -> true
        | _ -> false

    let decLit (m: string) (scale: int) =
        ctx.State.UsesRuntime <- true
        ELit($"fable_rt.decLit(%s{m}, %d{scale})", tDec)

    let isBig (x: Fable.Expr) =
        match x.Type with
        | Fable.Number(BigInt, _) -> true
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
    // (`xs.Head` and `xs.Tail` of an empty list raise, as on .NET)
    | "Microsoft.FSharp.Collections.FSharpList`1", ("get_Head" | "get_Tail"), x :: _ ->
        let field =
            if name = "get_Head" then
                "Head"
            else
                "Tail"

        let ty = mapType ctx r t

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let empty = ELit(stringLiteral "The input list was empty.", tStr)

                EIf(
                    ETest(xs.Head, "Empty", typeOf xs.Head),
                    raiseDotnet ctx r "System.InvalidOperationException" empty t,
                    EGet(xs.Head, PCase("Cons", field), ty),
                    ty
                )
            )
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
    // `box x :? int`: a test of what an `obj` holds
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "TypeTestGeneric", [ x ] when
        info.GenericArgs.Length = 1
        && (unwrapNullness x.Type = Fable.Any
            || (isInterfaceType ctx.Com x.Type && isFatIfaceTy (mapType ctx r x.Type))
            || isInterfaceType ctx.Com (unwrapNullness info.GenericArgs.Head))
        ->
        lw ctx (Fable.Test(x, Fable.TypeTest info.GenericArgs.Head, r))
    // `x :? T` where Fable keeps it a call: of an exception class, or of a class of objects
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "TypeTestGeneric", [ x ] when
        (match info.GenericArgs with
         | [ g ] ->
             match unwrapNullness g with
             | Fable.DeclaredType(cls, _) -> (tryExnEnt ctx r cls).IsSome || (objInfo ctx r cls).IsSome
             | _ -> false
         | _ -> false)
        ->
        match unwrapNullness info.GenericArgs.Head with
        | Fable.DeclaredType(cls, _) when (tryExnEnt ctx r cls).IsSome ->
            let ent = (tryExnEnt ctx r cls).Value
            bindArgs ctx [ lw ctx x ] (fun xs -> EExnTest(xs.Head, ent))
        | Fable.DeclaredType(cls, gs) ->
            let o = (objInfo ctx r cls).Value
            let typeRef = objTypeRef o (gs |> List.map (mapTypeArg ctx r))
            bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.objIs($0, %s{typeRef})", xs, tBool))
        | _ -> fail r "internal: a type test"
    // `x :?> Circle`: an object of that class, or InvalidCastException
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", ("UnboxFast" | "UnboxGeneric"), [ Uncast x ] when
        (objOfType ctx r t).IsSome && (objOfType ctx r x.Type).IsSome
        ->
        let o = (objOfType ctx r t).Value
        let source = (objOfType ctx r x.Type).Value

        if ancestors source |> List.exists (fun k -> k.FullName = o.FullName) then
            lw ctx x
        else
            rt $"fable_rt.objCast($0, %s{objTypeRef o (objArgs ctx r t)})" [ x ] tAny
    // (a cast that changes nothing here: an exception of a known class is an `exn`)
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", ("UnboxFast" | "UnboxGeneric"), [ x ] when
        mapType ctx r x.Type = mapType ctx r t
        && unwrapNullness x.Type <> Fable.Any
        && (not (isFatIfaceTy (mapType ctx r x.Type))
            || unwrapNullness x.Type = unwrapNullness t)
        ->
        lw ctx x
    // ---- ranges: `a .. b`, `a .. step .. b` ----
    | "Microsoft.FSharp.Core.Operators", ("op_Range" | "op_RangeStep"), _ ->
        let lo, step, hi =
            match args with
            | [ a; b ] -> a, None, b
            | [ a; s; b ] -> a, Some s, b
            | _ -> fail r "internal: a range"

        let one (lit: string) =
            match step with
            | Some s -> lw ctx s
            | None -> ELit(lit, mapType ctx r lo.Type)

        let fn, irs =
            match lo.Type with
            | Fable.Number(Int32, _) -> "rangeInt", [ lw ctx lo; one "1"; lw ctx hi ]
            | Fable.Number(Int64, _) -> "rangeInt64", [ lw ctx lo; one "1"; lw ctx hi ]
            | Fable.Number(UInt64, _) -> "rangeUInt64", [ lw ctx lo; one "1"; lw ctx hi ]
            | Fable.Number(Decimal, _) -> "rangeDecimal", [ lw ctx lo; one "fable_rt.decLit(1, 0)"; lw ctx hi ]
            | Fable.Number(BigInt, _) ->
                "rangeBigInt",
                [
                    lw ctx lo
                    (match step with
                     | Some s -> lw ctx s
                     | None -> EEmit("fable_rt.bigOf(@as(i32, 1))", [], mapType ctx r lo.Type))
                    lw ctx hi
                ]
            | Fable.Number(Float64, _) -> "rangeFloat", [ lw ctx lo; one "1.0"; lw ctx hi ]
            | Fable.Char when step.IsNone -> "rangeChar", [ lw ctx lo; lw ctx hi ]
            | other -> fail r "the Zig target does not support a range of this type yet (%A)" other

        bindArgs ctx irs (fun xs -> ECall(libraryTarget ctx "Seq" fn, [], xs, mapType ctx r t))
    | "Microsoft.FSharp.Collections.SeqModule", ("Sum" | "Average" | "SumBy" | "AverageBy"), _ ->
        let item =
            match t with
            | _ when name.EndsWith "By" -> t
            | _ -> t

        let seqArg = List.last args

        let listIr =
            match seqArg with
            | Fable.TypeCast(inner, _) when (listItem inner.Type).IsSome -> lw ctx inner
            | _ ->
                let itemTy =
                    match seqArg.Type with
                    | Fable.DeclaredType(_, [ i ]) -> mapType ctx r i
                    | _ -> mapType ctx r item

                bindArgs
                    ctx
                    [ lw ctx seqArg ]
                    (fun xs ->
                        ECall(libraryTarget ctx "Seq" "toList", [ itemTy ], xs, TEnt(listEnt ctx.State, [ itemTy ]))
                    )

        let ty = mapType ctx r t

        match name, args with
        | "Sum", [ _ ] when ty = TPrim "fable_rt.NetDecimal" ->
            bindArgs ctx [ listIr ] (fun xs -> ERt("fable_rt.listSumDec($0)", xs, ty))
        | "Sum", [ _ ] -> bindArgs ctx [ listIr ] (fun xs -> EEmit("fable_rt.listSum($0)", xs, ty))
        | "Average", [ _ ] -> bindArgs ctx [ listIr ] (fun xs -> ERt("fable_rt.listAverage($0)", xs, ty))
        | "SumBy", [ f; _ ] ->
            bindArgs ctx [ lw ctx f; listIr ] (fun xs -> ERt($"fable_rt.listSumBy(%s{zigTypeName ty}, $0, $1)", xs, ty))
        | "AverageBy", [ f; _ ] ->
            bindArgs
                ctx
                [ lw ctx f; listIr ]
                (fun xs -> ERt($"fable_rt.listAverageBy(%s{zigTypeName ty}, $0, $1)", xs, ty))
        | _ -> fail r "internal: a sum"

    // .NET's members by domain: tasks and async (Fable2Zig.Dotnet.Async.fs)
    | DomainCall "async" ctx r info t lowered -> lowered
    // ---- the entry of a map ----
    // (an entry is a pair here: making one is making the pair, and `KeyValue(k, v)` is the pair)
    | "System.Collections.Generic.KeyValuePair`2", ".ctor", [ k; v ] ->
        lw ctx (Fable.Value(Fable.NewTuple([ k; v ], false), r))
    | "Microsoft.FSharp.Core.Operators", "KeyValuePattern", [ kv ] -> lw ctx kv
    | "System.Collections.Generic.KeyValuePair`2", ("get_Key" | "get_Value"), [ kv ] ->
        bindArgs
            ctx
            [ lw ctx kv ]
            (fun xs ->
                EGet(
                    xs.Head,
                    PItem(
                        if name = "get_Key" then
                            0
                        else
                            1
                    ),
                    mapType ctx r t
                )
            )
    // ---- the item of this round of a `for ... in` loop ----
    | _, "get_Current", [ Fable.IdentExpr e ] when ctx.Enumerators.ContainsKey e.Name -> EVar ctx.Enumerators[e.Name]

    // .NET's members by domain: arrays, 2D arrays, .NET's mutable collections, lazy, spans, weak references (Fable2Zig.Dotnet.Collections.fs)
    | DomainCall "collections" ctx r info t lowered -> lowered
    // .NET's members by domain: StringBuilder, Split, Join, Format, chars and strings (Fable2Zig.Dotnet.Text.fs)
    | DomainCall "text" ctx r info t lowered -> lowered
    // ---- comparison of what is not a number: by `compare` ----
    | "Microsoft.FSharp.Core.Operators", "Max", [ a; b ] ->
        pure' "fable_rt.maxOf(@as($R, $0), $1)" [ a; b ] (mapType ctx r a.Type)
    | "Microsoft.FSharp.Core.Operators", "Min", [ a; b ] ->
        pure' "fable_rt.minOf(@as($R, $0), $1)" [ a; b ] (mapType ctx r a.Type)
    | "Microsoft.FSharp.Core.Operators", "Hash", [ x ] ->
        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.hash(%s{typedArg ctx r x 0})", xs, tI32))
    | "Microsoft.FSharp.Core.Operators",
      ("op_LessThan" | "op_GreaterThan" | "op_LessThanOrEqual" | "op_GreaterThanOrEqual" | "Compare"),
      [ a; b ] ->
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
                let order = EEmit("fable_rt.compareOf($0, $1)", xs, tI32)

                match op with
                | Some op -> EPrim(op, [ order; ELit("0", tI32) ], tBool)
                | None -> order
            )
    // ---- failures ----
    | "Microsoft.FSharp.Core.Operators", "FailWith", [ msg ] -> raiseDotnet ctx r "System.Exception" (lw ctx msg) t
    | "Microsoft.FSharp.Core.Operators", "InvalidOp", [ msg ] ->
        raiseDotnet ctx r "System.InvalidOperationException" (lw ctx msg) t
    | "Microsoft.FSharp.Core.Operators", "InvalidArg", [ arg; msg ] ->
        raiseArgument ctx r "System.ArgumentException" (lw ctx msg) arg t
    | "Microsoft.FSharp.Core.Operators", "NullArg", [ arg ] ->
        let message = ELit(stringLiteral "Value cannot be null.", tStr)
        raiseArgument ctx r "System.ArgumentNullException" message arg t
    // `System.Exception("...")` and the other classes: a new exception with that message
    // `Exception(message, inner)`: the exception, with the one inside it
    | cls, ".ctor", [ message; inner ] when
        dotnetExceptions.ContainsKey cls
        && message.Type = Fable.String
        && (
            match inner.Type with
            | Fable.DeclaredType(e, _) -> e.FullName = "System.Exception" || dotnetExceptions.ContainsKey e.FullName
            | _ -> false
        )
        ->
        bindArgsIn
            true
            ctx
            [ lw ctx message ]
            (fun xs ->
                let outer = EExnNew(dotnetExnEnt ctx cls, xs)
                bindArgs ctx [ outer; lw ctx inner ] (fun ys -> EEmit("fable_rt.exnWithInner($0, $1)", ys, tExn))
            )
    | cls, ".ctor", args when
        dotnetExceptions.ContainsKey cls
        && args |> List.forall (fun a -> a.Type = Fable.String)
        ->
        let message =
            match cls, args with
            | "System.ObjectDisposedException", [ objectName ] ->
                bindArgs
                    ctx
                    [ lw ctx objectName ]
                    (fun xs ->
                        EEmit(
                            "fable_rt.format(.{ \"Cannot access a disposed object.\\nObject name: '\", $0, \"'.\" })",
                            xs,
                            tStr
                        )
                    )
            | _, [] when defaultExnMessages.ContainsKey cls -> ELit(stringLiteral defaultExnMessages[cls], tStr)
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

        // (the parameter an ArgumentException is about, its `ParamName`)
        let parameter =
            match cls, args with
            | ("System.ArgumentNullException" | "System.ArgumentOutOfRangeException"), parameter :: _ -> Some parameter
            | "System.ArgumentException", [ _; parameter ] -> Some parameter
            | _ -> None

        match parameter with
        | Some p ->
            bindArgsIn
                true
                ctx
                [ message; lw ctx p ]
                (fun xs -> withParamName ctx (EExnNew(dotnetExnEnt ctx cls, [ xs.Head ])) xs.[1] id)
        | None -> bindArgsIn true ctx [ message ] (fun xs -> EExnNew(dotnetExnEnt ctx cls, xs))
    // `ArgumentException(message, parameter, inner)`
    | "System.ArgumentException", ".ctor", [ message; parameter; inner ] when
        message.Type = Fable.String && parameter.Type = Fable.String
        ->
        bindArgsIn
            true
            ctx
            [ withParameter ctx (lw ctx message) parameter; lw ctx parameter; lw ctx inner ]
            (fun xs ->
                let made = EExnNew(dotnetExnEnt ctx "System.ArgumentException", [ xs.Head ])

                withParamName
                    ctx
                    made
                    xs.[1]
                    (fun named ->
                        bindArgs ctx [ named; xs.[2] ] (fun ys -> EEmit("fable_rt.exnWithInner($0, $1)", ys, tExn))
                    )
            )
    | ("System.ArgumentException" | "System.ArgumentNullException" | "System.ArgumentOutOfRangeException"),
      "get_ParamName",
      [ x ] -> bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.exnParamName($0)", xs, tStr))
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
    | "Microsoft.FSharp.Collections.FSharpList`1", "get_Empty", _ -> ECon(mapType ctx r t, "Empty", [], None)
    | entity, "get_InnerException", [ x ] when entity = "System.Exception" || dotnetExceptions.ContainsKey entity ->
        rt "fable_rt.exnInner($0)" [ x ] tExn
    | "Microsoft.FSharp.Core.Operators", "IsNull", [ Fable.Call(Fable.Import(imp, _, _), inner, _, _) ] when
        imp.Selector = "get_InnerException"
        ->
        pure' "fable_rt.exnHasNoInner($0)" [ inner.ThisArg.Value ] tBool
    | entity, "get_Message", x :: _ when entity = "System.Exception" || dotnetExceptions.ContainsKey entity ->
        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.exnMessage($0)", xs, tStr))
    | entity, "get_StackTrace", x :: _ when entity = "System.Exception" || dotnetExceptions.ContainsKey entity ->
        ctx.State.UsesStackTrace <- true

        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.exnStackTrace($0)", xs, tStr))
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
    // .NET's members by domain: decimal, bigint, checked arithmetic (Fable2Zig.Dotnet.Numbers.fs)
    | DomainCall "numbers" ctx r info t lowered -> lowered
    // .NET's members by domain, in Fable2Zig.Dotnet.fs (enums, Convert and BitConverter,
    // Random, Nullable, Stack and Queue, tuples): here, in their place among the cases
    | DomainCall "misc" ctx r info t lowered -> lowered
    // ---- obj ----
    | "Microsoft.FSharp.Core.Operators", "Box", [ x ] when unwrapNullness x.Type <> Fable.Any -> boxed ctx x
    | "Microsoft.FSharp.Core.Operators", "Box", [ x ] -> lw ctx x
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"),
      ("Unbox" | "UnboxGeneric" | "UnboxFast"),
      [ Uncast x ] when unwrapNullness x.Type = Fable.Any && unwrapNullness t <> Fable.Any -> unboxed ctx r x t
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"),
      ("Unbox" | "UnboxGeneric" | "UnboxFast"),
      [ Uncast x ] when
        isInterfaceType ctx.Com x.Type
        && isFatIfaceTy (mapType ctx r x.Type)
        && unwrapNullness t <> Fable.Any
        ->
        ifaceDowncast ctx r x t
    // `obj.ReferenceEquals(a, b)` and `PhysicalEquality a b`: the same cell (what F# boxes for
    // the call is looked through: a record is not copied by it on .NET)
    | ("System.Object" | "Microsoft.FSharp.Core.LanguagePrimitives"),
      ("ReferenceEquals" | "PhysicalEquality"),
      [ Uncast a; Uncast b ] ->
        let a, b =
            if a.Type = b.Type then
                a, b
            else
                Fable.TypeCast(a, Fable.Any), Fable.TypeCast(b, Fable.Any)

        // (numbers, chars and bools are boxed one by one for the call: never the same object)
        match a.Type, b.Type with
        | (Fable.Number _ | Fable.Char | Fable.Boolean), _
        | _, (Fable.Number _ | Fable.Char | Fable.Boolean) ->
            lw ctx (Fable.Sequential [ a; b; Fable.Value(Fable.BoolConstant false, r) ])
        | _ ->

            // (a record, a union or a tuple that is a value here has no identity to compare)
            match mapType ctx r a.Type with
            | TEnt(e, _) when e.Kind = KRecord || e.Kind = KValueUnion ->
                fail
                    r
                    "the Zig target keeps %s as a value, which has no identity: ReferenceEquals and PhysicalEquality cannot be answered as on .NET (mark the type [<ReferenceEquality>] to give its values one)"
                    e.Ref.FullName
            | TTuple _ ->
                fail
                    r
                    "the Zig target keeps tuples as values, which have no identity: ReferenceEquals cannot be answered as on .NET"
            | _ -> pure' "fable_rt.refEql($0, $1)" [ a; b ] tBool
    // `x.Equals(o)`: by the type's `Equals`, through an object
    | "System.Object", "Equals", [ a; b ] ->
        let asObj (x: Fable.Expr) =
            match x with
            | Uncast inner when unwrapNullness inner.Type <> Fable.Any -> Fable.TypeCast(inner, Fable.Any)
            | _ -> x

        pure' "fable_rt.eql($0, $1)" [ asObj a; asObj b ] tBool
    | ("System.Object" | "System.String" | "System.Boolean" | "System.Char" | "System.SByte" | "System.Byte" | "System.Int16" | "System.UInt16" | "System.Int32" | "System.UInt32" | "System.Int64" | "System.UInt64" | "System.Single" | "System.Double" | "System.Decimal" | "System.Numerics.BigInteger"),
      "GetHashCode",
      [ x ] -> pure' "fable_rt.hash($0)" [ x ] tI32
    | "System.Collections.Generic.EqualityComparer`1", "Equals", [ _; a; b ] ->
        pure' "fable_rt.eql($0, $1)" [ a; b ] tBool
    | "System.Collections.Generic.EqualityComparer`1", "GetHashCode", [ _; x ] -> pure' "fable_rt.hash($0)" [ x ] tI32
    | "System.Collections.Generic.EqualityComparer`1", "get_Default", [] -> EUnit
    // ---- numbers ----
    | "System.MathF", _, _ -> dotnetCall ctx r "System.Math" name info t
    | ("System.Double" | "System.Single"),
      ("IsNaN" | "IsInfinity" | "IsPositiveInfinity" | "IsNegativeInfinity" | "IsFinite"),
      [ x ] ->
        let f =
            match name with
            | "IsNaN" -> "isNan"
            | "IsInfinity" -> "isInf"
            | "IsPositiveInfinity" -> "isPositiveInf"
            | "IsNegativeInfinity" -> "isNegativeInf"
            | _ -> "isFinite"

        pure' $"std.math.%s{f}($0)" [ x ] tBool
    // `Math.DivRem(a, b)`: `struct (a / b, a % b)`; with `&rem`, the remainder goes there
    | ("System.Math" | "System.Numerics.BigInteger"), "DivRem", a :: b :: rest ->
        let n = divRemTemps.Value.Value
        divRemTemps.Value.Value <- n + 1
        let ai = AST.makeTypedIdent a.Type $"divRemA%d{n}"
        let bi = AST.makeTypedIdent b.Type $"divRemB%d{n}"

        let op k =
            if isBig a then
                // (bigint's operators are calls)
                let selector =
                    if k = BinaryDivide then
                        "op_Division"
                    else
                        "op_Modulus"

                Fable.Call(
                    Fable.Import(
                        {
                            Selector = selector
                            Path = Replacements.DotnetPrefix + "System.Numerics.BigInteger"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create())
                        },
                        Fable.Any,
                        None
                    ),
                    { info with
                        Args = [ Fable.IdentExpr ai; Fable.IdentExpr bi ]
                        ThisArg = None
                    },
                    a.Type,
                    r
                )
            else
                Fable.Operation(Fable.Binary(k, Fable.IdentExpr ai, Fable.IdentExpr bi), [], a.Type, r)

        let body =
            match rest, t with
            | [ Fable.Operation(Fable.Unary(UnaryAddressOf, (Fable.IdentExpr _ as out)), _, _, _) ], _ ->
                Fable.Sequential [ Fable.Set(out, Fable.ValueSet, a.Type, op BinaryModulus, r); op BinaryDivide ]
            | [], Fable.Tuple(_, isStruct) ->
                Fable.Value(Fable.NewTuple([ op BinaryDivide; op BinaryModulus ], isStruct), r)
            | _ -> fail r "the Zig target does not support this DivRem yet"

        lw ctx (Fable.Let(ai, a, Fable.Let(bi, b, body)))
    | ("Microsoft.FSharp.Core.Operators" | "System.Numerics.BigInteger"),
      ("op_BitwiseAnd" | "op_BitwiseOr" | "op_ExclusiveOr" | "op_LeftShift" | "op_RightShift"),
      [ a; b ] when isBig a ->
        let f =
            match name with
            | "op_BitwiseAnd" -> "bigAnd"
            | "op_BitwiseOr" -> "bigOr"
            | "op_ExclusiveOr" -> "bigXor"
            | "op_LeftShift" -> "bigShl"
            | _ -> "bigShr"

        pure' $"fable_rt.%s{f}($0, $1)" [ a; b ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), "Abs", [ x ] ->
        rt "fable_rt.absOf(@as($R, $0))" [ x ] (mapType ctx r x.Type)
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), "Sign", [ x ] ->
        rt $"fable_rt.signOf(%s{typedArg ctx r x 0})" [ x ] tI32
    | "Microsoft.FSharp.Core.Operators", "PowInteger", [ x; n ] ->
        pure' "fable_rt.pown(@as($R, $0), $1)" [ x; n ] (mapType ctx r x.Type)
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), ("op_Exponentiation" | "Pow"), [ x; y ] ->
        pure' "std.math.pow($R, $0, $1)" [ x; y ] (mapType ctx r x.Type)
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), "Round", [ x ] ->
        pure' "fable_rt.roundEven(@as($R, $0))" [ x ] (mapType ctx r x.Type)
    | "System.Math", "Round", [ x; digits ] when isInt digits -> pure' "fable_rt.roundTo($0, $1)" [ x; digits ] tF64
    | "System.Math", "Log", [ x; b ] -> pure' "fable_rt.logBase($0, $1)" [ x; b ] tF64
    | "System.Math", "Clamp", [ x; lo; hi ] ->
        rt "fable_rt.clamp(@as($R, $0), $1, $2)" [ x; lo; hi ] (mapType ctx r x.Type)
    | "System.Math", ("Max" | "Min"), [ a; b ] ->
        let f =
            if name = "Max" then
                "mathMax"
            else
                "mathMin"

        pure' $"fable_rt.%s{f}(@as($R, $0), $1)" [ a; b ] (mapType ctx r a.Type)
    | "System.Math", "get_PI", [] -> ELit("std.math.pi", tF64)
    | "System.Math", "get_E", [] -> ELit("std.math.e", tF64)
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"),
      ("Sqrt" | "Sin" | "Cos" | "Tan" | "Exp" | "Log" | "Log10" | "Floor" | "Ceiling" | "Truncate" | "Asin" | "Acos" | "Atan" | "Sinh" | "Cosh" | "Tanh" | "Log2"),
      [ x ] ->
        let zig =
            match name with
            | "Sqrt" -> "@sqrt($0)"
            | "Sin" -> "@sin($0)"
            | "Cos" -> "@cos($0)"
            | "Tan" -> "@tan($0)"
            | "Exp" -> "@exp($0)"
            | "Log" -> "@log($0)"
            | "Log10" -> "@log10($0)"
            | "Log2" -> "@log2($0)"
            | "Floor" -> "@floor($0)"
            | "Ceiling" -> "@ceil($0)"
            | "Truncate" -> "@trunc($0)"
            | "Asin" -> "std.math.asin($0)"
            | "Acos" -> "std.math.acos($0)"
            | "Atan" -> "std.math.atan($0)"
            | "Sinh" -> "std.math.sinh($0)"
            | "Cosh" -> "std.math.cosh($0)"
            | _ -> "std.math.tanh($0)"

        pure' (zig.Replace("$0", "@as($R, $0)")) [ x ] (mapType ctx r x.Type)
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), ("Atan2" | "Atan2"), [ y; x ] ->
        pure' "std.math.atan2(@as(f64, $0), @as(f64, $1))" [ y; x ] tF64
    // `char "a"` and `Char.Parse "a"`: a string of exactly one char
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.ExtraTopLevelOperators"), "ToChar", [ x ]
    | "System.Char", "Parse", [ x ] when unwrapNullness x.Type = Fable.String ->
        rt "fable_rt.strToChar($0)" [ x ] (TPrim "u16")
    // text to numbers: F#'s conversions read `0x`, `0o`, `0b` and `_`; .NET's `Parse` does not
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.ExtraTopLevelOperators"), _, [ x ] when
        name.StartsWith("To", System.StringComparison.Ordinal)
        && unwrapNullness x.Type = Fable.String
        ->
        let ty = mapType ctx r t

        if isFloatTy ty then
            rt "fable_rt.parseFloat($R, $0)" [ x ] ty
        elif intBits ty > 0 then
            rt "fable_rt.parseIntFs($R, $0)" [ x ] ty
        elif t = Fable.Boolean then
            rt "fable_rt.parseBool($0)" [ x ] ty
        else
            fail r "the Zig target does not support %s.%s of a string yet" entity name
    | ("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte" | "System.UInt16" | "System.UInt32" | "System.UInt64"),
      "Parse",
      [ x ] -> rt "fable_rt.parseInt($R, $0)" [ x ] (mapType ctx r t)
    | ("System.Double" | "System.Single"), "Parse", [ x ] -> rt "fable_rt.parseFloat($R, $0)" [ x ] (mapType ctx r t)
    | "System.Boolean", "Parse", [ x ] -> rt "fable_rt.parseBool($0)" [ x ] tBool
    // (`Int32.Parse(s, provider)`: the invariant culture's, as without one)
    | ("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte" | "System.UInt16" | "System.UInt32" | "System.UInt64" | "System.Double" | "System.Single"),
      "Parse",
      [ x; provider ] when
        (match unwrapNullness provider.Type with
         | Fable.DeclaredType(e, _) ->
             e.FullName = "System.IFormatProvider"
             || e.FullName = "System.Globalization.CultureInfo"
         | _ -> false)
        ->
        dotnetCall ctx r entity name { info with Args = [ x ] } t
    // `TryParse(s, &v)`: what F# gives is `(ok, v)`, with `v` an out-variable of its own; or
    // `TryParse` given as a function, whose `v` is a ref cell (`f(s, r)`). On failure `v` is the
    // type's default, as on .NET.
    | ("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte" | "System.UInt16" | "System.UInt32" | "System.UInt64" | "System.Double" | "System.Single" | "System.Decimal" | "System.Boolean" | "System.Numerics.BigInteger"),
      "TryParse",
      [ x; out ] when
        (match out with
         | Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr o), _, _, _) -> ctx.Vars.ContainsKey o.Name
         // (`&r.contents` of a ref cell)
         | Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.Get(cell, Fable.FieldGet info, _, _)), _, _, _) ->
             info.Name = "contents"
             && (
                 match cell.Type with
                 | Fable.DeclaredType(e, [ _ ]) -> e.FullName = refName
                 | _ -> false
             )
         | _ ->
             match out.Type with
             | Fable.DeclaredType(e, [ _ ]) -> e.FullName = refName
             | _ -> false)
        ->
        let valueType =
            match out with
            | Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr o), _, _, _) -> unByref o.Type
            | Fable.Operation(Fable.Unary(UnaryAddressOf, (Fable.Get _ as place)), _, _, _) -> place.Type
            | _ ->
                match out.Type with
                | Fable.DeclaredType(_, [ v ]) -> v
                | _ -> fail r "internal: TryParse"

        let ty = mapType ctx r valueType
        let tmp = AST.makeTypedIdent (Fable.Option(valueType, false)) "parsed"

        let parsed =
            Fable.Emit(
                {
                    Macro = $"fable_rt.tryParseAny(%s{zigTypeName ty}, $0)"
                    IsStatement = false
                    CallInfo = Fable.CallInfo.Create(args = [ x ])
                },
                Fable.Option(valueType, false),
                r
            )

        let orDefault =
            Fable.Emit(
                {
                    Macro = $"fable_rt.orDefault(%s{zigTypeName ty}, $0)"
                    IsStatement = false
                    CallInfo = Fable.CallInfo.Create(args = [ Fable.IdentExpr tmp ])
                },
                valueType,
                r
            )

        let store =
            match out with
            | Fable.Operation(Fable.Unary(UnaryAddressOf, (Fable.IdentExpr _ as v)), _, _, _) ->
                Fable.Set(v, Fable.ValueSet, valueType, orDefault, r)
            | Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.Get(cell, _, _, _)), _, _, _) ->
                Fable.Set(cell, Fable.FieldSet "contents", valueType, orDefault, r)
            | refCell -> Fable.Set(refCell, Fable.FieldSet "contents", valueType, orDefault, r)

        let isSome = Fable.Test(Fable.IdentExpr tmp, Fable.OptionTest true, r)

        lw ctx (Fable.Let(tmp, parsed, Fable.Sequential [ store; isSome ]))
    | ("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte" | "System.UInt16" | "System.UInt32" | "System.UInt64"),
      "Parse",
      [ s; Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32(512 | 515), _), _) ] ->
        rt "fable_rt.parseHex($R, $0)" [ s ] (mapType ctx r t)
    // sums and averages: the runtime adds with `+` of the item type
    | "Microsoft.FSharp.Collections.ListModule", "Sum", [ xs ] when mapType ctx r t = TPrim "fable_rt.NetDecimal" ->
        rt "fable_rt.listSumDec($0)" [ xs ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ListModule", "Sum", [ xs ] -> pure' "fable_rt.listSum($0)" [ xs ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ListModule", "SumBy", [ f; xs ] ->
        trySpecListHof
            ctx
            r
            name
            args
            t
            (function
            | [ f'; xs' ] -> rt "fable_rt.listSumBy($R, $0, $1)" [ f'; xs' ] (mapType ctx r t)
            | _ -> rt "fable_rt.listSumBy($R, $0, $1)" [ f; xs ] (mapType ctx r t)
            )
        |> Option.defaultWith (fun () -> rt "fable_rt.listSumBy($R, $0, $1)" [ f; xs ] (mapType ctx r t))
    | "Microsoft.FSharp.Collections.ListModule", "Average", [ xs ] ->
        rt "fable_rt.listAverage($0)" [ xs ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ListModule", "AverageBy", [ f; xs ] ->
        rt "fable_rt.listAverageBy($R, $0, $1)" [ f; xs ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Sum", [ a ] when mapType ctx r t = TPrim "fable_rt.NetDecimal" ->
        rt "fable_rt.arraySumDec($0)" [ a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Sum", [ a ] -> pure' "fable_rt.arraySum($0)" [ a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "Average", [ a ] ->
        rt "fable_rt.arrayAverage($0)" [ a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.ArrayModule", "SumBy", [ f; a ] ->
        trySpecArrayHof
            ctx
            r
            name
            args
            t
            (function
            | [ f'; a' ] -> rt "fable_rt.arraySumBy($R, $0, $1)" [ f'; a' ] (mapType ctx r t)
            | _ -> rt "fable_rt.arraySumBy($R, $0, $1)" [ f; a ] (mapType ctx r t)
            )
        |> Option.defaultWith (fun () -> rt "fable_rt.arraySumBy($R, $0, $1)" [ f; a ] (mapType ctx r t))
    | "Microsoft.FSharp.Collections.ArrayModule", "AverageBy", [ f; a ] ->
        rt "fable_rt.arrayAverageBy($R, $0, $1)" [ f; a ] (mapType ctx r t)
    | "System.Array", "Copy", [ Uncast src; Uncast dst; n ] ->
        rt "fable_rt.arrayCopyRange($0, 0, $1, 0, $2)" [ src; dst; n ] tVoid
    | "System.Array", "Copy", [ Uncast src; si; Uncast dst; di; n ] ->
        rt "fable_rt.arrayCopyRange($0, $1, $2, $3, $4)" [ src; si; dst; di; n ] tVoid
    | "System.Array", "IndexOf", [ Uncast a; Uncast x ] -> rt "fable_rt.arrayIndexOf($0, $1, 0, null)" [ a; x ] tI32
    | "System.Array", "IndexOf", [ Uncast a; Uncast x; start ] ->
        rt "fable_rt.arrayIndexOf($0, $1, $2, null)" [ a; x; start ] tI32
    | "System.Array", "IndexOf", [ Uncast a; Uncast x; start; count ] ->
        rt "fable_rt.arrayIndexOf($0, $1, $2, $3)" [ a; x; start; count ] tI32
    | "System.Array", "ConvertAll", [ a; f ] -> rt "fable_rt.arrayMap($R, $0, $1)" [ f; a ] (mapType ctx r t)
    | "Microsoft.FSharp.Core.Operators.OperatorIntrinsics", "SetArraySlice", [ target; lo; hi; source ] ->
        rt "fable_rt.arraySetSlice($0, $1, $2, $3)" [ target; lo; hi; source ] tVoid

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
    | _ ->
        // (where the value is a function that is applied at once, Fable gives the read the type
        // of the application: the option's item type is the one to go by)
        let t =
            match entity, name, args with
            | ("Microsoft.FSharp.Core.FSharpOption`1" | "Microsoft.FSharp.Core.FSharpValueOption`1"),
              "get_Value",
              o :: _ ->
                match o.Type with
                | Fable.Option(item, _) -> item
                | _ -> t
            | _ -> t

        // (a member of F#'s list reached through a trait call, `(^a: (member Length: int) x)`,
        // comes with the list's type as its type argument; the functions take the item's)
        let info =
            match entity, info.ThisArg with
            | "Microsoft.FSharp.Collections.FSharpList`1", Some this ->
                match this.Type with
                | Fable.List item -> { info with GenericArgs = [ item ] }
                | _ -> info
            | _ -> info

        let fallback args' =
            match libraryFunction entity name with
            | Some(file, fn) -> libraryCall ctx r file fn info args' t
            | None -> fail r "the Zig target does not support %s.%s yet" entity name

        match
            if entity = "Microsoft.FSharp.Collections.ListModule" then
                trySpecListHof ctx r name args t fallback
            else
                None
        with
        | Some lowered -> lowered
        | None -> fallback args

/// The item type of a cell type of one type argument.
and itemOf (x: Expr) : Ty =
    match typeOf x with
    | TEnt(_, [ item ]) -> item
    | _ -> fail None "internal: not a collection"

/// What a `for ... in` loop walks, lowered: a list (of a list, a set, or a map's entries) or
/// a string. None for a source that is walked some other way.
and forInSource (ctx: Ctx) (source: Fable.Expr) : (Expr * string) option =
    let (Uncast inner) = source

    match inner.Type with
    | Fable.List _ -> Some(lw ctx inner, "list")
    | Fable.Array(_, (Fable.MutableArray | Fable.ImmutableArray)) -> Some(lw ctx inner, "array")
    | Fable.DeclaredType(ent, _) when
        ent.FullName = "System.Collections.Generic.ICollection`1"
        || ent.FullName = "System.Collections.Generic.Dictionary`2.KeyCollection"
        || ent.FullName = "System.Collections.Generic.Dictionary`2.ValueCollection"
        ->
        Some(lw ctx inner, "list")
    | Fable.String -> Some(lw ctx inner, "string")
    | t when isSeqType t -> Some(lw ctx inner, "seq")
    // (the matches and the groups of a regular expression: their sequences)
    | Fable.DeclaredType(coll, []) when
        coll.FullName = "System.Text.RegularExpressions.MatchCollection"
        || coll.FullName = "System.Text.RegularExpressions.GroupCollection"
        ->
        let isMatches =
            coll.FullName.EndsWith("MatchCollection", System.StringComparison.Ordinal)

        let item =
            Fable.DeclaredType(
                {
                    FullName =
                        (if isMatches then
                             "System.Text.RegularExpressions.Match"
                         else
                             "System.Text.RegularExpressions.Group")
                    Path = Fable.CoreAssemblyName "System.Text.RegularExpressions"
                },
                []
            )

        let seqType =
            Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IEnumerable`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ item ]
            )

        Some(
            libraryCall
                ctx
                None
                "Regex"
                (if isMatches then
                     "matchesToSeq"
                 else
                     "groupsToSeq")
                (Fable.CallInfo.Create(args = [ inner ]))
                [ inner ]
                seqType,
            "seq"
        )
    | Fable.Array(_, Fable.ResizeArray) ->
        Some(
            bindArgs
                ctx
                [ lw ctx inner ]
                (fun xs -> EEmit("fable_rt.raToList($0)", xs, TEnt(listEnt ctx.State, [ itemOf xs.Head ]))),
            "list"
        )
    | Fable.DeclaredType(ent, [ k; v ]) when isDictionaryName ent.FullName ->
        let pairTy = TTuple [ mapType ctx None k; mapType ctx None v ]

        Some(
            bindArgs
                ctx
                [ lw ctx inner ]
                (fun xs -> EEmit("fable_rt.dictToList($0)", xs, TEnt(listEnt ctx.State, [ pairTy ]))),
            "list"
        )
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.HashSet`1" ->
        Some(
            bindArgs
                ctx
                [ lw ctx inner ]
                (fun xs -> EEmit("fable_rt.setToList($0)", xs, TEnt(listEnt ctx.State, [ mapType ctx None item ]))),
            "list"
        )
    | Fable.DeclaredType(ent, [ item ]) when
        ent.FullName = "System.Collections.Generic.Stack`1"
        || ent.FullName = "System.Collections.Generic.Queue`1"
        ->
        let file =
            if ent.FullName.EndsWith("Stack`1", System.StringComparison.Ordinal) then
                "Stack"
            else
                "Queue"

        let info = Fable.CallInfo.Create(args = [ inner ], genArgs = [ item ])
        Some(libraryCall ctx None file "toList" info [ inner ] (Fable.List item), "list")
    | Fable.DeclaredType(ent, genArgs) when ent.FullName = mapName || ent.FullName = setName ->
        let file =
            if ent.FullName = mapName then
                "Map"
            else
                "Set"

        let info = Fable.CallInfo.Create(args = [ inner ], genArgs = genArgs)

        let listTy =
            match genArgs with
            | [ k; v ] -> Fable.List(Fable.Tuple([ k; v ], false))
            | [ item ] -> Fable.List item
            | _ -> Fable.Any

        Some(libraryCall ctx None file "toList" info [ inner ] listTy, "list")
    | _ -> None

/// A call of a function of the part of the runtime library that is written in F# (`List.fs`,
/// ...). Its type parameters are found by name, from the signature of the FSharp.Core
/// function it stands for, and given in the order of their names: that is the order in which
/// the library declares them.
and libraryCall
    (ctx: Ctx)
    (r: SourceLocation option)
    (file: string)
    (fn: string)
    (info: Fable.CallInfo)
    (args: Fable.Expr list)
    (t: Fable.Type)
    : Expr
    =
    // (an empty generic value of the library made at obj, as a generalized `let xs = Seq.empty`
    // is: made again at the type the parameter wants. The type arguments are taken in the order
    // the signature first names its type parameters, and only when every other argument agrees)
    let args =
        let rec namesIn (acc: string list) (t: Fable.Type) =
            match t with
            | Fable.GenericParam(n, _, _) ->
                if List.contains n acc then
                    acc
                else
                    acc @ [ n ]
            | _ -> t.Generics |> List.fold namesIn acc

        let rec hasAny (t: Fable.Type) =
            match t with
            | Fable.Any -> true
            | _ -> t.Generics |> List.exists hasAny

        let isOpenEmpty (a: Fable.Expr) =
            match a with
            | Fable.Call(Fable.Import(imp, _, _), ci, typ, _) ->
                (match imp.Kind with
                 | Fable.LibraryImport _ -> true
                 | _ -> false)
                && ci.Args.IsEmpty
                && ci.ThisArg.IsNone
                && hasAny typ
            | _ -> false

        let names = info.SignatureArgTypes |> List.fold namesIn []

        if
            args |> List.exists isOpenEmpty
            && info.SignatureArgTypes.Length = args.Length
            && not names.IsEmpty
            && names.Length = info.GenericArgs.Length
            && not (info.GenericArgs |> List.exists (fun t -> hasAny t || hasTypeParams t))
        then
            let subst = List.zip names info.GenericArgs |> Map.ofList
            let wanted = info.SignatureArgTypes |> List.map (substFableType subst)

            let agrees =
                List.forall2
                    (fun (w: Fable.Type) (a: Fable.Expr) ->
                        isOpenEmpty a
                        || hasAny a.Type
                        || (
                            match w, a.Type with
                            | (Fable.LambdaType _ | Fable.DelegateType _), _ -> true
                            | _ -> w = a.Type
                        )
                    )
                    wanted
                    args

            if agrees then
                List.map2
                    (fun (w: Fable.Type) (a: Fable.Expr) ->
                        match a with
                        | Fable.Call(callee, ci, _, r) when
                            isOpenEmpty a && not (hasAny w) && w.Generics.Length = ci.GenericArgs.Length
                            ->
                            Fable.Call(callee, { ci with GenericArgs = w.Generics }, w, r)
                        | _ -> a
                    )
                    wanted
                    args
            else
                args
        else
            args

    let found = Dictionary<string, Fable.Type>()

    // `Seq.collect` and `Seq.concat` are generic in the type of the collections too
    // (`'Collection :> seq<'U>`): the library's take sequences, so a function that gives a list
    // gives the sequence of it.
    let info, args =
        match file, fn, info.GenericArgs, args with
        | "Seq", "collect", [ t; _; u ], [ mapping; source ] when
            (match mapping.Type with
             | Fable.LambdaType(_, ret) -> not (isSeqType ret)
             | _ -> false)
            ->
            let x: Fable.Ident =
                {
                    Name = "collected"
                    Type = t
                    IsMutable = false
                    IsThisArgument = false
                    IsCompilerGenerated = true
                    Range = None
                    IsInlineIfLambda = false
                }

            let seqU = Fable.DeclaredType(seqEntRef, [ u ])

            let wrapped =
                Fable.Lambda(
                    x,
                    Fable.TypeCast(
                        Fable.CurriedApply(
                            mapping,
                            [ Fable.IdentExpr x ],
                            (match mapping.Type with
                             | Fable.LambdaType(_, ret) -> ret
                             | _ -> Fable.Any),
                            None
                        ),
                        seqU
                    ),
                    None
                )

            { info with
                GenericArgs = [ t; u ]
                SignatureArgTypes = []
                MemberRef = None
            },
            [ wrapped; source ]
        | "Seq", "collect", [ t; _; u ], _ ->
            { info with
                GenericArgs = [ t; u ]
                SignatureArgTypes = []
                MemberRef = None
            },
            args
        // (a sequence of lists or arrays: each is seen as a sequence first)
        | "Seq", ("concat" | "transpose"), [ coll; t ], [ source ] when not (isSeqType coll) ->
            let seqT = Fable.DeclaredType(seqEntRef, [ t ])

            let x: Fable.Ident =
                {
                    Name = "part"
                    Type = coll
                    IsMutable = false
                    IsThisArgument = false
                    IsCompilerGenerated = true
                    Range = None
                    IsInlineIfLambda = false
                }

            let asSeq = Fable.Lambda(x, Fable.TypeCast(Fable.IdentExpr x, seqT), None)

            let mapped =
                Fable.Call(
                    Fable.Import(
                        {
                            Selector = "Map"
                            Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Collections.SeqModule"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                        },
                        Fable.Any,
                        None
                    ),
                    { Fable.CallInfo.Create(args = [ asSeq; source ]) with GenericArgs = [ coll; seqT ] },
                    Fable.DeclaredType(seqEntRef, [ seqT ]),
                    None
                )

            { info with
                GenericArgs = [ t ]
                SignatureArgTypes = []
                MemberRef = None
            },
            [ mapped ]
        | "Seq", ("concat" | "transpose"), [ _; t ], _ ->
            { info with
                GenericArgs = [ t ]
                SignatureArgTypes = []
                MemberRef = None
            },
            args
        | _ -> info, args

    let args =
        args
        |> List.filter (fun a ->
            match a.Type with
            | Fable.DeclaredType(ent, _) -> ent.FullName <> "Microsoft.FSharp.Control.FSharpAsyncBuilder"
            | _ -> true
        )

    // (the optional timeout and cancellation of `Async.RunSynchronously` and `Start` are not
    // taken)
    let args =
        match file, fn with
        | "Async", ("runSynchronously" | "startImmediate" | "startAsync") -> List.truncate 1 args
        | _ -> args

    // (where FSharp.Core takes a sequence and is given a list, the library takes the list; an
    // empty value whose item type F# left open, `obj` on .NET, gets `unit`: nothing can depend
    // on it)
    // (`Seq.empty` whose type argument Fable gives as `obj`: the result's type says it)
    let info =
        match file, fn, info.GenericArgs, t with
        | "Seq", "empty", [ Fable.Any ], Fable.DeclaredType(_, [ item ]) when item <> Fable.Any ->
            { info with GenericArgs = [ item ] }
        | _ -> info

    // (a function of one type argument: an untyped `None` given to it is of that type)
    let emptyItem =
        match info.GenericArgs with
        | [ only ] when only <> Fable.Any -> only
        | _ -> Fable.Any

    let args =
        args
        |> List.map (fun arg ->
            match arg with
            | _ when
                file = "Seq"
                || file = "Async"
                || file = "Task"
                || file = "ResizeArray"
                || file = "HashSet"
                || file = "Stack"
                || file = "Queue"
                || file = "ListCollector"
                ->
                arg
            | Fable.Value(Fable.NewOption(None, Fable.Any, isStruct), r) ->
                Fable.Value(Fable.NewOption(None, emptyItem, isStruct), r)
            | Uncast inner when
                (match arg.Type with
                 | Fable.DeclaredType(seq, _) -> seq.FullName = "System.Collections.Generic.IEnumerable`1"
                 | _ -> false)
                && (listItem inner.Type).IsSome
                ->
                inner
            | _ -> arg
        )

    // (an instance member: the object's type has the type parameters of its type)
    let calledMember = info.MemberRef |> Option.bind ctx.Com.TryGetMember

    let ownerParams =
        match info.MemberRef with
        | Some(Fable.MemberRef(entRef, _)) ->
            match ctx.Com.TryGetEntity entRef with
            | Some ent when not ent.IsFSharpModule -> ent.GenericParameters |> List.map (fun g -> g.Name)
            | _ -> []
        | _ -> []

    match info.ThisArg, info.MemberRef with
    | Some this, Some(Fable.MemberRef(entRef, _)) when not ownerParams.IsEmpty ->
        unify
            found
            (Fable.DeclaredType(entRef, ownerParams |> List.map (fun n -> Fable.GenericParam(n, false, []))))
            this.Type
    | _ -> ()

    let sigArgs =
        match info.ThisArg with
        | Some _ when info.SignatureArgTypes.Length + 1 = args.Length -> args.Tail
        | _ -> args

    if info.SignatureArgTypes.Length = sigArgs.Length then
        List.iter2
            (fun (pattern: Fable.Type) (arg: Fable.Expr) ->
                match pattern, arg.Type with
                | Fable.DeclaredType(seq, [ item ]), actual when
                    seq.FullName = "System.Collections.Generic.IEnumerable`1"
                    && (listItem actual).IsSome
                    ->
                    unify found item (listItem actual).Value
                | _ -> unify found pattern arg.Type
            )
            info.SignatureArgTypes
            sigArgs

    // what no argument tells (`Map.empty`) is in the call's own type arguments
    let allParams =
        ownerParams
        @ (
            match calledMember with
            | Some m -> m.GenericParameters |> List.map (fun g -> g.Name)
            | None -> []
        )

    if allParams.Length = info.GenericArgs.Length then
        for (n, ty) in List.zip allParams info.GenericArgs do
            if not (found.ContainsKey n) then
                found[n] <- ty

    // (a member of a generic type that is not generic itself: the type arguments of the
    // call are those of the object's type, in their order)
    match info.ThisArg with
    | Some this when
        found.Count <> info.GenericArgs.Length
        && (
            match this.Type with
            | Fable.DeclaredType(_, targs) -> targs.Length = info.GenericArgs.Length
            | _ -> false
        )
        ->
        found.Clear()
        info.GenericArgs |> List.iteri (fun i ty -> found[$"%03d{i}"] <- ty)
    | _ -> ()

    if found.Count <> info.GenericArgs.Length then
        // (no argument tells: the call's own type arguments, in their order, which is the
        // order of their names in FSharp.Core and in the library)
        match info.GenericArgs with
        | given when found.Count = 0 -> given |> List.iteri (fun i ty -> found[$"%03d{i}"] <- ty)
        | _ ->
            fail
                r
                "the Zig target cannot tell the type arguments of this call of %s yet (%A from %A of %A)"
                fn
                (List.ofSeq found.Keys)
                allParams
                info.GenericArgs

    let typeArgs =
        found
        |> Seq.sortWith (fun a b -> System.String.CompareOrdinal(a.Key, b.Key))
        |> Seq.map (fun kv ->
            match kv.Value with
            | Fable.Any -> tAny
            | other -> mapType ctx r other
        )
        |> List.ofSeq

    // (inside the library file itself the function is one of the file's own)
    let own =
        System.IO.Path.GetFileNameWithoutExtension(ctx.Com.CurrentFile) = file
        && ctx.Members.ContainsKey fn

    let target =
        if own then
            fn
        else
            importAlias ctx (Fable.Transforms.AST.getLibPath ctx.Com file) + "." + fn

    // (a property is read with a unit argument that the library function does not take; a
    // collection given where FSharp.Core takes a sequence is walked as the list of what it
    // holds)
    let lowerArg (arg: Fable.Expr) : Expr =
        match arg with
        // (these modules take sequences as they are)
        | _ when
            file = "Seq"
            || file = "Async"
            || file = "Task"
            || file = "ResizeArray"
            || file = "HashSet"
            || file = "Stack"
            || file = "Queue"
            || file = "ListCollector"
            ->
            lw ctx arg
        // (a sequence given to a function that takes a list: the list of what it gives)
        | Fable.TypeCast(inner, _)
        | inner when isSeqType inner.Type && isSeqType arg.Type ->
            match inner.Type with
            | Fable.DeclaredType(_, [ item ]) ->
                let itemTy = mapType ctx r item

                bindArgs
                    ctx
                    [ lw ctx inner ]
                    (fun xs ->
                        ECall(libraryTarget ctx "Seq" "toList", [ itemTy ], xs, TEnt(listEnt ctx.State, [ itemTy ]))
                    )
            | _ -> lw ctx arg
        | Fable.TypeCast(inner, Fable.DeclaredType(seq, _)) when
            seq.FullName = "System.Collections.Generic.IEnumerable`1"
            && (listItem inner.Type).IsNone
            && (forInSource ctx inner).IsSome
            ->
            match forInSource ctx inner with
            | Some(listExpr, "list") -> listExpr
            | _ -> lw ctx arg
        | _ -> lw ctx arg

    // (a unit argument is not given to the library function, but what computes it runs, in its
    // place: `async { return raise e }` raises)
    let isPlainUnit (arg: Fable.Expr) =
        match arg with
        | Fable.Value(Fable.UnitConstant, _)
        | Fable.IdentExpr _ -> true
        | _ -> false

    let kept = args |> List.filter (fun arg -> not (isUnit arg.Type && isPlainUnit arg))

    let lowered = kept |> List.map lowerArg

    bindArgs
        ctx
        lowered
        (fun xs ->
            let given =
                List.zip kept xs
                |> List.filter (fun (arg, _) -> not (isUnit arg.Type))
                |> List.map snd

            let effects =
                List.zip kept xs
                |> List.filter (fun (arg, _) -> isUnit arg.Type)
                |> List.map snd

            let call =
                ECall(
                    target,
                    typeArgs,
                    (match given with
                     | [] -> [ EUnit ]
                     | _ -> given),
                    mapType ctx r t
                )

            List.foldBack (fun effect acc -> ESeq(effect, acc)) effects call
        )

/// Specialize hot `List.*` and `Array.*` higher-order functions directly into local TRMC /
/// direct loops in the caller's file when given a known lambda, local function, or callable,
/// avoiding closure allocation and indirect `.code` calls.
and private hasAnyType (t: Fable.Type) =
    match t with
    | Fable.Any -> true
    | _ -> t.Generics |> List.exists hasAnyType

and private isOpenEmptyArg (a: Fable.Expr) =
    match a with
    | Fable.Call(Fable.Import(imp, _, _), ci, typ, _) ->
        (match imp.Kind with
         | Fable.LibraryImport _ -> true
         | _ -> false)
        && ci.Args.IsEmpty
        && ci.ThisArg.IsNone
        && hasAnyType typ
    | _ -> false

and private isKnownNonNeg (ctx: Ctx) (e: Fable.Expr) = isKnownNonNegExpr ctx e

and private canSpecFnExpr (ctx: Ctx) (e: Fable.Expr) =
    match e with
    | Fable.Lambda _
    | Fable.Delegate _ -> true
    | _ -> (tryCallable ctx e).IsSome

and private peelLeadingLets (e: Expr) =
    let rec go acc e =
        match e with
        | ELet(v, r, b) -> go ((v, r) :: acc) b
        | _ -> List.rev acc, e

    go [] e

and private withLoweredExpr
    (ctx: Ctx)
    (fableTy: Fable.Type)
    (nameHint: string)
    (ir: Expr)
    (build: Fable.Expr -> Expr)
    : Expr
    =
    let v = ctx.State.NewVar(nameHint, typeOf ir, VLocal, false)
    let id = AST.makeTypedIdent fableTy $"%s{nameHint}$%d{v.Id}"
    ctx.Vars[id.Name] <- v

    try
        ELet(v, ir, build (Fable.IdentExpr id))
    finally
        ctx.Vars.Remove id.Name |> ignore

and private tryExtractSpec
    (ctx: Ctx)
    (arity: int)
    (argTys: Ty list)
    (retTy: Ty)
    (fIr: Expr)
    : ((Var * Expr) list * (Var list * Expr list * (Expr list -> Expr))) option
    =
    let preBinds, core = peelLeadingLets fIr

    let capsOk (caps: Expr list) =
        caps
        |> List.forall (
            function
            | EVar v -> not v.FMutable && v.Kind <> VGlobal
            | _ -> false
        )

    match core with
    | EClosure(target, cTypeArgs, caps, cloTy) when capsOk caps ->
        let matchesLocal (fnName: string) =
            let mutable found = None
            let mutable i = ctx.State.Fns.Count - 1

            while i >= 0 && found.IsNone do
                let fn = ctx.State.Fns[i]

                if fn.Name = fnName then
                    found <- Some fn

                i <- i - 1

            match found with
            | Some fn when
                fn.Params.Length = caps.Length + arity
                && fn.TypeParams.Length = cTypeArgs.Length
                ->
                let inst =
                    if fn.TypeParams.IsEmpty then
                        Map.empty
                    else
                        Map.ofList (List.zip fn.TypeParams cTypeArgs)

                let fullTys = (caps |> List.map typeOf) @ argTys

                if
                    List.forall2 (fun (q: Var) t -> zigType (substTy inst q.Ty) = zigType t) fn.Params fullTys
                    && zigType (substTy inst fn.Ret) = zigType retTy
                then
                    Some fnName
                else
                    None
            | _ -> None

        let resolvedTarget =
            match arity, cloTy with
            | 1, TFn([ p0 ], r0) ->
                match matchesLocal target with
                | Some n -> Some n
                | None when
                    target.Contains(".")
                    && caps.IsEmpty
                    && zigType p0 = zigType argTys[0]
                    && zigType r0 = zigType retTy
                    ->
                    Some target
                | _ -> None
            | 2, TFn([ p0; p1 ], r0) ->
                match matchesLocal target with
                | Some n -> Some n
                | None when
                    target.Contains(".")
                    && caps.IsEmpty
                    && zigType p0 = zigType argTys[0]
                    && zigType p1 = zigType argTys[1]
                    && zigType r0 = zigType retTy
                    ->
                    Some target
                | _ -> None
            | 2, TFn([ _ ], TFn([ _ ], _)) ->
                match ctx.State.Curried2.TryGetValue target with
                | true, target2 -> matchesLocal target2
                | _ -> None
            | _ -> None

        resolvedTarget
        |> Option.map (fun callTargetName ->
            let capParams =
                caps
                |> List.map (fun c ->
                    match c with
                    | EVar v -> ctx.State.NewVar(v.Base, v.Ty, VParam, false)
                    | _ -> ctx.State.NewVar("cap", typeOf c, VParam, false)
                )

            let callWith (loopArgs: Expr list) =
                ECall(callTargetName, cTypeArgs, (capParams |> List.map EVar) @ loopArgs, retTy)

            preBinds, (capParams, caps, callWith)
        )
    | _ -> None

and private addSpecLoop
    (ctx: Ctx)
    (r: SourceLocation option)
    (hint: string)
    (capParams: Var list)
    (loopParams: Var list)
    (retTy: Ty)
    (buildBody: string -> Ty list -> Expr -> Expr)
    =
    let fnName = uniqueName ctx $"%s{ctx.FnBase}_%s{hint}"
    let typeArgs = ctx.TypeParams |> List.map TGen
    let allParams = capParams @ loopParams
    let dummyCall = ECall(fnName, typeArgs, (allParams |> List.map EVar), retTy)
    let body = buildBody fnName typeArgs dummyCall

    ctx.State.Fns.Add
        {
            Name = fnName
            TypeParams = ctx.TypeParams
            Params = allParams
            Modes = allParams |> List.map (fun _ -> MPlain)
            Ret = retTy
            Body = body
            RetFrom = None
            Raises = RNever
            Stores = false
            IsLocal = true
            IsEntryPoint = false
            Range = r
        }

    fnName, typeArgs

and trySpecListHof
    (ctx: Ctx)
    (r: SourceLocation option)
    (name: string)
    (args: Fable.Expr list)
    (t: Fable.Type)
    (fallback: Fable.Expr list -> Expr)
    : Expr option
    =
    let listElem (ty: Ty) =
        match ty with
        | TEnt(e, [ elem ]) when e.Ref.FullName = listName && elem <> TPrim "void" -> Some elem
        | _ -> None

    if args |> List.exists isOpenEmptyArg then
        None
    else
        match name, args with
        | "Initialize", [ n; f ] when canSpecFnExpr ctx f ->
            let outListTy = mapType ctx r t

            match listElem outListTy with
            | Some outElem ->
                let nonNeg = isKnownNonNeg ctx n
                let lenIr = lw ctx n
                let lenV = ctx.State.NewVar("len", tI32, VLocal, false)
                let lenId = AST.makeTypedIdent n.Type $"len$%d{lenV.Id}"
                let fIr = lw ctx f

                match tryExtractSpec ctx 1 [ tI32 ] outElem fIr with
                | Some(preBinds, (capParams, caps, callSpec)) ->
                    let iV = ctx.State.NewVar("i", tI32, VParam, false)
                    let nV = ctx.State.NewVar("n", tI32, VParam, false)

                    let fnName, typeArgs =
                        addSpecLoop
                            ctx
                            r
                            "list_init"
                            capParams
                            [ iV; nV ]
                            outListTy
                            (fun self tArgs _ ->
                                let yV = ctx.State.NewVar("y", outElem, VLocal, false)
                                let nextIV = ctx.State.NewVar("next", tI32, VLocal, false)
                                let tailV = ctx.State.NewVar("tail", outListTy, VLocal, false)

                                EIf(
                                    EPrim("eq", [ EVar iV; EVar nV ], tBool),
                                    ECon(outListTy, "Empty", [], None),
                                    ELet(
                                        yV,
                                        callSpec [ EVar iV ],
                                        ELet(
                                            nextIV,
                                            EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32),
                                            ELet(
                                                tailV,
                                                ECall(
                                                    self,
                                                    tArgs,
                                                    (capParams |> List.map EVar) @ [ EVar nextIV; EVar nV ],
                                                    outListTy
                                                ),
                                                ECon(outListTy, "Cons", [ EVar yV; EVar tailV ], None)
                                            )
                                        )
                                    ),
                                    outListTy
                                )
                            )

                    let callExpr =
                        ECall(fnName, typeArgs, caps @ [ ELit("0", tI32); EVar lenV ], outListTy)

                    let body =
                        if nonNeg then
                            callExpr
                        else
                            ctx.State.UsesRuntime <- true

                            let negCheck =
                                EIf(
                                    EPrim("lt", [ EVar lenV; ELit("0", tI32) ], tBool),
                                    ERt("@as(fable_rt.Raised!void, fable_rt.countNegative($0))", [ EVar lenV ], tVoid),
                                    EUnit,
                                    tVoid
                                )

                            ESeq(negCheck, callExpr)

                    let wrapped = List.foldBack (fun (v, x) acc -> ELet(v, x, acc)) preBinds body
                    Some(ELet(lenV, lenIr, wrapped))
                | None ->
                    ctx.Vars[lenId.Name] <- lenV

                    try
                        Some(
                            ELet(
                                lenV,
                                lenIr,
                                withLoweredExpr ctx f.Type "fn" fIr (fun fId -> fallback [ Fable.IdentExpr lenId; fId ])
                            )
                        )
                    finally
                        ctx.Vars.Remove lenId.Name |> ignore
            | None -> None

        | ("Map" | "MapIndexed" | "Filter" | "Where" | "Choose"), [ f; xs ] when canSpecFnExpr ctx f ->
            let outListTy = mapType ctx r t
            let inListTy = mapType ctx r xs.Type

            match listElem inListTy, listElem outListTy with
            | Some inElem, Some outElem ->
                let arity, specArgTys, specRetTy =
                    match name with
                    | "Map" -> 1, [ inElem ], outElem
                    | "MapIndexed" -> 2, [ tI32; inElem ], outElem
                    | "Filter"
                    | "Where" -> 1, [ inElem ], tBool
                    | "Choose" -> 1, [ inElem ], TOpt outElem
                    | _ -> 1, [ inElem ], outElem

                let fIr = lw ctx f

                match tryExtractSpec ctx arity specArgTys specRetTy fIr with
                | Some(preBinds, (capParams, caps, callSpec)) ->
                    let fnName, typeArgs, initArgs =
                        match name with
                        | "Map" ->
                            let restV = ctx.State.NewVar("rest", inListTy, VParam, false)

                            let n, tArgs =
                                addSpecLoop
                                    ctx
                                    r
                                    "list_map"
                                    capParams
                                    [ restV ]
                                    outListTy
                                    (fun self tArgs _ ->
                                        let headV = ctx.State.NewVar("head", inElem, VLocal, false)
                                        let tailV = ctx.State.NewVar("tail", inListTy, VLocal, false)
                                        let yV = ctx.State.NewVar("y", outElem, VLocal, false)
                                        let mappedV = ctx.State.NewVar("mapped", outListTy, VLocal, false)

                                        EIf(
                                            ETest(EVar restV, "Empty", inListTy),
                                            ECon(outListTy, "Empty", [], None),
                                            ELet(
                                                headV,
                                                EGet(EVar restV, PCase("Cons", "Head"), inElem),
                                                ELet(
                                                    tailV,
                                                    EGet(EVar restV, PCase("Cons", "Tail"), inListTy),
                                                    ELet(
                                                        yV,
                                                        callSpec [ EVar headV ],
                                                        ELet(
                                                            mappedV,
                                                            ECall(
                                                                self,
                                                                tArgs,
                                                                (capParams |> List.map EVar) @ [ EVar tailV ],
                                                                outListTy
                                                            ),
                                                            ECon(outListTy, "Cons", [ EVar yV; EVar mappedV ], None)
                                                        )
                                                    )
                                                )
                                            ),
                                            outListTy
                                        )
                                    )

                            n, tArgs, (fun xsVar -> [ xsVar ])
                        | "MapIndexed" ->
                            let iV = ctx.State.NewVar("i", tI32, VParam, false)
                            let restV = ctx.State.NewVar("rest", inListTy, VParam, false)

                            let n, tArgs =
                                addSpecLoop
                                    ctx
                                    r
                                    "list_mapi"
                                    capParams
                                    [ iV; restV ]
                                    outListTy
                                    (fun self tArgs _ ->
                                        let headV = ctx.State.NewVar("head", inElem, VLocal, false)
                                        let tailV = ctx.State.NewVar("tail", inListTy, VLocal, false)
                                        let yV = ctx.State.NewVar("y", outElem, VLocal, false)
                                        let nextIV = ctx.State.NewVar("next", tI32, VLocal, false)
                                        let mappedV = ctx.State.NewVar("mapped", outListTy, VLocal, false)

                                        EIf(
                                            ETest(EVar restV, "Empty", inListTy),
                                            ECon(outListTy, "Empty", [], None),
                                            ELet(
                                                headV,
                                                EGet(EVar restV, PCase("Cons", "Head"), inElem),
                                                ELet(
                                                    tailV,
                                                    EGet(EVar restV, PCase("Cons", "Tail"), inListTy),
                                                    ELet(
                                                        yV,
                                                        callSpec [ EVar iV; EVar headV ],
                                                        ELet(
                                                            nextIV,
                                                            EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32),
                                                            ELet(
                                                                mappedV,
                                                                ECall(
                                                                    self,
                                                                    tArgs,
                                                                    (capParams |> List.map EVar)
                                                                    @ [ EVar nextIV; EVar tailV ],
                                                                    outListTy
                                                                ),
                                                                ECon(
                                                                    outListTy,
                                                                    "Cons",
                                                                    [ EVar yV; EVar mappedV ],
                                                                    None
                                                                )
                                                            )
                                                        )
                                                    )
                                                )
                                            ),
                                            outListTy
                                        )
                                    )

                            n, tArgs, (fun xsVar -> [ ELit("0", tI32); xsVar ])
                        | "Filter"
                        | "Where" ->
                            let restV = ctx.State.NewVar("rest", inListTy, VParam, false)

                            let n, tArgs =
                                addSpecLoop
                                    ctx
                                    r
                                    "list_filter"
                                    capParams
                                    [ restV ]
                                    outListTy
                                    (fun self tArgs _ ->
                                        let headV = ctx.State.NewVar("head", inElem, VLocal, false)
                                        let tailV = ctx.State.NewVar("tail", inListTy, VLocal, false)
                                        let keepV = ctx.State.NewVar("keep", tBool, VLocal, false)
                                        let filteredV = ctx.State.NewVar("filtered", outListTy, VLocal, false)

                                        let tailCall =
                                            ECall(
                                                self,
                                                tArgs,
                                                (capParams |> List.map EVar) @ [ EVar tailV ],
                                                outListTy
                                            )

                                        EIf(
                                            ETest(EVar restV, "Empty", inListTy),
                                            ECon(outListTy, "Empty", [], None),
                                            ELet(
                                                headV,
                                                EGet(EVar restV, PCase("Cons", "Head"), inElem),
                                                ELet(
                                                    tailV,
                                                    EGet(EVar restV, PCase("Cons", "Tail"), inListTy),
                                                    ELet(
                                                        keepV,
                                                        callSpec [ EVar headV ],
                                                        EIf(
                                                            EVar keepV,
                                                            ELet(
                                                                filteredV,
                                                                tailCall,
                                                                ECon(
                                                                    outListTy,
                                                                    "Cons",
                                                                    [ EVar headV; EVar filteredV ],
                                                                    None
                                                                )
                                                            ),
                                                            tailCall,
                                                            outListTy
                                                        )
                                                    )
                                                )
                                            ),
                                            outListTy
                                        )
                                    )

                            n, tArgs, (fun xsVar -> [ xsVar ])
                        | _ ->
                            // "Choose"
                            let restV = ctx.State.NewVar("rest", inListTy, VParam, false)
                            let optOutTy = TOpt outElem

                            let n, tArgs =
                                addSpecLoop
                                    ctx
                                    r
                                    "list_choose"
                                    capParams
                                    [ restV ]
                                    outListTy
                                    (fun self tArgs _ ->
                                        let headV = ctx.State.NewVar("head", inElem, VLocal, false)
                                        let tailV = ctx.State.NewVar("tail", inListTy, VLocal, false)
                                        let resV = ctx.State.NewVar("chosen", optOutTy, VLocal, false)
                                        let yV = ctx.State.NewVar("y", outElem, VLocal, false)
                                        let chosenTailV = ctx.State.NewVar("tail_out", outListTy, VLocal, false)

                                        let tailCall =
                                            ECall(
                                                self,
                                                tArgs,
                                                (capParams |> List.map EVar) @ [ EVar tailV ],
                                                outListTy
                                            )

                                        EIf(
                                            ETest(EVar restV, "Empty", inListTy),
                                            ECon(outListTy, "Empty", [], None),
                                            ELet(
                                                headV,
                                                EGet(EVar restV, PCase("Cons", "Head"), inElem),
                                                ELet(
                                                    tailV,
                                                    EGet(EVar restV, PCase("Cons", "Tail"), inListTy),
                                                    ELet(
                                                        resV,
                                                        callSpec [ EVar headV ],
                                                        EIf(
                                                            ETest(EVar resV, "None", optOutTy),
                                                            tailCall,
                                                            ELet(
                                                                yV,
                                                                EGet(EVar resV, PSome, outElem),
                                                                ELet(
                                                                    chosenTailV,
                                                                    tailCall,
                                                                    ECon(
                                                                        outListTy,
                                                                        "Cons",
                                                                        [ EVar yV; EVar chosenTailV ],
                                                                        None
                                                                    )
                                                                )
                                                            ),
                                                            outListTy
                                                        )
                                                    )
                                                )
                                            ),
                                            outListTy
                                        )
                                    )

                            n, tArgs, (fun xsVar -> [ xsVar ])

                    let xsIr = coerceTy ctx inListTy (lw ctx xs)

                    let callExpr =
                        bindArgs ctx [ xsIr ] (fun ys -> ECall(fnName, typeArgs, caps @ initArgs ys.Head, outListTy))

                    Some(List.foldBack (fun (v, x) acc -> ELet(v, x, acc)) preBinds callExpr)
                | None -> Some(withLoweredExpr ctx f.Type "fn" fIr (fun fId -> fallback [ fId; xs ]))
            | _ -> None

        | "Fold", [ f; state; xs ] when canSpecFnExpr ctx f ->
            let stateTy = mapType ctx r t
            let inListTy = mapType ctx r xs.Type

            match listElem inListTy with
            | Some inElem ->
                let fIr = lw ctx f

                match tryExtractSpec ctx 2 [ stateTy; inElem ] stateTy fIr with
                | Some(preBinds, (capParams, caps, callSpec)) ->
                    let accV = ctx.State.NewVar("acc", stateTy, VParam, false)
                    let restV = ctx.State.NewVar("rest", inListTy, VParam, false)

                    let fnName, typeArgs =
                        addSpecLoop
                            ctx
                            r
                            "list_fold"
                            capParams
                            [ accV; restV ]
                            stateTy
                            (fun self tArgs _ ->
                                let headV = ctx.State.NewVar("head", inElem, VLocal, false)
                                let tailV = ctx.State.NewVar("tail", inListTy, VLocal, false)
                                let nextV = ctx.State.NewVar("next", stateTy, VLocal, false)

                                EIf(
                                    ETest(EVar restV, "Empty", inListTy),
                                    EVar accV,
                                    ELet(
                                        headV,
                                        EGet(EVar restV, PCase("Cons", "Head"), inElem),
                                        ELet(
                                            tailV,
                                            EGet(EVar restV, PCase("Cons", "Tail"), inListTy),
                                            ELet(
                                                nextV,
                                                callSpec [ EVar accV; EVar headV ],
                                                ECall(
                                                    self,
                                                    tArgs,
                                                    (capParams |> List.map EVar) @ [ EVar nextV; EVar tailV ],
                                                    stateTy
                                                )
                                            )
                                        )
                                    ),
                                    stateTy
                                )
                            )

                    let stateIr = coerceTy ctx stateTy (lw ctx state)
                    let xsIr = coerceTy ctx inListTy (lw ctx xs)

                    let callExpr =
                        bindArgs
                            ctx
                            [ stateIr; xsIr ]
                            (fun ys -> ECall(fnName, typeArgs, caps @ [ ys[0]; ys[1] ], stateTy))

                    Some(List.foldBack (fun (v, x) acc -> ELet(v, x, acc)) preBinds callExpr)
                | None -> Some(withLoweredExpr ctx f.Type "fn" fIr (fun fId -> fallback [ fId; state; xs ]))
            | None -> None

        | ("Iterate" | "IterateIndexed" | "Exists" | "ForAll" | "TryFind" | "SumBy"), [ f; xs ] when canSpecFnExpr ctx f ->
            let inListTy = mapType ctx r xs.Type
            let outTy = mapType ctx r t

            match listElem inListTy with
            | Some inElem ->
                let shape =
                    match name with
                    | "Iterate" -> Some(1, [ inElem ], tVoid)
                    | "IterateIndexed" -> Some(2, [ tI32; inElem ], tVoid)
                    | "Exists"
                    | "ForAll" -> Some(1, [ inElem ], tBool)
                    | "TryFind" ->
                        match outTy with
                        | TOpt elem when zigType elem = zigType inElem -> Some(1, [ inElem ], tBool)
                        | _ -> None
                    | "SumBy" when intBits outTy > 0 || isFloatTy outTy -> Some(1, [ inElem ], outTy)
                    | _ -> None

                match shape with
                | Some(arity, specArgTys, specRetTy) ->
                    let fIr = lw ctx f

                    match tryExtractSpec ctx arity specArgTys specRetTy fIr with
                    | Some(preBinds, (capParams, caps, callSpec)) ->
                        let fnName, typeArgs, retTy, initArgs =
                            match name with
                            | "Iterate" ->
                                let restV = ctx.State.NewVar("rest", inListTy, VParam, false)

                                let n, tArgs =
                                    addSpecLoop
                                        ctx
                                        r
                                        "list_iter"
                                        capParams
                                        [ restV ]
                                        tVoid
                                        (fun self tArgs _ ->
                                            let headV = ctx.State.NewVar("head", inElem, VLocal, false)
                                            let tailV = ctx.State.NewVar("tail", inListTy, VLocal, false)

                                            EIf(
                                                ETest(EVar restV, "Empty", inListTy),
                                                EUnit,
                                                ELet(
                                                    headV,
                                                    EGet(EVar restV, PCase("Cons", "Head"), inElem),
                                                    ELet(
                                                        tailV,
                                                        EGet(EVar restV, PCase("Cons", "Tail"), inListTy),
                                                        ESeq(
                                                            callSpec [ EVar headV ],
                                                            ECall(
                                                                self,
                                                                tArgs,
                                                                (capParams |> List.map EVar) @ [ EVar tailV ],
                                                                tVoid
                                                            )
                                                        )
                                                    )
                                                ),
                                                tVoid
                                            )
                                        )

                                n, tArgs, tVoid, (fun xsVar -> [ xsVar ])
                            | "IterateIndexed" ->
                                let iV = ctx.State.NewVar("i", tI32, VParam, false)
                                let restV = ctx.State.NewVar("rest", inListTy, VParam, false)

                                let n, tArgs =
                                    addSpecLoop
                                        ctx
                                        r
                                        "list_iteri"
                                        capParams
                                        [ iV; restV ]
                                        tVoid
                                        (fun self tArgs _ ->
                                            let headV = ctx.State.NewVar("head", inElem, VLocal, false)
                                            let tailV = ctx.State.NewVar("tail", inListTy, VLocal, false)
                                            let nextIV = ctx.State.NewVar("next", tI32, VLocal, false)

                                            EIf(
                                                ETest(EVar restV, "Empty", inListTy),
                                                EUnit,
                                                ELet(
                                                    headV,
                                                    EGet(EVar restV, PCase("Cons", "Head"), inElem),
                                                    ELet(
                                                        tailV,
                                                        EGet(EVar restV, PCase("Cons", "Tail"), inListTy),
                                                        ESeq(
                                                            callSpec [ EVar iV; EVar headV ],
                                                            ELet(
                                                                nextIV,
                                                                EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32),
                                                                ECall(
                                                                    self,
                                                                    tArgs,
                                                                    (capParams |> List.map EVar)
                                                                    @ [ EVar nextIV; EVar tailV ],
                                                                    tVoid
                                                                )
                                                            )
                                                        )
                                                    )
                                                ),
                                                tVoid
                                            )
                                        )

                                n, tArgs, tVoid, (fun xsVar -> [ ELit("0", tI32); xsVar ])
                            | "Exists" ->
                                let restV = ctx.State.NewVar("rest", inListTy, VParam, false)

                                let n, tArgs =
                                    addSpecLoop
                                        ctx
                                        r
                                        "list_exists"
                                        capParams
                                        [ restV ]
                                        tBool
                                        (fun self tArgs _ ->
                                            let headV = ctx.State.NewVar("head", inElem, VLocal, false)
                                            let tailV = ctx.State.NewVar("tail", inListTy, VLocal, false)
                                            let condV = ctx.State.NewVar("hit", tBool, VLocal, false)

                                            EIf(
                                                ETest(EVar restV, "Empty", inListTy),
                                                ELit("false", tBool),
                                                ELet(
                                                    headV,
                                                    EGet(EVar restV, PCase("Cons", "Head"), inElem),
                                                    ELet(
                                                        tailV,
                                                        EGet(EVar restV, PCase("Cons", "Tail"), inListTy),
                                                        ELet(
                                                            condV,
                                                            callSpec [ EVar headV ],
                                                            EIf(
                                                                EVar condV,
                                                                ELit("true", tBool),
                                                                ECall(
                                                                    self,
                                                                    tArgs,
                                                                    (capParams |> List.map EVar) @ [ EVar tailV ],
                                                                    tBool
                                                                ),
                                                                tBool
                                                            )
                                                        )
                                                    )
                                                ),
                                                tBool
                                            )
                                        )

                                n, tArgs, tBool, (fun xsVar -> [ xsVar ])
                            | "ForAll" ->
                                let restV = ctx.State.NewVar("rest", inListTy, VParam, false)

                                let n, tArgs =
                                    addSpecLoop
                                        ctx
                                        r
                                        "list_forall"
                                        capParams
                                        [ restV ]
                                        tBool
                                        (fun self tArgs _ ->
                                            let headV = ctx.State.NewVar("head", inElem, VLocal, false)
                                            let tailV = ctx.State.NewVar("tail", inListTy, VLocal, false)
                                            let condV = ctx.State.NewVar("ok", tBool, VLocal, false)

                                            EIf(
                                                ETest(EVar restV, "Empty", inListTy),
                                                ELit("true", tBool),
                                                ELet(
                                                    headV,
                                                    EGet(EVar restV, PCase("Cons", "Head"), inElem),
                                                    ELet(
                                                        tailV,
                                                        EGet(EVar restV, PCase("Cons", "Tail"), inListTy),
                                                        ELet(
                                                            condV,
                                                            callSpec [ EVar headV ],
                                                            EIf(
                                                                EVar condV,
                                                                ECall(
                                                                    self,
                                                                    tArgs,
                                                                    (capParams |> List.map EVar) @ [ EVar tailV ],
                                                                    tBool
                                                                ),
                                                                ELit("false", tBool),
                                                                tBool
                                                            )
                                                        )
                                                    )
                                                ),
                                                tBool
                                            )
                                        )

                                n, tArgs, tBool, (fun xsVar -> [ xsVar ])
                            | "TryFind" ->
                                let restV = ctx.State.NewVar("rest", inListTy, VParam, false)

                                let n, tArgs =
                                    addSpecLoop
                                        ctx
                                        r
                                        "list_tryFind"
                                        capParams
                                        [ restV ]
                                        outTy
                                        (fun self tArgs _ ->
                                            let headV = ctx.State.NewVar("head", inElem, VLocal, false)
                                            let tailV = ctx.State.NewVar("tail", inListTy, VLocal, false)
                                            let condV = ctx.State.NewVar("hit", tBool, VLocal, false)

                                            EIf(
                                                ETest(EVar restV, "Empty", inListTy),
                                                ECon(outTy, "None", [], None),
                                                ELet(
                                                    headV,
                                                    EGet(EVar restV, PCase("Cons", "Head"), inElem),
                                                    ELet(
                                                        tailV,
                                                        EGet(EVar restV, PCase("Cons", "Tail"), inListTy),
                                                        ELet(
                                                            condV,
                                                            callSpec [ EVar headV ],
                                                            EIf(
                                                                EVar condV,
                                                                ECon(outTy, "Some", [ EVar headV ], None),
                                                                ECall(
                                                                    self,
                                                                    tArgs,
                                                                    (capParams |> List.map EVar) @ [ EVar tailV ],
                                                                    outTy
                                                                ),
                                                                outTy
                                                            )
                                                        )
                                                    )
                                                ),
                                                outTy
                                            )
                                        )

                                n, tArgs, outTy, (fun xsVar -> [ xsVar ])
                            | _ ->
                                // "SumBy"
                                let accV = ctx.State.NewVar("acc", outTy, VParam, false)
                                let restV = ctx.State.NewVar("rest", inListTy, VParam, false)

                                let n, tArgs =
                                    addSpecLoop
                                        ctx
                                        r
                                        "list_sumBy"
                                        capParams
                                        [ accV; restV ]
                                        outTy
                                        (fun self tArgs _ ->
                                            let headV = ctx.State.NewVar("head", inElem, VLocal, false)
                                            let tailV = ctx.State.NewVar("tail", inListTy, VLocal, false)
                                            let valV = ctx.State.NewVar("v", outTy, VLocal, false)
                                            let nextV = ctx.State.NewVar("next", outTy, VLocal, false)

                                            EIf(
                                                ETest(EVar restV, "Empty", inListTy),
                                                EVar accV,
                                                ELet(
                                                    headV,
                                                    EGet(EVar restV, PCase("Cons", "Head"), inElem),
                                                    ELet(
                                                        tailV,
                                                        EGet(EVar restV, PCase("Cons", "Tail"), inListTy),
                                                        ELet(
                                                            valV,
                                                            callSpec [ EVar headV ],
                                                            ELet(
                                                                nextV,
                                                                EPrim("add", [ EVar accV; EVar valV ], outTy),
                                                                ECall(
                                                                    self,
                                                                    tArgs,
                                                                    (capParams |> List.map EVar)
                                                                    @ [ EVar nextV; EVar tailV ],
                                                                    outTy
                                                                )
                                                            )
                                                        )
                                                    )
                                                ),
                                                outTy
                                            )
                                        )

                                n, tArgs, outTy, (fun xsVar -> [ ELit("0", outTy); xsVar ])

                        let xsIr = coerceTy ctx inListTy (lw ctx xs)

                        let callExpr =
                            bindArgs ctx [ xsIr ] (fun ys -> ECall(fnName, typeArgs, caps @ initArgs ys.Head, retTy))

                        Some(List.foldBack (fun (v, x) acc -> ELet(v, x, acc)) preBinds callExpr)
                    | None -> Some(withLoweredExpr ctx f.Type "fn" fIr (fun fId -> fallback [ fId; xs ]))
                | None -> None
            | None -> None
        | _ -> None

and trySpecArrayHof
    (ctx: Ctx)
    (r: SourceLocation option)
    (name: string)
    (args: Fable.Expr list)
    (t: Fable.Type)
    (fallback: Fable.Expr list -> Expr)
    : Expr option
    =
    let arrElem (ty: Ty) =
        match ty with
        | TEnt(e, [ elem ]) when e.Ref.FullName = "System.Array" && elem <> TPrim "void" -> Some elem
        | _ -> None

    if args |> List.exists isOpenEmptyArg then
        None
    else
        match name, args with
        | "Initialize", [ n; f ] when canSpecFnExpr ctx f ->
            let outArrTy = mapType ctx r t

            match arrElem outArrTy with
            | Some outElem ->
                let nonNeg = isKnownNonNeg ctx n
                let lenIr = lw ctx n
                let lenArgV = ctx.State.NewVar("len", tI32, VLocal, false)
                let lenId = AST.makeTypedIdent n.Type $"len$%d{lenArgV.Id}"
                let fIr = lw ctx f

                match tryExtractSpec ctx 1 [ tI32 ] outElem fIr with
                | Some(preBinds, (capParams, caps, callSpec)) ->
                    ctx.State.UsesRuntime <- true
                    let lenV = ctx.State.NewVar("n", tI32, VParam, false)
                    let bufTy = TPrim $"fable_rt.ArrayBuf(%s{zigType outArrTy})"

                    let fnName, typeArgs =
                        addSpecLoop
                            ctx
                            r
                            "arr_init"
                            capParams
                            [ lenV ]
                            outArrTy
                            (fun _ _ _ ->
                                let bufV = ctx.State.NewVar("buf", bufTy, VLocal, true)
                                let iV = ctx.State.NewVar("i", tI32, VLocal, true)
                                let yV = ctx.State.NewVar("y", outElem, VLocal, false)
                                let exV = ctx.State.NewVar("ex", tExn, VLocal, false)

                                let loop =
                                    EWhile(
                                        EPrim("lt", [ EVar iV; EVar lenV ], tBool),
                                        ELet(
                                            yV,
                                            callSpec [ EVar iV ],
                                            ESeq(
                                                EEmit(
                                                    "fable_rt.arrayBufPush($0, $1)",
                                                    [ EVar yV; EAddr(EVar bufV, false) ],
                                                    tVoid
                                                ),
                                                EAssign(iV, EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32))
                                            )
                                        )
                                    )

                                let guarded =
                                    ETry(
                                        loop,
                                        exV,
                                        ESeq(
                                            EEmit("fable_rt.arrayBufAbandon($0)", [ EAddr(EVar bufV, false) ], tVoid),
                                            ERaise(EVar exV, tVoid)
                                        ),
                                        tVoid
                                    )

                                let fillAndFinish =
                                    ELet(
                                        bufV,
                                        EEmit(
                                            $"fable_rt.arrayBufNew(%s{zigType outArrTy}, @as(usize, @intCast($0)))",
                                            [ EVar lenV ],
                                            bufTy
                                        ),
                                        ELet(
                                            iV,
                                            ELit("0", tI32),
                                            ESeq(
                                                guarded,
                                                EEmit("fable_rt.arrayBufFinish($R, $0)", [ EVar bufV ], outArrTy)
                                            )
                                        )
                                    )

                                if nonNeg then
                                    fillAndFinish
                                else
                                    let negCheck =
                                        EIf(
                                            EPrim("lt", [ EVar lenV; ELit("0", tI32) ], tBool),
                                            ERt(
                                                "@as(fable_rt.Raised!void, fable_rt.countNegative($0))",
                                                [ EVar lenV ],
                                                tVoid
                                            ),
                                            EUnit,
                                            tVoid
                                        )

                                    ESeq(negCheck, fillAndFinish)
                            )

                    let callExpr = ECall(fnName, typeArgs, caps @ [ EVar lenArgV ], outArrTy)
                    let wrapped = List.foldBack (fun (v, x) acc -> ELet(v, x, acc)) preBinds callExpr
                    Some(ELet(lenArgV, lenIr, wrapped))
                | None ->
                    ctx.Vars[lenId.Name] <- lenArgV

                    try
                        Some(
                            ELet(
                                lenArgV,
                                lenIr,
                                withLoweredExpr ctx f.Type "fn" fIr (fun fId -> fallback [ Fable.IdentExpr lenId; fId ])
                            )
                        )
                    finally
                        ctx.Vars.Remove lenId.Name |> ignore
            | None -> None

        | ("Map" | "MapIndexed" | "Filter" | "Where"), [ f; a ] when canSpecFnExpr ctx f ->
            let outArrTy = mapType ctx r t
            let inArrTy = mapType ctx r a.Type

            match arrElem inArrTy, arrElem outArrTy with
            | Some inElem, Some outElem ->
                let arity, specArgTys, specRetTy =
                    match name with
                    | "Map" -> 1, [ inElem ], outElem
                    | "MapIndexed" -> 2, [ tI32; inElem ], outElem
                    | _ -> 1, [ inElem ], tBool

                let fIr = lw ctx f

                match tryExtractSpec ctx arity specArgTys specRetTy fIr with
                | Some(preBinds, (capParams, caps, callSpec)) ->
                    ctx.State.UsesRuntime <- true
                    let aV = ctx.State.NewVar("a", inArrTy, VParam, false)

                    let hint =
                        match name with
                        | "Map" -> "arr_map"
                        | "MapIndexed" -> "arr_mapi"
                        | _ -> "arr_filter"

                    let fnName, typeArgs =
                        addSpecLoop
                            ctx
                            r
                            hint
                            capParams
                            [ aV ]
                            outArrTy
                            (fun _ _ _ ->
                                let lenV = ctx.State.NewVar("len", tI32, VLocal, false)
                                let iV = ctx.State.NewVar("i", tI32, VLocal, true)
                                let xV = ctx.State.NewVar("x", inElem, VLocal, false)
                                let exV = ctx.State.NewVar("ex", tExn, VLocal, false)

                                let itemRead =
                                    EEmit(
                                        "fable_rt.arrayItemAt($0, @as(usize, @intCast($1)))",
                                        [ EVar aV; EVar iV ],
                                        inElem
                                    )

                                match name with
                                | "Map"
                                | "MapIndexed" ->
                                    let bufTy = TPrim $"fable_rt.ArrayBuf(%s{zigType outArrTy})"
                                    let bufV = ctx.State.NewVar("buf", bufTy, VLocal, true)
                                    let yV = ctx.State.NewVar("y", outElem, VLocal, false)

                                    let callNode =
                                        if name = "Map" then
                                            callSpec [ EVar xV ]
                                        else
                                            callSpec [ EVar iV; EVar xV ]

                                    let loop =
                                        EWhile(
                                            EPrim("lt", [ EVar iV; EVar lenV ], tBool),
                                            ELet(
                                                xV,
                                                itemRead,
                                                ELet(
                                                    yV,
                                                    callNode,
                                                    ESeq(
                                                        EEmit(
                                                            "fable_rt.arrayBufPush($0, $1)",
                                                            [ EVar yV; EAddr(EVar bufV, false) ],
                                                            tVoid
                                                        ),
                                                        EAssign(iV, EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32))
                                                    )
                                                )
                                            )
                                        )

                                    let guarded =
                                        ETry(
                                            loop,
                                            exV,
                                            ESeq(
                                                EEmit(
                                                    "fable_rt.arrayBufAbandon($0)",
                                                    [ EAddr(EVar bufV, false) ],
                                                    tVoid
                                                ),
                                                ERaise(EVar exV, tVoid)
                                            ),
                                            tVoid
                                        )

                                    ELet(
                                        lenV,
                                        EEmit("fable_rt.arrayLen($0)", [ EVar aV ], tI32),
                                        ELet(
                                            bufV,
                                            EEmit(
                                                $"fable_rt.arrayBufNew(%s{zigType outArrTy}, @as(usize, @intCast($0)))",
                                                [ EVar lenV ],
                                                bufTy
                                            ),
                                            ELet(
                                                iV,
                                                ELit("0", tI32),
                                                ESeq(
                                                    guarded,
                                                    EEmit("fable_rt.arrayBufFinish($R, $0)", [ EVar bufV ], outArrTy)
                                                )
                                            )
                                        )
                                    )
                                | _ ->
                                    let fbTy = TPrim "fable_rt.FilterBuf"
                                    let fbV = ctx.State.NewVar("fb", fbTy, VLocal, true)
                                    let keepV = ctx.State.NewVar("keep", tBool, VLocal, false)

                                    let loop =
                                        EWhile(
                                            EPrim("lt", [ EVar iV; EVar lenV ], tBool),
                                            ELet(
                                                xV,
                                                itemRead,
                                                ELet(
                                                    keepV,
                                                    callSpec [ EVar xV ],
                                                    ESeq(
                                                        EEmit(
                                                            "fable_rt.arrayFilterSet($0, @as(usize, @intCast($1)), $2)",
                                                            [ EAddr(EVar fbV, false); EVar iV; EVar keepV ],
                                                            tVoid
                                                        ),
                                                        EAssign(iV, EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32))
                                                    )
                                                )
                                            )
                                        )

                                    let guarded =
                                        ETry(
                                            loop,
                                            exV,
                                            ESeq(
                                                EEmit(
                                                    "fable_rt.arrayFilterAbandon($0)",
                                                    [ EAddr(EVar fbV, false) ],
                                                    tVoid
                                                ),
                                                ERaise(EVar exV, tVoid)
                                            ),
                                            tVoid
                                        )

                                    ELet(
                                        lenV,
                                        EEmit("fable_rt.arrayLen($0)", [ EVar aV ], tI32),
                                        ELet(
                                            fbV,
                                            EEmit(
                                                "fable_rt.arrayFilterNew(@as(usize, @intCast($0)))",
                                                [ EVar lenV ],
                                                fbTy
                                            ),
                                            ELet(
                                                iV,
                                                ELit("0", tI32),
                                                ESeq(
                                                    guarded,
                                                    EEmit(
                                                        "fable_rt.arrayFilterFinish($0, $1)",
                                                        [ EVar aV; EVar fbV ],
                                                        outArrTy
                                                    )
                                                )
                                            )
                                        )
                                    )
                            )

                    let aIr = lw ctx a

                    let callExpr =
                        bindArgs ctx [ aIr ] (fun ys -> ECall(fnName, typeArgs, caps @ [ ys.Head ], outArrTy))

                    Some(List.foldBack (fun (v, x) acc -> ELet(v, x, acc)) preBinds callExpr)
                | None -> Some(withLoweredExpr ctx f.Type "fn" fIr (fun fId -> fallback [ fId; a ]))
            | _ -> None

        | "Fold", [ f; state; a ] when canSpecFnExpr ctx f ->
            let stateTy = mapType ctx r t
            let inArrTy = mapType ctx r a.Type

            match arrElem inArrTy with
            | Some inElem ->
                let fIr = lw ctx f

                match tryExtractSpec ctx 2 [ stateTy; inElem ] stateTy fIr with
                | Some(preBinds, (capParams, caps, callSpec)) ->
                    ctx.State.UsesRuntime <- true
                    let accV = ctx.State.NewVar("acc", stateTy, VParam, false)
                    let iV = ctx.State.NewVar("i", tI32, VParam, false)
                    let lenV = ctx.State.NewVar("len", tI32, VParam, false)
                    let aV = ctx.State.NewVar("a", inArrTy, VParam, false)

                    let fnName, typeArgs =
                        addSpecLoop
                            ctx
                            r
                            "arr_fold"
                            capParams
                            [ accV; iV; lenV; aV ]
                            stateTy
                            (fun self tArgs _ ->
                                let xV = ctx.State.NewVar("x", inElem, VLocal, false)
                                let nextAccV = ctx.State.NewVar("next_acc", stateTy, VLocal, false)
                                let nextIV = ctx.State.NewVar("next_i", tI32, VLocal, false)

                                EIf(
                                    EPrim("lt", [ EVar iV; EVar lenV ], tBool),
                                    ELet(
                                        xV,
                                        EEmit(
                                            "fable_rt.arrayItemAt($0, @as(usize, @intCast($1)))",
                                            [ EVar aV; EVar iV ],
                                            inElem
                                        ),
                                        ELet(
                                            nextAccV,
                                            callSpec [ EVar accV; EVar xV ],
                                            ELet(
                                                nextIV,
                                                EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32),
                                                ECall(
                                                    self,
                                                    tArgs,
                                                    (capParams |> List.map EVar)
                                                    @ [ EVar nextAccV; EVar nextIV; EVar lenV; EVar aV ],
                                                    stateTy
                                                )
                                            )
                                        )
                                    ),
                                    EVar accV,
                                    stateTy
                                )
                            )

                    let stateIr = coerceTy ctx stateTy (lw ctx state)
                    let aIr = lw ctx a
                    let lenArgV = ctx.State.NewVar("len", tI32, VLocal, false)

                    let callExpr =
                        bindArgs
                            ctx
                            [ stateIr; aIr ]
                            (fun ys ->
                                ELet(
                                    lenArgV,
                                    EEmit("fable_rt.arrayLen($0)", [ ys[1] ], tI32),
                                    ECall(
                                        fnName,
                                        typeArgs,
                                        caps @ [ ys[0]; ELit("0", tI32); EVar lenArgV; ys[1] ],
                                        stateTy
                                    )
                                )
                            )

                    Some(List.foldBack (fun (v, x) acc -> ELet(v, x, acc)) preBinds callExpr)
                | None -> Some(withLoweredExpr ctx f.Type "fn" fIr (fun fId -> fallback [ fId; state; a ]))
            | None -> None

        | ("Iterate" | "IterateIndexed" | "Exists" | "ForAll" | "SumBy"), [ f; a ] when canSpecFnExpr ctx f ->
            let inArrTy = mapType ctx r a.Type
            let outTy = mapType ctx r t

            match arrElem inArrTy with
            | Some inElem ->
                let shape =
                    match name with
                    | "Iterate" -> Some(1, [ inElem ], tVoid)
                    | "IterateIndexed" -> Some(2, [ tI32; inElem ], tVoid)
                    | "Exists"
                    | "ForAll" -> Some(1, [ inElem ], tBool)
                    | "SumBy" when intBits outTy > 0 || isFloatTy outTy -> Some(1, [ inElem ], outTy)
                    | _ -> None

                match shape with
                | Some(arity, specArgTys, specRetTy) ->
                    let fIr = lw ctx f

                    match tryExtractSpec ctx arity specArgTys specRetTy fIr with
                    | Some(preBinds, (capParams, caps, callSpec)) ->
                        ctx.State.UsesRuntime <- true
                        let iV = ctx.State.NewVar("i", tI32, VParam, false)
                        let lenV = ctx.State.NewVar("len", tI32, VParam, false)
                        let aV = ctx.State.NewVar("a", inArrTy, VParam, false)

                        let itemRead =
                            EEmit("fable_rt.arrayItemAt($0, @as(usize, @intCast($1)))", [ EVar aV; EVar iV ], inElem)

                        let fnName, typeArgs, retTy, mkArgs =
                            match name with
                            | "Iterate" ->
                                let n, tArgs =
                                    addSpecLoop
                                        ctx
                                        r
                                        "arr_iter"
                                        capParams
                                        [ iV; lenV; aV ]
                                        tVoid
                                        (fun self tArgs _ ->
                                            let xV = ctx.State.NewVar("x", inElem, VLocal, false)
                                            let nextIV = ctx.State.NewVar("next", tI32, VLocal, false)

                                            EIf(
                                                EPrim("lt", [ EVar iV; EVar lenV ], tBool),
                                                ELet(
                                                    xV,
                                                    itemRead,
                                                    ESeq(
                                                        callSpec [ EVar xV ],
                                                        ELet(
                                                            nextIV,
                                                            EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32),
                                                            ECall(
                                                                self,
                                                                tArgs,
                                                                (capParams |> List.map EVar)
                                                                @ [ EVar nextIV; EVar lenV; EVar aV ],
                                                                tVoid
                                                            )
                                                        )
                                                    )
                                                ),
                                                EUnit,
                                                tVoid
                                            )
                                        )

                                n, tArgs, tVoid, (fun aVar lVar -> [ ELit("0", tI32); lVar; aVar ])
                            | "IterateIndexed" ->
                                let n, tArgs =
                                    addSpecLoop
                                        ctx
                                        r
                                        "arr_iteri"
                                        capParams
                                        [ iV; lenV; aV ]
                                        tVoid
                                        (fun self tArgs _ ->
                                            let xV = ctx.State.NewVar("x", inElem, VLocal, false)
                                            let nextIV = ctx.State.NewVar("next", tI32, VLocal, false)

                                            EIf(
                                                EPrim("lt", [ EVar iV; EVar lenV ], tBool),
                                                ELet(
                                                    xV,
                                                    itemRead,
                                                    ESeq(
                                                        callSpec [ EVar iV; EVar xV ],
                                                        ELet(
                                                            nextIV,
                                                            EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32),
                                                            ECall(
                                                                self,
                                                                tArgs,
                                                                (capParams |> List.map EVar)
                                                                @ [ EVar nextIV; EVar lenV; EVar aV ],
                                                                tVoid
                                                            )
                                                        )
                                                    )
                                                ),
                                                EUnit,
                                                tVoid
                                            )
                                        )

                                n, tArgs, tVoid, (fun aVar lVar -> [ ELit("0", tI32); lVar; aVar ])
                            | "Exists" ->
                                let n, tArgs =
                                    addSpecLoop
                                        ctx
                                        r
                                        "arr_exists"
                                        capParams
                                        [ iV; lenV; aV ]
                                        tBool
                                        (fun self tArgs _ ->
                                            let xV = ctx.State.NewVar("x", inElem, VLocal, false)
                                            let condV = ctx.State.NewVar("hit", tBool, VLocal, false)
                                            let nextIV = ctx.State.NewVar("next", tI32, VLocal, false)

                                            EIf(
                                                EPrim("lt", [ EVar iV; EVar lenV ], tBool),
                                                ELet(
                                                    xV,
                                                    itemRead,
                                                    ELet(
                                                        condV,
                                                        callSpec [ EVar xV ],
                                                        EIf(
                                                            EVar condV,
                                                            ELit("true", tBool),
                                                            ELet(
                                                                nextIV,
                                                                EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32),
                                                                ECall(
                                                                    self,
                                                                    tArgs,
                                                                    (capParams |> List.map EVar)
                                                                    @ [ EVar nextIV; EVar lenV; EVar aV ],
                                                                    tBool
                                                                )
                                                            ),
                                                            tBool
                                                        )
                                                    )
                                                ),
                                                ELit("false", tBool),
                                                tBool
                                            )
                                        )

                                n, tArgs, tBool, (fun aVar lVar -> [ ELit("0", tI32); lVar; aVar ])
                            | "ForAll" ->
                                let n, tArgs =
                                    addSpecLoop
                                        ctx
                                        r
                                        "arr_forall"
                                        capParams
                                        [ iV; lenV; aV ]
                                        tBool
                                        (fun self tArgs _ ->
                                            let xV = ctx.State.NewVar("x", inElem, VLocal, false)
                                            let condV = ctx.State.NewVar("ok", tBool, VLocal, false)
                                            let nextIV = ctx.State.NewVar("next", tI32, VLocal, false)

                                            EIf(
                                                EPrim("lt", [ EVar iV; EVar lenV ], tBool),
                                                ELet(
                                                    xV,
                                                    itemRead,
                                                    ELet(
                                                        condV,
                                                        callSpec [ EVar xV ],
                                                        EIf(
                                                            EVar condV,
                                                            ELet(
                                                                nextIV,
                                                                EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32),
                                                                ECall(
                                                                    self,
                                                                    tArgs,
                                                                    (capParams |> List.map EVar)
                                                                    @ [ EVar nextIV; EVar lenV; EVar aV ],
                                                                    tBool
                                                                )
                                                            ),
                                                            ELit("false", tBool),
                                                            tBool
                                                        )
                                                    )
                                                ),
                                                ELit("true", tBool),
                                                tBool
                                            )
                                        )

                                n, tArgs, tBool, (fun aVar lVar -> [ ELit("0", tI32); lVar; aVar ])
                            | _ ->
                                // "SumBy"
                                let accV = ctx.State.NewVar("acc", outTy, VParam, false)

                                let n, tArgs =
                                    addSpecLoop
                                        ctx
                                        r
                                        "arr_sumBy"
                                        capParams
                                        [ accV; iV; lenV; aV ]
                                        outTy
                                        (fun self tArgs _ ->
                                            let xV = ctx.State.NewVar("x", inElem, VLocal, false)
                                            let valV = ctx.State.NewVar("v", outTy, VLocal, false)
                                            let nextAccV = ctx.State.NewVar("next_acc", outTy, VLocal, false)
                                            let nextIV = ctx.State.NewVar("next_i", tI32, VLocal, false)

                                            EIf(
                                                EPrim("lt", [ EVar iV; EVar lenV ], tBool),
                                                ELet(
                                                    xV,
                                                    itemRead,
                                                    ELet(
                                                        valV,
                                                        callSpec [ EVar xV ],
                                                        ELet(
                                                            nextAccV,
                                                            EPrim("add", [ EVar accV; EVar valV ], outTy),
                                                            ELet(
                                                                nextIV,
                                                                EPrim("add", [ EVar iV; ELit("1", tI32) ], tI32),
                                                                ECall(
                                                                    self,
                                                                    tArgs,
                                                                    (capParams |> List.map EVar)
                                                                    @ [
                                                                        EVar nextAccV
                                                                        EVar nextIV
                                                                        EVar lenV
                                                                        EVar aV
                                                                    ],
                                                                    outTy
                                                                )
                                                            )
                                                        )
                                                    )
                                                ),
                                                EVar accV,
                                                outTy
                                            )
                                        )

                                n, tArgs, outTy, (fun aVar lVar -> [ ELit("0", outTy); ELit("0", tI32); lVar; aVar ])

                        let aIr = lw ctx a
                        let lenArgV = ctx.State.NewVar("len", tI32, VLocal, false)

                        let callExpr =
                            bindArgs
                                ctx
                                [ aIr ]
                                (fun ys ->
                                    ELet(
                                        lenArgV,
                                        EEmit("fable_rt.arrayLen($0)", [ ys.Head ], tI32),
                                        ECall(fnName, typeArgs, caps @ mkArgs ys.Head (EVar lenArgV), retTy)
                                    )
                                )

                        Some(List.foldBack (fun (v, x) acc -> ELet(v, x, acc)) preBinds callExpr)
                    | None -> Some(withLoweredExpr ctx f.Type "fn" fIr (fun fId -> fallback [ fId; a ]))
                | None -> None
            | None -> None
        | _ -> None

/// A statement: its value, if it has one, is not used.
and asStmt (ctx: Ctx) (ir: Expr) : Expr =
    if isVoid (typeOf ir) then
        ir
    else
        ELet(ctx.State.NewVar("discard", typeOf ir, VLocal, false), ir, EUnit)

and lwStmt (ctx: Ctx) (e: Fable.Expr) : Expr = asStmt ctx (lw ctx e)

let isEntryPoint (info: Fable.MemberFunctionOrValue) =
    info.Attributes
    |> Seq.exists (fun att -> att.Entity.FullName = "Microsoft.FSharp.Core.EntryPointAttribute")

let lowerFile (com: Compiler) (file: Fable.File) : FileState =
    let state = FileState()

    // (the constructors of this file's classes, for `Activator.CreateInstance` of a known type)
    fileCtors().Clear()

    let rec collectCtors (decls: Fable.Declaration list) =
        for d in decls do
            match d with
            | Fable.MemberDeclaration m ->
                match com.TryGetMember m.MemberRef with
                | Some info when info.IsConstructor ->
                    match info.DeclaringEntity with
                    | Some ent ->
                        let ps =
                            m.Args
                            |> List.filter (fun a -> not a.IsThisArgument)
                            |> List.map (fun a -> a.Type)

                        let known =
                            match fileCtors().TryGetValue ent.FullName with
                            | true, l -> l
                            | _ -> []

                        fileCtors().[ent.FullName] <- known @ [ m.Name, m.MemberRef, ps ]
                    | None -> ()
                | _ -> ()
            | Fable.ModuleDeclaration md -> collectCtors md.Members
            | Fable.ClassDeclaration c ->
                match c.Constructor with
                | Some m ->
                    let ps =
                        m.Args
                        |> List.filter (fun a -> not a.IsThisArgument)
                        |> List.map (fun a -> a.Type)

                    let known =
                        match fileCtors().TryGetValue c.Entity.FullName with
                        | true, l -> l
                        | _ -> []

                    fileCtors().[c.Entity.FullName] <- known @ [ m.Name, m.MemberRef, ps ]
                | None -> ()
            | _ -> ()

    collectCtors file.Declarations
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
            Boxed = HashSet()
            NonNull = HashSet()
            Positive = HashSet()
            NonNeg = HashSet()
            BoundedBelowMax = HashSet()
            Lengths = Dictionary()
            ConstLen = Dictionary()
            KnownTypes = Dictionary()
            InBounds = HashSet()
            Enumerators = Dictionary()
            OutTuples = Dictionary()
            CaughtExn = None
            InCtor = false
        }

    let report (r: SourceLocation option) (msg: string) =
        com.AddLog(msg, Severity.Error, ?range = r, fileName = com.CurrentFile)

    let attached = List<Fable.MemberDecl>()
    let mutable actions = 0
    /// the module value that holds a static field -> its type
    let staticTypes = Dictionary<string, Fable.Type>()

    let rec membersOf (decls: Fable.Declaration list) : Fable.MemberDecl list =
        decls
        |> List.collect (fun d ->
            match d with
            // a secondary or explicit constructor of an object class: takes `self_obj` first, runs
            // any delegating/base constructor on it, writes this class's fields, and runs any `then`
            // block directly against the live object.
            | Fable.MemberDeclaration m when
                (match com.TryGetMember m.MemberRef with
                 | Some info when info.IsConstructor ->
                     match info.DeclaringEntity with
                     | Some cls ->
                         (try
                             (objInfo (newCtx m.Name) None cls).IsSome
                          with ZigError _ ->
                              false)
                     | None -> false
                 | _ -> false)
                ->
                let cls = (com.TryGetMember m.MemberRef).Value.DeclaringEntity.Value
                let o = (objInfo (newCtx m.Name) None cls).Value

                let selfId, args =
                    match m.Args with
                    | first :: _ when first.IsThisArgument -> first, m.Args
                    | _ ->
                        let s = objSelfIdent o
                        s, s :: m.Args

                let ownFields = caseFields (TEnt(o.Part, [])) ""

                let isSysObjCtor (x: Fable.Expr) =
                    match x with
                    | Fable.Call(Fable.Import(imp, _, _), _, _, _) ->
                        imp.Selector = ".ctor" && imp.Path = Replacements.DotnetPrefix + "System.Object"
                    | _ -> false

                let rec rewriteSelf (e: Fable.Expr) : Fable.Expr =
                    match e with
                    | Fable.Call(Fable.Import(imp, _, _), _, _, _) when
                        imp.Selector = ".ctor" && imp.Path = Replacements.DotnetPrefix + "System.Object"
                        ->
                        Fable.Value(Fable.UnitConstant, None)
                    | Fable.Value(Fable.ThisValue _, r) -> Fable.IdentExpr { selfId with Range = r }
                    | _ -> e |> AST.visit rewriteSelf

                let rec endsWithIdent (name: string) (e: Fable.Expr) =
                    match e with
                    | Fable.IdentExpr id -> id.Name = name
                    | Fable.Sequential xs when not xs.IsEmpty -> endsWithIdent name (List.last xs)
                    | Fable.Let(_, _, b)
                    | Fable.LetRec(_, b) -> endsWithIdent name b
                    | Fable.TypeCast(x, _) -> endsWithIdent name x
                    | _ -> false

                let rec stripReturnIdent (name: string) (e: Fable.Expr) : Fable.Expr =
                    match e with
                    | Fable.IdentExpr id when id.Name = name -> Fable.Value(Fable.UnitConstant, id.Range)
                    | Fable.Sequential xs when not xs.IsEmpty ->
                        let rev = List.rev xs
                        Fable.Sequential(List.rev (stripReturnIdent name rev.Head :: rev.Tail))
                    | Fable.Let(id, v, b) -> Fable.Let(id, v, stripReturnIdent name b)
                    | Fable.LetRec(bs, b) -> Fable.LetRec(bs, stripReturnIdent name b)
                    | Fable.TypeCast(x, _) -> stripReturnIdent name x
                    | other -> Fable.Sequential [ other; Fable.Value(Fable.UnitConstant, None) ]

                let emitOwnFields (values: Fable.Expr list) (r: SourceLocation option) =
                    let ownValues =
                        if values.Length > ownFields.Length then
                            List.skip (values.Length - ownFields.Length) values
                        else
                            values

                    let sets =
                        List.map2
                            (fun (fname, _) (v: Fable.Expr) ->
                                Fable.Set(Fable.IdentExpr selfId, Fable.FieldSet fname, v.Type, rewriteSelf v, r)
                            )
                            ownFields
                            ownValues

                    Fable.Sequential(sets @ [ Fable.Value(Fable.UnitConstant, r) ])

                let isTypeOfClass (entFullName: string) (t: Fable.Type) =
                    match t with
                    | Fable.DeclaredType(c, _) -> c.FullName = entFullName
                    | _ -> false

                let rec initTail (e: Fable.Expr) : Fable.Expr =
                    match e with
                    // Delegating secondary constructor (`new() = C(args)`)
                    | Fable.Call(callee, call, Fable.DeclaredType(c, cArgs), r) when
                        c.FullName = o.FullName && isConstructorCall com call
                        ->
                        Fable.Call(
                            callee,
                            { call with
                                ThisArg = Some(Fable.IdentExpr selfId)
                                Args = call.Args |> List.map rewriteSelf
                                GenericArgs =
                                    if call.GenericArgs.IsEmpty then
                                        cArgs
                                    else
                                        call.GenericArgs
                            },
                            Fable.Unit,
                            r
                        )
                    // Explicit constructor with `then` (`let this = created in (rest; this)`)
                    | Fable.Let(thisId, created, bodyAfter) when
                        isTypeOfClass o.FullName created.Type && endsWithIdent thisId.Name bodyAfter
                        ->
                        Fable.Sequential
                            [
                                initTail created
                                Fable.Let(
                                    thisId,
                                    Fable.IdentExpr selfId,
                                    rewriteSelf (stripReturnIdent thisId.Name bodyAfter)
                                )
                            ]
                    // Derived explicit constructor with compiler-generated base call:
                    // `let base = Base(args) in { inherited @ own }`
                    | Fable.Let(baseId, Fable.Call(baseCallee, baseCall, Fable.DeclaredType(baseRef, bArgs), cr), inner) when
                        o.Parent.IsSome
                        && baseRef.FullName = o.Parent.Value.FullName
                        && isConstructorCall com baseCall
                        ->
                        let bArgs =
                            if baseCall.GenericArgs.IsEmpty then
                                bArgs
                            else
                                baseCall.GenericArgs

                        Fable.Sequential
                            [
                                Fable.Call(
                                    baseCallee,
                                    { baseCall with
                                        ThisArg = Some(Fable.IdentExpr selfId)
                                        Args = baseCall.Args |> List.map rewriteSelf
                                        GenericArgs = bArgs
                                    },
                                    Fable.Unit,
                                    cr
                                )
                                Fable.Let(baseId, Fable.IdentExpr selfId, initTail inner)
                            ]
                    // Explicit constructor record literal (`{ X = ... }`)
                    | Fable.Value(Fable.NewRecord(values, ent, _), r) when
                        ent.FullName = o.FullName && values.Length >= ownFields.Length
                        ->
                        emitOwnFields values r
                    | Fable.Let(id, v, b) -> Fable.Let(id, rewriteSelf v, initTail b)
                    | Fable.LetRec(bs, b) ->
                        Fable.LetRec(bs |> List.map (fun (id, v) -> id, rewriteSelf v), initTail b)
                    | Fable.Sequential xs ->
                        let xs = xs |> List.filter (not << isSysObjCtor)

                        match List.rev xs, o.Parent with
                        | [ x ], _ -> initTail x
                        // (`{ inherit Base(args); Own = x }` when Base has a primary constructor)
                        | Fable.Value(Fable.NewRecord(values, ent, _), r) :: Fable.Call(callee,
                                                                                        call,
                                                                                        Fable.DeclaredType(baseRef,
                                                                                                           bArgs),
                                                                                        cr) :: before,
                          Some p when
                            ent.FullName = o.FullName
                            && baseRef.FullName = p.FullName
                            && isConstructorCall com call
                            && values.Length >= ownFields.Length
                            ->
                            let bArgs =
                                if call.GenericArgs.IsEmpty then
                                    bArgs
                                else
                                    call.GenericArgs

                            let callExpr =
                                Fable.Call(
                                    callee,
                                    { call with
                                        ThisArg = Some(Fable.IdentExpr selfId)
                                        Args = call.Args |> List.map rewriteSelf
                                        GenericArgs = bArgs
                                    },
                                    Fable.Unit,
                                    cr
                                )

                            let setsExpr = emitOwnFields values r
                            let before = before |> List.rev |> List.map rewriteSelf
                            Fable.Sequential(before @ [ callExpr; setsExpr ])
                        | rev, _ ->
                            let before = rev.Tail |> List.rev |> List.map rewriteSelf
                            Fable.Sequential(before @ [ initTail rev.Head ])
                    | Fable.IfThenElse(c, a, b, r) -> Fable.IfThenElse(rewriteSelf c, initTail a, initTail b, r)
                    | Fable.TypeCast(x, _) -> initTail x
                    | _ ->
                        report
                            e.Range
                            $"the Zig target does not support this secondary constructor of %s{o.FullName} yet"

                        e

                [
                    { m with
                        Args = args
                        Body = initTail m.Body
                    }
                ]
            | Fable.MemberDeclaration m -> [ m ]
            | Fable.ModuleDeclaration m -> membersOf m.Members
            // A top-level statement runs when the program starts, in its place among the
            // module-level values. The initializer of a type's static fields (`static let`,
            // `static member val`) gives each its first value.
            | Fable.ActionDeclaration a ->
                let rec flat (e: Fable.Expr) =
                    match e with
                    | Fable.Sequential stmts -> stmts |> List.collect flat
                    | _ -> [ e ]

                let stmts =
                    match a.Body with
                    | Fable.Call(Fable.Delegate(_, body, _, _), _, _, _) -> flat body
                    | body -> flat body

                let value (name: string) (body: Fable.Expr) (isMutable: bool) : Fable.MemberDecl =
                    {
                        Name = name
                        Args = []
                        Body = body
                        MemberRef =
                            Fable.GeneratedMember.Value(name, body.Type, isInstance = false, isMutable = isMutable)
                        IsMangled = false
                        ImplementedSignatureRef = None
                        UsedNames = Set.empty
                        XmlDoc = None
                        Tags = []
                    }

                stmts
                |> List.choose (fun stmt ->
                    match stmt with
                    | Fable.Set(Fable.IdentExpr id, Fable.FieldSet name, _, v, _) when
                        state.StaticFields.ContainsKey(id.Name + "." + name)
                        ->
                        Some(value state.StaticFields[id.Name + "." + name] v true)
                    | Fable.Value(Fable.UnitConstant, _) -> None
                    | _ ->
                        actions <- actions + 1
                        Some(value $"top_level_%d{actions}" stmt false)
                )
            | Fable.ClassDeclaration c ->
                match com.TryGetEntity c.Entity with
                | Some ent ->
                    for f in ent.FSharpFields do
                        if f.IsStatic then
                            let name =
                                c.Name
                                + "__static_"
                                + System.Text.RegularExpressions.Regex.Replace(f.Name, "[^A-Za-z0-9_]", "_")

                            state.StaticFields[c.Name + "." + f.Name] <- name
                            staticTypes[name] <- f.FieldType
                | None -> ()

                match com.TryGetEntity c.Entity with
                | Some ent when ent.IsInterface ->
                    try
                        entOf (newCtx c.Name) None c.Entity |> ignore
                    with ZigError(msg, r) ->
                        report r msg
                // (an attribute: only the compiler looks at it)
                | Some ent when
                    (match ent.BaseType with
                     | Some bt -> bt.Entity.FullName = "System.Attribute"
                     | None -> false)
                    ->
                    ()
                // a class deriving from System.Exception: its constructor makes the exception,
                // of the message given to the base constructor and its fields
                | Some ent when isExceptionClass ent ->
                    try
                        tryExnEnt (newCtx c.Name) None c.Entity |> ignore

                        let message =
                            match c.BaseCall with
                            | Some(Fable.Call(_, info, _, _)) ->
                                match info.Args with
                                | msg :: _ when msg.Type = Fable.String -> msg
                                | _ ->
                                    Fable.Value(
                                        Fable.StringConstant $"Exception of type '%s{ent.FullName}' was thrown.",
                                        None
                                    )
                            | _ ->
                                Fable.Value(
                                    Fable.StringConstant $"Exception of type '%s{ent.FullName}' was thrown.",
                                    None
                                )

                        let fields =
                            (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                            |> List.map (fun f -> f.Name)

                        match c.Constructor with
                        | Some ctor ->
                            let finish (values: Fable.Expr list) =
                                Fable.Value(Fable.NewRecord(message :: values, c.Entity, []), None)

                            attached.Add
                                { ctor with
                                    Body =
                                        constructorBodyWith fields (fieldDefaults (newCtx c.Name) ent) finish ctor.Body
                                }
                        | None -> report None $"the Zig target needs a primary constructor of %s{c.Name}"

                        for m in c.AttachedMembers do
                            report
                                m.Body.Range
                                $"the Zig target does not support this kind of member of an exception class yet (%s{c.Name}.%s{m.Name})"
                    with ZigError(msg, r) ->
                        report r msg
                | Some ent when
                    not (ent.IsFSharpExceptionDeclaration || ent.IsFSharpModule)
                    && (try
                            (objInfo (newCtx c.Name) None c.Entity).IsSome
                        with ZigError(msg, r) ->
                            report r msg
                            false)
                    ->
                    // a class that takes part in inheritance: its constructor computes its
                    // chain of fields; its type and tables of virtual members are emitted
                    let o = (objInfo (newCtx c.Name) None c.Entity).Value

                    try
                        match c.Constructor with
                        | Some ctor ->
                            let selfId, args =
                                match ctor.Args with
                                | first :: _ when first.IsThisArgument -> first, ctor.Args
                                | _ ->
                                    let s = objSelfIdent o
                                    s, s :: ctor.Args

                            attached.Add
                                { ctor with
                                    Args = args
                                    Body =
                                        objConstructorBody
                                            o
                                            selfId
                                            (fieldDefaults (newCtx c.Name) ent)
                                            c.BaseCall
                                            ctor.Body
                                }
                        | None -> ()

                        state.Objs.Add(objDecl (newCtx c.Name) None o (dotnetTypeName com ent))
                    with ZigError(msg, r) ->
                        report r msg

                    // what it overrides, its `default` members, and what it implements
                    attached.AddRange(
                        c.AttachedMembers
                        |> List.choose (fun m ->
                            let info = com.TryGetMember m.MemberRef

                            let compiled =
                                match info with
                                | Some info -> implFnName com info
                                | None -> m.Name

                            if m.Name = "ToString" then
                                Some { m with Name = c.Name + "__ToString" }
                            elif
                                compiled.Contains "."
                                || (
                                    match info with
                                    | Some info ->
                                        info.IsOverrideOrExplicitInterfaceImplementation || info.IsDispatchSlot
                                    | None -> false
                                )
                            then
                                Some { m with Name = implName c.Name compiled }
                            else
                                report
                                    m.Body.Range
                                    $"the Zig target does not support this kind of member yet (%s{c.Name}.%s{m.Name})"

                                None
                        )
                    )
                | Some ent when not (ent.IsFSharpExceptionDeclaration || ent.IsFSharpModule) ->
                    try
                        entOf (newCtx c.Name) None c.Entity |> ignore

                        // a class: its constructor makes the object
                        match c.Constructor with
                        | Some ctor when not (ent.IsFSharpRecord || ent.IsFSharpUnion) ->
                            let genArgs =
                                ent.GenericParameters
                                |> List.map (fun g -> Fable.GenericParam(g.Name, false, []))

                            let fields =
                                (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                                |> List.map (fun f -> f.Name)

                            attached.Add
                                { ctor with
                                    Body =
                                        constructorBody
                                            c.Entity
                                            genArgs
                                            fields
                                            (fieldDefaults (newCtx c.Name) ent)
                                            ctor.Body
                                }
                        | _ -> ()
                    with ZigError(msg, r) ->
                        report r msg

                    // What a type overrides or implements is a function like its other members:
                    // `ToString`, and the members of the interfaces it implements.
                    attached.AddRange(
                        c.AttachedMembers
                        |> List.choose (fun m ->
                            let compiled =
                                match com.TryGetMember m.MemberRef with
                                | Some info -> implFnName com info
                                | None -> m.Name

                            if m.Name = "ToString" then
                                Some { m with Name = c.Name + "__ToString" }
                            elif m.Name = "Equals" || m.Name = "GetHashCode" then
                                Some { m with Name = c.Name + "__" + m.Name }
                            elif compiled.Contains "." then
                                Some { m with Name = implName c.Name compiled }
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

    // (a static field that nothing initializes, `[<DefaultValue>] static val mutable`: its
    // default value)
    let decls =
        let given = decls |> List.map (fun d -> d.Name) |> set

        let defaults =
            staticTypes
            |> Seq.filter (fun kv -> not (given.Contains kv.Key))
            |> Seq.map (fun kv ->
                let body =
                    Fable.Call(
                        Fable.Import(
                            {
                                Selector = "DefaultOf"
                                Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators.Unchecked"
                                Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                            },
                            Fable.Any,
                            None
                        ),
                        Fable.CallInfo.Create(genArgs = [ kv.Value ]),
                        kv.Value,
                        None
                    )

                ({
                    Name = kv.Key
                    Args = []
                    Body = body
                    MemberRef = Fable.GeneratedMember.Value(kv.Key, kv.Value, isInstance = false, isMutable = true)
                    IsMangled = false
                    ImplementedSignatureRef = None
                    UsedNames = Set.empty
                    XmlDoc = None
                    Tags = []
                }
                : Fable.MemberDecl)
            )
            |> List.ofSeq

        defaults @ decls

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

    let effBodyType (info: Fable.MemberFunctionOrValue) (body: Fable.Expr) =
        match info.ReturnParameter.Type with
        | Fable.Nullable(_, false) as n when unwrapNullness n = unwrapNullness body.Type -> n
        | _ -> body.Type

    // What the file declares is known before any body is lowered: bodies call each other.
    for d in decls do
        let info = com.GetMember d.MemberRef

        try
            reserved.Add d.Name |> ignore

            let retFable = effBodyType info d.Body

            if info.IsValue then
                let ty = mapType (newCtx d.Name) d.Body.Range retFable

                // (a static field can be assigned: it is `static let mutable` or the field
                // behind `static member val`)
                members[d.Name] <-
                    if info.IsMutable || state.StaticFields.ContainsValue d.Name then
                        MValue ty
                    else
                        MConst ty
            else
                members[d.Name] <-
                    MFunction(
                        typeParamsOf info,
                        // (a member without parameters, as `[<CLIEvent>]` makes, takes unit)
                        (if d.Args.IsEmpty && not (isEntryPoint info) then
                             [ Fable.Unit ]
                         else
                             d.Args |> List.map (fun a -> a.Type)),
                        retFable
                    )
        with ZigError(msg, r) ->
            report r msg

    for d in decls do
        let info = com.GetMember d.MemberRef
        let typeParams = typeParamsOf info

        let inObjCtor =
            info.IsConstructor
            && (
                match info.DeclaringEntity with
                | Some cls ->
                    (try
                        (objInfo (newCtx d.Name) None cls).IsSome
                     with ZigError _ ->
                         false)
                | None -> false
            )

        let ctx =
            { newCtx d.Name with
                TypeParams = typeParams
                InCtor = inObjCtor
            }

        try
            let retFable = effBodyType info d.Body

            if info.IsValue then
                match members.TryGetValue d.Name, lw ctx (wrapNullCast retFable d.Body) with
                | (true, MConst ty), ELit(text, _) -> state.Consts.Add((d.Name, ty, text))
                // A value that is not a literal is computed when the program starts, by a
                // function of its own, and kept until the program ends.
                | (true, (MConst ty | MValue ty)), body ->
                    let body = coerceTy ctx ty body

                    if true then
                        let init = uniqueName ctx (d.Name + "_init")
                        state.Values.Add((d.Name, ty, init))

                        state.Fns.Add
                            {
                                Name = init
                                TypeParams = []
                                Params = []
                                Modes = []
                                Ret = ty
                                Body = body
                                RetFrom = None
                                Raises = RNever
                                Stores = false
                                IsLocal = false
                                IsEntryPoint = false
                                Range = d.Body.Range
                            }
                | _ -> () // its type was rejected above
            else
                let entry = isEntryPoint info

                let args =
                    if d.Args.IsEmpty then
                        [ AST.makeTypedIdent Fable.Unit "unitVar" ]
                    else
                        d.Args

                let ps =
                    if
                        entry
                        && (d.Args.IsEmpty || d.Args |> List.forall (fun a -> a.Type = Fable.Unit))
                    then
                        [] // (`main ()`)
                    else
                        args
                        |> List.map (fun a ->
                            // (the object a member is called on is not null: the call checks)
                            let ty =
                                match mapType ctx a.Range a.Type with
                                | TOpt t when t = tObj && a.IsThisArgument -> tObj
                                | ty -> ty

                            let v = state.NewVar(a.Name, ty, VParam, false)
                            ctx.Vars[a.Name] <- v
                            v
                        )

                let ret = mapType ctx d.Body.Range retFable
                let d = { d with Body = wrapNullCast retFable (typeTaskBuilders d.Body) }

                // `[<StackArena(bytes)>]`: what the function allocates comes from its stack
                match
                    info.Attributes
                    |> Seq.tryFind (fun a ->
                        a.Entity.FullName.EndsWith("StackArenaAttribute", System.StringComparison.Ordinal)
                    )
                with
                | Some att ->
                    let bytes =
                        match att.ConstructorArgs with
                        | [ :? int as n ] -> n
                        | _ -> fail d.Body.Range "[<StackArena>] needs its size in bytes, as a literal"

                    if isManaged ret || ps |> List.exists (fun p -> isManaged p.Ty) then
                        fail
                            d.Body.Range
                            "%s: a [<StackArena>] function cannot take or give values that live on the heap (they would outlive the arena)"
                            d.Name

                    state.Arenas[d.Name] <- bytes
                | None -> ()

                let body =
                    let raw = lw ctx d.Body

                    if ret = tVoid then
                        raw
                    else
                        coerceTy ctx ret raw

                // a test (xUnit's `[<Fact>]`, NUnit's `[<Test>]`): `zig test` runs it
                if
                    info.Attributes
                    |> Seq.exists (fun a ->
                        let n = a.Entity.FullName

                        n.EndsWith("FactAttribute", System.StringComparison.Ordinal)
                        || n.EndsWith(".TestAttribute", System.StringComparison.Ordinal)
                    )
                then
                    state.Tests.Add((info.DisplayName, d.Name))

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
        with
        // (an `inline` member: F# puts its body in at each use, which compile on their own; its
        // compiled body, which the target cannot make, is never called)
        | ZigError _ when
            (match d.MemberRef with
             | Fable.MemberRef _ ->
                 match com.TryGetMember d.MemberRef with
                 | Some m -> m.IsInline
                 | None -> false
             | _ -> false)
            ->
            ()
        | ZigError(msg, r) ->
            report
                (match r with
                 | Some _ -> r
                 | None -> d.Body.Range)
                msg
        // (a case the target did not foresee: an error at the declaration, not a crash of the
        // whole file)
        | e when not (e :? System.OutOfMemoryException) ->
            report
                d.Body.Range
                $"internal error of the Zig target while compiling %s{d.Name}: %s{e.GetType().Name}: %s{e.Message}"

    settleCyclic state
    settleCycles state
    state
