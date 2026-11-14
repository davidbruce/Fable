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
        /// inside a `for ... in` loop: the enumerator's name, and the variable that holds the
        /// item of this round
        Enumerators: Dictionary<string, Var>
        /// `(ok, value)` of a `TryGet...(&value)` whose value has no default here: the option
        /// that stands for it
        OutTuples: Dictionary<string, Var>
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
                || e.Hooks.IsSome
                || e.Cases |> List.exists (fun (_, fs) -> fs |> List.exists (snd >> isManagedDecl))

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
let settleCyclic (state: FileState) =
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
        | TPrim "fable_rt.Exn"
        | TPrim "fable_rt.Obj" -> [], true
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
let settleCycles (state: FileState) =
    let rec reachesOpaque (t: Ty) : bool =
        match t with
        | TFn _
        | TPrim "fable_rt.Exn"
        | TPrim "fable_rt.Obj" -> true
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
        // (a new object: every field of its chain can be assigned)
        | EEmit(m, [ chain ], TPrim "fable_rt.Obj") when
            m.StartsWith("fable_rt.objNew(", System.StringComparison.Ordinal)
            ->
            let rec fieldsOf (t: Ty) =
                match t with
                | TEnt(e, _) when e.Name.EndsWith("__chain", System.StringComparison.Ordinal) ->
                    caseFields t "" |> List.collect (snd >> fieldsOf)
                | TEnt(e, _) when e.Name.EndsWith("__part", System.StringComparison.Ordinal) ->
                    caseFields t "" |> List.map snd
                | _ -> []

            for fieldTy in fieldsOf (typeOf chain) do
                if reachesOpaque fieldTy then
                    holds <- true
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
let mutable sharedTargetCount = 0

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
                sharedTargetCount <- sharedTargetCount + 1

                let unitArg = AST.makeTypedIdent Fable.Unit "unitVar"

                let args =
                    if ids.IsEmpty then
                        [ unitArg ]
                    else
                        ids

                let fnId =
                    AST.makeTypedIdent
                        (Fable.DelegateType(args |> List.map (fun a -> a.Type), body.Type))
                        $"match_target_%d{sharedTargetCount}"

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
    // (`Nullable<T>`: an option)
    | Fable.Nullable(t, _) -> TOpt(mapType ctx r t)
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
    | Fable.DeclaredType(ent, []) when isWitnessClass ctx ent -> tVoid
    | Fable.DeclaredType(ent, _) when (objInfo ctx r ent).IsSome -> tObj
    // an async computation: the record of the library's Async.fs; the builder has no state
    // (F#'s `Event<'T>`: the record of the library's Event.fs)
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpEvent`1" ->
        TEnt(libRecordEnt ctx "Event" "EventOf_1", [ mapType ctx r item ])
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
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Diagnostics.Stopwatch" ->
        TEnt(libRecordEnt ctx "Stopwatch" "StopwatchOf", [])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.Stack`1" ->
        TEnt(libRecordEnt ctx "Stack" "StackOf_1", [ mapType ctx r item ])
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

        TEnt(
            anonEnt ctx.State (members |> List.map (fun (_, n, _, _) -> n) |> Array.ofList),
            // (functions in the signatures as values have them: uncurried)
            members
            |> List.map (fun (_, _, args, ret) ->
                TFn(
                    args |> List.map (FableTransforms.uncurryType >> mapType ctx r),
                    mapType ctx r (FableTransforms.uncurryType ret)
                )
            )
        )
    | Fable.DeclaredType(ent, genArgs) -> TEnt(entOf ctx r ent, genArgs |> List.map (mapTypeArg ctx r))
    | Fable.Any -> tAny
    | _ -> fail r "the Zig target does not support this type yet (%A)" t

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

        // A class is a reference: a counted cell of its fields, which can all be assigned. An
        // interface is a struct of function values, one for each of its members.
        let isClass =
            not (ent.IsFSharpRecord || ent.IsFSharpUnion || ent.IsInterface || ent.IsFSharpModule)

        if isClass then
            match ent.BaseType with
            // (a struct's base is System.ValueType: it is a plain value here)
            | Some bt when bt.Entity.FullName = "System.ValueType" && ent.IsValueType -> ()
            | Some bt when bt.Entity.FullName <> "System.Object" ->
                fail
                    r
                    "the Zig target does not support inheritance yet (%s inherits %s)"
                    entRef.FullName
                    bt.Entity.FullName
            | _ -> ()

        if not (ent.IsFSharpRecord || ent.IsFSharpUnion || ent.IsInterface || isClass) then
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
            (isClass && not ent.IsValueType)
            || ent.IsFSharpRecord
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
                    if isReference then
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
                    if isClass then
                        (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                        |> List.map (fun f -> f.Name)
                    elif ent.IsFSharpRecord then
                        (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                        |> List.filter (fun f -> f.IsMutable)
                        |> List.map (fun f -> f.Name)
                    else
                        []
                Managed = false
                Cyclic = false
                ReachesOpaque = false
                Copyable = true
                IsLocal = isLocal
                Hooks = None
                Overrides = []
            }

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
                            TFn(
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
                | Some ent when isClassEntity ent && not ent.IsValueType && not (isExceptionClass ent) ->
                    let derives =
                        match ent.BaseType with
                        | Some bt -> bt.Entity.FullName <> "System.Object"
                        | None -> false

                    ignore derives
                    Some ent
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
    match t with
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
            | "TaskOf_1" -> [ "fable_task", TOpt(TEnt(resultEnt ctx.State, [ TGen "T"; tExn ])) ]
            | "TaskSourceOf_1" -> [ "task", TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ TGen "T" ]) ]
            | "ReplyChannelOf_1" -> [ "reply", TFn([ TGen "T" ], tVoid) ]
            // (its body takes the mailbox itself: what a program sees of it is a cell)
            | "MailboxOf_1" ->
                [
                    "queue", TEnt(netEnt ctx.State "ResizeArray", [ TGen "T" ])
                    "waiting", TOpt(TFn([ TGen "T" ], tVoid))
                    "started", tBool
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
            | "CancellationSource" -> [ "cancelled"; "handlers"; "disposed" ]
            | "HandOver" -> [ "handedOver" ]
            | "Timer" -> [ "live" ]
            | "StopwatchOf" -> [ "elapsed"; "startedAt"; "running" ]
            | "TaskOf_1" -> [ "fable_task" ]
            | "MailboxOf_1" -> [ "waiting"; "started" ]
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
let mutable divRemTemps = 0

/// Is this a culture or a format provider given to a .NET method (`CultureInfo.InvariantCulture`)?
let isCulture (x: Fable.Expr) =
    match x.Type with
    | Fable.DeclaredType(e, _) ->
        e.FullName = "System.Globalization.CultureInfo"
        || e.FullName = "System.IFormatProvider"
    | _ -> false

/// (for the names of the values of a printf that is used as a function)
let mutable printfValues = 0

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
            "Empty Singleton Delay OfList OfArray Append Map MapIndexed Filter Where Choose Collect Concat Initialize InitializeInfinite Unfold Take Truncate Skip TakeWhile SkipWhile Zip Indexed Pairwise Iterate IterateIndexed Fold ToList ToArray Length IsEmpty TryHead Head TryLast Last TryItem Item TryFind Find TryPick Pick Exists ForAll Contains Reduce Reverse Sort SortBy SortDescending Distinct Max Min MaxBy MinBy GroupBy CountBy Cache
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

/// Does a declared type (not an interface) implement the interface? None when that is not
/// known here.
let implements (com: Compiler) (t: Fable.Type) (ifaceFullName: string) : bool option =
    match t with
    | Fable.DeclaredType(entRef, _) ->
        match com.TryGetEntity entRef with
        | Some ent when not ent.IsInterface ->
            Some(
                ent.DeclaredInterfaces
                |> Seq.exists (fun i -> i.Entity.FullName = ifaceFullName)
            )
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
    match t with
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

    {
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

/// The constructor of a class that takes part in inheritance: the chain of its fields, the
/// parent's (which its constructor computes, first) and its own.
let objConstructorBody
    (o: ObjInfo)
    (defaults: string -> Fable.Expr option)
    (baseCall: Fable.Expr option)
    (body: Fable.Expr)
    : Fable.Expr
    =
    let fields = caseFields (TEnt(o.Part, [])) "" |> List.map fst

    let baseId (t: Fable.Type) : Fable.Ident =
        {
            Name = "base_chain"
            Type = t
            IsMutable = false
            IsThisArgument = false
            IsCompilerGenerated = true
            Range = None
            IsInlineIfLambda = false
        }

    let finish (values: Fable.Expr list) =
        let own = Fable.Value(Fable.NewRecord(values, o.Part.Ref, ownArgs o), None)

        let chain =
            match o.Parent with
            | Some p -> [ Fable.IdentExpr(baseId (chainTypeOf p o.ParentArgs)); own ]
            | None -> [ own ]

        Fable.Value(Fable.NewRecord(chain, o.Chain.Ref, ownArgs o), None)

    let inner = constructorBodyWith fields defaults finish body

    match o.Parent, baseCall with
    | Some p, Some(Fable.Call(callee, info, _, r)) ->
        Fable.Let(baseId (chainTypeOf p o.ParentArgs), Fable.Call(callee, info, chainTypeOf p o.ParentArgs, r), inner)
    | Some _, _ ->
        raise (
            ZigError($"the Zig target does not support this call of the base constructor of %s{o.FullName} yet", None)
        )
    | None, _ -> inner

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
    | _ -> false

/// Has this type a default value here (what .NET's is: zero, false, null of a string, None)?
let rec hasDefault (t: Fable.Type) : bool =
    match t with
    | Fable.Number _
    | Fable.Char
    | Fable.Boolean
    | Fable.String
    | Fable.Unit
    | Fable.Option _ -> true
    | Fable.Tuple(ts, _) -> List.forall hasDefault ts
    | _ -> false

/// The default value of a class's field the constructor does not set (`[<DefaultValue>] val
/// mutable`), if its type has one
let fieldDefaults (ent: Fable.Entity) (name: string) : Fable.Expr option =
    ent.FSharpFields
    |> List.tryFind (fun f -> f.Name = name && not f.IsStatic && hasDefault f.FieldType)
    |> Option.map (fun f ->
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
            Fable.CallInfo.Create(genArgs = [ f.FieldType ]),
            f.FieldType,
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

/// Whether a type is another with obj in some of its places
let rec moreGeneral (t: Fable.Type) (wanted: Fable.Type) : bool =
    match t, wanted with
    | Fable.Any, _ -> true
    | Fable.LambdaType(a, r), Fable.LambdaType(a2, r2) -> moreGeneral a a2 && moreGeneral r r2
    | _ -> t = wanted

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
        // (a value boxed and unboxed again)
        | Fable.TypeCast(inner, Fable.Any), _ when inner.Type = wanted -> inner
        // (an object where a value of a type is wanted: unboxed)
        | _, _ when e.Type = Fable.Any && not (hasTypeParams wanted) && wanted <> Fable.Any ->
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

let rec lw (ctx: Ctx) (e: Fable.Expr) : Expr =
    match e with
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
    // `Circle 1.0`: the constructor computes the chain of fields; the object is made of it
    | Fable.Call(callee, info, Fable.DeclaredType(cls, clsArgs), r) when
        isConstructorCall ctx.Com info && (objInfo ctx r cls).IsSome
        ->
        let o = (objInfo ctx r cls).Value

        if o.IsAbstract then
            fail r "the abstract class %s cannot be made" o.FullName

        let typeRef = objTypeRef o (clsArgs |> List.map (mapTypeArg ctx r))

        let made =
            bindArgs
                ctx
                [ lw ctx (Fable.Call(callee, info, chainTypeOf o clsArgs, r)) ]
                (fun xs -> EEmit($"fable_rt.objNew(%s{typeRef}, $0)", xs, tObj))

        // (`type C() as this`, here or in a class above: its self reference is the object)
        let selfFields =
            let rec levels (o: ObjInfo) =
                o
                :: (
                    match o.Parent with
                    | Some p -> levels p
                    | None -> []
                )

            levels o
            |> List.collect (fun level ->
                match ctx.Com.TryGetEntity level.Ref with
                | Some ent ->
                    ent.FSharpFields
                    |> List.filter (fun f ->
                        not f.IsStatic && isSelfRefType (Fable.DeclaredType(level.Ref, [])) f.FieldType
                    )
                    |> List.map (fun f -> f.Name, selfRefType f.FieldType)
                | None -> []
            )

        if selfFields.IsEmpty then
            made
        else
            let objT = Fable.DeclaredType(cls, [])
            let objId = AST.makeTypedIdent objT "made"
            let v = ctx.State.NewVar("made", tObj, VLocal, false)
            ctx.Vars[objId.Name] <- v

            let fills =
                selfFields
                |> List.map (fun (name, refT) ->
                    let optT, itemT =
                        match refT with
                        | Fable.DeclaredType(_, [ Fable.Option(c, _) as o ]) -> o, c
                        | _ -> fail r "internal: a self reference"

                    let fieldInfo: Fable.FieldInfo =
                        {
                            Name = name
                            FieldType = Some refT
                            IsMutable = true
                            MaybeCalculated = false
                            Tags = []
                        }

                    Fable.Set(
                        Fable.Get(Fable.IdentExpr objId, Fable.GetKind.FieldGet fieldInfo, refT, r),
                        Fable.FieldSet "contents",
                        optT,
                        Fable.Value(
                            Fable.NewOption(Some(Fable.TypeCast(Fable.IdentExpr objId, itemT)), itemT, false),
                            r
                        ),
                        r
                    )
                )

            ELet(v, made, ESeq(lwStmt ctx (Fable.Sequential fills), EVar v))
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
            (fun xs ->
                let fn =
                    EGet(EEmit($"fable_rt.objVt($R, $0, %d{level.Depth})", [ xs.Head ], table), PField slot, slotTy)

                ECallClo(fn, xs, mapType ctx r t)
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
            (fun xs ->
                let fn =
                    EGet(EEmit($"fable_rt.objVt($R, $0, %d{level.Depth})", [ xs.Head ], table), PField slot, slotTy)

                ECallClo(fn, [ xs.Head; EUnit ], mapType ctx r t)
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
            (fun xs ->
                EGet(
                    EEmit($"fable_rt.objPart($R, &[_]type{{ %s{parts} }}, $0)", xs, TPtr(part, false)),
                    PField field.Name,
                    fty
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
        let fty = caseFields part "" |> List.find (fun (f, _) -> f = name) |> snd
        let parts = partNamesOf ctx r level largs

        bindArgs
            ctx
            [ lw ctx x; lw ctx value ]
            (fun xs ->
                let place =
                    EGet(
                        EEmit($"fable_rt.objPart($R, &[_]type{{ %s{parts} }}, $0)", [ xs[0] ], TPtr(part, false)),
                        PField name,
                        fty
                    )

                EStore(place, xs[1])
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
    // `o :? T` of an `obj` (not one F# made by boxing a value of a known type, as `use` does)
    | Fable.Test(x, Fable.TypeTest t, r) when x.Type = Fable.Any && (let (Unboxed inner) = x in inner.Type = Fable.Any) ->
        match t with
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
            let found = ctx.State.NewVar("unboxed", TOpt(mapType ctx r t), VLocal, false)

            bindArgs
                ctx
                [ lw ctx x ]
                (fun xs ->
                    ELet(
                        found,
                        EEmit("fable_rt.tryUnbox($R, $0)", xs, TOpt(mapType ctx r t)),
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
        | Fable.Null Fable.String -> ELit("@as(fable_rt.String, null)", tStr)
        | Fable.Null Fable.Any ->
            ctx.State.UsesRuntime <- true
            ELit("@as(fable_rt.Any, null)", tAny)
        | Fable.Null Fable.MetaType ->
            ctx.State.UsesRuntime <- true
            EEmit("fable_rt.reflect.nullType()", [], TPrim "fable_rt.reflect.Type")
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
            bindArgsIn true ctx (values |> List.map (lw ctx)) (fun xs -> ECon(ty, "", xs, None))
        | Fable.NewUnion(values, tag, entRef, genArgs) ->
            let ent = entOf ctx r entRef
            let ty = TEnt(ent, genArgs |> List.map (mapTypeArg ctx r))
            let case = fst (List.item tag ent.Cases)
            bindArgsIn true ctx (values |> List.map (lw ctx)) (fun xs -> ECon(ty, case, xs, None))
        | Fable.NewTuple(values, _) ->
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

            bindArgsIn true ctx (values |> List.map (lw ctx)) (fun xs -> ECon(ty, "", xs, None))
        // `[| a; b |]`, and an array of a given length
        | Fable.NewArray(Fable.ArrayValues values, t, _) ->
            let ty = TEnt(arrayEnt ctx.State, [ mapTypeArg ctx r t ])
            let holes = values |> List.mapi (fun i _ -> $"$%d{i}") |> String.concat ", "

            bindArgs
                ctx
                (values |> List.map (lw ctx))
                (fun xs -> EEmit($"fable_rt.arrayOf($R, .{{ %s{holes} }})", xs, ty))
        | Fable.NewArray(Fable.ArrayAlloc size, t, _) ->
            let ty = TEnt(arrayEnt ctx.State, [ mapTypeArg ctx r t ])
            bindArgs ctx [ lw ctx size ] (fun xs -> ERt("fable_rt.arrayZero($R, $0)", xs, ty))
        | Fable.NewArray(Fable.ArrayFrom(Uncast source), t, _) when source.Type = Fable.List t ->
            let ty = TEnt(arrayEnt ctx.State, [ mapTypeArg ctx r t ])
            bindArgs ctx [ lw ctx source ] (fun xs -> EEmit("fable_rt.arrayOfList($R, $0)", xs, ty))
        | Fable.NewList(headAndTail, t) ->
            let ty = mapType ctx r (Fable.List t)

            match headAndTail with
            | Some(head, tail) ->
                bindArgsIn true ctx [ lw ctx head; lw ctx tail ] (fun xs -> ECon(ty, "Cons", xs, None))
            | None -> ECon(ty, "Empty", [], None)
        // (a `None` whose item type Fable lost: Zig's `null` fits the option it is given to)
        | Fable.NewOption(None, Fable.Any, _) -> ELit("null", TOpt tVoid)
        | Fable.NewOption(value, t, isStruct) ->
            let ty = mapType ctx r (Fable.Option(t, isStruct))

            match value with
            | Some v -> bindArgsIn true ctx [ lw ctx v ] (fun xs -> ECon(ty, "Some", xs, None))
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
        && not (hasDefault out.Type)
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

                ELet(
                    restV,
                    source,
                    EWhile(
                        EPrim("not", [ ETest(EVar restV, "Empty", listTy) ], tBool),
                        ELet(
                            cur,
                            EGet(EVar restV, PCase("Cons", "Head"), itemTy),
                            ESeq(EAssign(restV, EGet(EVar restV, PCase("Cons", "Tail"), listTy)), lwStmt ctx loopBody)
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
                                ESeq(EAssign(i, EPrim("add", [ EVar i; ELit("1", tI32) ], tI32)), lwStmt ctx loopBody)
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

        ctx.Vars[id.Name] <- v
        ctx.Boxed.Add id.Name |> ignore
        ELet(v, rhs, lw ctx body)

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
        ctx.Vars[id.Name] <- v
        ELet(v, place, lw ctx body)

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

    // `x :? IDisposable` where the type of x is known (what `use` asks): true if the type
    // implements the interface
    // (.NET's enumerators are disposable: what `use e = s.GetEnumerator()` in inlined code asks)
    | Fable.Test(Unboxed inner, Fable.TypeTest(Fable.DeclaredType(ifaceRef, _)), _) when
        ifaceRef.FullName = "System.IDisposable"
        && (
            match inner.Type with
            | Fable.DeclaredType(e, _) -> e.FullName = "System.Collections.Generic.IEnumerator`1"
            | _ -> false
        )
        ->
        ESeq(lwStmt ctx inner, ELit("true", tBool))
    // (a value of the interface itself: it is one)
    | Fable.Test(Unboxed inner, Fable.TypeTest(Fable.DeclaredType(ifaceRef, _) as ifaceType), _) when
        isInterfaceType ctx.Com ifaceType
        && (
            match inner.Type with
            | Fable.DeclaredType(e, _) -> e.FullName = ifaceRef.FullName
            | _ -> false
        )
        ->
        ESeq(lwStmt ctx inner, ELit("true", tBool))
    | Fable.Test(Unboxed inner, Fable.TypeTest(Fable.DeclaredType(ifaceRef, _) as ifaceType), _) when
        isInterfaceType ctx.Com ifaceType
        && (implements ctx.Com inner.Type ifaceRef.FullName).IsSome
        ->
        ESeq(
            lwStmt ctx inner,
            ELit(
                string ((implements ctx.Com inner.Type ifaceRef.FullName).Value)
                |> fun b -> b.ToLowerInvariant(), tBool
            )
        )

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
                (implements ctx.Com inner.Type (imp.Path.Substring Replacements.DotnetPrefix.Length)) = Some true
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
                (fun xs -> ECall(target, genArgs |> List.map (mapTypeArg ctx r), xs, mapType ctx r t))
        | _ -> fail r "internal: not a declared type"

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
    // a member of an interface: a field of its struct of function values (a property is read
    // by calling its getter)
    | Fable.Get(x, Fable.FieldGet info, t, r) when isInterfaceType ctx.Com x.Type ->
        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let fields = caseFields (typeOf xs.Head) ""
                // (a mangled interface's member is named in full: `Ns.IFoo.get_Bar`)
                let name = info.Name.Substring(info.Name.LastIndexOf '.' + 1)

                // (and its overload's hash, `SumZ35CD86D0`)
                let name =
                    if fields |> List.exists (fun (f, _) -> f = name || f = "get_" + name) then
                        name
                    else
                        System.Text.RegularExpressions.Regex.Replace(name, "Z?[0-9A-F]{8}$", "")

                // (an overload: the one whose hash Fable gave the name, `get_ItemZ524259A4`)
                let name =
                    if fields |> List.exists (fun (f, _) -> f = name || f = "get_" + name) then
                        name
                    else
                        let full = info.Name.Substring(info.Name.LastIndexOf '.' + 1)

                        match x.Type with
                        | Fable.DeclaredType(iref, _) ->
                            match ctx.Com.TryGetEntity iref with
                            | Some ient ->
                                let genParams = ient.GenericParameters |> List.map (fun g -> g.Name)

                                ient.MembersFunctionsAndValues
                                |> Seq.filter (fun m -> m.IsDispatchSlot && m.CompiledName = name)
                                |> Seq.tryFind (fun m ->
                                    let groups = m.CurriedParameterGroups |> List.map (List.map (fun p -> p.Type))

                                    full = name + OverloadSuffix.getHash genParams groups
                                )
                                |> Option.map (fun m -> slotKey ient m.CompiledName (paramTypesOf m))
                                |> Option.defaultValue name
                            | None -> name
                        | _ -> name

                match fields |> List.tryFind (fun (f, _) -> f = name) with
                | Some(f, fty) -> EGet(xs.Head, PField f, fty)
                | None ->
                    match fields |> List.tryFind (fun (f, _) -> f = "get_" + name) with
                    | Some(f, fty) -> ECallClo(EGet(xs.Head, PField f, fty), [ EUnit ], mapType ctx r t)
                    | None -> fail r "the Zig target cannot find the member %s of this interface (%A)" info.Name t
            )

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
    // a value of a .NET interface seen as one it inherits (an `IEvent` as an `IObservable`): the
    // struct of the other's members, taken from it
    | Fable.TypeCast(x, (Fable.DeclaredType(target, _) as targetType)) when
        (match target.Path with
         | Fable.SourcePath _ -> false
         | _ -> true)
        && (
            match x.Type with
            | Fable.DeclaredType(source, _) ->
                source.FullName <> target.FullName
                && (
                    match source.Path with
                    | Fable.SourcePath _ -> false
                    | _ -> true
                )
                && (
                    match ctx.Com.TryGetEntity source, ctx.Com.TryGetEntity target with
                    | Some s, Some t -> s.IsInterface && t.IsInterface
                    | _ -> false
                )
            | _ -> false
        )
        // (both structs of members: not a sequence, a dictionary, ..., which are what they are)
        && (let isStruct (ty: Ty) =
                match ty with
                | TEnt(e, _) -> e.Name.StartsWith("fable_anon_", System.StringComparison.Ordinal)
                | _ -> false

            isStruct (mapType ctx e.Range targetType)
            && isStruct (mapType ctx e.Range x.Type))
        ->
        let targetTy = mapType ctx e.Range targetType

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let fromFields = caseFields (typeOf xs.Head) ""

                let values =
                    caseFields targetTy ""
                    |> List.map (fun (f, fty) ->
                        match fromFields |> List.tryFind (fun (g, _) -> g = f) with
                        | Some(_, gty) -> EDup(EGet(xs.Head, PField f, gty), gty)
                        | None -> fail e.Range "the Zig target cannot see %A as %A yet" x.Type targetType
                    )

                ECon(targetTy, "", values, None)
            )
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
    // an interface given where an interface it inherits is expected: the members that one has
    | Fable.TypeCast(x, (Fable.DeclaredType _ as ifaceType)) when
        isInterfaceType ctx.Com ifaceType
        && isInterfaceType ctx.Com x.Type
        && mapType ctx e.Range ifaceType <> mapType ctx e.Range x.Type
        ->
        let ifaceTy = mapType ctx e.Range ifaceType

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let members =
                    caseFields ifaceTy "" |> List.map (fun (f, fty) -> EGet(xs.Head, PField f, fty))

                ECon(ifaceTy, "", members, None)
            )

    // a value given where an interface is expected: each member, a function value that
    // holds the object
    | Fable.TypeCast(x, (Fable.DeclaredType(ifaceRef, _) as ifaceType)) when
        isInterfaceType ctx.Com ifaceType && not (isInterfaceType ctx.Com x.Type)
        ->
        let ifaceTy = mapType ctx e.Range ifaceType

        let typeName, typeArgs =
            match x.Type with
            | Fable.DeclaredType(classRef, genArgs) ->
                classPrefix ctx e.Range classRef (Some ifaceRef.FullName), genArgs |> List.map (mapType ctx e.Range)
            | other -> fail e.Range "the Zig target cannot make an interface of a value of this type yet (%A)" other

        let classRef =
            match x.Type with
            | Fable.DeclaredType(classRef, _) -> classRef
            | _ -> fail e.Range "internal: not a declared type"

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let members =
                    caseFields ifaceTy ""
                    |> List.map (fun (f, fty) ->
                        EClosure(interfaceImpl ctx e.Range classRef ifaceRef.FullName f, typeArgs, [ xs.Head ], fty)
                    )

                ECon(ifaceTy, "", members, None)
            )

    // `{ new IShape with ... }`: each member, a function value of its own
    // `{ new Shape("x") with member _.Area() = ... }`: an object of a class of its own that
    // derives from Shape. Its fields are the function values of its members (which hold what
    // they capture); its table calls them.
    | Fable.ObjectExpr(members, Fable.DeclaredType(baseRef, _), Some(Fable.Call(callee, call, _, cr))) when
        (objInfo ctx e.Range baseRef).IsSome
        ->
        let parent = (objInfo ctx e.Range baseRef).Value
        let n = ctx.State.ObjInfos.Count
        let prefix = $"%s{cleanIdent ctx.FnBase}__obj%d{n}"

        let slots =
            members
            |> List.map (fun m ->
                let slot =
                    match ctx.Com.TryGetMember m.MemberRef with
                    | Some info -> info.CompiledName
                    | None -> m.Name

                match virtualSlot parent slot with
                | Some(_, ty) -> slot, ty, m
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
                TypeParams = []
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
        let chain = synth "chain" [ "base", TEnt(parent.Chain, []); "own", TEnt(part, []) ]

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
                Gens = []
                ParentArgs = []
            }

        ctx.State.ObjInfos[info.FullName] <- box info
        let overridden = slots |> List.map (fun (slot, _, _) -> slot) |> set

        let tables =
            ancestors info
            |> List.rev
            |> List.map (fun level ->
                match level.Table with
                | Some vt ->
                    let entries =
                        level.Slots
                        |> List.map (fun (slot, slotTy) ->
                            let target =
                                if overridden.Contains slot then
                                    "@raw:" + prefix + "__" + slot
                                else
                                    implementationOf ctx.Com e.Range parent slot

                            slot, target, ([]: Ty list), slotTy
                        )

                    Some(TEnt(vt, []), entries)
                | None -> None
            )

        ctx.State.Objs.Add
            {
                TypeName = prefix + "__type"
                TypeParams = []
                Chain = TEnt(chain, [])
                DotnetName = parent.FullName.Substring(parent.FullName.LastIndexOf '.' + 1) + "@" + string n
                Parent = Some(objTypeRef parent [])
                Tables = tables
                ToString =
                    ancestors parent
                    |> List.tryFind (fun k -> classImplements ctx.Com k "ToString")
                    |> Option.map (fun k -> k.Prefix + "__ToString", ([]: Ty list))
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
                Thunks =
                    slots
                    |> List.map (fun (slot, ty, _) ->
                        prefix + "__" + slot, TPtr(TEnt(part, []), false), partNames info, slot, ty
                    )
            }

        let baseChain = Fable.Call(callee, call, chainType parent, cr)

        let closures =
            slots |> List.map (fun (_, _, m) -> Fable.Delegate(m.Args, m.Body, None, []))

        let value =
            Fable.Value(
                Fable.NewRecord(
                    [ baseChain; Fable.Value(Fable.NewRecord(closures, part.Ref, []), None) ],
                    chain.Ref,
                    []
                ),
                None
            )

        bindArgs ctx [ lw ctx value ] (fun xs -> EEmit($"fable_rt.objNew(&%s{objTypeName info}, $0)", xs, tObj))

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
        let ifaceTy = mapType ctx e.Range ifaceType

        let rec usesIdent (name: string) (e: Fable.Expr) =
            match e with
            | Fable.IdentExpr id -> id.Name = name
            | _ -> getSubExpressions e |> List.exists (usesIdent name)

        // (two members of one name, as `IEnumerator<'T>.Current` and `IEnumerator.Current`: the one
        // whose result is the type the struct keeps)
        let candidates =
            members
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
                    | TFn(_, ret) -> mapType ctx e.Range m.Body.Type = ret
                    | _ -> false

                let notObj (m: Fable.ObjectExprMember) = m.Body.Type <> Fable.Any

                several
                |> List.tryFind (snd >> returns)
                |> Option.orElse (several |> List.tryFind (snd >> notObj))
                |> Option.defaultValue several.Head
                |> snd
                |> Some

        let closures =
            caseFields ifaceTy ""
            |> List.map (fun (f, fty) ->
                match pick f fty with
                | Some m ->
                    match m.Args with
                    | this :: args ->
                        if usesIdent this.Name m.Body then
                            fail e.Range "the Zig target does not support `this` in an object expression yet"

                        lw ctx (Fable.Delegate(args, m.Body, None, []))
                    | [] -> fail e.Range "internal: a member without its object"
                | None -> fail e.Range "the Zig target cannot find the member %s in this object expression" f
            )

        bindArgsIn true ctx closures (fun xs -> ECon(ifaceTy, "", xs, None))

    | Fable.Get(x, kind, t, r) ->
        let ty = mapType ctx r t

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let v = xs.Head

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

        // (an argument made at a more general type than the parameter's, see adaptTo)
        let allArgs =
            match tryCallable ctx callee with
            | Some c when
                c.ArgTypes.Length = allArgs.Length
                && c.TypeParams.Length = info.GenericArgs.Length
                && allArgs |> List.exists (fun a -> hasTypeParams a.Type |> not)
                ->
                let subst = List.zip c.TypeParams info.GenericArgs |> Map.ofList

                List.map2
                    (fun (p: Fable.Type) (a: Fable.Expr) ->
                        let wanted = substFableType subst p

                        if hasTypeParams wanted then
                            a
                        else
                            adaptTo ctx.Com wanted a
                    )
                    c.ArgTypes
                    allArgs
            | _ -> allArgs

        let args = allArgs |> List.map (lw ctx)

        match tryCallable ctx callee, callee with
        | Some c, _ ->
            let typeArgs, _ =
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

                    Seq.foldBack
                        (fun (v, x) body -> ELet(v, x, body))
                        temps
                        (ECall(c.Target, typeArgs, c.Captures @ xs, ty))
                )
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
    // (a property of an interface: by calling its setter, a field of its struct)
    | Fable.Set(x, Fable.FieldSet name, _, value, r) when isInterfaceType ctx.Com x.Type ->
        bindArgs
            ctx
            [ lw ctx x; lw ctx value ]
            (fun xs ->
                // (a mangled interface's member is named in full: `Ns.IFoo.set_Bar`)
                let short = name.Substring(name.LastIndexOf '.' + 1)

                let setter =
                    if short.StartsWith("set_", System.StringComparison.Ordinal) then
                        short
                    else
                        "set_" + short

                match caseFields (typeOf xs[0]) "" |> List.tryFind (fun (f, _) -> f = setter) with
                | Some(f, fty) -> ECallClo(EGet(xs[0], PField f, fty), [ xs[1] ], tVoid)
                | None -> fail r "the Zig target cannot find the setter of %s of this interface" name
            )
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

    | Fable.Set(Fable.IdentExpr id, Fable.ValueSet, _, value, r) when ctx.Boxed.Contains id.Name ->
        let cell = EGet(EVar ctx.Vars[id.Name], PField "contents", mapType ctx r id.Type)
        bindArgs ctx [ lw ctx value ] (fun xs -> EStore(cell, xs.Head))

    | Fable.Set(Fable.IdentExpr id, Fable.ValueSet, _, value, r) ->
        match ctx.Vars.TryGetValue id.Name, ctx.Members.TryGetValue id.Name with
        | (true, ({ Ty = TPtr(t, _) } as v)), _ ->
            bindArgs ctx [ lw ctx value ] (fun xs -> EStore(EDeref(EVar v, t), xs.Head))
        | (true, v), _ -> EAssign(v, lw ctx value)
        // (a module-level value: what it held is given up once the new value is in place)
        | _, (true, MValue ty) ->
            ctx.State.UsesRuntime <- true

            bindArgs
                ctx
                [ lw ctx value ]
                (fun xs ->
                    EEmit("fable_rt.store(&$0, fable_rt.dup($1))", [ globalVar id.Name ty true; xs.Head ], tVoid)
                )
        | _ -> fail r "the Zig target cannot assign to `%s`" id.Name

    | Fable.Set(Fable.Import(imp, t, _), Fable.ValueSet, _, value, r) when (importedValue ctx imp).IsSome ->
        let name, _ = (importedValue ctx imp).Value
        let ty = mapType ctx r t
        ctx.State.UsesRuntime <- true

        bindArgs
            ctx
            [ lw ctx value ]
            (fun xs -> EEmit("fable_rt.store(&$0, fable_rt.dup($1))", [ globalVar name ty true; xs.Head ], tVoid))

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

    // (`box e.InnerException`: null when there is none)
    | Fable.TypeCast(Fable.Call(Fable.Import(imp, _, _), info, _, _), Fable.Any) when
        imp.Selector = "get_InnerException" && info.ThisArg.IsSome
        ->
        ctx.State.UsesRuntime <- true
        bindArgs ctx [ lw ctx info.ThisArg.Value ] (fun xs -> EEmit("fable_rt.exnInnerBoxed($0)", xs, tAny))
    // `x :> obj` and `box x`: an object holds it
    | Fable.TypeCast(x, Fable.Any) when x.Type <> Fable.Any -> boxed ctx x
    // `o :?> T` of an `obj`
    | Fable.TypeCast(x, t) when x.Type = Fable.Any && t <> Fable.Any -> unboxed ctx e.Range x t
    | Fable.TypeCast(x, t) ->
        let ir = lw ctx x

        if typeOf ir = mapType ctx e.Range t then
            ir
        else
            fail e.Range "the Zig target does not support %s yet" (exprKind e)

    // Pattern matching arrives as a decision tree whose leaves name a target and the values
    // its variables are bound to. A target reached from several leaves is lowered once per leaf.
    | Fable.DecisionTree(expr, targets) ->
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
    match t with
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

    match t with
    | Fable.DeclaredType(cls, gs) when (objInfo ctx r cls).IsSome ->
        let o = (objInfo ctx r cls).Value
        let typeRef = objTypeRef o (gs |> List.map (mapTypeArg ctx r))
        bindArgs ctx [ lw ctx x ] (fun xs -> ERt($"fable_rt.anyToClass($0, %s{typeRef})", xs, tObj))
    | _ -> bindArgs ctx [ lw ctx x ] (fun xs -> ERt("fable_rt.unbox($R, $0)", xs, mapType ctx r t))

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
        x.Type = Fable.Any && info.GenericArgs.Length = 1
        ->
        lw ctx (Fable.Test(x, Fable.TypeTest info.GenericArgs.Head, r))
    // `x :? T` where Fable keeps it a call: of an exception class, or of a class of objects
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "TypeTestGeneric", [ x ] when
        (match info.GenericArgs with
         | [ Fable.DeclaredType(cls, _) ] -> (tryExnEnt ctx r cls).IsSome || (objInfo ctx r cls).IsSome
         | _ -> false)
        ->
        match info.GenericArgs with
        | [ Fable.DeclaredType(cls, _) ] when (tryExnEnt ctx r cls).IsSome ->
            let ent = (tryExnEnt ctx r cls).Value
            bindArgs ctx [ lw ctx x ] (fun xs -> EExnTest(xs.Head, ent))
        | [ Fable.DeclaredType(cls, gs) ] ->
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
            rt $"fable_rt.objCast($0, %s{objTypeRef o (objArgs ctx r t)})" [ x ] tObj
    // (a cast that changes nothing here: an exception of a known class is an `exn`)
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", ("UnboxFast" | "UnboxGeneric"), [ x ] when
        mapType ctx r x.Type = mapType ctx r t
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
    | "System.Exception", "get_InnerException", [ x ] -> rt "fable_rt.exnInner($0)" [ x ] tExn
    | "Microsoft.FSharp.Core.Operators", "IsNull", [ Fable.Call(Fable.Import(imp, _, _), inner, _, _) ] when
        imp.Selector = "get_InnerException"
        ->
        pure' "fable_rt.exnHasNoInner($0)" [ inner.ThisArg.Value ] tBool
    | "System.Exception", "get_Message", x :: _ ->
        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.exnMessage($0)", xs, tStr))
    | "System.Exception", "get_StackTrace", x :: _ ->
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
    | "Microsoft.FSharp.Core.Operators", "Box", [ x ] when x.Type <> Fable.Any -> boxed ctx x
    | "Microsoft.FSharp.Core.Operators", "Box", [ x ] -> lw ctx x
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"),
      ("Unbox" | "UnboxGeneric" | "UnboxFast"),
      [ Uncast x ] when x.Type = Fable.Any && t <> Fable.Any -> unboxed ctx r x t
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
            | Uncast inner when inner.Type <> Fable.Any -> Fable.TypeCast(inner, Fable.Any)
            | _ -> x

        pure' "fable_rt.eql($0, $1)" [ asObj a; asObj b ] tBool
    | "System.Object", "GetHashCode", [ x ] -> pure' "fable_rt.hash($0)" [ x ] tI32
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
        let n = divRemTemps
        divRemTemps <- divRemTemps + 1
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
    | "System.Char", "Parse", [ x ] when x.Type = Fable.String -> rt "fable_rt.strToChar($0)" [ x ] (TPrim "u16")
    // text to numbers: F#'s conversions read `0x`, `0o`, `0b` and `_`; .NET's `Parse` does not
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.ExtraTopLevelOperators"), _, [ x ] when
        name.StartsWith("To", System.StringComparison.Ordinal) && x.Type = Fable.String
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
        (match provider.Type with
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
        rt "fable_rt.listSumBy($R, $0, $1)" [ f; xs ] (mapType ctx r t)
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
        rt "fable_rt.arraySumBy($R, $0, $1)" [ f; a ] (mapType ctx r t)
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

        match libraryFunction entity name with
        | Some(file, fn) -> libraryCall ctx r file fn info args t
        | None -> fail r "the Zig target does not support %s.%s yet" entity name

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
        | "Seq", "concat", [ coll; t ], [ source ] when not (isSeqType coll) ->
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
        | "Seq", "concat", [ _; t ], _ ->
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
            Enumerators = Dictionary()
            OutTuples = Dictionary()
            CaughtExn = None
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
            // a secondary constructor of a class: like the primary one, it gives the chain of
            // fields (that the primary constructor computes)
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

                let rec chainTail (e: Fable.Expr) : Fable.Expr =
                    match e with
                    | Fable.Call(callee, call, Fable.DeclaredType(c, _), r) when
                        c.FullName = o.FullName && isConstructorCall com call
                        ->
                        Fable.Call(callee, call, chainTypeOf o (ownArgs o), r)
                    // (`new(x) = { X = x; ... }` of a class without a base: its fields are the
                    // whole chain)
                    | Fable.Value(Fable.NewRecord(values, ent, _), r) when
                        ent.FullName = o.FullName
                        && o.Parent.IsNone
                        && values.Length = (caseFields (TEnt(o.Part, [])) "").Length
                        ->
                        let own = Fable.Value(Fable.NewRecord(values, o.Part.Ref, ownArgs o), r)
                        Fable.Value(Fable.NewRecord([ own ], o.Chain.Ref, ownArgs o), r)
                    | Fable.Let(id, v, b) -> Fable.Let(id, v, chainTail b)
                    | Fable.LetRec(bs, b) -> Fable.LetRec(bs, chainTail b)
                    | Fable.Sequential xs ->
                        // (`inherit obj()`, which F# puts first, makes nothing here)
                        let xs =
                            xs
                            |> List.filter (fun x ->
                                match x with
                                | Fable.Call(Fable.Import(imp, _, _), _, _, _) ->
                                    not (
                                        imp.Selector = ".ctor"
                                        && imp.Path = Replacements.DotnetPrefix + "System.Object"
                                    )
                                | _ -> true
                            )

                        match List.rev xs, o.Parent with
                        | [ x ], _ -> chainTail x
                        // (`{ inherit Base(args); Own = x }`: the base's chain, then this class's
                        // part)
                        | Fable.Value(Fable.NewRecord(values, ent, _), r) :: Fable.Call(callee,
                                                                                        call,
                                                                                        Fable.DeclaredType(baseRef, _),
                                                                                        cr) :: before,
                          Some p when
                            ent.FullName = o.FullName
                            && baseRef.FullName = p.FullName
                            && isConstructorCall com call
                            && values.Length = (caseFields (TEnt(o.Part, [])) "").Length
                            ->
                            let baseId = AST.makeTypedIdent (chainTypeOf p o.ParentArgs) "base_chain"
                            let own = Fable.Value(Fable.NewRecord(values, o.Part.Ref, ownArgs o), r)

                            let made =
                                Fable.Let(
                                    baseId,
                                    Fable.Call(callee, call, chainTypeOf p o.ParentArgs, cr),
                                    Fable.Value(
                                        Fable.NewRecord([ Fable.IdentExpr baseId; own ], o.Chain.Ref, ownArgs o),
                                        r
                                    )
                                )

                            match before with
                            | [] -> made
                            | _ -> Fable.Sequential(List.rev before @ [ made ])
                        | rev, _ -> Fable.Sequential(List.rev (chainTail rev.Head :: rev.Tail))
                    | Fable.IfThenElse(c, a, b, r) -> Fable.IfThenElse(c, chainTail a, chainTail b, r)
                    | Fable.TypeCast(x, _) -> chainTail x
                    | _ ->
                        report
                            e.Range
                            $"the Zig target does not support this secondary constructor of %s{o.FullName} yet"

                        e

                [ { m with Body = chainTail m.Body } ]
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
                                { ctor with Body = constructorBodyWith fields (fieldDefaults ent) finish ctor.Body }
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
                            attached.Add
                                { ctor with Body = objConstructorBody o (fieldDefaults ent) c.BaseCall ctor.Body }
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
                                    Body = constructorBody c.Entity genArgs fields (fieldDefaults ent) ctor.Body
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

    // What the file declares is known before any body is lowered: bodies call each other.
    for d in decls do
        let info = com.GetMember d.MemberRef

        try
            reserved.Add d.Name |> ignore

            if info.IsValue then
                let ty = mapType (newCtx d.Name) d.Body.Range d.Body.Type

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
                        d.Body.Type
                    )
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
                // A value that is not a literal is computed when the program starts, by a
                // function of its own, and kept until the program ends.
                | (true, (MConst ty | MValue ty)), body ->
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
                    if entry then
                        [] // (the argument array is not available yet)
                    else
                        args
                        |> List.map (fun a ->
                            let v = state.NewVar(a.Name, mapType ctx a.Range a.Type, VParam, false)
                            ctx.Vars[a.Name] <- v
                            v
                        )

                let ret = mapType ctx d.Body.Range d.Body.Type
                let d = { d with Body = typeTaskBuilders d.Body }

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

                let body = lw ctx d.Body

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
