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

/// .NET's standard numeric formats (`N2`); anything else is a custom one (`0.00`).
let private isStandardNetFormat (net: string) =
    System.Text.RegularExpressions.Regex.IsMatch(net, "^[A-Za-z][0-9]{0,2}$")

/// A .NET numeric format the runtime knows: a standard one, or a custom one of ASCII text.
let private checkNetFormat (r: SourceLocation option) (net: string) =
    if isStandardNetFormat net then
        if not (System.Text.RegularExpressions.Regex.IsMatch(net, "^[DdXxBbNnFfEeGgRrPpCc][0-9]{0,2}$")) then
            fail r "the Zig target does not support the .NET format `%s` yet" net
    elif net |> Seq.exists (fun c -> int c > 127) then
        fail r "the Zig target does not support a .NET format with characters beyond ASCII yet (`%s`)" net

/// Text inside a Zig string literal.
let private zigEscape (text: string) =
    text.Replace("\\", "\\\\").Replace("\"", "\\\"")

/// The function that implements a member of an interface for a type: `Counter__Probe_IShape_Area`
/// (the compiled name of the implementation is the interface's name and the member's).
let private implName (typeName: string) (compiledName: string) : string =
    typeName
    + "__"
    + System.Text.RegularExpressions.Regex.Replace(compiledName, "[^A-Za-z0-9_]", "_")

/// The members of an interface, as the fields of the struct of function values that stands
/// for it: the compiled name (`Area`, `get_Name`), and the types of the arguments and result.
let private interfaceMembers (ent: Fable.Entity) : (string * Fable.Type list * Fable.Type) list =
    ent.MembersFunctionsAndValues
    // (a property is there as itself and as its getter)
    |> Seq.filter (fun m -> m.IsDispatchSlot && not (m.IsProperty && not m.IsGetter && not m.IsSetter))
    |> Seq.distinctBy (fun m -> m.CompiledName)
    |> Seq.map (fun m ->
        let args =
            match m.CurriedParameterGroups |> List.concat |> List.map (fun p -> p.Type) with
            | [] -> [ Fable.Unit ]
            | ts -> ts

        m.CompiledName, args, m.ReturnParameter.Type
    )
    |> List.ofSeq

/// The members of an interface and of the interfaces it inherits, each with the full name of
/// the interface that declares it (type arguments of an inherited generic interface are put in).
let rec private allInterfaceMembers
    (com: Compiler)
    (ent: Fable.Entity)
    (subst: Map<string, Fable.Type>)
    : (string * string * Fable.Type list * Fable.Type) list
    =
    let rec sub (t: Fable.Type) =
        match t with
        | Fable.GenericParam(n, _, _) when subst.ContainsKey n -> subst[n]
        | _ -> t.MapGenerics sub

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
let private settleManaged (state: FileState) =
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
let private settleCycles (state: FileState) =
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
                Hooks = None
                Overrides = []
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
let private defaultExnMessages =
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
let private taskCodeName = "Fable.Library.Zig.Task.TaskCode`1"

let private resultName = "Microsoft.FSharp.Core.FSharpResult`2"
let private mapName = "Microsoft.FSharp.Collections.FSharpMap`2"
let private setName = "Microsoft.FSharp.Collections.FSharpSet`1"

/// F#'s `Result`: a union of the runtime library.
let private resultEnt (state: FileState) : Ent =
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
let private choiceEnt (state: FileState) (fullName: string) : Ent =
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
                Hooks = None
                Overrides = []
            }

        state.Ents["$array"] <- e
        state.UsesRuntime <- true
        e

/// .NET's mutable collections, cells of the runtime library whose contents can be assigned:
/// `List<T>` (ResizeArray), `Dictionary<K, V>`, `HashSet<T>`.
let private netEnt (state: FileState) (name: string) : Ent =
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
let private anonEnt (state: FileState) (names: string[]) : Ent =
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
let private lazyEnt (state: FileState) : Ent =
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
    }

let private tObj = TPrim "fable_rt.Obj"
/// `obj`: an object (of a class, or a boxed value), or null
let private tAny = TOpt tObj

/// Is `name` read in `e`? (Not by a binding of a read that is itself never read: such
/// bindings are left out.)
let rec private liveUse (name: string) (e: Fable.Expr) : bool =
    match e with
    | Fable.IdentExpr i -> i.Name = name
    | Fable.Let(other, (Fable.Get(Fable.IdentExpr _, _, _, _) | Fable.IdentExpr _), body) when
        not other.IsMutable && not (liveUse other.Name body)
        ->
        liveUse name body
    | _ -> AST.getSubExpressions e |> List.exists (liveUse name)

/// A dictionary: .NET's, or what F#'s `dict` and `readOnlyDict` give
let private isDictionaryName (name: string) =
    name = "System.Collections.Generic.Dictionary`2"
    || name = "System.Collections.Generic.IDictionary`2"
    || name = "System.Collections.Generic.IReadOnlyDictionary`2"


let private isClassEntity (ent: Fable.Entity) =
    not (
        ent.IsFSharpRecord
        || ent.IsFSharpUnion
        || ent.IsInterface
        || ent.IsFSharpModule
        || ent.IsFSharpExceptionDeclaration
        || ent.IsValueType
    )

/// .NET's name of a type: `Probe+Circle` for a class in module `Probe`.
let rec private dotnetTypeName (com: Compiler) (ent: Fable.Entity) : string =
    match ent.DeclaringEntity with
    | Some d ->
        match com.TryGetEntity d with
        | Some outer -> dotnetTypeName com outer + "+" + ent.CompiledName
        | None -> ent.FullName
    | None -> ent.FullName

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
    | Fable.DelegateType(args, ret) -> TFn(args |> List.map (mapType ctx r), mapType ctx r ret)
    | Fable.Tuple(ts, _) -> TTuple(ts |> List.map (mapType ctx r))
    // (`Tuple<'T>`, which F# does not write as a tuple)
    | Fable.DeclaredType(ent, [ t ]) when ent.FullName = "System.Tuple`1" || ent.FullName = "System.ValueTuple`1" ->
        TTuple [ mapType ctx r t ]
    // (`None` and `[]` whose item type F# leaves as `obj` are of `obj` here too)
    | Fable.Option(t, _) -> TOpt(mapType ctx r t)
    // (`Nullable<T>`: an option)
    | Fable.Nullable(t, _) -> TOpt(mapType ctx r t)
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
        let item = mapType ctx r t

        if isManaged item then
            fail
                r
                "the Zig target does not support spans of values that are counted (strings, records with references, ...) yet"

        TSlice(item, ent.FullName = "System.ReadOnlySpan`1")
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
    | Fable.DeclaredType(ent, _) when (objInfo ctx r ent).IsSome -> tObj
    // an async computation: the record of the library's Async.fs; the builder has no state
    // (.NET's stack and queue: records of the library's Stack.fs and Queue.fs)
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.Stack`1" ->
        TEnt(libRecordEnt ctx "Stack" "StackOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.Queue`1" ->
        TEnt(libRecordEnt ctx "Queue" "QueueOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "Microsoft.FSharp.Control.FSharpAsync`1" ->
        TEnt(libRecordEnt ctx "Async" "AsyncOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, []) when ent.FullName = "Microsoft.FSharp.Control.FSharpAsyncBuilder" -> tVoid
    // a task and what the builder makes of `task { }`: records of the library's Task.fs; the
    // builder has no state
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Threading.Tasks.Task`1" ->
        TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ mapType ctx r item ])
    | Fable.DeclaredType(ent, []) when ent.FullName = "System.Threading.Tasks.Task" ->
        TEnt(libRecordEnt ctx "Task" "TaskOf_1", [ tVoid ])
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
            isClass
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
                            name, TFn(args |> List.map (mapType ctx r), mapType ctx r ret)
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
                        |> List.map (fun f -> f.Name, mapType ctx r (FableTransforms.uncurryType f.FieldType))
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
                | Some ent when isClassEntity ent ->
                    let derives =
                        match ent.BaseType with
                        | Some bt -> bt.Entity.FullName <> "System.Object"
                        | None -> false

                    // (a generic class is still a plain counted cell unless it shows that it
                    // takes part in inheritance)
                    if
                        ent.GenericParameters.IsEmpty
                        || ent.IsAbstractClass
                        || derives
                        || ent.MembersFunctionsAndValues |> Seq.exists (fun m -> m.IsDispatchSlot)
                    then
                        Some ent
                    else
                        None
                | _ -> None
            | _ -> None

        match found with
        | None ->
            ctx.State.ObjInfos[entRef.FullName] <- null
            None
        | Some ent ->
            if not ent.GenericParameters.IsEmpty then
                fail
                    r
                    "the Zig target does not support generic classes that take part in inheritance yet (%s)"
                    entRef.FullName

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
                }

            // (registered before its fields are mapped: they may mention the class)
            ctx.State.ObjInfos[entRef.FullName] <- box info

            let fields =
                (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                |> List.map (fun f -> f.Name, mapType ctx r (FableTransforms.uncurryType f.FieldType))

            part.Cases <- [ "", fields ]
            part.MutableFields <- fields |> List.map fst

            chain.Cases <-
                [
                    "",
                    (match parent with
                     | Some p -> [ "base", TEnt(p.Chain, []) ]
                     | None -> [])
                    @ [ "own", TEnt(part, []) ]
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
                    Hooks = None
                    Overrides = []
                }

            ctx.State.Ents[entRef.FullName] <- e

            try
                e.Cases <-
                    [
                        "",
                        (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic))
                        |> List.map (fun f -> f.Name, mapType ctx r (FableTransforms.uncurryType f.FieldType))
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
            | "Cont_1" -> [ "ok", TFn([ TGen "T" ], tVoid); "fail", TFn([ tExn ], tVoid) ]
            | "TaskOf_1" -> [ "fable_task", TEnt(resultEnt ctx.State, [ TGen "T"; tExn ]) ]
            | "TaskCode_1" -> [ "code", TFn([ tVoid ], TGen "T") ]
            | _ -> []

        let e =
            {
                Name = libraryTarget ctx file name
                Ref =
                    {
                        FullName = $"Fable.Library.Zig.%s{file}.%s{name.Replace('_', '`')}"
                        Path = Fable.CoreAssemblyName "FSharp.Core"
                    }
                Kind = KRecord
                TypeParams = [ "T" ]
                Cases = [ "", fields ]
                MutableFields = []
                Managed = true
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
                Cases = [ "", [ "next", TFn([ tVoid ], TOpt(TGen "T")) ] ]
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

/// A module-level value of another file: its name there, and whether it can be assigned.
let private importedValue (ctx: Ctx) (imp: Fable.ImportInfo) : (string * bool) option =
    match imp.Kind with
    | Fable.MemberImport memberRef ->
        match ctx.Com.TryGetMember memberRef with
        | Some m when m.IsValue -> Some(importAlias ctx imp.Path + "." + imp.Selector, m.IsMutable)
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

/// `kprintf cont fmt args` as `cont (sprintf fmt args)`.
let private kprintf
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
let mutable private divRemTemps = 0

/// Is this a culture or a format provider given to a .NET method (`CultureInfo.InvariantCulture`)?
let private isCulture (x: Fable.Expr) =
    match x.Type with
    | Fable.DeclaredType(e, _) ->
        e.FullName = "System.Globalization.CultureInfo"
        || e.FullName = "System.IFormatProvider"
    | _ -> false

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

/// The item type of what is a list here: a list, or a collection that `Map.keys` gives.
let private listItem (t: Fable.Type) : Fable.Type option =
    match t with
    | Fable.List item -> Some item
    | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Collections.Generic.ICollection`1" -> Some item
    | _ -> None

/// The functions of FSharp.Core that the part of the runtime library written in F# has: the
/// file, and the name there (the name FSharp.Core compiles the function to).
let private libraryFunction (entity: string) (name: string) : (string * string) option =
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
let private unByref (t: Fable.Type) : Fable.Type =
    match t with
    | Fable.DeclaredType(ent, [ inner; _ ]) when ent.FullName = "Microsoft.FSharp.Core.byref`2" -> inner
    | _ -> t

/// A read of what a byref points at, typed as that: `string s.[i]`, `%d` of it.
let private readByref (e: Fable.Expr) : Fable.Expr =
    match e.Type with
    | Fable.DeclaredType(ent, [ inner; _ ]) when ent.FullName = "Microsoft.FSharp.Core.byref`2" ->
        Fable.TypeCast(e, inner)
    | _ -> e

/// The expression under the casts and unboxing that F# puts around `x` in `use x = ...`.
let rec private (|Unboxed|) (e: Fable.Expr) : Fable.Expr =
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
let private implements (com: Compiler) (t: Fable.Type) (ifaceFullName: string) : bool option =
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
let private seqEntRef: Fable.EntityRef =
    {
        FullName = "System.Collections.Generic.IEnumerable`1"
        Path = Fable.CoreAssemblyName "System.Runtime"
    }


let private taskCodeOf (t: Fable.Type) : Fable.Type =
    Fable.DeclaredType(
        {
            FullName = taskCodeName
            Path = Fable.CoreAssemblyName "FSharp.Core"
        },
        [ t ]
    )

/// F#'s resumable code (`TaskCode`): a delegate of a byref to a state machine.
let rec private isResumableCode (t: Fable.Type) : bool =
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
let private typeTaskBuilders (body: Fable.Expr) : Fable.Expr =
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
                | _ -> Fable.Any

            Fable.Call(callee, info, t, r)
        | _ -> e
    )

/// Is this F#'s `seq<'T>`?
let private isSeqType (t: Fable.Type) : bool =
    match t with
    | Fable.DeclaredType(ent, [ _ ]) -> ent.FullName = "System.Collections.Generic.IEnumerable`1"
    | _ -> false

/// Is this the type of an interface?
let private isInterfaceType (com: Compiler) (t: Fable.Type) : bool =
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
let rec private ancestors (o: ObjInfo) : ObjInfo list =
    o
    :: (
        match o.Parent with
        | Some p -> ancestors p
        | None -> []
    )

let private chainType (o: ObjInfo) : Fable.Type = Fable.DeclaredType(o.Chain.Ref, [])

/// The Zig name of a class's type (`Circle__type`).
let private objTypeName (o: ObjInfo) : string = callTarget (o.Prefix + "__type")

/// The structs of fields of a class and the classes above it, the root's first, as Zig text.
let private partNames (o: ObjInfo) : string =
    ancestors o
    |> List.rev
    |> List.map (fun k -> callTarget k.Part.Name)
    |> String.concat ", "

/// The class of the chain that declares a field.
let private fieldOwner (o: ObjInfo) (field: string) : ObjInfo option =
    ancestors o
    |> List.tryFind (fun k -> caseFields (TEnt(k.Part, [])) "" |> List.exists (fun (f, _) -> f = field))

/// The class that introduced a virtual member, and the type of its function value.
let private virtualSlot (o: ObjInfo) (slot: string) : (ObjInfo * Ty) option =
    ancestors o
    |> List.tryPick (fun k ->
        k.Slots
        |> List.tryFind (fun (s, _) -> s = slot)
        |> Option.map (fun (_, ty) -> k, ty)
    )

/// Does the class itself implement the virtual member (`override`, or `default` in the class that
/// introduces it)?
let private classImplements (com: Compiler) (k: ObjInfo) (slot: string) : bool =
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
let private implementationOf (com: Compiler) (r: SourceLocation option) (o: ObjInfo) (slot: string) : string =
    match ancestors o |> List.tryFind (fun k -> classImplements com k slot) with
    | Some k -> implName k.Prefix slot
    | None -> fail r "the Zig target finds no implementation of %s for %s" slot o.FullName

/// The compiled name of the member a call goes to.
let private slotName (com: Compiler) (call: Fable.CallInfo) (fieldName: string) : string =
    match call.MemberRef |> Option.bind com.TryGetMember with
    | Some m -> m.CompiledName
    | None -> fieldName.Substring(fieldName.LastIndexOf '.' + 1)

let private isConstructorCall (com: Compiler) (call: Fable.CallInfo) : bool =
    match call.MemberRef |> Option.bind com.TryGetMember with
    | Some m -> m.IsConstructor
    | None -> false

/// The prefix of the functions of a class's members: for an object, of the class of its chain
/// that implements `iface` when one is given.
let private classPrefixWith
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

let private classPrefix
    (ctx: Ctx)
    (r: SourceLocation option)
    (classRef: Fable.EntityRef)
    (iface: string option)
    : string
    =
    classPrefixWith ctx.Com (objInfo ctx r) (fun c -> (entOf ctx r c).Name) classRef iface

/// The function that implements member `name` of interface `iface` for a class: the class's
/// own, or the one of the nearest class above it that has one. (A member is implemented under
/// the name of the interface written in `interface X with`, which may inherit `iface`.)
let private interfaceImpl
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
                    && m.CompiledName.EndsWith("." + name, System.StringComparison.Ordinal)
                )
                |> Option.map (fun m -> implName prefix m.CompiledName)
            | None -> None
        )

    match found with
    | Some f -> f
    | None -> implName (classPrefix ctx r classRef (Some iface)) (iface + "." + name)

/// What the file emits for a class that takes part in inheritance that it declares.
let private objDecl (com: Compiler) (r: SourceLocation option) (o: ObjInfo) (dotnetName: string) : ObjDecl =
    let classes = ancestors o |> List.rev

    let tables =
        classes
        |> List.map (fun level ->
            match level.Table with
            | Some vt when not o.IsAbstract ->
                let entries =
                    level.Slots
                    |> List.map (fun (slot, slotTy) -> slot, implementationOf com r o slot, slotTy)

                Some(TEnt(vt, []), entries)
            | _ -> None
        )

    {
        TypeName = o.Prefix + "__type"
        Chain = TEnt(o.Chain, [])
        DotnetName = dotnetName
        Parent = o.Parent |> Option.map (fun p -> p.Prefix + "__type")
        Tables = tables
        ToString =
            ancestors o
            |> List.tryFind (fun k -> classImplements com k "ToString")
            |> Option.map (fun k -> k.Prefix + "__ToString")
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
let private constructorBodyWith
    (fieldNames: string list)
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

    let rec usesThis (e: Fable.Expr) =
        match e with
        | Fable.Value(Fable.ThisValue _, _) -> true
        | _ -> getSubExpressions e |> List.exists usesThis

    let rec fieldsOf (e: Fable.Expr) : Fable.Expr =
        match e with
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
                    match set.TryGetValue f with
                    | true, id -> Fable.IdentExpr id
                    | _ ->
                        raise (
                            ZigError(
                                $"the Zig target needs every field of a class to be given a value in its constructor (`%s{f}`)",
                                None
                            )
                        )
                )

            finish values
        | stmt :: rest ->
            match stmt with
            | Fable.Sequential xs -> build (xs @ rest)
            | Fable.Value(Fable.UnitConstant, _) -> build rest
            // (the constructor of System.Object)
            | Fable.Call(Fable.Import(imp, _, _), _, _, _) when
                imp.Selector = ".ctor" && imp.Path.EndsWith "System.Object"
                ->
                build rest
            | Fable.Set(Fable.Value(Fable.ThisValue _, _), Fable.FieldSet name, t, value, _) ->
                let id = fieldIdent name t
                let value = fieldsOf value
                set[name] <- id
                Fable.Let(id, value, build rest)
            | Fable.Let(id, value, body) -> Fable.Let(id, fieldsOf value, build (body :: rest))
            | other -> Fable.Sequential [ fieldsOf other; build rest ]

    build [ body ]

let private constructorBody
    (classRef: Fable.EntityRef)
    (genArgs: Fable.Type list)
    (fieldNames: string list)
    (body: Fable.Expr)
    : Fable.Expr
    =
    constructorBodyWith fieldNames (fun values -> Fable.Value(Fable.NewRecord(values, classRef, genArgs), None)) body

/// The constructor of a class that takes part in inheritance: the chain of its fields, the
/// parent's (which its constructor computes, first) and its own.
let private objConstructorBody (o: ObjInfo) (baseCall: Fable.Expr option) (body: Fable.Expr) : Fable.Expr =
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
        let own = Fable.Value(Fable.NewRecord(values, o.Part.Ref, []), None)

        let chain =
            match o.Parent with
            | Some p -> [ Fable.IdentExpr(baseId (chainType p)); own ]
            | None -> [ own ]

        Fable.Value(Fable.NewRecord(chain, o.Chain.Ref, []), None)

    let inner = constructorBodyWith fields finish body

    match o.Parent, baseCall with
    | Some p, Some(Fable.Call(callee, info, _, r)) ->
        Fable.Let(baseId (chainType p), Fable.Call(callee, info, chainType p, r), inner)
    | Some _, _ ->
        raise (
            ZigError($"the Zig target does not support this call of the base constructor of %s{o.FullName} yet", None)
        )
    | None, _ -> inner

/// A module-level value, of this file or (`alias.name`) of another.
let private globalVar (name: string) (ty: Ty) (isMutable: bool) : Expr =
    EVar
        {
            Id = 0
            Base = name
            Ty = ty
            Kind = VGlobal
            FMutable = isMutable
        }

/// Is the variable used inside a function that is declared in `e`?
let private usedInFunction (name: string) (e: Fable.Expr) : bool =
    let rec go (inside: bool) (e: Fable.Expr) : bool =
        match e with
        | Fable.IdentExpr id -> inside && id.Name = name
        | Fable.Lambda(_, body, _)
        | Fable.Delegate(_, body, _, _) -> go true body
        | Fable.ObjectExpr(members, _, _) -> members |> List.exists (fun m -> go true m.Body)
        | _ -> getSubExpressions e |> List.exists (go inside)

    go false e

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

/// Has this type a default value here (what .NET's is: zero, false, null of a string, None)?
let rec private hasDefault (t: Fable.Type) : bool =
    match t with
    | Fable.Number _
    | Fable.Char
    | Fable.Boolean
    | Fable.String
    | Fable.Unit
    | Fable.Option _ -> true
    | Fable.Tuple(ts, _) -> List.forall hasDefault ts
    | _ -> false

/// The item type of `IEnumerator<T>`.
let private enumeratorItem (t: Fable.Type) : Fable.Type =
    match t with
    | Fable.DeclaredType(_, [ item ]) -> item
    | _ -> Fable.Any

/// What Fable makes of `for x in s do body` after `let enumerator = s.GetEnumerator()`:
/// `try (while enumerator.MoveNext() do body) finally enumerator.Dispose()`, perhaps followed
/// by more code. The body of the loop, and what follows the loop.
let private forInLoop (enumerator: string) (rest: Fable.Expr) : (Fable.Expr * Fable.Expr option) option =
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

let rec lw (ctx: Ctx) (e: Fable.Expr) : Expr =
    match e with
    // ---- objects of classes that take part in inheritance ----
    // `base`: the object itself, seen as its parent class
    | Fable.Value(Fable.BaseValue(Some id, _), _) -> lw ctx (Fable.IdentExpr id)
    // `Circle 1.0`: the constructor computes the chain of fields; the object is made of it
    | Fable.Call(callee, info, Fable.DeclaredType(cls, _), r) when
        isConstructorCall ctx.Com info && (objInfo ctx r cls).IsSome
        ->
        let o = (objInfo ctx r cls).Value

        if o.IsAbstract then
            fail r "the abstract class %s cannot be made" o.FullName

        bindArgs
            ctx
            [ lw ctx (Fable.Call(callee, info, chainType o, r)) ]
            (fun xs -> EEmit($"fable_rt.objNew(&%s{objTypeName o}, $0)", xs, tObj))
    // `base.Describe()`: the implementation its parent class has, called directly
    | Fable.Call(Fable.Get(Fable.Value(Fable.BaseValue(Some id, baseTy), _), Fable.FieldGet field, _, _), call, t, r) when
        (objOfType ctx r baseTy).IsSome
        ->
        let o = (objOfType ctx r baseTy).Value
        let slot = slotName ctx.Com call field.Name
        let target = implementationOf ctx.Com r o slot

        let args =
            match call.Args with
            | [] -> [ EUnit ]
            | given -> given |> List.map (lw ctx)

        bindArgs ctx (lw ctx (Fable.IdentExpr id) :: args) (fun xs -> ECall(target, [], xs, mapType ctx r t))
    // `shape.Area()`: through the table of the class that introduced the member
    | Fable.Call(Fable.Get(x, Fable.FieldGet field, _, _), call, t, r) when
        (match objOfType ctx r x.Type with
         | Some o -> (virtualSlot o (slotName ctx.Com call field.Name)).IsSome
         | None -> false)
        ->
        let o = (objOfType ctx r x.Type).Value
        let slot = slotName ctx.Com call field.Name
        let level, slotTy = (virtualSlot o slot).Value

        let args =
            match call.Args with
            | [] -> [ EUnit ]
            | given -> given |> List.map (lw ctx)

        let table = TPtr(TEnt(level.Table.Value, []), true)

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
        let table = TPtr(TEnt(level.Table.Value, []), true)

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
        let level = (fieldOwner (objOfType ctx r x.Type).Value field.Name).Value
        let part = TEnt(level.Part, [])
        let fty = caseFields part "" |> List.find (fun (f, _) -> f = field.Name) |> snd

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                EGet(
                    EEmit($"fable_rt.objPart($R, &[_]type{{ %s{partNames level} }}, $0)", xs, TPtr(part, false)),
                    PField field.Name,
                    fty
                )
            )
    | Fable.Set(x, Fable.FieldSet name, _, value, r) when
        (match objOfType ctx r x.Type with
         | Some o -> (fieldOwner o name).IsSome
         | None -> false)
        ->
        let level = (fieldOwner (objOfType ctx r x.Type).Value name).Value
        let part = TEnt(level.Part, [])
        let fty = caseFields part "" |> List.find (fun (f, _) -> f = name) |> snd

        bindArgs
            ctx
            [ lw ctx x; lw ctx value ]
            (fun xs ->
                let place =
                    EGet(
                        EEmit(
                            $"fable_rt.objPart($R, &[_]type{{ %s{partNames level} }}, $0)",
                            [ xs[0] ],
                            TPtr(part, false)
                        ),
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
        | Fable.DeclaredType(cls, _) when (objInfo ctx r cls).IsSome ->
            let o = (objInfo ctx r cls).Value
            ctx.State.UsesRuntime <- true
            bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.anyIsClass($0, &%s{objTypeName o})", xs, tBool))
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
    | Fable.Test(x, Fable.TypeTest(Fable.DeclaredType(cls, _)), r) when
        (objInfo ctx r cls).IsSome && (objOfType ctx r x.Type).IsSome
        ->
        let o = (objInfo ctx r cls).Value
        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.objIs($0, &%s{objTypeName o})", xs, tBool))
    | Fable.Value(kind, r) ->
        match kind with
        | Fable.UnitConstant -> EUnit
        // `null`: of a string and of `obj` (other types have no null here)
        | Fable.Null Fable.String -> ELit("@as(fable_rt.String, null)", tStr)
        | Fable.Null Fable.Any ->
            ctx.State.UsesRuntime <- true
            ELit("@as(fable_rt.Any, null)", tAny)
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
            let ty =
                TEnt(anonEnt ctx.State names, genArgs |> List.map (FableTransforms.uncurryType >> mapTypeArg ctx r))

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
                // a sequence: start a walk, and ask it for each item until it has none
                let walkTy = TEnt(walkEnt ctx, [ itemTy ])
                let nextTy = TFn([ tVoid ], TOpt itemTy)
                let walk = ctx.State.NewVar("walk", walkTy, VLocal, false)
                let go = ctx.State.NewVar("go", tBool, VLocal, true)
                let next = ctx.State.NewVar("next", TOpt itemTy, VLocal, false)

                ELet(
                    walk,
                    ECallClo(EGet(source, PField "fable_seq", TFn([ tVoid ], walkTy)), [ EUnit ], walkTy),
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
            bindArgs
                ctx
                [ lw ctx value ]
                (fun xs ->
                    match xs.Head with
                    | EDeref(p, _) -> p
                    | EVar x -> EAddr(EVar x, not x.FMutable)
                    | _ -> fail id.Range "the Zig target cannot take the address of this yet"
                )

        // (the address of what cannot be assigned, as F# takes to copy a struct record with
        // some fields changed, only reads)
        let ty =
            match mapType ctx id.Range id.Type, typeOf place with
            | TPtr(t, false), (TPtr(t2, true) as actual) when t = t2 -> actual
            | ty, _ -> ty

        let v = ctx.State.NewVar(id.Name, ty, VLocal, false)
        ctx.Vars[id.Name] <- v
        ELet(v, place, lw ctx body)

    // (a part of a value that a pattern names and nothing uses: Zig rejects a constant that is
    // never read)
    | Fable.Let(id, (Fable.Get(Fable.IdentExpr _, _, _, _) | Fable.IdentExpr _), body) when
        not id.IsMutable && not (liveUse id.Name body)
        ->
        lw ctx body
    | Fable.Let(id, value, body) ->
        let rhs = lw ctx value
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
                match ir with
                // (a byref passed on is the pointer it is)
                | EDeref(p, _) -> p
                | EVar v -> EAddr(EVar v, not v.FMutable)
                | _ -> fail r "the Zig target can only take the address of a variable (`&x`)"
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

    // a member of an interface: a field of its struct of function values (a property is read
    // by calling its getter)
    | Fable.Get(x, Fable.FieldGet info, t, r) when isInterfaceType ctx.Com x.Type ->
        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                let fields = caseFields (typeOf xs.Head) ""

                match fields |> List.tryFind (fun (f, _) -> f = info.Name) with
                | Some(f, fty) -> EGet(xs.Head, PField f, fty)
                | None ->
                    match fields |> List.tryFind (fun (f, _) -> f = "get_" + info.Name) with
                    | Some(f, fty) -> ECallClo(EGet(xs.Head, PField f, fty), [ EUnit ], mapType ctx r t)
                    | None -> fail r "the Zig target cannot find the member %s of this interface" info.Name
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
            | _ -> fail e.Range "the Zig target cannot use a value of this type as a sequence yet (%A)" x.Type

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

                            slot, target, slotTy
                        )

                    Some(TEnt(vt, []), entries)
                | None -> None
            )

        ctx.State.Objs.Add
            {
                TypeName = prefix + "__type"
                Chain = TEnt(chain, [])
                DotnetName = parent.FullName.Substring(parent.FullName.LastIndexOf '.' + 1) + "@" + string n
                Parent = Some(parent.Prefix + "__type")
                Tables = tables
                ToString =
                    ancestors parent
                    |> List.tryFind (fun k -> classImplements ctx.Com k "ToString")
                    |> Option.map (fun k -> k.Prefix + "__ToString")
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

    | Fable.ObjectExpr(members, ifaceType, None) when isInterfaceType ctx.Com ifaceType ->
        let ifaceTy = mapType ctx e.Range ifaceType

        let byName =
            members
            |> List.map (fun m ->
                let compiled =
                    match ctx.Com.TryGetMember m.MemberRef with
                    | Some info -> info.CompiledName
                    | None -> m.Name

                compiled, m
            )
            |> dict

        let rec usesIdent (name: string) (e: Fable.Expr) =
            match e with
            | Fable.IdentExpr id -> id.Name = name
            | _ -> getSubExpressions e |> List.exists (usesIdent name)

        let closures =
            caseFields ifaceTy ""
            |> List.map (fun (f, _) ->
                match byName.TryGetValue f with
                | true, m ->
                    match m.Args with
                    | this :: args ->
                        if usesIdent this.Name m.Body then
                            fail e.Range "the Zig target does not support `this` in an object expression yet"

                        lw ctx (Fable.Delegate(args, m.Body, None, []))
                    | [] -> fail e.Range "internal: a member without its object"
                | _ -> fail e.Range "the Zig target cannot find the member %s in this object expression" f
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

    | Fable.Call(callee, info, t, r) ->
        let ty = mapType ctx r t

        // (a member of a type is a function whose first argument is the object)
        let allArgs = Option.toList info.ThisArg @ info.Args
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

            let wantsAddress =
                if c.ArgTypes.Length = allArgs.Length then
                    List.map2
                        (fun (p: Fable.Type) (a: Fable.Expr) -> isByref p && not (isByref a.Type))
                        c.ArgTypes
                        allArgs
                else
                    allArgs |> List.map (fun _ -> false)

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
                                | EVar v, true -> EAddr(EVar v, true)
                                | EAddr _, _
                                | _, false -> x
                                | _ ->
                                    let v = ctx.State.NewVar("inref", typeOf x, VLocal, false)
                                    temps.Add((v, x))
                                    EAddr(EVar v, true)
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
    | Fable.DeclaredType(cls, _) when (objInfo ctx r cls).IsSome ->
        let o = (objInfo ctx r cls).Value
        bindArgs ctx [ lw ctx x ] (fun xs -> ERt($"fable_rt.anyToClass($0, &%s{objTypeName o})", xs, tObj))
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
and checkShowable (ctx: Ctx) (r: SourceLocation option) (t: Fable.Type) : unit =
    let seen = HashSet<string>()

    let rec go (t: Fable.Type) =
        match t with
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
        | Fable.AnonymousRecordType(_, genArgs, _) -> List.iter go genArgs
        | Fable.DeclaredType(ent, [ inner ]) when ent.FullName = "System.Collections.Generic.IEnumerable`1" -> go inner
        | Fable.DeclaredType(ent, [ inner ]) when ent.FullName = "System.Lazy`1" -> go inner
        | Fable.Tuple(_, true) -> fail r "the Zig target cannot write a struct tuple with %%A yet"
        | Fable.LambdaType _
        | Fable.DelegateType _ -> fail r "the Zig target cannot write a function value with %%A yet"
        | Fable.DeclaredType(entRef, genArgs) ->
            List.iter go genArgs

            if
                not (dotnetExceptions.ContainsKey entRef.FullName)
                && entRef.FullName <> mapName
                && entRef.FullName <> setName
                && entRef.FullName <> "System.Collections.Generic.Dictionary`2"
                && entRef.FullName <> "System.Collections.Generic.HashSet`1"
                && seen.Add entRef.FullName
            then
                match ctx.Com.TryGetEntity entRef with
                | Some ent when ent.IsFSharpUnion ->
                    for case in ent.UnionCases do
                        for field in case.UnionCaseFields do
                            go field.FieldType
                | Some ent when ent.IsFSharpRecord || ent.IsFSharpExceptionDeclaration ->
                    for field in (ent.FSharpFields |> List.filter (fun f -> not f.IsStatic)) do
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

                if
                    (letter = 'P' || letter = 'O')
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
                    match value.Type with
                    // (a number of 16 bits without a sign and a char are the same type in Zig; at
                    // the top the compiler can tell them apart, inside a value it cannot)
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

    let zigTypeOf (ty: Ty) =
        match ty with
        | TPrim name -> name
        | _ -> fail r "internal: not a number type"

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
        | [ Fable.DeclaredType(cls, _) ] ->
            let o = (objInfo ctx r cls).Value
            bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.objIs($0, &%s{objTypeName o})", xs, tBool))
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
            rt $"fable_rt.objCast($0, &%s{objTypeName o})" [ x ] tObj
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
            bindArgs ctx [ lw ctx f; listIr ] (fun xs -> ERt($"fable_rt.listSumBy(%s{zigTypeOf ty}, $0, $1)", xs, ty))
        | "AverageBy", [ f; _ ] ->
            bindArgs
                ctx
                [ lw ctx f; listIr ]
                (fun xs -> ERt($"fable_rt.listAverageBy(%s{zigTypeOf ty}, $0, $1)", xs, ty))
        | _ -> fail r "internal: a sum"

    // ---- task: the builder (which has no state) and the members of a task ----
    | "Microsoft.FSharp.Control.TaskBuilderModule", "task", _ -> EUnit
    | ("Microsoft.FSharp.Control.TaskBuilder" | "Microsoft.FSharp.Control.TaskBuilderBase" | "Microsoft.FSharp.Control.TaskBuilderExtensions.LowPriority" | "Microsoft.FSharp.Control.TaskBuilderExtensions.HighPriority" | "Microsoft.FSharp.Control.TaskBuilderExtensions.MediumPriority"),
      _,
      _ when entity.StartsWith("Microsoft.FSharp.Control.TaskBuilder", System.StringComparison.Ordinal) ->
        let member' = name.Substring(name.LastIndexOf '.' + 1)

        let given =
            args
            |> List.filter (fun a ->
                match a.Type with
                | Fable.DeclaredType(ent, _) -> ent.FullName <> "Microsoft.FSharp.Control.TaskBuilder"
                | _ -> true
            )

        let itemOf (t: Fable.Type) =
            match t with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Unit

        let retItem (f: Fable.Expr) =
            match f.Type with
            | Fable.LambdaType(_, ret)
            | Fable.DelegateType(_, ret) -> itemOf ret
            | _ -> Fable.Unit

        let typeArgs =
            match member', given with
            | "Run", [ c ] -> [ itemOf c.Type ]
            | "Delay", [ f ] -> [ retItem f ]
            | "Return", [ x ] -> [ x.Type ]
            | "Bind", [ task; cont ] -> [ itemOf task.Type; retItem cont ]
            | "ReturnFrom", [ task ] -> [ itemOf task.Type ]
            | "Combine", [ _; second ] -> [ itemOf second.Type ]
            | ("TryWith" | "TryFinally"), b :: _ -> [ itemOf b.Type ]
            | "For", [ sq; _ ] -> [ itemOf sq.Type ]
            | _ -> []

        let resultTy =
            match member' with
            | "Run" -> t
            | _ when t <> Fable.Any -> t
            | _ -> taskCodeOf (List.tryHead typeArgs |> Option.defaultValue Fable.Unit)

        libraryCall
            ctx
            r
            "Task"
            ("builder" + member')
            { info with
                GenericArgs = typeArgs
                SignatureArgTypes = []
                MemberRef = None
                ThisArg = None
                Args = given
            }
            given
            resultTy
    | "System.Threading.Tasks.Task`1", ("get_Result" | "Wait" | "get_IsCompleted" | "get_IsFaulted"), [ task ] ->
        let fn =
            match name with
            | "get_Result" -> "resultOf"
            | "Wait" -> "waitFor"
            | "get_IsCompleted" -> "isCompleted"
            | _ -> "isFaulted"

        let item =
            match task.Type with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Unit

        libraryCall
            ctx
            r
            "Task"
            fn
            { info with
                GenericArgs = [ item ]
                SignatureArgTypes = []
                MemberRef = None
                ThisArg = None
                Args = [ task ]
            }
            [ task ]
            t
    | "System.Threading.Tasks.Task", ("Wait" | "get_IsCompleted" | "get_IsFaulted"), [ task ] ->
        let fn =
            match name with
            | "Wait" -> "waitFor"
            | "get_IsCompleted" -> "isCompleted"
            | _ -> "isFaulted"

        // (a member of Task called on a Task<'T>: the item type is the object's)
        let item =
            match task.Type with
            | Fable.DeclaredType(ent, [ item ]) when ent.FullName = "System.Threading.Tasks.Task`1" -> item
            | _ -> Fable.Unit

        libraryCall
            ctx
            r
            "Task"
            fn
            { info with
                GenericArgs = [ item ]
                SignatureArgTypes = []
                MemberRef = None
                ThisArg = None
                Args = [ task ]
            }
            [ task ]
            t
    | "System.Threading.Tasks.Task", "FromResult", [ x ] ->
        libraryCall
            ctx
            r
            "Task"
            "fromResult"
            { info with
                GenericArgs = [ x.Type ]
                SignatureArgTypes = []
                MemberRef = None
            }
            [ x ]
            t
    | "System.Threading.Tasks.Task", "Delay", [ ms ] ->
        libraryCall
            ctx
            r
            "Task"
            "delay"
            { info with
                GenericArgs = []
                SignatureArgTypes = []
                MemberRef = None
            }
            [ ms ]
            t
    | "System.Threading.Tasks.Task", "get_CompletedTask", [] ->
        libraryCall
            ctx
            r
            "Task"
            "completedTask"
            { info with
                GenericArgs = []
                SignatureArgTypes = []
                MemberRef = None
            }
            []
            t
    | "System.Threading.Tasks.Task", "WhenAll", [ tasks ] ->
        let item =
            match t with
            | Fable.DeclaredType(_, [ Fable.Array(item, _) ]) -> item
            | _ -> Fable.Unit

        let tasksSeq =
            match tasks with
            | Fable.Value(Fable.NewArray(Fable.ArrayValues _, _, _), _) ->
                Fable.TypeCast(
                    tasks,
                    Fable.DeclaredType(
                        seqEntRef,
                        [
                            (match tasks.Type with
                             | Fable.Array(i, _) -> i
                             | i -> i)
                        ]
                    )
                )
            | _ -> tasks

        libraryCall
            ctx
            r
            "Task"
            "whenAll"
            { info with
                GenericArgs = [ item ]
                SignatureArgTypes = []
                MemberRef = None
            }
            [ tasksSeq ]
            t

    // ---- async: `async` is the builder, which has no state ----
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators", "DefaultAsyncBuilder", _ -> EUnit

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

    // ---- arrays ----
    // ---- two-dimensional arrays: arrays that know their rows and columns ----
    | "Microsoft.FSharp.Collections.Array2DModule", "ZeroCreate", [ rows; cols ] ->
        rt "fable_rt.array2DZero($R, $0, $1)" [ rows; cols ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "Create", [ rows; cols; x ] ->
        rt "fable_rt.array2DCreate($R, $0, $1, $2)" [ rows; cols; x ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "Initialize", [ rows; cols; f ] ->
        rt "fable_rt.array2DInit($R, $0, $1, $2)" [ rows; cols; f ] (mapType ctx r t)
    | ("Microsoft.FSharp.Collections.Array2DModule" | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"),
      ("Get" | "GetArray2D"),
      [ a; i; j ] -> rt "fable_rt.array2DGet($0, $1, $2)" [ a; i; j ] (mapType ctx r t)
    | ("Microsoft.FSharp.Collections.Array2DModule" | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions"),
      ("Set" | "SetArray2D"),
      [ a; i; j; v ] -> rt "fable_rt.array2DSet($0, $1, $2, $3)" [ a; i; j; v ] tVoid
    | "Microsoft.FSharp.Collections.Array2DModule", ("Length1" | "Length2"), [ a ] ->
        pure'
            $"""fable_rt.array2DLength($0, %s{if name = "Length1" then
                                                  "0"
                                              else
                                                  "1"})"""
            [ a ]
            tI32
    | "Microsoft.FSharp.Collections.Array2DModule", ("Base1" | "Base2"), [ a ] -> ESeq(lwStmt ctx a, ELit("0", tI32))
    | "System.Array", "GetLength", [ a; d ] -> rt "fable_rt.arrayGetLength($0, $1)" [ a; d ] tI32
    | "Microsoft.FSharp.Collections.Array2DModule", ("Copy" | "Rebase"), [ a ] ->
        pure' "fable_rt.array2DCopy($0)" [ a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "CopyTo", [ src; si; sj; dst; ti; tj; n1; n2 ] ->
        rt "fable_rt.array2DBlit($0, $1, $2, $3, $4, $5, $6, $7)" [ src; si; sj; dst; ti; tj; n1; n2 ] tVoid
    | "Microsoft.FSharp.Core.Operators.OperatorIntrinsics", "GetArraySlice2D", [ a; lo1; hi1; lo2; hi2 ] ->
        pure' "fable_rt.array2DSlice($0, $1, $2, $3, $4)" [ a; lo1; hi1; lo2; hi2 ] (mapType ctx r t)
    // `array2D rows`: rows given as a list or an array of lists or arrays
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators", "CreateArray2D", [ Uncast rows ] when
        (match rows.Type with
         | Fable.List(Fable.List _ | Fable.Array _)
         | Fable.Array((Fable.List _ | Fable.Array _), _) -> true
         | _ -> false)
        ->
        rt "fable_rt.array2DOfRows($R, $0)" [ rows ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "Map", [ f; a ] ->
        rt "fable_rt.array2DMap($R, $0, $1)" [ f; a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "MapIndexed", [ f; a ] ->
        rt "fable_rt.array2DMapi($R, $0, $1)" [ f; a ] (mapType ctx r t)
    | "Microsoft.FSharp.Collections.Array2DModule", "Iterate", [ f; a ] ->
        rt "fable_rt.array2DIter($0, $1)" [ f; a ] tVoid
    | "Microsoft.FSharp.Collections.Array2DModule", "IterateIndexed", [ f; a ] ->
        rt "fable_rt.array2DIteri($0, $1)" [ f; a ] tVoid
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

    // ---- .NET's mutable collections ----
    | "System.Collections.Generic.List`1", ".ctor", ([] | [ _ ]) when
        (match args with
         | [ (Uncast inner as x) ] -> (listItem inner.Type).IsSome || isInt x
         | _ -> true)
        ->
        let ty = mapType ctx r t

        match args with
        | [ Uncast x ] when (listItem x.Type).IsSome -> pure' "fable_rt.raOfList($R, $0)" [ x ] ty
        | [ n ] -> bindArgs ctx [ lwStmt ctx n ] (fun _ -> pure' "fable_rt.raNew($R)" [] ty)
        | _ -> pure' "fable_rt.raNew($R)" [] ty
    // (from any other sequence)
    | "System.Collections.Generic.List`1", ".ctor", [ items ] when not (isInt items) ->
        libraryCall ctx r "ResizeArray" "ofSeq" info args t
    | "System.Collections.Generic.List`1", _, r0 :: rest ->
        match name, rest with
        | "Add", [ x ] -> pure' "fable_rt.raAdd($0, $1)" [ r0; x ] tVoid
        | "AddRange", [ Uncast xs ] when (listItem xs.Type).IsSome ->
            pure' "fable_rt.raAddList($0, $1)" [ r0; xs ] tVoid
        | "get_Item", [ i ] -> rt "fable_rt.raGet($0, $1)" [ r0; i ] (mapType ctx r t)
        | "set_Item", [ i; x ] -> rt "fable_rt.raSet($0, $1, $2)" [ r0; i; x ] tVoid
        | "get_Count", [] -> pure' "fable_rt.raCount($0)" [ r0 ] tI32
        | "Insert", [ i; x ] -> rt "fable_rt.raInsert($0, $1, $2)" [ r0; i; x ] tVoid
        | "RemoveAt", [ i ] -> rt "fable_rt.raRemoveAt($0, $1)" [ r0; i ] tVoid
        | "Remove", [ x ] -> pure' "fable_rt.raRemove($0, $1)" [ r0; x ] tBool
        | "Contains", [ x ] -> pure' "fable_rt.raContains($0, $1)" [ r0; x ] tBool
        | "IndexOf", [ x ] -> pure' "fable_rt.raIndexOf($0, $1)" [ r0; x ] tI32
        | "Clear", [] -> pure' "fable_rt.raClear($0)" [ r0 ] tVoid
        | "Reverse", [] -> pure' "fable_rt.raReverse($0)" [ r0 ] tVoid
        | "Sort", [] -> pure' "fable_rt.raSort($0)" [ r0 ] tVoid
        | "ToArray", [] -> pure' "fable_rt.raToArray($0)" [ r0 ] (mapType ctx r t)
        // (`Find` gives `default(T)` when nothing matches: the library's `tryFind`, and the
        // default where the type has one)
        | ("Find" | "FindLast"), [ _ ] ->
            if not (hasDefault t) then
                fail
                    r
                    "the Zig target does not support ResizeArray.%s of items whose default is null on .NET; use a function of the List or Seq module"
                    name

            let found =
                libraryCall ctx r "ResizeArray" ("try" + name) info args (Fable.Option(t, false))

            bindArgs ctx [ found ] (fun xs -> EEmit("fable_rt.orDefault($R, $0)", xs, mapType ctx r t))
        | "IndexOf", [ _; _ ] -> libraryCall ctx r "ResizeArray" "indexOfFrom" info args t
        | "IndexOf", [ _; _; _ ] -> libraryCall ctx r "ResizeArray" "indexOfRange" info args t
        | "BinarySearch", [ _ ] -> libraryCall ctx r "ResizeArray" "binarySearch" info args t
        | ("FindAll" | "FindIndex" | "FindLastIndex" | "Exists" | "TrueForAll" | "ForEach" | "RemoveAll" | "RemoveRange" | "GetRange" | "InsertRange"),
          _
        | "AddRange", [ _ ] ->
            let fn = name.Substring(0, 1).ToLowerInvariant() + name.Substring(1)
            libraryCall ctx r "ResizeArray" fn info args t
        | _ -> fail r "the Zig target does not support ResizeArray.%s yet" name
    // (F#'s `dict` and `readOnlyDict`: dictionaries that cannot be changed)
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators", ("CreateDictionary" | "CreateReadOnlyDictionary"), [ pairs ] ->
        match forInSource ctx pairs with
        | Some(listIr, "list") ->
            bindArgs ctx [ listIr ] (fun xs -> EEmit("fable_rt.dictOfList($R, $0, true)", xs, mapType ctx r t))
        | Some(seqIr, "seq") ->
            let itemTy = itemOf seqIr

            bindArgs
                ctx
                [ seqIr ]
                (fun xs ->
                    bindArgs
                        ctx
                        [
                            ECall(
                                libraryTarget ctx "Seq" "toList",
                                [ itemTy ],
                                xs,
                                TEnt(listEnt ctx.State, [ itemTy ])
                            )
                        ]
                        (fun ls -> EEmit("fable_rt.dictOfList($R, $0, true)", ls, mapType ctx r t))
                )
        | _ -> fail r "the Zig target does not support dict of this kind of sequence yet"
    // `Dictionary(other)`: a copy of another dictionary or of a map
    | "System.Collections.Generic.Dictionary`2", ".ctor", [ Uncast source ] when
        (match source.Type with
         | Fable.DeclaredType(ent, _) -> isDictionaryName ent.FullName || ent.FullName = mapName
         | _ -> false)
        ->
        match forInSource ctx source with
        | Some(listIr, "list") ->
            bindArgs ctx [ listIr ] (fun xs -> EEmit("fable_rt.dictOfList($R, $0, false)", xs, mapType ctx r t))
        | _ -> fail r "the Zig target cannot copy this into a Dictionary yet"
    | ("System.Collections.Generic.IDictionary`2" | "System.Collections.Generic.IReadOnlyDictionary`2"), _, _ ->
        dotnetCall ctx r "System.Collections.Generic.Dictionary`2" name info t
    // (what a dictionary is as a collection of its entries)
    | ("System.Collections.Generic.ICollection`1" | "System.Collections.Generic.IReadOnlyCollection`1"),
      ("get_Count" | "Clear"),
      [ d ] when
        (match d.Type with
         | Fable.DeclaredType(ent, _) -> isDictionaryName ent.FullName
         | _ -> false)
        ->
        if name = "Clear" then
            rt "fable_rt.htClear($0)" [ d ] tVoid
        else
            pure' "fable_rt.htCount($0)" [ d ] tI32
    | ("System.Collections.Generic.Dictionary`2.KeyCollection" | "System.Collections.Generic.Dictionary`2.ValueCollection"),
      "get_Count",
      [ xs ] -> pure' "fable_rt.listCount($0)" [ xs ] tI32
    | ("System.Collections.Generic.Dictionary`2" | "System.Collections.Generic.HashSet`1"), ".ctor", [] ->
        pure' "fable_rt.htNew($R)" [] (mapType ctx r t)
    | "System.Collections.Generic.HashSet`1", ".ctor", [ Uncast xs ] when (listItem xs.Type).IsSome ->
        pure' "fable_rt.setOfList($R, $0)" [ xs ] (mapType ctx r t)
    // (a capacity: nothing to do here)
    | "System.Collections.Generic.HashSet`1", ".ctor", [ n ] when isInt n ->
        bindArgs ctx [ lwStmt ctx n ] (fun _ -> pure' "fable_rt.htNew($R)" [] (mapType ctx r t))
    | "System.Collections.Generic.HashSet`1", ".ctor", [ _ ] -> libraryCall ctx r "HashSet" "ofSeq" info args t
    | "System.Collections.Generic.Dictionary`2", _, d :: rest ->
        match name, rest with
        | "Add", [ k; v ] -> rt "fable_rt.dictAdd($0, $1, $2)" [ d; k; v ] tVoid
        | "set_Item", [ k; v ] -> rt "fable_rt.dictSet($0, $1, $2)" [ d; k; v ] tVoid
        | "get_Item", [ k ] -> rt "fable_rt.dictGet($0, $1)" [ d; k ] (mapType ctx r t)
        | "ContainsKey", [ k ] -> pure' "fable_rt.dictContainsKey($0, $1)" [ d; k ] tBool
        | "ContainsValue", [ v ] -> pure' "fable_rt.dictContainsValue($0, $1)" [ d; v ] tBool
        | "Remove", [ k ] -> rt "fable_rt.htRemove($0, $1)" [ d; k ] tBool
        | "get_Count", [] -> pure' "fable_rt.htCount($0)" [ d ] tI32
        | "Clear", [] -> rt "fable_rt.htClear($0)" [ d ] tVoid
        | "get_Keys", [] -> pure' "fable_rt.dictKeys($0)" [ d ] (mapType ctx r t)
        | "get_Values", [] -> pure' "fable_rt.dictValues($0)" [ d ] (mapType ctx r t)
        | "TryGetValue", [ k; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
            ctx.Vars.ContainsKey out.Name
            ->
            let outVar = ctx.Vars[out.Name]
            let tmp = ctx.State.NewVar("found", TOpt outVar.Ty, VLocal, false)
            ctx.State.UsesRuntime <- true

            bindArgs
                ctx
                [ lw ctx d; lw ctx k ]
                (fun xs ->
                    ELet(
                        tmp,
                        EEmit("fable_rt.dictTryGet($0, $1)", xs, TOpt outVar.Ty),
                        EIf(
                            EPrim("not", [ ETest(EVar tmp, "None", TOpt outVar.Ty) ], tBool),
                            ESeq(EAssign(outVar, EGet(EVar tmp, PSome, outVar.Ty)), ELit("true", tBool)),
                            ELit("false", tBool),
                            tBool
                        )
                    )
                )
        | _ -> fail r "the Zig target does not support Dictionary.%s yet" name
    | "System.Collections.Generic.HashSet`1", _, h :: rest ->
        match name, rest with
        | "Add", [ x ] -> pure' "fable_rt.setAdd($0, $1)" [ h; x ] tBool
        | "Contains", [ x ] -> pure' "fable_rt.dictContainsKey($0, $1)" [ h; x ] tBool
        | "Remove", [ x ] -> rt "fable_rt.htRemove($0, $1)" [ h; x ] tBool
        | "get_Count", [] -> pure' "fable_rt.htCount($0)" [ h ] tI32
        | "Clear", [] -> rt "fable_rt.htClear($0)" [ h ] tVoid
        | "UnionWith", [ Uncast xs ] when (listItem xs.Type).IsSome ->
            pure' "fable_rt.setUnionList($0, $1)" [ h; xs ] tVoid
        | "CopyTo", [ _ ] ->
            libraryCall
                ctx
                r
                "HashSet"
                "copyTo"
                { info with SignatureArgTypes = [] }
                (args
                 @ [
                     Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 0, Fable.NumberInfo.Empty), None)
                 ])
                t
        | "CopyTo", [ _; _; _ ] -> libraryCall ctx r "HashSet" "copyToCount" info args t
        | ("UnionWith" | "IntersectWith" | "ExceptWith" | "SymmetricExceptWith" | "Overlaps" | "SetEquals" | "IsSubsetOf" | "IsSupersetOf" | "IsProperSubsetOf" | "IsProperSupersetOf" | "CopyTo"),
          _ ->
            let fn = name.Substring(0, 1).ToLowerInvariant() + name.Substring(1)
            libraryCall ctx r "HashSet" fn info args t
        | _ -> fail r "the Zig target does not support HashSet.%s yet" name

    // ---- lazy ----
    | "Microsoft.FSharp.Control.LazyExtensions", "Create", [ f ] ->
        pure' "fable_rt.lazyNew($R, $0)" [ f ] (mapType ctx r t)
    | "Microsoft.FSharp.Control.LazyExtensions", "CreateFromValue", [ v ] ->
        pure' "fable_rt.lazyOf($R, $0)" [ v ] (mapType ctx r t)
    | ("Microsoft.FSharp.Control.LazyExtensions" | "System.Lazy`1"), ("Force" | "get_Value"), l :: _ ->
        rt "fable_rt.lazyForce($0)" [ l ] (mapType ctx r t)
    | "System.Lazy`1", "get_IsValueCreated", [ l ] -> pure' "fable_rt.lazyIsCreated($0)" [ l ] tBool

    // ---- spans: slices of the arrays they view ----
    | ("System.Span`1" | "System.ReadOnlySpan`1"), ".ctor", [ a ] when
        (match a.Type with
         | Fable.Array _ -> true
         | _ -> false)
        ->
        pure' "$0.items" [ a ] (mapType ctx r t)
    | ("System.Span`1" | "System.ReadOnlySpan`1"), ".ctor", [ a; start; n ] ->
        rt "fable_rt.spanSlice($0.items, $1, $2)" [ a; start; n ] (mapType ctx r t)
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "get_Length", [ sp ] ->
        pure' "@as(i32, @intCast($0.len))" [ sp ] tI32
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "get_Item", [ sp; i ] ->
        // (the item's place: a byref, which is read here, or kept by a byref variable)
        let item =
            match mapType ctx r t with
            | TPtr(item, _) -> item
            | other -> other

        let ptr =
            rt "fable_rt.spanRef($0, $1)" [ sp; i ] (TPtr(item, entity = "System.ReadOnlySpan`1"))

        bindArgs ctx [ ptr ] (fun xs -> EDeref(xs.Head, item))
    | "System.Span`1", "set_Item", [ sp; i; x ] -> rt "fable_rt.spanSet($0, $1, $2)" [ sp; i; x ] tVoid
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "Slice", [ sp; start ] ->
        rt "fable_rt.spanSlice($0, $1, null)" [ sp; start ] (mapType ctx r t)
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "Slice", [ sp; start; n ] ->
        rt "fable_rt.spanSlice($0, $1, $2)" [ sp; start; n ] (mapType ctx r t)
    | "System.Span`1", "op_Implicit", [ sp ] -> lw ctx sp
    | ("System.Span`1" | "System.ReadOnlySpan`1"), "ToArray", [ sp ] ->
        pure' "fable_rt.arrayOf($R, .{})" [] (mapType ctx r t) |> ignore
        fail r "the Zig target does not support Span.ToArray yet"
    | "System.Span`1", "Fill", [ sp; x ] -> pure' "@memset($0, $1)" [ sp; x ] tVoid

    // ---- weak references ----
    | "System.WeakReference`1", ".ctor", [ target ] -> pure' "fable_rt.weakNew($R, $0)" [ target ] (mapType ctx r t)
    | "System.WeakReference`1", "SetTarget", [ w; target ] -> pure' "fable_rt.weakSet($0, $1)" [ w; target ] tVoid
    | "System.WeakReference`1",
      "TryGetTarget",
      [ w; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
        ctx.Vars.ContainsKey out.Name
        ->
        let outVar = ctx.Vars[out.Name]
        let tmp = ctx.State.NewVar("target", TOpt outVar.Ty, VLocal, false)
        ctx.State.UsesRuntime <- true

        bindArgs
            ctx
            [ lw ctx w ]
            (fun xs ->
                ELet(
                    tmp,
                    EEmit("fable_rt.weakTryGet($0)", xs, TOpt outVar.Ty),
                    EIf(
                        EPrim("not", [ ETest(EVar tmp, "None", TOpt outVar.Ty) ], tBool),
                        ESeq(EAssign(outVar, EGet(EVar tmp, PSome, outVar.Ty)), ELit("true", tBool)),
                        ELit("false", tBool),
                        tBool
                    )
                )
            )
    // `GC.Collect()`: free every cycle that is dead now
    | "System.GC", "Collect", [] -> pure' "_ = fable_rt.collect()" [] tVoid

    // ---- StringBuilder ----
    | "System.Text.StringBuilder", ".ctor", [] -> pure' "fable_rt.sbNew(null)" [] (mapType ctx r t)
    | "System.Text.StringBuilder", ".ctor", [ init ] when init.Type = Fable.String ->
        pure' "fable_rt.sbNew($0)" [ init ] (mapType ctx r t)
    | "System.Text.StringBuilder", ("Append" | "AppendLine"), sb :: rest when rest.Length <= 1 ->
        let f =
            if name = "Append" then
                "sbAppend"
            else
                "sbAppendLine"

        match rest with
        | [] -> pure' $"fable_rt.%s{f}($0, @as(fable_rt.String, null))" [ sb ] (mapType ctx r t)
        | [ x ] ->
            bindArgs
                ctx
                [ lw ctx sb; lw ctx x ]
                (fun xs -> EEmit($"fable_rt.%s{f}($0, %s{typedArg ctx r x 1})", xs, mapType ctx r t))
        | _ -> fail r "the Zig target does not support this StringBuilder.%s yet" name
    | "System.Text.StringBuilder", "get_Length", [ sb ] -> pure' "fable_rt.sbLength($0)" [ sb ] tI32
    | "System.Text.StringBuilder", "Clear", [ sb ] -> pure' "fable_rt.sbClear($0)" [ sb ] (mapType ctx r t)
    | ("System.Object" | "System.Text.StringBuilder" | "Microsoft.FSharp.Core.Operators"), "ToString", [ sb ] when
        (match sb.Type with
         | Fable.DeclaredType(ent, _) -> ent.FullName = "System.Text.StringBuilder"
         | _ -> false)
        ->
        pure' "fable_rt.sbToString($0)" [ sb ] tStr

    // ---- Split, Join, Format ----
    | "System.String", "Split", s0 :: rest ->
        // (separators, then a count of parts (a number), then options (an enum))
        let isEnum (x: Fable.Expr) =
            match x.Type with
            | Fable.Number(_, Fable.NumberInfo.IsEnum _) -> true
            | _ -> false

        let sepArg, more =
            match rest with
            | [] -> None, []
            | x :: more -> Some x, more

        let count =
            match more with
            | c :: _ when not (isEnum c) -> lw ctx c
            | _ -> ELit("2147483647", tI32)

        let opts =
            match more |> List.tryFind isEnum with
            | Some o -> lw ctx o
            | None -> ELit("0", tI32)

        let call macro (xs: Fable.Expr list) =
            ctx.State.UsesRuntime <- true

            bindArgs
                ctx
                (s0 :: xs |> List.map (lw ctx) |> fun l -> l @ [ count; opts ])
                (fun irs -> ERt(macro, irs, mapType ctx r t))

        match sepArg |> Option.map (fun a -> a, a.Type) with
        | None -> call "fable_rt.strSplitChars($0, &.{}, $1, @intCast($2))" []
        | Some(c, Fable.Char) -> call "fable_rt.strSplitChars($0, &.{ $1 }, $2, @intCast($3))" [ c ]
        | Some(a, Fable.Array(Fable.Char, _)) -> call "fable_rt.strSplitChars($0, $1.items, $2, @intCast($3))" [ a ]
        | Some(sep, Fable.String) -> call "fable_rt.strSplitString($0, $1, $2, @intCast($3))" [ sep ]
        | Some(a, Fable.Array(Fable.String, _)) -> call "fable_rt.strSplitStrings($0, $1.items, $2, @intCast($3))" [ a ]
        | _ -> fail r "the Zig target does not support this String.Split yet"
    | "System.String", "Join", [ sep; items ]
    | "Microsoft.FSharp.Core.StringModule", "Concat", [ sep; items ] when sep.Type = Fable.String ->
        let (Uncast inner) = items

        let listIr =
            match inner.Type with
            | Fable.Array(item, _) ->
                bindArgs
                    ctx
                    [ lw ctx inner ]
                    (fun xs -> EEmit("fable_rt.arrayToList($0)", xs, TEnt(listEnt ctx.State, [ mapType ctx r item ])))
            | t when isSeqType t ->
                let itemTy = itemOf (lw ctx inner)

                bindArgs
                    ctx
                    [ lw ctx inner ]
                    (fun xs ->
                        ECall(libraryTarget ctx "Seq" "toList", [ itemTy ], xs, TEnt(listEnt ctx.State, [ itemTy ]))
                    )
            | _ ->
                match forInSource ctx inner with
                | Some(listExpr, "list") -> listExpr
                | _ -> fail r "the Zig target cannot join a value of this type yet (%A)" inner.Type

        ctx.State.UsesRuntime <- true
        bindArgs ctx [ lw ctx sep; listIr ] (fun xs -> EEmit("fable_rt.joinList($0, $1)", xs, tStr))
    | "System.String", "Format", (Fable.Value(Fable.StringConstant fmt, _)) :: values ->
        compositeFormat ctx r fmt values t
    // (a culture changes nothing here: formatting is the invariant culture's)
    | "System.String", "Format", culture :: (Fable.Value(Fable.StringConstant fmt, _)) :: values when isCulture culture ->
        compositeFormat ctx r fmt values t
    | "System.Text.StringBuilder", "AppendFormat", sb :: rest ->
        let rest =
            match rest with
            | culture :: more when isCulture culture -> more
            | _ -> rest

        match rest with
        | (Fable.Value(Fable.StringConstant fmt, _)) :: values ->
            bindArgs
                ctx
                [ lw ctx sb; compositeFormat ctx r fmt values Fable.String ]
                (fun xs -> EEmit("fable_rt.sbAppend($0, $1)", xs, mapType ctx r t))
        | _ -> fail r "the Zig target needs the format of AppendFormat to be a literal"
    | _, "ToString", [ x; culture ] when isCulture culture ->
        dotnetCall
            ctx
            r
            "Microsoft.FSharp.Core.Operators"
            "ToString"
            { info with
                Args = [ x ]
                ThisArg = None
            }
            t
    | "System.String", "LastIndexOf", [ s; x; start ] when x.Type = Fable.Char && isInt start ->
        rt "fable_rt.strLastIndexOfCharFrom($0, $1, $2)" [ s; x; start ] tI32
    | "System.String", "LastIndexOf", [ s; x; start ] when x.Type = Fable.String && isInt start ->
        rt "fable_rt.strLastIndexOfFrom($0, $1, $2)" [ s; x; start ] tI32
    | "System.String", "LastIndexOf", [ s; x; Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 4, _), _) ] when
        x.Type = Fable.String
        ->
        rt "fable_rt.strLastIndexOf($0, $1)" [ s; x ] tI32
    | "System.String",
      "LastIndexOf",
      [ s; x; start; Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 4, _), _) ] when x.Type = Fable.String ->
        rt "fable_rt.strLastIndexOfFrom($0, $1, $2)" [ s; x; start ] tI32
    | "System.String", "IndexOf", [ s; x; start; Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 4, _), _) ] when
        x.Type = Fable.String
        ->
        rt "fable_rt.strIndexOf($0, $1, $2)" [ s; x; start ] tI32
    | "System.String", "IndexOfAny", [ s; Uncast chars ] ->
        rt "fable_rt.strIndexOfAny($0, $1, 0, null)" [ s; chars ] tI32
    | "System.String", "IndexOfAny", [ s; Uncast chars; start ] ->
        rt "fable_rt.strIndexOfAny($0, $1, $2, null)" [ s; chars; start ] tI32
    | "System.String", "IndexOfAny", [ s; Uncast chars; start; count ] ->
        rt "fable_rt.strIndexOfAny($0, $1, $2, $3)" [ s; chars; start; count ] tI32
    | "System.String", ("Trim" | "TrimStart" | "TrimEnd"), [ s; Uncast chars ] when
        (match chars.Type with
         | Fable.Array(Fable.Char, _) -> true
         | _ -> false)
        ->
        let ends =
            match name with
            | "Trim" -> "true, true"
            | "TrimStart" -> "true, false"
            | _ -> "false, true"

        rt $"fable_rt.strTrimAny($0, %s{ends}, $1)" [ s; chars ] tStr
    | "System.String", ("Trim" | "TrimStart" | "TrimEnd"), s :: chars when
        chars.Length > 1 && chars |> List.forall (fun c -> c.Type = Fable.Char)
        ->
        let arr =
            Fable.Value(Fable.NewArray(Fable.ArrayValues chars, Fable.Char, Fable.MutableArray), r)

        dotnetCall
            ctx
            r
            entity
            name
            { info with
                Args = [ arr ]
                ThisArg = Some s
            }
            t
    | "System.String", "ToCharArray", [ s; start; n ] ->
        rt "fable_rt.strToCharsRange($0, $1, $2)" [ s; start; n ] (mapType ctx r t)
    | "System.String", ".ctor", [ Uncast chars; start; n ] when
        (match chars.Type with
         | Fable.Array(Fable.Char, _) -> true
         | _ -> false)
        ->
        rt "fable_rt.strOfCharsRange($0, $1, $2)" [ chars; start; n ] tStr
    | "System.String", "Join", [ sep; Uncast values; start; n ] when
        (match values.Type with
         | Fable.Array(Fable.String, _) -> true
         | _ -> false)
        ->
        rt "fable_rt.strJoinRange($0, $1, $2, $3)" [ sep; values; start; n ] tStr
    | "System.String",
      "Compare",
      [ a; ia; b; ib; n; Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 kind, _), _) ] when
        kind = 4 || kind = 5
        ->
        rt
            (if kind = 5 then
                 "fable_rt.strCompareRange($0, $1, $2, $3, $4, true)"
             else
                 "fable_rt.strCompareRange($0, $1, $2, $3, $4, false)")
            [ a; ia; b; ib; n ]
            tI32
    // (`String.Concat` of a sequence, a list or an array of strings: their join)
    | "System.String", "Concat", [ Uncast values ] when values.Type <> Fable.String ->
        dotnetCall
            ctx
            r
            "System.String"
            "Join"
            { info with
                Args = [ Fable.Value(Fable.StringConstant "", None); values ]
                ThisArg = None
            }
            t
    | "Microsoft.FSharp.Core.Operators.OperatorIntrinsics", "GetStringSlice", [ s; lo; hi ] ->
        rt "fable_rt.strSliceRange($0, $1, $2)" [ s; lo; hi ] tStr
    | "System.Environment", "get_NewLine", [] -> pure' "fable_rt.newLine()" [] tStr
    | "System.Uri", "EscapeDataString", [ s ] -> rt "fable_rt.uriEscape($0, false)" [ s ] tStr
    | "System.Uri", "EscapeUriString", [ s ] -> rt "fable_rt.uriEscape($0, true)" [ s ] tStr
    | "System.Uri", "UnescapeDataString", [ s ] -> rt "fable_rt.uriUnescape($0)" [ s ] tStr
    | "System.Text.StringBuilder", ("get_Chars" | "get_Item"), [ sb; i ] ->
        rt "fable_rt.sbCharAt($0, $1)" [ sb; i ] (TPrim "u16")
    | "System.Text.StringBuilder", ("set_Chars" | "set_Item"), [ sb; i; c ] ->
        rt "fable_rt.sbSetChar($0, $1, $2)" [ sb; i; c ] tVoid
    | "System.Text.StringBuilder", "ToString", [ sb; start; n ] ->
        rt "fable_rt.sbToStringRange($0, $1, $2)" [ sb; start; n ] tStr
    | "System.Text.StringBuilder", "Replace", [ sb; a; b ] when a.Type = Fable.Char ->
        pure' "fable_rt.sbReplaceChar($0, $1, $2)" [ sb; a; b ] (mapType ctx r t)
    | "System.Text.StringBuilder", "Append", [ sb; c; n ] when c.Type = Fable.Char && isInt n ->
        rt "fable_rt.sbAppendRepeat($0, $1, $2)" [ sb; c; n ] (mapType ctx r t)
    | "System.Text.StringBuilder", "Replace", [ sb; a; b ] when a.Type = Fable.String ->
        rt "fable_rt.sbReplace($0, $1, $2)" [ sb; a; b ] (mapType ctx r t)
    | "System.String", "ToCharArray", [ s0 ] -> rt "fable_rt.strToChars($0)" [ s0 ] (mapType ctx r t)
    | "System.String", ".ctor", [ chars ] when
        (match chars.Type with
         | Fable.Array(Fable.Char, _) -> true
         | _ -> false)
        ->
        pure' "fable_rt.strOfChars($0)" [ chars ] tStr
    | "System.Char",
      ("IsDigit" | "IsLetter" | "IsLetterOrDigit" | "IsUpper" | "IsLower" | "IsNumber" | "IsPunctuation" | "IsSymbol" | "IsSeparator" | "IsControl" | "IsSurrogate"),
      [ c ] -> pure' $"fable_rt.unicode.is%s{name.Substring 2}($0)" [ c ] tBool
    | "System.Char", "GetNumericValue", [ c ] -> pure' "fable_rt.charNumericValue($0)" [ c ] tF64
    | "System.Char",
      ("IsDigit" | "IsLetter" | "IsLetterOrDigit" | "IsUpper" | "IsLower" | "IsNumber" | "IsPunctuation" | "IsSymbol" | "IsSeparator" | "IsControl" | "IsSurrogate" | "IsWhiteSpace"),
      [ s; i ] when s.Type = Fable.String ->
        rt $"fable_rt.strCharIs($0, $1, fable_rt.unicode.is%s{name.Substring 2})" [ s; i ] tBool
    | "System.Char", "GetUnicodeCategory", [ c ] -> pure' "fable_rt.charCategory($0)" [ c ] tI32
    | "System.Char", "GetUnicodeCategory", [ s; i ] -> rt "fable_rt.strCharCategory($0, $1)" [ s; i ] tI32
    | "System.Char", "ToString", [ c ] when c.Type = Fable.Char ->
        dotnetCall
            ctx
            r
            "Microsoft.FSharp.Core.Operators"
            "ToString"
            { info with
                Args = [ c ]
                ThisArg = None
            }
            t
    // comparisons that say how: ordinal, or ordinal with the case ignored (a culture's order is
    // not known here)
    | "System.String", ("Equals" | "StartsWith" | "EndsWith" | "IndexOf" | "Compare" | "Contains"), _ when
        (match List.tryLast args with
         | Some last ->
             match last.Type with
             | Fable.Number(_, Fable.NumberInfo.IsEnum ent) -> ent.FullName = "System.StringComparison"
             | _ -> false
         | None -> false)
        ->
        let how =
            match List.last args with
            | Fable.Value(Fable.NumberConstant(v, _), _) ->
                match v with
                | Fable.NumberValue.Int32 n -> n
                | _ -> -1
            | _ -> -1

        let a, b =
            match args with
            | [ a; b; _ ] -> a, b
            | _ -> fail r "the Zig target does not support this String.%s yet" name

        match how with
        | 4 ->
            match name with
            | "Equals" -> pure' "fable_rt.strEql($0, $1)" [ a; b ] tBool
            | "StartsWith" -> rt "fable_rt.strStartsWith($0, $1)" [ a; b ] tBool
            | "EndsWith" -> rt "fable_rt.strEndsWith($0, $1)" [ a; b ] tBool
            | "IndexOf" when b.Type = Fable.Char -> rt "fable_rt.strIndexOfChar($0, $1, 0)" [ a; b ] tI32
            | "IndexOf" -> rt "fable_rt.strIndexOf($0, $1, 0)" [ a; b ] tI32
            | "Contains" when b.Type = Fable.Char -> rt "fable_rt.strContainsChar($0, $1)" [ a; b ] tBool
            | "Contains" -> rt "fable_rt.strContains($0, $1)" [ a; b ] tBool
            | _ -> pure' "fable_rt.strCompare($0, $1)" [ a; b ] tI32
        | 5 ->
            match name with
            | "Equals" -> pure' "fable_rt.strEqualsIgnoreCase($0, $1)" [ a; b ] tBool
            | "StartsWith" -> rt "fable_rt.strStartsWithIgnoreCase($0, $1)" [ a; b ] tBool
            | "EndsWith" -> rt "fable_rt.strEndsWithIgnoreCase($0, $1)" [ a; b ] tBool
            | "IndexOf" -> rt "fable_rt.strIndexOfIgnoreCase($0, $1)" [ a; b ] tI32
            | "Contains" ->
                bindArgs
                    ctx
                    [ rt "fable_rt.strIndexOfIgnoreCase($0, $1)" [ a; b ] tI32 ]
                    (fun xs -> EPrim("ge", [ xs.Head; ELit("0", tI32) ], tBool))
            | _ -> pure' "fable_rt.strCompareIgnoreCase($0, $1)" [ a; b ] tI32
        | _ ->
            fail
                r
                "the Zig target does not support comparing strings by a culture (String.%s with StringComparison %d): use Ordinal or OrdinalIgnoreCase"
                name
                how

    // ---- chars: each code unit to what .NET maps it to (there is no current culture) ----
    | "System.Char", ("ToUpper" | "ToUpperInvariant"), [ c ] -> pure' "fable_rt.unicode.toUpper($0)" [ c ] tChar
    | "System.Char", ("ToLower" | "ToLowerInvariant"), [ c ] -> pure' "fable_rt.unicode.toLower($0)" [ c ] tChar
    | "System.Char", "IsWhiteSpace", [ c ] -> pure' "fable_rt.unicode.isWhiteSpace($0)" [ c ] tBool
    // ---- strings ----
    // (what a null string or an argument out of range raises on .NET, it raises here: those
    // calls are `ERt`. The `String` module takes a null string for an empty one.)
    | "Microsoft.FSharp.Core.Operators.Unchecked", "DefaultOf", [] when t = Fable.String ->
        ELit("@as(fable_rt.String, null)", tStr)
    | "Microsoft.FSharp.Core.Operators.Unchecked", "DefaultOf", [] ->
        match t with
        | Fable.Number(BigInt, _) -> pure' "fable_rt.bigOf(@as(i32, 0))" [] (mapType ctx r t)
        | Fable.Number(Decimal, _) -> ELit("fable_rt.NetDecimal{}", mapType ctx r t)
        | Fable.Number _
        | Fable.Char -> ELit("0", mapType ctx r t)
        | Fable.Boolean -> ELit("false", tBool)
        | Fable.Any -> ELit("@as(fable_rt.Any, null)", tAny)
        | Fable.Option(inner, _)
        | Fable.Nullable(inner, _) -> ECon(mapType ctx r t, "None", [], None)
        // (a union of one case without fields has one value, which stands for it; null on
        // .NET, where nothing but a test for null tells them apart)
        | Fable.DeclaredType(entRef, []) when
            (match ctx.Com.TryGetEntity entRef with
             | Some ent ->
                 ent.IsFSharpUnion
                 && ent.UnionCases.Length = 1
                 && ent.UnionCases.Head.UnionCaseFields.IsEmpty
             | None -> false)
            ->
            let ent = ctx.Com.GetEntity entRef
            ECon(mapType ctx r t, ent.UnionCases.Head.Name, [], None)
        | _ -> fail r "the Zig target has no default value of this type (%A); .NET's is null" t
    | "Microsoft.FSharp.Core.Operators", "IsNull", [ x ] when x.Type = Fable.String || x.Type = Fable.Any ->
        pure' "($0 == null)" [ x ] tBool
    | "System.Decimal", "Equals", [ a; b ] when isDec a && isDec b -> pure' "fable_rt.eql($0, $1)" [ a; b ] tBool
    // `x.Equals y` and `x.CompareTo y` of numbers, chars and bools (NaN equals NaN, as .NET's
    // `Equals` has it)
    | ("System.Double" | "System.Single" | "System.Int32" | "System.Int64" | "System.Int16" | "System.SByte" | "System.Byte" | "System.UInt16" | "System.UInt32" | "System.UInt64" | "System.Char" | "System.Boolean" | "System.Decimal" | "System.Numerics.BigInteger"),
      ("Equals" | "CompareTo"),
      [ a; b ] when a.Type = b.Type ->
        if name = "Equals" then
            pure' "(fable_rt.compare($0, $1) == 0)" [ a; b ] tBool
        else
            pure' "fable_rt.compare($0, $1)" [ a; b ] tI32
    | "System.String", "get_Length", [ s ] when neverNull s -> pure' "fable_rt.strLength($0)" [ s ] tI32
    | "System.String", "get_Length", [ s ] -> rt "fable_rt.strLen($0)" [ s ] tI32
    | "Microsoft.FSharp.Core.StringModule", "Length", [ s ] -> pure' "fable_rt.strLength($0)" [ s ] tI32
    | "System.String", "get_Chars", [ s; i ]
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions", "GetString", [ s; i ] ->
        rt "fable_rt.strAt($0, $1)" [ s; i ] tChar
    | "System.String", "IsNullOrEmpty", [ s ] -> pure' "fable_rt.strIsNullOrEmpty($0)" [ s ] tBool
    | "System.String", "IsNullOrWhiteSpace", [ s ] -> pure' "fable_rt.strIsNullOrWhiteSpace($0)" [ s ] tBool
    | "System.String", "CompareOrdinal", [ a; b ] -> pure' "fable_rt.strCompare($0, $1)" [ a; b ] tI32
    // `x.Equals y` of a value of F#'s: its equality (structural for records, unions, lists, ...)
    // (`Equals` of arrays is that of .NET's objects: they are the same array)
    | "System.Object", "Equals", Uncast a :: Uncast b :: _ when
        a.Type = b.Type
        && (
            match a.Type with
            | Fable.Array _ -> true
            | _ -> false
        )
        ->
        pure' "($0 == $1)" [ a; b ] tBool
    | "System.Object", "Equals", Uncast a :: Uncast b :: _ when a.Type = b.Type && a.Type <> Fable.String ->
        bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim("eql", xs, tBool))
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
    | "Microsoft.FSharp.Core.Operators", ("op_Addition" | "op_Subtraction"), [ a; _ ] when
        (match a.Type with
         | Fable.DeclaredType(ent, _) -> ent.FullName = setName
         | _ -> false)
        ->
        let fn =
            if name = "op_Addition" then
                "opAddition"
            else
                "opSubtraction"

        let item =
            match a.Type with
            | Fable.DeclaredType(_, [ item ]) -> item
            | _ -> Fable.Any

        libraryCall
            ctx
            r
            "Set"
            fn
            { info with
                GenericArgs = [ item ]
                MemberRef = None
                SignatureArgTypes = []
            }
            args
            t
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
        // (the left string is given up to the append, which grows it in place when nothing
        // else refers to it: `s <- s + x` in a loop is not quadratic)
        | [ a; b ] -> bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EEmit("fable_rt.strAppend($0, $1)", xs, tStr))
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
    // `x.ToString("N2")` of a number: one of .NET's standard formats
    | _, "ToString", [ x; Fable.Value(Fable.StringConstant net, _) ] when
        (match x.Type with
         | Fable.Number _ -> true
         | _ -> false)
        ->
        checkNetFormat r net
        let net = zigEscape net

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs ->
                EEmit(
                    $"fable_rt.format(.{{ fable_rt.arg(.{{ .net = \"%s{net}\" }}, %s{typedArg ctx r x 0}) }})",
                    xs,
                    tStr
                )
            )
    | _, "ToString", [ x ] when
        entity <> "Microsoft.FSharp.Core.Operators"
        && (
            match x.Type with
            | Fable.Number _ -> true
            | _ -> false
        )
        ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t
    | ("Microsoft.FSharp.Core.Operators" | "System.Object"), "ToString", [ x ] when x.Type = Fable.Any ->
        if entity = "System.Object" then
            rt "fable_rt.anyToString($0, false)" [ x ] tStr
        else
            rt "fable_rt.anyToString($0, true)" [ x ] tStr
    | ("Microsoft.FSharp.Core.Operators" | "System.Object"), "ToString", [ x ] when (ownToString ctx x.Type).IsSome ->
        bindArgs ctx [ lw ctx x ] (fun xs -> ECall((ownToString ctx x.Type).Value, [], xs @ [ EUnit ], tStr))
    | ("Microsoft.FSharp.Core.Operators" | "System.Object"), "ToString", [ x ] when x.Type <> unByref x.Type ->
        dotnetCall
            ctx
            r
            entity
            name
            { info with
                Args = [ readByref x ]
                ThisArg = None
            }
            t
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
        | Fable.Option _
        | Fable.Tuple _
        | Fable.List _ -> pure' "fable_rt.toText($0)" [ x ] tStr
        | Fable.DeclaredType(ent, _) when ent.FullName = mapName || ent.FullName = setName ->
            pure' "fable_rt.toText($0)" [ x ] tStr
        // (an object: its class's ToString, or .NET's name of its class)
        | Fable.DeclaredType _ when (objOfType ctx r x.Type).IsSome -> rt "fable_rt.objText($0)" [ x ] tStr
        | Fable.Char ->
            bindArgs
                ctx
                [ lw ctx x ]
                (fun xs -> EEmit("fable_rt.format(.{ fable_rt.arg(.{ .kind = 'c' }, @as(u16, $0)) })", xs, tStr))
        | Fable.Boolean
        | Fable.Number _ ->
            bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"fable_rt.format(.{{ %s{typedArg ctx r x 0} }})", xs, tStr))
        // (a type parameter: what the type it stands for gives, known when the Zig is compiled)
        | Fable.GenericParam _ -> rt "fable_rt.genericText($0)" [ x ] tStr
        | other -> fail r "the Zig target cannot turn a value of this type into text yet (%A)" other
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
        raiseDotnet ctx r "System.ArgumentException" (withParameter ctx (lw ctx msg) arg) t
    | "Microsoft.FSharp.Core.Operators", "NullArg", [ arg ] ->
        let message = ELit(stringLiteral "Value cannot be null.", tStr)
        raiseDotnet ctx r "System.ArgumentNullException" (withParameter ctx message arg) t
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
    | "Microsoft.FSharp.Collections.FSharpList`1", "get_Empty", _ -> ECon(mapType ctx r t, "Empty", [], None)
    | "System.IO.Path", "GetFileName", [ path ] -> pure' "fable_rt.pathFileName($0)" [ path ] tStr
    | "System.Exception", "get_InnerException", [ x ] -> rt "fable_rt.exnInner($0)" [ x ] tExn
    | "Microsoft.FSharp.Core.Operators", "IsNull", [ Fable.Call(Fable.Import(imp, _, _), inner, _, _) ] when
        imp.Selector = "get_InnerException"
        ->
        pure' "fable_rt.exnHasNoInner($0)" [ inner.ThisArg.Value ] tBool
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
    // ---- decimal: a value of the runtime (`fable_rt.NetDecimal`) ----
    | ("Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicFunctions" | "System.Decimal"),
      ("MakeDecimal" | ".ctor"),
      [ lo; mid; hi; negative; scale ] ->
        match lo, mid, hi, negative, scale with
        | Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 lo, _), _),
          Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 mid, _), _),
          Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 hi, _), _),
          Fable.Value(Fable.BoolConstant negative, _),
          Fable.Value(Fable.NumberConstant(Fable.NumberValue.UInt8 scale, _), _) ->
            let m =
                (bigint (uint32 hi) <<< 64) + (bigint (uint32 mid) <<< 32) + bigint (uint32 lo)

            let m =
                if negative then
                    -m
                else
                    m

            decLit (string m) (int scale)
        | _ -> rt "fable_rt.decOfParts($0, $1, $2, $3, $4)" [ lo; mid; hi; negative; scale ] tDec
    | "System.Decimal", ".ctor", [ Uncast bits ] when
        (match bits.Type with
         | Fable.Array(Fable.Number(Int32, _), _) -> true
         | _ -> false)
        ->
        rt "fable_rt.decOfBits($0)" [ bits ] tDec
    | "System.Decimal", "GetBits", [ d ] -> pure' "fable_rt.decGetBits($0)" [ d ] (mapType ctx r t)
    | "System.Decimal", ("get_Zero" | "get_One" | "get_MinusOne" | "get_MaxValue" | "get_MinValue"), [] ->
        match name with
        | "get_Zero" -> decLit "0" 0
        | "get_One" -> decLit "1" 0
        | "get_MinusOne" -> decLit "-1" 0
        | "get_MaxValue" -> decLit "79228162514264337593543950335" 0
        | _ -> decLit "-79228162514264337593543950335" 0
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.ExtraTopLevelOperators" | "System.Convert"),
      "ToDecimal",
      [ x ] ->
        match x.Type with
        | Fable.String -> rt "fable_rt.decParse($0, true)" [ x ] tDec
        | _ when isDec x -> lw ctx x
        | _ -> rt $"fable_rt.decOf(%s{typedArg ctx r x 0})" [ x ] tDec
    | "System.Decimal", (".ctor" | "op_Implicit" | "op_Explicit"), [ x ] when not (isDec x) ->
        rt $"fable_rt.decOf(%s{typedArg ctx r x 0})" [ x ] tDec
    | "System.Decimal", "Parse", [ x ] -> rt "fable_rt.decParse($0, false)" [ x ] tDec
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Decimal"),
      ("op_Addition" | "op_Subtraction" | "op_Multiply" | "op_Division" | "op_Modulus" | "Add" | "Subtract" | "Multiply" | "Divide" | "Remainder"),
      [ a; b ] when isDec a ->
        let f =
            match name with
            | "op_Addition"
            | "Add" -> "decAdd"
            | "op_Subtraction"
            | "Subtract" -> "decSub"
            | "op_Multiply"
            | "Multiply" -> "decMul"
            | "op_Division"
            | "Divide" -> "decDiv"
            | _ -> "decRem"

        rt $"fable_rt.%s{f}($0, $1)" [ a; b ] tDec
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Decimal"),
      ("op_UnaryNegation" | "Negate"),
      [ a ] when isDec a -> pure' "fable_rt.decNeg($0)" [ a ] tDec
    | ("Microsoft.FSharp.Core.Operators" | "System.Decimal"), "op_UnaryPlus", [ a ] when isDec a -> lw ctx a
    | ("Microsoft.FSharp.Core.Operators" | "System.Math" | "System.Decimal"), "Abs", [ a ] when isDec a ->
        pure' "fable_rt.decAbs($0)" [ a ] tDec
    | ("Microsoft.FSharp.Core.Operators" | "System.Math" | "System.Decimal"), "Sign", [ a ] when isDec a ->
        pure' "fable_rt.decSign($0)" [ a ] tI32
    | ("Microsoft.FSharp.Core.Operators" | "System.Math" | "System.Decimal"), "Round", [ a ] when isDec a ->
        pure' "fable_rt.decRound($0, 0, true)" [ a ] tDec
    | ("System.Math" | "System.Decimal"), "Round", [ a; digits ] when isDec a && isInt digits ->
        pure' "fable_rt.decRound($0, $1, true)" [ a; digits ] tDec
    | ("Microsoft.FSharp.Core.Operators" | "System.Math" | "System.Decimal"), ("Floor" | "Ceiling" | "Truncate"), [ a ] when
        isDec a
        ->
        let how =
            match name with
            | "Floor" -> "down"
            | "Ceiling" -> "up"
            | _ -> "toward_zero"

        pure' $"fable_rt.decWhole($0, .%s{how})" [ a ] tDec
    | "System.Decimal", "Compare", [ a; b ] -> pure' "fable_rt.decCompare($0, $1)" [ a; b ] tI32
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Decimal" | "System.Convert"),
      _,
      [ x ] when
        isDec x
        && (name.StartsWith("To", System.StringComparison.Ordinal) || name = "op_Explicit")
        && name <> "ToString"
        && name <> "ToDecimal"
        ->
        let ty = mapType ctx r t

        if isFloatTy ty then
            pure' $"fable_rt.decToFloat(%s{zigTypeOf ty}, $0)" [ x ] ty
        elif intBits ty > 0 then
            rt $"fable_rt.decToInt(%s{zigTypeOf ty}, $0)" [ x ] ty
        else
            fail r "the Zig target cannot convert a decimal to %A yet" t

    // ---- bigint: a counted cell of the runtime (`fable_rt.BigInt`) ----
    | "Microsoft.FSharp.Core.NumericLiterals.NumericLiteralI", ("FromZero" | "FromOne"), ([] | [ _ ]) ->
        pure'
            (if name = "FromZero" then
                 "fable_rt.bigOf(@as(i32, 0))"
             else
                 "fable_rt.bigOf(@as(i32, 1))")
            []
            tBig
    | "Microsoft.FSharp.Core.NumericLiterals.NumericLiteralI", ("FromInt32" | "FromInt64"), [ x ] ->
        pure' $"fable_rt.bigOf(%s{typedArg ctx r x 0})" [ x ] tBig
    | "Microsoft.FSharp.Core.NumericLiterals.NumericLiteralI", "FromString", [ x ] ->
        rt "fable_rt.bigParse($0)" [ x ] tBig
    | "System.Numerics.BigInteger", ".ctor", [ x ] when not (isBig x) ->
        pure' $"fable_rt.bigOf(%s{typedArg ctx r x 0})" [ x ] tBig
    | "System.Numerics.BigInteger", "get_Zero", [] -> pure' "fable_rt.bigOf(@as(i32, 0))" [] tBig
    | "System.Numerics.BigInteger", "get_One", [] -> pure' "fable_rt.bigOf(@as(i32, 1))" [] tBig
    | "System.Numerics.BigInteger", "get_MinusOne", [] -> pure' "fable_rt.bigOf(@as(i32, -1))" [] tBig
    | "System.Numerics.BigInteger", "Parse", [ x ] -> rt "fable_rt.bigParse($0)" [ x ] tBig
    | "System.Numerics.BigInteger", "Pow", [ x; n ]
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked"), "PowInteger", [ x; n ] when
        isBig x
        ->
        rt "fable_rt.bigPow($0, $1)" [ x; n ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Numerics.BigInteger"),
      ("op_Addition" | "op_Subtraction" | "op_Multiply" | "Add" | "Subtract" | "Multiply"),
      [ a; b ] when isBig a ->
        let f =
            match name with
            | "op_Addition"
            | "Add" -> "bigAdd"
            | "op_Subtraction"
            | "Subtract" -> "bigSub"
            | _ -> "bigMul"

        pure' $"fable_rt.%s{f}($0, $1)" [ a; b ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "System.Numerics.BigInteger"),
      ("op_Division" | "op_Modulus" | "Divide" | "Remainder"),
      [ a; b ] when isBig a ->
        let quotient =
            if name = "op_Division" || name = "Divide" then
                "true"
            else
                "false"

        rt ("fable_rt.bigDivRem($0, $1, " + quotient + ")") [ a; b ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Numerics.BigInteger"),
      ("op_UnaryNegation" | "Negate"),
      [ a ] when isBig a -> pure' "fable_rt.bigNeg($0)" [ a ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "System.Numerics.BigInteger"), "op_UnaryPlus", [ a ] when isBig a -> lw ctx a
    | ("Microsoft.FSharp.Core.Operators" | "System.Numerics.BigInteger" | "System.Math"), "Abs", [ a ] when isBig a ->
        pure' "fable_rt.bigAbs($0)" [ a ] tBig
    | ("Microsoft.FSharp.Core.Operators" | "System.Math"), "Sign", [ a ] when isBig a ->
        pure' "fable_rt.bigSign($0)" [ a ] tI32
    | "System.Numerics.BigInteger", "get_Sign", [ a ] -> pure' "fable_rt.bigSign($0)" [ a ] tI32
    | "System.Numerics.BigInteger", "get_IsZero", [ a ] -> pure' "(fable_rt.bigSign($0) == 0)" [ a ] tBool
    | "System.Numerics.BigInteger", "Compare", [ a; b ] -> pure' "fable_rt.bigCompare($0, $1)" [ a; b ] tI32
    | ("Microsoft.FSharp.Core.Operators" | "Microsoft.FSharp.Core.Operators.Checked" | "System.Numerics.BigInteger"),
      _,
      [ x ] when
        isBig x
        && (name.StartsWith("To", System.StringComparison.Ordinal) || name = "op_Explicit")
        && name <> "ToString"
        ->
        let ty = mapType ctx r t

        if isFloatTy ty then
            pure' $"fable_rt.bigToFloat(%s{zigTypeOf ty}, $0)" [ x ] ty
        elif intBits ty > 0 then
            rt $"fable_rt.bigToInt(%s{zigTypeOf ty}, $0)" [ x ] ty
        elif ty = tBig then
            lw ctx x
        else
            fail r "the Zig target cannot convert a bigint to %A yet" t
    | ("Microsoft.FSharp.Core.Operators" | "System.Numerics.BigInteger"), ("ToBigInt" | "op_Implicit"), [ x ] ->
        pure' $"fable_rt.bigOf(%s{typedArg ctx r x 0})" [ x ] tBig

    // ---- `open Checked`: whole-number arithmetic and conversions that raise on overflow ----
    | "Microsoft.FSharp.Core.Operators.Checked", ("op_Addition" | "op_Subtraction" | "op_Multiply"), [ a; b ] ->
        let ty = mapType ctx r a.Type

        if intBits ty > 0 then
            let f =
                match name with
                | "op_Addition" -> "Add"
                | "op_Subtraction" -> "Sub"
                | _ -> "Mul"

            rt $"fable_rt.checked%s{f}(@as($R, $0), $1)" [ a; b ] ty
        else
            let op =
                match name with
                | "op_Addition" -> "add"
                | "op_Subtraction" -> "sub"
                | _ -> "mul"

            bindArgs ctx [ lw ctx a; lw ctx b ] (fun xs -> EPrim(op, xs, ty))
    | "Microsoft.FSharp.Core.Operators.Checked", "op_UnaryNegation", [ a ] ->
        let ty = mapType ctx r a.Type

        if intBits ty > 0 then
            rt "fable_rt.checkedNeg(@as($R, $0))" [ a ] ty
        else
            bindArgs ctx [ lw ctx a ] (fun xs -> EPrim("neg", xs, ty))
    | "Microsoft.FSharp.Core.Operators.Checked", _, [ x ] when name.StartsWith("To", System.StringComparison.Ordinal) ->
        let ty = mapType ctx r t

        if x.Type = Fable.String then
            dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t
        elif intBits ty > 0 then
            bindArgs ctx [ lw ctx x ] (fun xs -> ERt($"fable_rt.checkedConv(%s{zigTypeOf ty}, $0)", xs, ty))
        else
            dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t

    // `use x = resource` in `seq { }`: what follows, then `x.Dispose()`
    | "Microsoft.FSharp.Core.CompilerServices.RuntimeHelpers", "EnumerateUsing", [ resource; body ] ->
        let rid = AST.makeTypedIdent resource.Type "resource"

        let dispose =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = "Dispose"
                        Path = Replacements.DotnetPrefix + "System.IDisposable"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = true))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(thisArg = Fable.IdentExpr rid),
                Fable.Unit,
                r
            )

        let unitArg = AST.makeTypedIdent Fable.Unit "unitVar"

        let thenFinally =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = "EnumerateThenFinally"
                        Path =
                            Replacements.DotnetPrefix
                            + "Microsoft.FSharp.Core.CompilerServices.RuntimeHelpers"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                { info with
                    Args =
                        [
                            Fable.CurriedApply(body, [ Fable.IdentExpr rid ], t, r)
                            Fable.Lambda(unitArg, dispose, None)
                        ]
                    GenericArgs =
                        (match t with
                         | Fable.DeclaredType(_, [ item ]) -> [ item ]
                         | _ -> [])
                    SignatureArgTypes = []
                    MemberRef = None
                },
                t,
                r
            )

        lw ctx (Fable.Let(rid, resource, thenFinally))
    // ---- enums: numbers of their underlying type ----
    | "System.Enum", "HasFlag", [ v; Uncast flag ] -> pure' "(($0 & $1) == $1)" [ v; flag ] tBool
    | "Microsoft.FSharp.Core.LanguagePrimitives", ("EnumOfValue" | "EnumToValue"), [ x ] ->
        if mapType ctx r x.Type = mapType ctx r t then
            lw ctx x
        else
            bindArgs ctx [ lw ctx x ] (fun xs -> EPrim("conv", xs, mapType ctx r t))
    | "System.Enum", "TryParse", s :: rest ->
        let enumTy =
            match info.GenericArgs with
            | [ e ] -> e
            | _ -> fail r "internal: Enum.TryParse"

        match enumTy with
        | Fable.Number(_, Fable.NumberInfo.IsEnum entRef) ->
            let cases =
                match ctx.Com.TryGetEntity entRef with
                | Some ent ->
                    ent.FSharpFields
                    |> List.choose (fun f ->
                        match f.LiteralValue with
                        | Some v when f.IsStatic -> Some(f.Name, string v)
                        | _ -> None
                    )
                | None -> fail r "the Zig target cannot see the cases of %s" entRef.FullName

            let num = zigTypeName (mapType ctx r enumTy)
            let names = cases |> List.map (fun (n, _) -> "\"" + n + "\"") |> String.concat ", "
            let values = cases |> List.map snd |> String.concat ", "

            let macro =
                $"fable_rt.enumTryParse($R, %s{num}, $0, &.{{ %s{names} }}, &[_]%s{num}{{ %s{values} }})"

            let pairTy = TTuple [ tBool; mapType ctx r enumTy ]

            match rest with
            // (`Enum.TryParse(s, &v)`: the value goes to `v`)
            | [ Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
                ctx.Vars.ContainsKey out.Name
                ->
                let outVar = ctx.Vars[out.Name]
                let pair = ctx.State.NewVar("parsed", pairTy, VLocal, false)
                ctx.State.UsesRuntime <- true

                bindArgs
                    ctx
                    [ lw ctx s ]
                    (fun xs ->
                        ELet(
                            pair,
                            EEmit(macro, xs, pairTy),
                            ESeq(EAssign(outVar, EGet(EVar pair, PItem 1, outVar.Ty)), EGet(EVar pair, PItem 0, tBool))
                        )
                    )
            | _ -> pure' macro [ s ] pairTy
        | _ -> fail r "the Zig target does not support Enum.TryParse of this type"
    // (`(||)` and `(&&)` given as functions: their arguments are values already)
    | "Microsoft.FSharp.Core.LanguagePrimitives.IntrinsicOperators", ("op_BooleanOr" | "op_BooleanAnd"), [ a; b ] ->
        bindArgs
            ctx
            [ lw ctx a; lw ctx b ]
            (fun xs ->
                EEmit(
                    (if name = "op_BooleanOr" then
                         "($0 or $1)"
                     else
                         "($0 and $1)"),
                    xs,
                    tBool
                )
            )
    // `Option.toObj` and `Option.ofObj`: of a type that has null here
    | ("Microsoft.FSharp.Core.OptionModule" | "Microsoft.FSharp.Core.ValueOption"), ("ToObj" | "OfObj"), [ x ] when
        (match
            (if name = "ToObj" then
                 t
             else
                 x.Type)
         with
         | Fable.String
         | Fable.Any -> true
         | _ -> false)
        ->
        if name = "ToObj" then
            pure' "fable_rt.optToObj($0)" [ x ] (mapType ctx r t)
        else
            pure' "fable_rt.optOfObj($0)" [ x ] (mapType ctx r t)
    // ---- System.Convert's text in a base, BitConverter, Base64 and hex ----
    | "System.BitConverter", "GetBytes", [ x ] ->
        pure' $"fable_rt.bitGetBytes(%s{typedArg ctx r x 0})" [ x ] (mapType ctx r t)
    | "System.BitConverter", "get_IsLittleEndian", [] ->
        ELit("(@import(\"builtin\").cpu.arch.endian() == .little)", tBool)
    | "System.BitConverter",
      ("Int64BitsToDouble" | "DoubleToInt64Bits" | "Int32BitsToSingle" | "SingleToInt32Bits" | "UInt64BitsToDouble" | "DoubleToUInt64Bits" | "UInt32BitsToSingle" | "SingleToUInt32Bits"),
      [ x ] -> pure' $"@as($R, @bitCast(%s{typedArg ctx r x 0}))" [ x ] (mapType ctx r t)
    | "System.BitConverter", "ToString", b :: rest ->
        match rest with
        | [] -> rt "fable_rt.bitToString($0, null, null)" [ b ] tStr
        | [ start ] -> rt "fable_rt.bitToString($0, $1, null)" [ b; start ] tStr
        | [ start; n ] -> rt "fable_rt.bitToString($0, $1, $2)" [ b; start; n ] tStr
        | _ -> fail r "the Zig target does not support this BitConverter.ToString yet"
    | "System.BitConverter", conv, [ b; i ] when conv.StartsWith("To", System.StringComparison.Ordinal) ->
        rt "fable_rt.bitTo($R, $0, $1)" [ b; i ] (mapType ctx r t)
    | "System.Convert", ("ToHexString" | "ToHexStringLower"), b :: rest ->
        let lower =
            if name = "ToHexStringLower" then
                "true"
            else
                "false"

        match rest with
        | [] -> rt $"fable_rt.hexOf($0, null, null, %s{lower})" [ b ] tStr
        | [ o; n ] -> rt $"fable_rt.hexOf($0, $1, $2, %s{lower})" [ b; o; n ] tStr
        | _ -> fail r "the Zig target does not support this Convert.%s yet" name
    | "System.Convert", "FromHexString", [ s ] -> rt "fable_rt.hexParse($0)" [ s ] (mapType ctx r t)
    | "System.Convert", "ToBase64String", [ b ] -> pure' "fable_rt.base64Of($0)" [ b ] tStr
    | "System.Convert", "FromBase64String", [ s ] -> rt "fable_rt.base64Parse($0)" [ s ] (mapType ctx r t)
    | "System.Convert", "ToString", [ x; b ] when
        isInt b
        && (
            match x.Type with
            | Fable.Number _ -> true
            | _ -> false
        )
        ->
        rt $"fable_rt.convToStringBase(%s{typedArg ctx r x 0}, $1)" [ x; b ] tStr
    | "System.Convert", conv, [ s; b ] when
        conv.StartsWith("To", System.StringComparison.Ordinal)
        && s.Type = Fable.String
        && isInt b
        ->
        rt "fable_rt.convParseBase($R, $0, $1)" [ s; b ] (mapType ctx r t)
    | "System.Convert", conv, [ s ] when
        conv.StartsWith("To", System.StringComparison.Ordinal)
        && s.Type = Fable.String
        && conv <> "ToString"
        && conv <> "ToChar"
        ->
        rt "fable_rt.convParse($R, $0)" [ s ] (mapType ctx r t)
    | "System.Convert", "ToChar", [ c ] when c.Type = Fable.Char -> lw ctx c
    // (of a char: its number, which must fit)
    | "System.Convert", conv, [ c ] when c.Type = Fable.Char && conv <> "ToString" ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators.Checked" conv info t
    // (of a float: rounded half to even, and raising where it does not fit)
    | "System.Convert", conv, [ x ] when
        conv.StartsWith("To", System.StringComparison.Ordinal)
        && (
            match x.Type with
            | Fable.Number((Float32 | Float64), _) -> true
            | _ -> false
        )
        && intBits (mapType ctx r t) > 0
        ->
        rt $"fable_rt.convFloatToInt($R, %s{typedArg ctx r x 0})" [ x ] (mapType ctx r t)
    // (of a whole number: the value, which must fit, as a checked conversion has it)
    | "System.Convert", conv, [ x ] when
        conv.StartsWith("To", System.StringComparison.Ordinal)
        && conv <> "ToString"
        && (
            match x.Type with
            | Fable.Number((Int8 | UInt8 | Int16 | UInt16 | Int32 | UInt32 | Int64 | UInt64 | NativeInt | UNativeInt), _) ->
                true
            | _ -> false
        )
        && intBits (mapType ctx r t) > 0
        ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators.Checked" conv info t
    | "System.Convert", ("ToSingle" | "ToDouble"), [ x ] ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators", ("ToSingle" | "ToDouble"), [ x ] when x.Type <> Fable.String ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t
    | "System.Convert", "ToChar", [ x ] -> dotnetCall ctx r "Microsoft.FSharp.Core.Operators.Checked" "ToChar" info t
    // ---- System.Random ----
    | "System.Random", ".ctor", [] -> pure' "fable_rt.randomUnseeded()" [] (mapType ctx r t)
    | "System.Random", ".ctor", [ seed ] -> pure' "fable_rt.randomNew($0)" [ seed ] (mapType ctx r t)
    | "System.Random", "get_Shared", [] -> pure' "fable_rt.randomShared()" [] (mapType ctx r t)
    | "System.Random", "Next", [ rnd ] -> pure' "fable_rt.randomNext($0)" [ rnd ] tI32
    | "System.Random", "Next", [ rnd; max ] -> rt "fable_rt.randomNextMax($0, $1)" [ rnd; max ] tI32
    | "System.Random", "Next", [ rnd; min; max ] -> rt "fable_rt.randomNextRange($0, $1, $2)" [ rnd; min; max ] tI32
    | "System.Random", "NextDouble", [ rnd ] -> pure' "fable_rt.randomNextDouble($0)" [ rnd ] tF64
    | "System.Random", "NextBytes", [ rnd; buffer ] -> pure' "fable_rt.randomNextBytes($0, $1)" [ rnd; buffer ] tVoid
    // ---- `Nullable<T>`: an option ----
    | "System.Nullable`1", ".ctor", [] -> ECon(mapType ctx r t, "None", [], None)
    | "System.Nullable`1", ".ctor", [ x ] ->
        bindArgs ctx [ lw ctx x ] (fun xs -> ECon(mapType ctx r t, "Some", xs, None))
    | "System.Nullable`1", "get_HasValue", [ n ] ->
        bindArgs ctx [ lw ctx n ] (fun xs -> EPrim("not", [ ETest(xs.Head, "None", typeOf xs.Head) ], tBool))
    | "System.Nullable`1", "get_Value", [ n ] -> rt "fable_rt.nullableValue($0)" [ n ] (mapType ctx r t)
    | "System.Nullable`1", "GetValueOrDefault", [ n ] when hasDefault t ->
        pure' "fable_rt.orDefault($R, $0)" [ n ] (mapType ctx r t)
    | "System.Nullable`1", "GetValueOrDefault", [ n; d ] -> pure' "($0 orelse $1)" [ n; d ] (mapType ctx r t)
    // `Nullable.int n` and the other conversions of a nullable: the value converted, if any
    | "Microsoft.FSharp.Linq.NullableModule", conv, [ value ] when
        conv.StartsWith("To", System.StringComparison.Ordinal)
        ->
        let sourceType =
            match value.Type with
            | Fable.Nullable(s, _)
            | Fable.Option(s, _) -> s
            | s -> s

        let targetType =
            match t with
            | Fable.Nullable(s, _)
            | Fable.Option(s, _) -> s
            | s -> s

        let v = AST.makeTypedIdent sourceType "v"

        let converted =
            if conv = "ToEnum" then
                Fable.TypeCast(Fable.IdentExpr v, targetType)
            else
                Fable.Call(
                    Fable.Import(
                        {
                            Selector = conv
                            Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.Operators"
                            Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                        },
                        Fable.Any,
                        None
                    ),
                    Fable.CallInfo.Create(args = [ Fable.IdentExpr v ], genArgs = [ sourceType ]),
                    targetType,
                    r
                )

        let mapping = Fable.Delegate([ v ], converted, None, [])

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
                { info with
                    Args = [ mapping; value ]
                    GenericArgs = [ sourceType; targetType ]
                    SignatureArgTypes = []
                    MemberRef = None
                },
                Fable.Option(targetType, false),
                r
            ))
    // ---- .NET's stack and queue: the library's Stack.fs and Queue.fs ----
    | ("System.Collections.Generic.Stack`1" | "System.Collections.Generic.Queue`1"), _, _ ->
        let file =
            if entity.EndsWith("Stack`1", System.StringComparison.Ordinal) then
                "Stack"
            else
                "Queue"

        let small (n: string) =
            n.Substring(0, 1).ToLowerInvariant() + n.Substring(1)

        match name, args with
        | ".ctor", [] -> libraryCall ctx r file "create" info [] t
        // (a capacity: nothing to do here)
        | ".ctor", [ n ] when isInt n ->
            bindArgs ctx [ lwStmt ctx n ] (fun _ -> libraryCall ctx r file "create" { info with Args = [] } [] t)
        | ".ctor", [ _ ] -> libraryCall ctx r file "ofSeq" info args t
        | "get_Count", _ -> libraryCall ctx r file "count" info args t
        // `TryPop(&v)` and the others: the value goes to `v`
        | ("TryPop" | "TryPeek" | "TryDequeue"),
          [ q; Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr out), _, _, _) ] when
            ctx.Vars.ContainsKey out.Name
            ->
            let outVar = ctx.Vars[out.Name]

            let found =
                libraryCall ctx r file (small name) { info with Args = [] } [ q ] (Fable.Option(out.Type, false))

            let opt = ctx.State.NewVar("found", TOpt outVar.Ty, VLocal, false)

            ELet(
                opt,
                found,
                EIf(
                    EPrim("not", [ ETest(EVar opt, "None", TOpt outVar.Ty) ], tBool),
                    ESeq(EAssign(outVar, EGet(EVar opt, PSome, outVar.Ty)), ELit("true", tBool)),
                    ELit("false", tBool),
                    tBool
                )
            )
        | _ -> libraryCall ctx r file (small name) info args t
    // ---- tuples: `Tuple(a, b)`, `Tuple.Create`, struct tuples, and the conversions between
    // them (a tuple is a Zig tuple, struct or not) ----
    | ("System.Tuple`1" | "System.Tuple`2" | "System.Tuple`3" | "System.Tuple`4" | "System.Tuple`5" | "System.Tuple`6" | "System.Tuple`7" | "System.ValueTuple`1" | "System.ValueTuple`2" | "System.ValueTuple`3" | "System.ValueTuple`4" | "System.ValueTuple`5" | "System.ValueTuple`6" | "System.ValueTuple`7"),
      ".ctor",
      items
    | ("System.Tuple" | "System.ValueTuple"), "Create", items ->
        lw ctx (Fable.Value(Fable.NewTuple(items, entity.StartsWith "System.ValueTuple"), r))
    | "System.TupleExtensions", ("ToValueTuple" | "ToTuple"), [ x ] ->
        let items =
            match x.Type with
            | Fable.Tuple(ts, _) -> ts
            | _ -> fail r "internal: not a tuple"

        let tmp = AST.makeTypedIdent x.Type "tuple"

        lw
            ctx
            (Fable.Let(
                tmp,
                x,
                Fable.Value(
                    Fable.NewTuple(
                        items
                        |> List.mapi (fun i t -> Fable.Get(Fable.IdentExpr tmp, Fable.TupleIndex i, t, r)),
                        name = "ToValueTuple"
                    ),
                    r
                )
            ))
    | ("System.Tuple`1" | "System.ValueTuple`1"), "get_Item1", [ x ] -> lw ctx (Fable.Get(x, Fable.TupleIndex 0, t, r))
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

    let args =
        match args |> List.filter (fun arg -> not (isUnit arg.Type)) with
        | [] -> [ EUnit ]
        | given -> given |> List.map lowerArg

    bindArgs ctx args (fun xs -> ECall(target, typeArgs, xs, mapType ctx r t))

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
            Boxed = HashSet()
            Enumerators = Dictionary()
            OutTuples = Dictionary()
            CaughtExn = None
        }

    let report (r: SourceLocation option) (msg: string) =
        com.AddLog(msg, Severity.Error, ?range = r, fileName = com.CurrentFile)

    let attached = List<Fable.MemberDecl>()
    let mutable actions = 0

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
                        Fable.Call(callee, call, chainType o, r)
                    | Fable.Let(id, v, b) -> Fable.Let(id, v, chainTail b)
                    | Fable.LetRec(bs, b) -> Fable.LetRec(bs, chainTail b)
                    | Fable.Sequential xs ->
                        let rev = List.rev xs
                        Fable.Sequential(List.rev (chainTail rev.Head :: rev.Tail))
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
                            state.StaticFields[c.Name + "." + f.Name] <-
                                c.Name
                                + "__static_"
                                + System.Text.RegularExpressions.Regex.Replace(f.Name, "[^A-Za-z0-9_]", "_")
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
                        | Some ctor -> attached.Add { ctor with Body = objConstructorBody o c.BaseCall ctor.Body }
                        | None -> ()

                        state.Objs.Add(objDecl com None o (dotnetTypeName com ent))
                    with ZigError(msg, r) ->
                        report r msg

                    // what it overrides, its `default` members, and what it implements
                    attached.AddRange(
                        c.AttachedMembers
                        |> List.choose (fun m ->
                            let info = com.TryGetMember m.MemberRef

                            let compiled =
                                match info with
                                | Some info -> info.CompiledName
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

                            attached.Add { ctor with Body = constructorBody c.Entity genArgs fields ctor.Body }
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
                                | Some info -> info.CompiledName
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
        with ZigError(msg, r) ->
            report
                (match r with
                 | Some _ -> r
                 | None -> d.Body.Range)
                msg

    settleCyclic state
    settleCycles state
    state
