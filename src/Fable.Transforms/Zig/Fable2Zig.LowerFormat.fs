/// Pure leaf helpers for formatting (`formatParts`, `showShapeOf`), type arguments,
/// exception descriptors, and statement/collection wrappers; compiled before `Lower.fs`.
module Fable.Transforms.Zig.LowerFormat

open System.Collections.Generic
open Fable
open Fable.AST
open Fable.Transforms
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.LowerContext
open Fable.Transforms.Zig.LowerTypes
open Fable.Transforms.Zig.LowerHelpers

/// The type arguments of a call of `c`, and what its type parameters stand for. They are what
/// Fable says they are when it says; otherwise they follow from the types of the arguments
/// and of the result.
let rec typeArgsOf
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


/// The exception `made` with its `ParamName` (bound first: what is bound is given up after)
and withParamName (ctx: Ctx) (made: Expr) (name: Expr) (k: Expr -> Expr) : Expr =
    bindArgs ctx [ made; name ] (fun ys -> k (EEmit("fable_rt.exnWithParam($0, $1)", ys, tExn)))


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
                    // (unit: the empty text, as .NET writes null)
                    | ('P' | 'O' | 's'), Fable.Unit -> 'T'
                    // (an object, an array, an exception, an object of a class, an interface: its
                    // own `ToString`, as .NET writes it; null as the empty text)
                    | ('P' | 'O' | 's'), (Fable.Any | Fable.Array _ | Fable.DeclaredType _ | Fable.Nullable _) -> 'T'
                    // (`%A` of an object of a class: its `ToString`, as F# writes it)
                    | 'A', Fable.DeclaredType(entRef, _) when (objInfo ctx r entRef).IsSome -> 'T'
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


/// The item type of a cell type of one type argument.
and itemOf (x: Expr) : Ty =
    match typeOf x with
    | TEnt(_, [ item ]) -> item
    | _ -> fail None "internal: not a collection"

/// `x`, of a class deriving from a collection with members only, as a value of the collection's
/// type given to `k`
and asCollectionBase (ctx: Ctx) (x: Fable.Expr) (k: Fable.Expr -> Fable.Expr) : Fable.Expr =
    let baseType = (collectionBase ctx.Com x.Type).Value

    match x with
    | Fable.IdentExpr id -> k (Fable.IdentExpr { id with Type = baseType })
    | _ ->
        let tmp = AST.makeTypedIdent baseType (tempName ctx "collection")
        Fable.Let(tmp, x, k (Fable.IdentExpr tmp))


/// `e`, after a check that `x` (lowered to `ir`), a .NET collection, is not null where it may be
and cellChecked (ctx: Ctx) (x: Fable.Expr) (ir: Expr) (e: Expr) : Expr =
    if mayBeNullCell ctx x then
        ctx.State.UsesRuntime <- true
        ESeq(ERt("fable_rt.checkCellNonNull($0)", [ ir ], tVoid), e)
    else
        e


/// A statement: its value, if it has one, is not used.
and asStmt (ctx: Ctx) (ir: Expr) : Expr =
    if isVoid (typeOf ir) then
        ir
    else
        ELet(ctx.State.NewVar("discard", typeOf ir, VLocal, false), ir, EUnit)
