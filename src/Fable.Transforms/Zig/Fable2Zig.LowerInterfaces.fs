/// Lowering for fat-pointer interfaces, collection/seq casts, and object expressions.
module Fable.Transforms.Zig.LowerInterfaces

open System.Collections.Generic
open Fable
open Fable.AST
open Fable.Transforms
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.LowerContext
open Fable.Transforms.Zig.LowerTypes
open Fable.Transforms.Zig.LowerHelpers
open Fable.Transforms.Zig.LowerFormat
open Fable.Transforms.Zig.Lower
open Fable.Transforms.Zig.LowerDotnet

/// `Seq.ofGetEnumerator (fun () -> getEnumerator)`: a sequence that walks what an
/// `IEnumerable<'T>` of the program's gives
let private lowerSeqOfGetEnumerator
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


/// Lower an interface call, interface/collection cast, or object expression; returns null otherwise.
let tryLower (ctx: Ctx) (e: Fable.Expr) : Expr =
    match e with
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

        // (a generic method's slot has its type parameters erased to `obj`: a value of another
        // type is boxed or unboxed, an interface of them adapted, see fable_rt.erasedConv)
        let erased (a: Ty) (b: Ty) =
            a <> b && (a = tAny || b = tAny || (isFatIfaceTy a && isFatIfaceTy b))

        let convertTo (ty: Ty) (x: Expr) =
            let c = coerceTy ctx ty x

            if erased (typeOf c) ty then
                ctx.State.UsesRuntime <- true
                bindArgs ctx [ c ] (fun xs -> EEmit("fable_rt.erasedConv($R, $0)", xs, ty))
            else
                c

        match resolveIfaceSlot ctx x.Type ifaceStructTy info.Name (Some argCount) with
        | Some(f, ptys, ret), _ ->
            let args =
                if rawArgs.IsEmpty then
                    [ EUnit ]
                else
                    let lowered = wrappedRawArgs |> List.map (lw ctx)

                    if ptys.Length = lowered.Length then
                        List.map2 convertTo ptys lowered
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
                        (fun iface -> convertTo (mapType ctx r t) (ECallIface(iface, f, given.Tail, ret)))
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
            bindArgs ctx [ lw ctx x ] (fun xs -> ECall(libraryTarget ctx "Seq" "ofCollection", [ itemTy ], xs, seqTy))
        // (an object of the program's that implements `IEnumerable<'T>`: what its
        // `GetEnumerator` gives)
        | Fable.DeclaredType({ Path = Fable.SourcePath _ }, _) when
            implements ctx.Com x.Type "System.Collections.Generic.IEnumerable`1" = Some true
            ->
            let obj = AST.makeTypedIdent x.Type (tempName ctx "enumerable")

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
        // (an `IList<'T>`, a `ReadOnlyCollection<'T>`: the array it is here)
        | Fable.DeclaredType(il, [ item ]) when
            il.FullName = "System.Collections.Generic.IList`1"
            || il.FullName = "System.Collections.ObjectModel.ReadOnlyCollection`1"
            ->
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
                        (fun cs -> ECall(libraryTarget ctx "Seq" "ofCollection", [ itemTy ], cs, seqTy))
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
    // (a cancellation registration given as an `IDisposable`: it is one here)
    | Fable.TypeCast(x, Fable.DeclaredType(target, _)) when
        target.FullName = "System.IDisposable"
        && (
            match x.Type with
            | Fable.DeclaredType(e, _) -> e.FullName = "System.Threading.CancellationTokenRegistration"
            | _ -> false
        )
        ->
        lw ctx x
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
    // (the non-generic IEnumerable: a sequence of objects here. Of an object, the items its
    // collection gives boxed; of a collection of values, its items boxed)
    | Fable.TypeCast(x, Fable.DeclaredType(target, [])) when target.FullName = "System.Collections.IEnumerable" ->
        let seqOf (item: Fable.Type) =
            Fable.DeclaredType(
                {
                    FullName = "System.Collections.Generic.IEnumerable`1"
                    Path = Fable.CoreAssemblyName "System.Runtime"
                },
                [ item ]
            )

        let seqCall (name: string) (args: Fable.Expr list) (genArgs: Fable.Type list) (t: Fable.Type) =
            Fable.Call(
                Fable.Import(
                    {
                        Selector = name
                        Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Collections.SeqModule"
                        Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                    },
                    Fable.Any,
                    None
                ),
                Fable.CallInfo.Create(args = args, genArgs = genArgs),
                t,
                e.Range
            )

        let (Uncast inner) = x

        match unwrapNullness inner.Type with
        | Fable.Any ->
            ctx.State.UsesRuntime <- true

            let items =
                Fable.Emit(
                    {
                        Macro = "try fable_rt.objItems($0)"
                        IsStatement = false
                        CallInfo = Fable.CallInfo.Create(args = [ inner ])
                    },
                    Fable.Array(Fable.Any, Fable.MutableArray),
                    e.Range
                )

            lw ctx (seqCall "OfArray" [ items ] [ Fable.Any ] (seqOf Fable.Any))
        | t ->
            let item =
                match t with
                | Fable.Array(i, _)
                | Fable.List i -> Some i
                | Fable.String -> Some Fable.Char
                | Fable.DeclaredType(_, [ i ]) -> Some i
                | _ -> None

            match item with
            | Some Fable.Any -> lw ctx (Fable.TypeCast(inner, seqOf Fable.Any))
            | Some i ->
                let v = AST.makeTypedIdent i (tempName ctx "item")
                let boxIt = Fable.Lambda(v, Fable.TypeCast(Fable.IdentExpr v, Fable.Any), None)
                lw ctx (seqCall "Map" [ boxIt; Fable.TypeCast(inner, seqOf i) ] [ i; Fable.Any ] (seqOf Fable.Any))
            | None -> fail e.Range "the Zig target cannot see a value of this type as an IEnumerable yet (%A)" t
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
             (c.FullName = "System.Collections.Generic.Comparer`1"
              && i.FullName = "System.Collections.Generic.IComparer`1")
             || (c.FullName = "System.Collections.Generic.EqualityComparer`1"
                 && i.FullName = "System.Collections.Generic.IEqualityComparer`1")
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
    // (a set seen as the collection of its items: the list of them, in order)
    | Fable.TypeCast(x, Fable.DeclaredType(c, [ _ ])) when
        (c.FullName = "System.Collections.Generic.ICollection`1"
         || c.FullName = "System.Collections.Generic.IReadOnlyCollection`1")
        && (
            match x.Type with
            | Fable.DeclaredType(m, [ _ ]) -> m.FullName = setName
            | _ -> false
        )
        ->
        let item =
            match x.Type with
            | Fable.DeclaredType(_, [ item ]) -> mapTypeArg ctx e.Range item
            | _ -> failwith "unreachable"

        bindArgs
            ctx
            [ lw ctx x ]
            (fun xs -> ECall(libraryTarget ctx "Set" "toList", [ item ], xs, TEnt(listEnt ctx.State, [ item ])))
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
                Layout = LayoutAuto
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
                        let held = AST.makeTypedIdent head.Type (tempName ctx "applied")
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

            // (a generic method's own type parameters: `obj`, as its slot has them erased)
            let erased =
                slotDelegates
                |> List.collect (fun (_, fnExpr) ->
                    match fnExpr with
                    | Fable.Delegate(args, body, _, _) ->
                        freeGens (
                            mapType ctx e.Range body.Type
                            :: (args |> List.map (fun a -> mapType ctx e.Range a.Type))
                        )
                    | _ -> []
                )
                |> List.distinct
                |> List.filter (fun g ->
                    not (List.contains g ctx.TypeParams) && not (ctx.State.GenAliases.ContainsKey g)
                )

            for g in erased do
                ctx.State.GenAliases[g] <- tAny

            let lifted =
                try
                    liftGroup ctx e.Range (slotDelegates |> List.map (fun (f, fnExpr) -> None, cleanIdent f, fnExpr))
                finally
                    for g in erased do
                        ctx.State.GenAliases.Remove g |> ignore

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

    | _ -> Unchecked.defaultof<Expr>
