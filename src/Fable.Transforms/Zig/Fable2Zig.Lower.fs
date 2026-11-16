/// Lowering: Fable AST -> ownership IR. Anything with control flow or effects that sits in an
/// argument position is let-bound first (ANF), keeping F# evaluation order.
module Fable.Transforms.Zig.Lower

open System.Collections.Generic
open Fable
open Fable.AST
open Fable.Transforms
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.LowerContext
open Fable.Transforms.Zig.LowerTypes
open Fable.Transforms.Zig.LowerHelpers

let rec lw (ctx: Ctx) (e: Fable.Expr) : Expr =
    match e with
    // (a value of a class deriving from `Dictionary` or `HashSet` with members only, as the
    // object of a call or what is cast: the collection it is, under the collection's type)
    | Fable.Call(callee, ({ ThisArg = Some x } as info), t, r) when (collectionBase ctx.Com x.Type).IsSome ->
        lw ctx (asCollectionBase ctx x (fun x -> Fable.Call(callee, { info with ThisArg = Some x }, t, r)))
    | Fable.TypeCast(x, target) when (collectionBase ctx.Com x.Type).IsSome ->
        lw ctx (asCollectionBase ctx x (fun x -> Fable.TypeCast(x, target)))
    // (`let coll = rs :> ICollection<_>` of a ResizeArray, a HashSet or a Dictionary: the variable
    // is the collection, so that what is done through it is done to the collection, as on .NET)
    | Fable.Let(id, Fable.TypeCast(Uncast inner, (Fable.DeclaredType(view, _))), body) when
        not id.IsMutable
        && (view.FullName = "System.Collections.Generic.ICollection`1"
            || view.FullName = "System.Collections.Generic.IReadOnlyCollection`1")
        && (
            match inner.Type with
            | Fable.Array _ -> true
            | Fable.DeclaredType(ent, _) ->
                ent.FullName = "System.Collections.Generic.List`1"
                || ent.FullName = "System.Collections.Generic.HashSet`1"
                || ent.FullName = "System.Collections.Generic.Dictionary`2"
            | _ -> false
        )
        ->
        let id' = { id with Type = inner.Type }

        let body =
            FableTransforms.replaceValues (Map.ofList [ id.Name, Fable.TypeCast(Fable.IdentExpr id', id.Type) ]) body

        lw ctx (Fable.Let(id', inner, body))
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
        let staged = AST.makeTypedIdent rTy (tempName ctx "staged")

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
        let held = AST.makeTypedIdent head.Type (tempName ctx "applied")
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
    // (a function of several arguments read from a field, which may hold null
    // (`[<DefaultValue>]`): null as it is, as .NET has it; else made curried as a variable is)
    | Fable.Extended(Fable.Curry(Fable.Get(_, Fable.FieldGet _, _, _) as f, arity), r) when arity >= 2 ->
        let n = ctx.State.NewVar("field_fn", tVoid, VLocal, false).Id
        let fId = AST.makeTypedIdent f.Type $"fieldFn$%d{n}"
        // (the field holds the function of all the arguments at once)
        let read = lw ctx f
        let v = ctx.State.NewVar("field_fn", typeOf read, VLocal, false)
        let curriedTy = mapType ctx r e.Type
        ctx.Vars[fId.Name] <- v

        ELet(
            v,
            read,
            EIf(
                EEmit("fable_rt.isNullOf($0)", [ EVar v ], tBool),
                EEmit("fable_rt.nullOf($R)", [], curriedTy),
                lw ctx (Fable.Extended(Fable.Curry(Fable.IdentExpr fId, arity), r)),
                curriedTy
            )
        )
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

        // (lowered in the order they run: what one statement tells of a variable holds for those
        // after it, not before)
        let beforeIrs = before |> List.map (lwStmt ctx)

        let raiseIr =
            bindArgs ctx [ lw ctx thrown ] (fun xs -> ERaise(xs.Head, mapType ctx e.Range e.Type))

        List.foldBack (fun ir acc -> ESeq(ir, acc)) beforeIrs raiseIr
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
            // (lowered in the order they run: what one statement tells of a variable (an
            // assignment forgets what was known of it) holds for those after it, not before)
            let restIrs = List.rev restRev |> List.map (lwStmt ctx)
            let lastIr = lw ctx last
            List.foldBack (fun ir acc -> ESeq(ir, acc)) restIrs lastIr

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
    // `Printf.bprintf sb fmt a b` and `kbprintf`
    | Fable.CurriedApply(Fable.Call(Fable.Import(imp, _, _), info, _, _), args, t, r) when
        imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.PrintfModule"
        && (imp.Selector = "PrintFormatToStringBuilder"
            || imp.Selector = "PrintFormatToStringBuilderThen")
        ->
        lw ctx (bprintf imp info args t r)
    | Fable.Call(Fable.Import(imp, _, _), info, t, r) when
        imp.Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Core.PrintfModule"
        && (imp.Selector = "PrintFormatToStringBuilder"
            || imp.Selector = "PrintFormatToStringBuilderThen")
        ->
        lw ctx (bprintf imp info [] t r)
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

        let v = AST.makeTypedIdent optT (tempName ctx "self")

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
            bindArgs ctx [ lw ctx x ] (fun xs -> ECall(libraryTarget ctx "Seq" "ofArray", [ itemTy ], xs, seqTy))
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
                match unwrapNullness x.Type with
                // (a value of a type parameter constrained to a type (`'b :> Lazy<'a>`): of that
                // type, when Zig instantiates the parameter with it)
                | Fable.GenericParam _ ->
                    bindArgs ctx [ ir ] (fun xs -> EEmit("fable_rt.asSame($R, fable_rt.dup($0))", xs, targetTy))
                | _ -> fail e.Range "the Zig target does not support %s yet" (exprKind e)

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

                // (a date, a time or a span with a format: its own ToString(format), .NET's)
                let dateEntity =
                    match ident.Type with
                    | Fable.DeclaredType(e, []) when
                        format <> ""
                        && (e.FullName = "System.DateTime"
                            || e.FullName = "System.DateTimeOffset"
                            || e.FullName = "System.DateOnly"
                            || e.FullName = "System.TimeOnly"
                            || e.FullName = "System.TimeSpan")
                        ->
                        Some e.FullName
                    | _ -> None

                match dateEntity with
                | Some entity ->
                    holes.Add(
                        Fable.Call(
                            Fable.Import(
                                {
                                    Selector = "ToString"
                                    Path = Replacements.DotnetPrefix + entity
                                    Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = true))
                                },
                                Fable.Any,
                                None
                            ),
                            Fable.CallInfo.Create(
                                thisArg = Fable.IdentExpr ident,
                                args = [ Fable.Value(Fable.StringConstant format, None) ],
                                sigArgTypes = [ Fable.String ]
                            ),
                            Fable.String,
                            r
                        )
                    )
                | None -> holes.Add(Fable.IdentExpr ident)

                let format =
                    if dateEntity.IsSome then
                        ""
                    else
                        format

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

        // (a type parameter that only a constraint of one of the function's names (`'b :> Lazy<'c>`,
        // F#'s generalization of a local function): the type argument of that one)
        let aliases =
            let known = Set.ofList (ctx.TypeParams @ ownGens)

            let rec constrained (t: Fable.Type) =
                match t with
                | Fable.GenericParam(name, _, constraints) when known.Contains name ->
                    [
                        for c in constraints do
                            match c with
                            | Fable.Constraint.CoercesTo(Fable.DeclaredType(_, targs)) ->
                                for k, targ in List.indexed targs do
                                    match targ with
                                    | Fable.GenericParam(v, _, _) when not (known.Contains v) ->
                                        v, TPrim $"fable_rt.typeArg(%s{genName name}, %d{k})"
                                    | _ -> ()
                            | _ -> ()
                    ]
                | Fable.DeclaredType(_, ts)
                | Fable.Tuple(ts, _) -> List.collect constrained ts
                | Fable.Array(t, _)
                | Fable.List t
                | Fable.Option(t, _) -> constrained t
                | Fable.LambdaType(a, b) -> constrained a @ constrained b
                | Fable.DelegateType(ts, b) -> List.collect constrained ts @ constrained b
                | _ -> []

            args
            |> List.collect (fun a -> constrained a.Type)
            |> List.distinctBy fst
            |> List.filter (fun (v, _) -> not (ctx.State.GenAliases.ContainsKey v))

        for v, ty in aliases do
            ctx.State.GenAliases[v] <- ty

        let bodyIr =
            try
                lw inner body
            finally
                for v, _ in aliases do
                    ctx.State.GenAliases.Remove v |> ignore

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
    // (other names of structural hashing, equality and comparison, and of values with a unit of
    // measure: what `hash`, `=`, `compare` and the value are)
    match entity, name with
    | ("Microsoft.FSharp.Core.Operators.Unchecked" | "Microsoft.FSharp.Core.LanguagePrimitives"),
      ("Hash" | "GenericHash" | "GenericLimitedHash" | "GenericHashWithComparer") when not info.Args.IsEmpty ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" "Hash" { info with Args = [ List.last info.Args ] } t
    | ("Microsoft.FSharp.Core.Operators.Unchecked" | "Microsoft.FSharp.Core.LanguagePrimitives"),
      ("Equals" | "GenericEquality" | "GenericEqualityER" | "GenericEqualityWithComparer") when info.Args.Length >= 2 ->
        let n = info.Args.Length
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" "op_Equality" { info with Args = info.Args.[n - 2 ..] } t
    | ("Microsoft.FSharp.Core.Operators.Unchecked" | "Microsoft.FSharp.Core.LanguagePrimitives"),
      ("Compare" | "GenericComparison" | "GenericComparisonWithComparer") when info.Args.Length >= 2 ->
        let n = info.Args.Length
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" "Compare" { info with Args = info.Args.[n - 2 ..] } t
    | "Microsoft.FSharp.Core.LanguagePrimitives", "PhysicalHash" when info.Args.Length = 1 ->
        ctx.State.UsesRuntime <- true
        bindArgs ctx [ lw ctx info.Args.Head ] (fun xs -> EEmit("fable_rt.physicalHash($0)", xs, tI32))
    | "Microsoft.FSharp.Core.LanguagePrimitives", m when
        m.EndsWith("WithMeasure", System.StringComparison.Ordinal)
        && info.Args.Length = 1
        ->
        lw ctx info.Args.Head
    // (`c.Compare(a, b)` of a `Comparer<'T>`: an IComparer here, `Default` or one of `Create`)
    | "System.Collections.Generic.Comparer`1", "Compare" when info.Args.Length = 2 && info.ThisArg.IsSome ->
        libraryCall ctx r "Array" "comparerCompare" info (info.ThisArg.Value :: info.Args) t
    | "System.Collections.Generic.Comparer`1", "Create" when info.Args.Length = 1 ->
        libraryCall ctx r "Array" "comparerOfDelegate" info info.Args t
    // (a format provider given to a number's, a date's or Convert's member: the culture is the
    // invariant one here, as without it; see `isCulture`)
    | ("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte" | "System.UInt16" | "System.UInt32" | "System.UInt64" | "System.Double" | "System.Single" | "System.Decimal" | "System.Numerics.BigInteger" | "System.Convert" | "System.DateTime" | "System.DateTimeOffset" | "System.TimeSpan" | "System.DateOnly" | "System.TimeOnly"),
      ("Parse" | "TryParse" | "ToString" | "ParseExact" | "TryParseExact") when info.Args |> List.exists isCulture ->
        dotnetCall ctx r entity name { info with Args = info.Args |> List.filter (isCulture >> not) } t
    | "System.Convert", m when
        m.StartsWith("To", System.StringComparison.Ordinal)
        && info.Args |> List.exists isCulture
        ->
        dotnetCall ctx r entity name { info with Args = info.Args |> List.filter (isCulture >> not) } t
    // (a culture as a value: nothing here, the invariant culture is the only one)
    | "System.Globalization.CultureInfo",
      ("get_InvariantCulture" | "get_CurrentCulture" | "get_CurrentUICulture" | "get_InvariantUICulture") -> EUnit
    | ("System.Double" | "System.Single"), ("Max" | "Min") when info.Args.Length = 2 ->
        dotnetCall ctx r "System.Math" name info t
    // (`byte x` and `sbyte x`, as F# names them in ExtraTopLevelOperators: Operators' conversions)
    | "Microsoft.FSharp.Core.ExtraTopLevelOperators", ("ToByte" | "ToSByte" | "ToDouble" | "ToSingle" | "ToInt32") when
        info.Args.Length = 1 && unwrapNullness info.Args.Head.Type <> Fable.String
        ->
        dotnetCall ctx r "Microsoft.FSharp.Core.Operators" name info t
    | "Microsoft.FSharp.Control.FSharpAsync", "Parallel" when info.Args.Length = 2 ->
        libraryCall ctx r "Async" "parallelAllMax" info info.Args t
    | "Microsoft.FSharp.Collections.ArrayModule.Parallel", "Reduce" ->
        dotnetCall ctx r "Microsoft.FSharp.Collections.ArrayModule" "Reduce" info t
    | _ ->

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
                            ECall(
                                libraryTarget ctx "Seq" "toList",
                                [ itemTy ],
                                xs,
                                TEnt(listEnt ctx.State, [ itemTy ])
                            )
                        )

            let ty = mapType ctx r t

            match name, args with
            | "Sum", [ _ ] when ty = TPrim "fable_rt.NetDecimal" ->
                bindArgs ctx [ listIr ] (fun xs -> ERt("fable_rt.listSumDec($0)", xs, ty))
            | "Sum", [ _ ] -> bindArgs ctx [ listIr ] (fun xs -> EEmit("fable_rt.listSum($0)", xs, ty))
            | "Average", [ _ ] -> bindArgs ctx [ listIr ] (fun xs -> ERt("fable_rt.listAverage($0)", xs, ty))
            | "SumBy", [ f; _ ] ->
                bindArgs
                    ctx
                    [ lw ctx f; listIr ]
                    (fun xs -> ERt($"fable_rt.listSumBy(%s{zigTypeName ty}, $0, $1)", xs, ty))
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
        | _, "get_Current", [ Fable.IdentExpr e ] when ctx.Enumerators.ContainsKey e.Name ->
            EVar ctx.Enumerators[e.Name]

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
        // `AggregateException(exceptions)` and `AggregateException(message, exceptions)`: the
        // exception with them inside it
        | "System.AggregateException", ".ctor", args when
            (match args with
             | [ arr ]
             | [ _; arr ] ->
                 (match arr.Type with
                  | Fable.Array(Fable.DeclaredType(e, _), _) ->
                      e.FullName = "System.Exception" || dotnetExceptions.ContainsKey e.FullName
                  | Fable.DeclaredType(s, [ Fable.DeclaredType(e, _) ]) ->
                      s.FullName = "System.Collections.Generic.IEnumerable`1"
                      && (e.FullName = "System.Exception" || dotnetExceptions.ContainsKey e.FullName)
                  | _ -> false)
                 && (args.Length = 1 || args.Head.Type = Fable.String)
             | _ -> false)
            ->
            let message, arr =
                match args with
                | [ arr ] -> ELit(stringLiteral "One or more errors occurred.", tStr), arr
                | message :: arr :: _ -> lw ctx message, arr
                | _ -> failwith "unreachable"

            // (a sequence of them: its array)
            let arr =
                match arr.Type with
                | Fable.DeclaredType(_, [ item ]) ->
                    Fable.Call(
                        Fable.Import(
                            {
                                Selector = "ToArray"
                                Path = Replacements.DotnetPrefix + "Microsoft.FSharp.Collections.SeqModule"
                                Kind = Fable.LibraryImport(Fable.LibraryImportInfo.Create(isInstanceMember = false))
                            },
                            Fable.Any,
                            None
                        ),
                        Fable.CallInfo.Create(args = [ arr ], genArgs = [ item ]),
                        Fable.Array(item, Fable.MutableArray),
                        r
                    )
                | _ -> arr

            bindArgsIn
                true
                ctx
                [ message ]
                (fun xs ->
                    let outer = EExnNew(dotnetExnEnt ctx "System.AggregateException", xs)
                    bindArgs ctx [ outer; lw ctx arr ] (fun ys -> EEmit("fable_rt.exnWithInners($0, $1)", ys, tExn))
                )
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
                | ("System.ArgumentNullException" | "System.ArgumentOutOfRangeException"), parameter :: _ ->
                    Some parameter
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
                            bindArgs
                                ctx
                                [ named; xs.[2] ]
                                (fun ys -> EEmit("fable_rt.exnWithInner($0, $1)", ys, tExn))
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
        | "System.AggregateException", "Flatten", [ x ] -> pure' "fable_rt.exnFlatten($0)" [ x ] tExn
        | "System.AggregateException", "get_InnerExceptions", [ x ] ->
            pure' "fable_rt.exnInnerList($0)" [ x ] (mapType ctx r t)
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
        // (`EqualityComparer<'T>.Default`: F#'s equality and hash, called directly; another
        // comparer, one of `Create`, is called through its IEqualityComparer)
        | "System.Collections.Generic.EqualityComparer`1", "Equals", [ IsDefaultEqualityComparer; a; b ] ->
            pure' "fable_rt.eql($0, $1)" [ a; b ] tBool
        | "System.Collections.Generic.EqualityComparer`1", "GetHashCode", [ IsDefaultEqualityComparer; x ] ->
            pure' "fable_rt.hash($0)" [ x ] tI32
        | "System.Collections.Generic.EqualityComparer`1", "Equals", [ c; a; b ] ->
            libraryCall ctx r "Array" "equalityComparerEquals" info [ c; a; b ] t
        | "System.Collections.Generic.EqualityComparer`1", "GetHashCode", [ c; x ] ->
            libraryCall ctx r "Array" "equalityComparerHash" info [ c; x ] t
        | "System.Collections.Generic.EqualityComparer`1", "get_Default", [] ->
            libraryCall ctx r "Array" "structuralEqualityComparer" info [ Fable.Value(Fable.UnitConstant, None) ] t
        | "System.Collections.Generic.EqualityComparer`1", "Create", [ eq; h ] ->
            libraryCall ctx r "Array" "equalityComparerOfDelegates" info [ eq; h ] t
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
                // (the contents of a ref cell given for the remainder, as F# passes `&r.contents`)
                | [ Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.Get(cell, Fable.FieldGet fi, _, _)), _, _, _) ], _
                | [ Fable.Get(cell, Fable.FieldGet fi, _, _) ], _ ->
                    Fable.Sequential
                        [
                            Fable.Set(cell, Fable.FieldSet fi.Name, a.Type, op BinaryModulus, r)
                            op BinaryDivide
                        ]
                // (a ref cell given for the remainder: its contents)
                | [ cell ], _ when
                    (match unwrapNullness cell.Type with
                     | Fable.DeclaredType(e, _) -> e.FullName = "Microsoft.FSharp.Core.FSharpRef`1"
                     | _ -> false)
                    ->
                    Fable.Sequential
                        [
                            Fable.Set(cell, Fable.FieldSet "contents", a.Type, op BinaryModulus, r)
                            op BinaryDivide
                        ]
                | _ ->
                    let text = (sprintf "%A" rest).Replace("\n", " ")

                    fail
                        r
                        "the Zig target does not support this DivRem yet (%s)"
                        (text.Substring(0, min 300 text.Length))

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
        | "System.Math", "Round", [ x; digits ] when isInt digits ->
            rt "fable_rt.roundTo(@as($R, $0), $1)" [ x; digits ] (mapType ctx r x.Type)
        | "System.Math", "Round", [ x; mode ] ->
            rt "fable_rt.roundModeOnly(@as($R, $0), @as(i32, @intCast($1)))" [ x; mode ] (mapType ctx r x.Type)
        | "System.Math", "Round", [ x; digits; mode ] ->
            rt "fable_rt.roundMode(@as($R, $0), $1, @as(i32, @intCast($2)))" [ x; digits; mode ] (mapType ctx r x.Type)
        | "System.Math", "Log", [ x; b ] -> pure' "fable_rt.logBase($0, $1)" [ x; b ] tF64
        | ("System.Math" | "System.Double" | "System.Single"), ("MaxMagnitude" | "MinMagnitude"), [ a; b ] ->
            let f =
                if name = "MaxMagnitude" then
                    "maxMagnitude"
                else
                    "minMagnitude"

            pure' $"fable_rt.%s{f}(@as($R, $0), $1)" [ a; b ] (mapType ctx r a.Type)
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
                rt "fable_rt.parseFloatFs($R, $0)" [ x ] ty
            elif intBits ty > 0 then
                rt "fable_rt.parseIntFs($R, $0)" [ x ] ty
            elif t = Fable.Boolean then
                rt "fable_rt.parseBool($0)" [ x ] ty
            else
                fail r "the Zig target does not support %s.%s of a string yet" entity name
        | ("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte" | "System.UInt16" | "System.UInt32" | "System.UInt64"),
          "Parse",
          [ x ] -> rt "fable_rt.parseInt($R, $0)" [ x ] (mapType ctx r t)
        | ("System.Double" | "System.Single"), "Parse", [ x ] ->
            rt "fable_rt.parseFloat($R, $0)" [ x ] (mapType ctx r t)
        | ("System.Double" | "System.Single"), "Parse", [ x; style ] ->
            rt "fable_rt.parseFloatStyle($R, $0, @as(i32, @intCast($1)))" [ x; style ] (mapType ctx r t)
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
          x :: (([ _ ] | [ _; _ ]) as rest) when
            (let out = List.last rest
             // (with a NumberStyles before the place: of a float only, see parseFloatStyle)
             (rest.Length = 1
              || entity = "System.Double"
              || entity = "System.Single"
              || entity = "System.Decimal")
             && match out with
                | Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr o), _, _, _) ->
                    ctx.Vars.ContainsKey o.Name
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
            let out = List.last rest

            let style =
                if rest.Length = 2 then
                    Some rest.Head
                else
                    None

            let valueType =
                match out with
                | Fable.Operation(Fable.Unary(UnaryAddressOf, Fable.IdentExpr o), _, _, _) -> unByref o.Type
                | Fable.Operation(Fable.Unary(UnaryAddressOf, (Fable.Get _ as place)), _, _, _) -> place.Type
                | _ ->
                    match out.Type with
                    | Fable.DeclaredType(_, [ v ]) -> v
                    | _ -> fail r "internal: TryParse"

            let ty = mapType ctx r valueType
            // (a name of its own: the program's variable may be called `parsed`)
            let tmp =
                AST.makeTypedIdent (Fable.Option(valueType, false)) (tempName ctx "parsed")

            let parsed =
                Fable.Emit(
                    {
                        Macro =
                            match style with
                            | Some _ when entity = "System.Decimal" ->
                                "fable_rt.decTryParseStyle($0, @as(i32, @intCast($1)))"
                            | Some _ -> $"fable_rt.tryParseFloatStyle(%s{zigTypeName ty}, $0, @as(i32, @intCast($1)))"
                            | None -> $"fable_rt.tryParseAny(%s{zigTypeName ty}, $0)"
                        IsStatement = false
                        CallInfo = Fable.CallInfo.Create(args = x :: Option.toList style)
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
        | "Microsoft.FSharp.Collections.ListModule", "Sum", [ xs ] ->
            pure' "fable_rt.listSum($0)" [ xs ] (mapType ctx r t)
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
        | "Microsoft.FSharp.Collections.ArrayModule", "Sum", [ a ] ->
            pure' "fable_rt.arraySum($0)" [ a ] (mapType ctx r t)
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

/// `x`, of a class deriving from a collection with members only, as a value of the collection's
/// type given to `k`
and asCollectionBase (ctx: Ctx) (x: Fable.Expr) (k: Fable.Expr -> Fable.Expr) : Fable.Expr =
    let baseType = (collectionBase ctx.Com x.Type).Value

    match x with
    | Fable.IdentExpr id -> k (Fable.IdentExpr { id with Type = baseType })
    | _ ->
        let tmp = AST.makeTypedIdent baseType (tempName ctx "collection")
        Fable.Let(tmp, x, k (Fable.IdentExpr tmp))

/// What a `for ... in` loop walks, lowered: a list (of a list, a set, or a map's entries) or
/// a string. None for a source that is walked some other way.
and forInSource (ctx: Ctx) (source: Fable.Expr) : (Expr * string) option =
    let (Uncast inner) = source

    match inner.Type with
    | Fable.List _ -> Some(lw ctx inner, "list")
    | Fable.Array(_, (Fable.MutableArray | Fable.ImmutableArray)) -> Some(lw ctx inner, "array")
    // (a `ReadOnlyCollection<'T>`, `IList<'T>`: an array here)
    | Fable.DeclaredType(ent, [ _ ]) when
        ent.FullName = "System.Collections.ObjectModel.ReadOnlyCollection`1"
        || ent.FullName = "System.Collections.Generic.IList`1"
        ->
        Some(lw ctx inner, "array")
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
                            // (a function of several arguments is kept uncurried, as in an
                            // object's field)
                            staticTypes[name] <- FableTransforms.uncurryType f.FieldType
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
                // a class deriving from `Dictionary` or `HashSet` with members only: its
                // constructor makes the collection, by the base constructor
                | Some ent when
                    (collectionBase
                        com
                        (Fable.DeclaredType(
                            c.Entity,
                            ent.GenericParameters
                            |> List.map (fun g -> Fable.GenericParam(g.Name, false, []))
                        )))
                        .IsSome
                    ->
                    let collectionType =
                        (collectionBase
                            com
                            (Fable.DeclaredType(
                                c.Entity,
                                ent.GenericParameters
                                |> List.map (fun g -> Fable.GenericParam(g.Name, false, []))
                            )))
                            .Value

                    match c.Constructor, c.BaseCall with
                    | Some ctor, Some(Fable.Call(callee, info, _, r)) ->
                        // (Fable types the base constructor's call as unit: it makes the collection)
                        let baseCall = Fable.Call(callee, info, collectionType, r)

                        let body =
                            match ctor.Body with
                            | Fable.Value(Fable.UnitConstant, _) -> baseCall
                            | body -> Fable.Sequential [ body; baseCall ]

                        attached.Add { ctor with Body = body }
                    | _ -> report None $"the Zig target needs a primary constructor of %s{c.Name}"

                    for m in c.AttachedMembers do
                        report
                            m.Body.Range
                            $"the Zig target does not support this kind of member of a collection's subclass yet (%s{c.Name}.%s{m.Name})"
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

    /// the type parameters of the type a member is of
    let typeParamsOfType (info: Fable.MemberFunctionOrValue) : string list =
        match info.DeclaringEntity |> Option.bind com.TryGetEntity with
        | Some ent when not ent.IsFSharpModule -> ent.GenericParameters |> List.map (fun g -> g.Name)
        | _ -> []

    /// (the implementation of a generic method of an interface: its slot has the method's type
    /// parameters erased to `obj`, and so has it)
    let isErasedImpl (info: Fable.MemberFunctionOrValue) =
        info.IsOverrideOrExplicitInterfaceImplementation
        && info.CompiledName.Contains "."
        && not info.GenericParameters.IsEmpty

    /// the type parameters of a function: those of the type it is a member of, then its own
    let typeParamsOf (info: Fable.MemberFunctionOrValue) : string list =
        let ofType = typeParamsOfType info

        if isErasedImpl info then
            ofType
        else
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

        // (an erased implementation: its own type parameters, and those Fable names in its types
        // from the interface's declaration, are `obj` in its body)
        let erasedHere =
            if isErasedImpl info then
                let ofType = set (typeParamsOfType info)

                let rec gens (t: Fable.Type) =
                    match t with
                    | Fable.GenericParam(n, _, _) -> [ n ]
                    | t -> t.Generics |> List.collect gens

                (info.GenericParameters |> List.map (fun g -> g.Name))
                @ (d.Body.Type :: (d.Args |> List.map (fun a -> a.Type)) |> List.collect gens)
                |> List.distinct
                |> List.filter (fun g -> not (ofType.Contains g) && not (state.GenAliases.ContainsKey g))
            else
                []

        for g in erasedHere do
            state.GenAliases[g] <- tAny

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

        for g in erasedHere do
            state.GenAliases.Remove g |> ignore

    settleCyclic state
    settleCycles state
    state
