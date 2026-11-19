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

open Fable.Transforms.Zig.LowerFormat

let rec lw (ctx: Ctx) (e: Fable.Expr) : Expr =
    match e with
    // ---- what the program imports from Zig (`[<Import("add", "./native.zig")>]`,
    // `[<ImportMember>]`, `[<ImportAll("std")>]`): used as it is. A function is called directly,
    // its arguments borrowed for the call (what it keeps, it dup's); what it returns is owned ----
    | Fable.Call(Fable.Import({ Kind = Fable.UserImport _ } as imp, _, _), info, t, r) ->
        lw ctx (userImportCall ctx imp info t r)
    | Fable.CurriedApply(Fable.Import({ Kind = Fable.UserImport _ } as imp, _, _), args, t, r) ->
        lw ctx (userImportCall ctx imp (Fable.CallInfo.Create(args = args)) t r)
    // (a member of an interface of a Zig type, `[<Erase; Import(...)>]`: the Zig type's own:
    // `x.add(1)`, `x.n`, `x.n = 2`)
    | Fable.Call(Fable.Get(x, Fable.FieldGet fi, _, _), info, t, r) when isErasedZig ctx x.Type ->
        let n = info.Args |> List.filter (fun a -> not (isUnit a.Type)) |> List.length

        let holes = List.init n (fun i -> $"$%d{i + 1}") |> String.concat ", "

        lw
            ctx
            (Fable.Emit(
                {
                    Macro = $"$0.%s{fi.Name}(%s{holes})"
                    IsStatement = false
                    CallInfo = { info with ThisArg = Some x }
                },
                t,
                r
            ))
    | Fable.Get(x, Fable.FieldGet fi, t, r) when isErasedZig ctx x.Type ->
        bindArgs ctx [ lw ctx x ] (fun xs -> EEmit($"$0.%s{fi.Name}", xs, mapType ctx r t))
    | Fable.Set(x, Fable.FieldSet name, _, v, _) when isErasedZig ctx x.Type ->
        bindArgs ctx [ lw ctx x; lw ctx v ] (fun xs -> EEmit($"$0.%s{name} = $1", xs, tVoid))
    // (a value whose type F# gives where it is used: `let answer: int = nativeOnly`)
    | Fable.TypeCast(Fable.Import({ Kind = Fable.UserImport _ } as imp, Fable.Any, _), t) when t <> Fable.Any ->
        lw ctx (Fable.Import(imp, t, None))
    | Fable.Import({ Kind = Fable.UserImport _ } as imp, t, r) ->
        match t with
        | Fable.LambdaType _
        | Fable.DelegateType _ ->
            fail r "the Zig target cannot use an imported function as a value yet: call it, or wrap it in a lambda"
        | _ -> EEmit(userImportTarget ctx imp, [], mapType ctx r t)
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
        // (`o :? IEnumerable`: a collection, whose items it can give as objects)
        | Fable.DeclaredType(cls, []) when cls.FullName = "System.Collections.IEnumerable" ->
            ctx.State.UsesRuntime <- true
            bindArgs ctx [ lw ctx x ] (fun xs -> EEmit("fable_rt.objHasItems($0)", xs, tBool))
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
    | Fable.Value _ -> LowerContext.lowerValueHook ctx e

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
                    LowerContext.libraryCallHook
                        ctx
                        r
                        "DateTimeOffset"
                        "tryParseOption"
                        { info with ThisArg = None }
                        [ info.Args.Head ]
                        (Fable.Option(out.Type, false))
                // (`DateTime.TryParse(s[, culture[, styles]], &d)`)
                | "TryParse" when imp.Path.EndsWith("System.DateTime", System.StringComparison.Ordinal) ->
                    LowerContext.libraryCallHook
                        ctx
                        r
                        "DateTime"
                        "tryParseOption"
                        { info with ThisArg = None }
                        [ info.Args.Head ]
                        (Fable.Option(out.Type, false))
                // (`TimeSpan.TryParse(s[, culture], &t)`)
                | "TryParse" when imp.Path.EndsWith("System.TimeSpan", System.StringComparison.Ordinal) ->
                    LowerContext.libraryCallHook
                        ctx
                        r
                        "TimeSpan"
                        "tryParseOption"
                        { info with ThisArg = None }
                        [ info.Args.Head ]
                        (Fable.Option(out.Type, false))
                // (`Guid.TryParse(s, &g)`)
                | "TryParse" when imp.Path.EndsWith("System.Guid", System.StringComparison.Ordinal) ->
                    LowerContext.libraryCallHook
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

                    LowerContext.libraryCallHook
                        ctx
                        r
                        "Uri"
                        fn
                        { info with ThisArg = None }
                        args
                        (Fable.Option(out.Type, false))
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
        && (LowerContext.forInSourceHook ctx getInfo.ThisArg.Value).IsSome
        && (forInLoop enumerator.Name rest).IsSome
        ->
        let loopBody, finalizer = (forInLoop enumerator.Name rest).Value
        let source, kind = (LowerContext.forInSourceHook ctx getInfo.ThisArg.Value).Value
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

                bindArgs
                    ctx
                    [ source ]
                    (fun xs ->
                        ELet(
                            walk,
                            ECallClo(EGet(xs.Head, PField "fable_seq", TFn([ tVoid ], walkTy)), [ EUnit ], walkTy),
                            ESeq(ETry(loop, exV, onRaise, tVoid), closeWalk ())
                        )
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
        LowerContext.libraryCallHook ctx r "Async" "sourceDispose" (Fable.CallInfo.Create(args = [ inner ])) [ inner ] t
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

        LowerContext.dotnetCallHook ctx r (imp.Path.Substring Replacements.DotnetPrefix.Length) imp.Selector info t

    // `[<Emit("...")>]`: Zig text, with `$0`, `$1`, ... standing for the arguments
    | Fable.Emit(info, t, r) ->
        let ty = mapType ctx r t

        if info.Macro.Contains "fable_rt." then
            ctx.State.UsesRuntime <- true

        // (`Fable.Core.Zig.Iso.pack x`: a call that takes `x`, given up when it is its last use,
        // dup'ed when the caller goes on using it, which makes it not isolated; see fable_rt.isoPack)
        // (and the library's boxes of a MailboxProcessor's messages, which take theirs the same
        // way: `$iso_send`, `$iso_hold`; see Async.fs's MessageQueue)
        // (`Iso.tryPack x`: the runtime gives the Iso or the value back, as a tuple of two options
        // (`$iso_trypack`); the Result is made here, of the type F# gave the call)
        if info.Macro = "$iso_trypack_result($0)" then
            match t with
            | Fable.DeclaredType(resultEnt, genArgs) when genArgs.Length = 2 ->
                let isoT = genArgs.[0]
                let valueT = genArgs.[1]

                let partsT =
                    Fable.Tuple([ Fable.Option(isoT, false); Fable.Option(valueT, false) ], false)

                let parts =
                    Fable.Emit(
                        {
                            Macro = "$iso_trypack($0)"
                            IsStatement = false
                            CallInfo = info.CallInfo
                        },
                        partsT,
                        r
                    )

                let v = AST.makeTypedIdent partsT (tempName ctx "parts")

                let item i ty =
                    Fable.Get(Fable.IdentExpr v, Fable.TupleIndex i, Fable.Option(ty, false), r)

                let some i ty =
                    Fable.Get(item i ty, Fable.OptionValue, ty, r)

                let case tag value =
                    Fable.Value(Fable.NewUnion([ value ], tag, resultEnt, genArgs), r)

                lw
                    ctx
                    (Fable.Let(
                        v,
                        parts,
                        Fable.IfThenElse(
                            Fable.Test(item 0 isoT, Fable.OptionTest true, r),
                            case 0 (some 0 isoT),
                            case 1 (some 1 valueT),
                            r
                        )
                    ))
            | _ -> fail r "internal: Iso.tryPack of an unexpected type"
        else

            let ownedCall =
                match info.Macro with
                | "$iso_pack($0)" -> Some "fable_rt.isoPack"
                | "$iso_send($0)" -> Some "fable_rt.isoSend"
                | "$iso_hold($0)" -> Some "fable_rt.isoHold"
                | "$iso_trypack($0)" -> Some "fable_rt.isoTryPack"
                | _ -> None

            if ownedCall.IsSome then
                ctx.State.UsesRuntime <- true
                let x = info.CallInfo.Args.Head

                bindArgs ctx [ lw ctx x ] (fun xs -> ECall(ownedCall.Value, [ mapTypeArg ctx r x.Type ], xs, ty))
            else

                // (an instance member: the object is `$0`, the arguments follow, as in the other targets)
                // (a C function's byref parameter, `out`/`ref`: its address, not the value read
                // through it, as a call of an F# function that takes a byref gives)
                let isCCall =
                    info.Macro.StartsWith("fable_rt.callC(", System.StringComparison.Ordinal)

                let args =
                    (Option.toList info.CallInfo.ThisArg @ info.CallInfo.Args)
                    |> List.filter (fun a -> not (isUnit a.Type))
                    |> List.map (fun a ->
                        let ir = lw ctx a

                        match a.Type with
                        | Fable.DeclaredType(ent, _) when isCCall && ent.FullName = "Microsoft.FSharp.Core.byref`2" ->
                            defaultArg (tryAddress ir) ir
                        | _ -> ir
                    )

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
    | LowerInterfaceExpr ctx lowered -> lowered

    | _ -> LowerContext.lowerExprTailHook ctx e

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
                NoEscape = []
                BodyK = None
                StoreFacts = [], false, false
                AssertedNoRaise = []
                AssertedStores = []
                NeedsChain = false
                PendingChainDeps = []
                BodyTc = None
            }

        if ctx.NoTailCalls then
            ctx.State.NoTailCalls.Add fn.FnName |> ignore

    fns


and lwStmt (ctx: Ctx) (e: Fable.Expr) : Expr = asStmt ctx (lw ctx e)
