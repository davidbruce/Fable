/// Lowering for constant/aggregate values, function application, calls, mutations, control
/// flow, loops, and decision trees.
module Fable.Transforms.Zig.LowerControl

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

let lowerValue (ctx: Ctx) (e: Fable.Expr) : Expr =
    match e with
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

    | _ -> fail e.Range "internal: expected Value"

/// Apply a function value to arguments, as many at a time as its type takes. (`subst` says
/// what the type parameters in `fTy` stand for, when it is the declared result type of a
/// generic function.)
let rec private applyValue
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


let lowerTail (ctx: Ctx) (e: Fable.Expr) : Expr =
    match e with
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

    // (`for i = 0 to arr.Length - 1` of a mutable array: .NET reads the bound again at each
    // iteration, so a loop that assigns the array runs to its new length)
    | Fable.ForLoop(id,
                    start,
                    (Fable.Operation(Fable.Binary(BinaryMinus,
                                                  Fable.Call(Fable.Import(getLen, _, _), lenInfo, _, _),
                                                  Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 1, _), _)),
                                     _,
                                     _,
                                     _) as limit),
                    body,
                    true,
                    r) when
        getLen.Selector = "get_Length"
        && (
            match lenInfo.ThisArg with
            | Some(Fable.IdentExpr a) ->
                a.IsMutable
                && (
                    match a.Type with
                    | Fable.Array(_, (Fable.MutableArray | Fable.ImmutableArray)) -> true
                    | _ -> false
                )
            | Some(Fable.Import({ Kind = Fable.MemberImport memberRef }, _, _)) ->
                match ctx.Com.TryGetMember memberRef with
                | Some m -> m.IsValue && m.IsMutable
                | None -> false
            | _ -> false
        )
        ->
        let i = { AST.makeTypedIdent id.Type (tempName ctx "i") with IsMutable = true }

        let one =
            Fable.Value(Fable.NumberConstant(Fable.NumberValue.Int32 1, Fable.NumberInfo.Empty), None)

        let cond =
            Fable.Operation(Fable.Binary(BinaryLessOrEqual, Fable.IdentExpr i, limit), [], Fable.Boolean, r)

        let step =
            Fable.Set(
                Fable.IdentExpr i,
                Fable.ValueSet,
                id.Type,
                Fable.Operation(Fable.Binary(BinaryPlus, Fable.IdentExpr i, one), [], id.Type, r),
                r
            )

        lw
            ctx
            (Fable.Let(
                i,
                start,
                Fable.WhileLoop(cond, Fable.Let(id, Fable.IdentExpr i, Fable.Sequential [ body; step ]), r)
            ))
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
