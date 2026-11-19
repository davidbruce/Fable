/// Specialize hot `List.*` and `Array.*` higher-order functions directly into local TRMC /
/// direct loops in the caller's file when given a known lambda, local function, or callable.
module Fable.Transforms.Zig.DotnetHofSpec

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

/// Specialize hot `List.*` and `Array.*` higher-order functions directly into local TRMC /
/// direct loops in the caller's file when given a known lambda, local function, or callable,
/// avoiding closure allocation and indirect `.code` calls.
let rec private hasAnyType (t: Fable.Type) =
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
        ctx.State.NoTailCalls.Add fnName |> ignore

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
        | "SumBy", [ f; xs ] when canSpecFnExpr ctx f ->
            let inListTy = mapType ctx r xs.Type
            let outTy = mapType ctx r t

            match listElem inListTy with
            | Some inElem when intBits outTy > 0 || isFloatTy outTy ->
                let fIr = lw ctx f

                match tryExtractSpec ctx 1 [ inElem ] outTy fIr with
                | Some(preBinds, (capParams, caps, callSpec)) ->
                    let accV = ctx.State.NewVar("acc", outTy, VParam, false)
                    let restV = ctx.State.NewVar("rest", inListTy, VParam, false)

                    let fnName, typeArgs =
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
                                                        (capParams |> List.map EVar) @ [ EVar nextV; EVar tailV ],
                                                        outTy
                                                    )
                                                )
                                            )
                                        )
                                    ),
                                    outTy
                                )
                            )

                    let xsIr = coerceTy ctx inListTy (lw ctx xs)

                    let callExpr =
                        bindArgs
                            ctx
                            [ xsIr ]
                            (fun ys -> ECall(fnName, typeArgs, caps @ [ ELit("0", outTy); ys.Head ], outTy))

                    Some(List.foldBack (fun (v, x) acc -> ELet(v, x, acc)) preBinds callExpr)
                | None -> Some(withLoweredExpr ctx f.Type "fn" fIr (fun fId -> fallback [ fId; xs ]))
            | _ -> None
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

                                match name with
                                | "Map"
                                | "MapIndexed" ->
                                    let bufTy = TPrim $"fable_rt.MapBuf(%s{zigType inArrTy}, %s{zigType outArrTy})"
                                    let bufV = ctx.State.NewVar("buf", bufTy, VLocal, true)
                                    let yV = ctx.State.NewVar("y", outElem, VLocal, false)

                                    let itemTake =
                                        EEmit(
                                            "fable_rt.arrayMapBufTake($0, @as(usize, @intCast($1)))",
                                            [ EAddr(EVar bufV, false); EVar iV ],
                                            inElem
                                        )

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
                                                itemTake,
                                                ELet(
                                                    yV,
                                                    callNode,
                                                    ESeq(
                                                        EEmit(
                                                            "fable_rt.arrayMapBufPush($0, $1)",
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
                                                    "fable_rt.arrayMapBufAbandon($0)",
                                                    [ EAddr(EVar bufV, false) ],
                                                    tVoid
                                                ),
                                                ERaise(EVar exV, tVoid)
                                            ),
                                            tVoid
                                        )

                                    ELet(
                                        bufV,
                                        EEmit($"fable_rt.arrayMapBufNew($0, %s{zigType outArrTy})", [ EVar aV ], bufTy),
                                        ELet(
                                            lenV,
                                            EEmit("fable_rt.arrayMapBufLen($0)", [ EAddr(EVar bufV, false) ], tI32),
                                            ELet(
                                                iV,
                                                ELit("0", tI32),
                                                ESeq(
                                                    guarded,
                                                    EEmit(
                                                        "fable_rt.arrayMapBufFinish($R, $0)",
                                                        [ EAddr(EVar bufV, false) ],
                                                        outArrTy
                                                    )
                                                )
                                            )
                                        )
                                    )
                                | _ ->
                                    let fbTy = TPrim $"fable_rt.FilterReuseBuf(%s{zigType inArrTy})"
                                    let fbV = ctx.State.NewVar("fb", fbTy, VLocal, true)
                                    let keepV = ctx.State.NewVar("keep", tBool, VLocal, false)

                                    let itemRead =
                                        EEmit(
                                            "fable_rt.arrayFilterBufItem($0, @as(usize, @intCast($1)))",
                                            [ EAddr(EVar fbV, false); EVar iV ],
                                            inElem
                                        )

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
                                                            "fable_rt.arrayFilterBufStep($0, @as(usize, @intCast($1)), $2)",
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
                                                    "fable_rt.arrayFilterBufAbandon($0)",
                                                    [ EAddr(EVar fbV, false) ],
                                                    tVoid
                                                ),
                                                ERaise(EVar exV, tVoid)
                                            ),
                                            tVoid
                                        )

                                    ELet(
                                        fbV,
                                        EEmit("fable_rt.arrayFilterBufNew($0)", [ EVar aV ], fbTy),
                                        ELet(
                                            lenV,
                                            EEmit("fable_rt.arrayFilterBufLen($0)", [ EAddr(EVar fbV, false) ], tI32),
                                            ELet(
                                                iV,
                                                ELit("0", tI32),
                                                ESeq(
                                                    guarded,
                                                    EEmit(
                                                        "fable_rt.arrayFilterBufFinish($0)",
                                                        [ EAddr(EVar fbV, false) ],
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
