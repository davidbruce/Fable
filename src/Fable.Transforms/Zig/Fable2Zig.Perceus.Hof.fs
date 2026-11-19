/// Local HOF specialization, known-closure folding, NoEscape/CallK, and NeedsChain analysis.
module internal Fable.Transforms.Zig.PerceusHof

open System.Collections.Generic
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.Facts
open Fable.Transforms.Zig.PerceusAnalysis

let capsAreImmutableVars (caps: Expr list) =
    caps
    |> List.forall (
        function
        | EVar v -> not v.FMutable && v.Kind <> VGlobal
        | _ -> false
    )

let isIfaceParamTy (t: Ty) =
    match t with
    | TEnt({ Kind = KIface }, _)
    | TOpt(TEnt({ Kind = KIface }, _)) -> true
    | _ -> false

let ifaceSourceVarsOk (src: IfaceSource) =
    match src with
    | ISrcCaptures caps -> capsAreImmutableVars caps
    | ISrcValue v
    | ISrcUpcast v -> capsAreImmutableVars [ v ]

let rec dropDeadClosures (e: Expr) : Expr =
    let isPureDeadIface rhs =
        match rhs with
        | EIface(_, src, _) -> ifaceSourceVarsOk src
        | ECon(t, "Some", [ inner ], None) when isIfaceParamTy t ->
            match inner with
            | EIface(_, src, _) -> ifaceSourceVarsOk src
            | EVar u -> capsAreImmutableVars [ EVar u ]
            | _ -> false
        | _ -> false

    match e with
    | ELet(v, (EClosure(_, _, caps, _) as rhs), body) ->
        let body' = dropDeadClosures body

        if not v.FMutable && capsAreImmutableVars caps && not ((fv body').Contains v.Id) then
            body'
        else
            ELet(v, rhs, body')
    | ELet(v, rhs, body) when isPureDeadIface rhs ->
        let body' = dropDeadClosures body

        if not v.FMutable && not ((fv body').Contains v.Id) then
            body'
        else
            ELet(v, rhs, body')
    | ELet(v, rhs, body) -> ELet(v, dropDeadClosures rhs, dropDeadClosures body)
    | ESeq(a, b) -> ESeq(dropDeadClosures a, dropDeadClosures b)
    | EIf(c, t, f, ty) -> EIf(dropDeadClosures c, dropDeadClosures t, dropDeadClosures f, ty)
    | EWhile(c, b) -> EWhile(dropDeadClosures c, dropDeadClosures b)
    | EFor(i, a, b, up, body) -> EFor(i, dropDeadClosures a, dropDeadClosures b, up, dropDeadClosures body)
    | EAssign(v, r) -> EAssign(v, dropDeadClosures r)
    | EStore(lv, r) -> EStore(dropDeadClosures lv, dropDeadClosures r)
    | ETry(b, v, h, ty) -> ETry(dropDeadClosures b, v, dropDeadClosures h, ty)
    | _ -> e

let resolveKnownClosure
    (env: Map<int, string * Ty list * Expr list * Ty>)
    (e: Expr)
    : (string * Ty list * Expr list * Ty) option
    =
    match e with
    | EClosure(target, typeArgs, caps, ty) when capsAreImmutableVars caps -> Some(target, typeArgs, caps, ty)
    | EVar v -> env.TryFind v.Id
    | _ -> None

/// Turn calls to known closures (`let f = closure(...) in f(x)` or direct `closure(...)(x)`)
/// into direct `ECall`s so no closure indirect call happens and unused closures can be dropped.
let rec foldKnownClosures
    (fns: Dictionary<string, FnInfo>)
    (curried2: Dictionary<string, string>)
    (env: Map<int, string * Ty list * Expr list * Ty>)
    (e: Expr)
    : Expr
    =
    let go = foldKnownClosures fns curried2 env

    let tryDirectCall (target: string) (cTypeArgs: Ty list) (caps: Expr list) (args: Expr list) (resTy: Ty) =
        match fns.TryGetValue target with
        | true, fn when
            fn.Params.Length = caps.Length + args.Length
            && fn.TypeParams.Length = cTypeArgs.Length
            ->
            let inst =
                if fn.TypeParams.IsEmpty then
                    Map.empty
                else
                    Map.ofList (List.zip fn.TypeParams cTypeArgs)

            let fullArgs = caps @ args

            if
                List.forall2 (fun (q: Var) a -> zigType (substTy inst q.Ty) = zigType (typeOf a)) fn.Params fullArgs
                && zigType (substTy inst fn.Ret) = zigType resTy
            then
                Some(ECall(target, cTypeArgs, fullArgs, resTy))
            else
                None
        | _ -> None

    match e with
    | ELet(v, r, b) ->
        let r' = go r

        let env' =
            match r' with
            | EClosure(target, cTypeArgs, caps, cloTy) when not v.FMutable && capsAreImmutableVars caps ->
                env.Add(v.Id, (target, cTypeArgs, caps, cloTy))
            | _ -> env

        ELet(v, r', foldKnownClosures fns curried2 env' b)
    | ESeq(a, b) -> ESeq(go a, go b)
    | EIf(c, t, f, ty) -> EIf(go c, go t, go f, ty)
    | EWhile(c, b) -> EWhile(go c, go b)
    | EFor(i, a, b, up, body) -> EFor(i, go a, go b, up, go body)
    | EAssign(v, r) -> EAssign(v, go r)
    | EStore(lv, r) -> EStore(go lv, go r)
    | ETry(b, v, h, ty) -> ETry(go b, v, go h, ty)
    | ERaise(x, ty) -> ERaise(go x, ty)
    | _ ->
        let e' =
            match flatKids e with
            | [] -> e
            | ks -> withFlatKids e (List.map go ks)

        match e' with
        | ECallClo(fExpr, args, resTy) ->
            match resolveKnownClosure env fExpr with
            | Some(target, cTypeArgs, caps, TFn(ps, _)) when args.Length = ps.Length ->
                match tryDirectCall target cTypeArgs caps args resTy with
                | Some call -> call
                | None -> e'
            | Some(target, cTypeArgs, caps, TFn([ _ ], TFn([ _ ], _))) when args.Length = 2 ->
                match curried2.TryGetValue target with
                | true, target2 ->
                    match tryDirectCall target2 cTypeArgs caps args resTy with
                    | Some call -> call
                    | None -> e'
                | _ -> e'
            | _ -> e'
        | _ -> e'

let genNameRx =
    System.Text.RegularExpressions.Regex("@\"'([^\"]+)\"", System.Text.RegularExpressions.RegexOptions.Compiled)

let rec exprSize (e: Expr) =
    match e with
    | ELet(_, r, b)
    | ESeq(r, b)
    | EWhile(r, b)
    | EStore(r, b) -> 1 + exprSize r + exprSize b
    | EIf(c, t, f, _) -> 1 + exprSize c + exprSize t + exprSize f
    | EFor(_, a, b, _, body) -> 1 + exprSize a + exprSize b + exprSize body
    | EAssign(_, r)
    | EDrop(_, r)
    | EUnpack(_, r)
    | EPromote(_, r)
    | ERaise(r, _) -> 1 + exprSize r
    | ETry(b, _, h, _) -> 1 + exprSize b + exprSize h
    | _ -> 1 + (flatKids e |> List.sumBy exprSize)

/// Fold calls to known closures and clone intra-file higher-order functions when passed known
/// local/file callbacks, turning indirect `f.code(...)` calls into direct calls with borrow
/// inference and TRMC preserved.
let specializeHofs (state: FileState) (hooks: HashSet<string>) : unit =
    let fns = Dictionary<string, FnInfo>()

    for fn in state.Fns do
        fns[fn.Name] <- fn

    let polishFn (fn: FnInfo) =
        fn.Body <-
            fn.Body
            |> foldKnownClosures fns state.Curried2 Map.empty
            |> dropDeadClosures
            |> cleanup

    for fn in state.Fns do
        polishFn fn

    let substStr (inst: Map<string, Ty>) (s: string) =
        if inst.IsEmpty || not (s.Contains("@\"'")) then
            s
        else
            genNameRx.Replace(
                s,
                fun m ->
                    match inst.TryFind m.Groups.[1].Value with
                    | Some ty -> zigType ty
                    | None -> m.Value
            )

    let rec instTy (inst: Map<string, Ty>) (t: Ty) =
        if inst.IsEmpty then
            t
        else
            match t with
            | TGen n ->
                match inst.TryFind n with
                | Some x -> x
                | None -> t
            | TPrim s when s.Contains("@\"'") -> TPrim(substStr inst s)
            | TEnt(ent, args) -> TEnt(ent, args |> List.map (instTy inst))
            | TOpt x -> TOpt(instTy inst x)
            | TTuple ts -> TTuple(ts |> List.map (instTy inst))
            | TPtr(x, c) -> TPtr(instTy inst x, c)
            | TSlice(x, c) -> TSlice(instTy inst x, c)
            | TArr(x, n) -> TArr(instTy inst x, n)
            | TFn(ps, r) -> TFn(ps |> List.map (instTy inst), instTy inst r)
            | TSlot(ps, r) -> TSlot(ps |> List.map (instTy inst), instTy inst r)
            | TTok(x, c) -> TTok(instTy inst x, c)
            | TPrim _ -> t

    let calleeUsesFnParam (calleeName: string) (pId: int) (body: Expr) =
        exists
            (function
            | ECallClo(EVar v, _, _) when v.Id = pId -> true
            | ECall(g, _, xs, _) when g <> calleeName && fns.ContainsKey g ->
                xs
                |> List.exists (
                    function
                    | EVar v -> v.Id = pId
                    | _ -> false
                )
            | _ -> false)
            body

    let memo = Dictionary<string, string>()

    let freshSpecName (baseName: string) =
        let mutable i = 0
        let mutable cand = $"%s{baseName}$spec%d{i}"

        while fns.ContainsKey cand do
            i <- i + 1
            cand <- $"%s{baseName}$spec%d{i}"

        cand

    let cloneSpecializedFn
        (callee: FnInfo)
        (callTypeArgs: Ty list)
        (specTypeParams: string list)
        (specMap: Map<int, string * Ty list * Expr list * Ty>)
        (specKey: string)
        =
        match memo.TryGetValue specKey with
        | true, existing -> existing
        | _ ->
            let specName = freshSpecName callee.Name
            memo[specKey] <- specName

            let inst =
                if callee.TypeParams.IsEmpty then
                    Map.empty
                else
                    Map.ofList (List.zip callee.TypeParams callTypeArgs)

            let varMap = Dictionary<int, Var>()
            let specParams = List<Var>()
            let capVarsByIdx = Dictionary<int, Var list>()
            let localCloWrappers = List<Var * Expr>()

            callee.Params
            |> List.iteri (fun idx p ->
                match specMap.TryFind idx with
                | Some(cloTarget, cloTypeArgs, cloCaps, _) ->
                    let freshCaps =
                        cloCaps
                        |> List.mapi (fun k c -> state.NewVar($"%s{p.Base}_c%d{k}", typeOf c, VParam, false))

                    for v in freshCaps do
                        specParams.Add v

                    capVarsByIdx[idx] <- freshCaps
                    let pTy = instTy inst p.Ty
                    let freshClo = state.NewVar(p.Base, pTy, VLocal, false)
                    varMap[p.Id] <- freshClo
                    localCloWrappers.Add((freshClo, EClosure(cloTarget, cloTypeArgs, freshCaps |> List.map EVar, pTy)))
                | None ->
                    let p' = state.NewVar(p.Base, instTy inst p.Ty, VParam, p.FMutable)
                    varMap[p.Id] <- p'
                    specParams.Add p'
            )

            let mapVar (v: Var) =
                match varMap.TryGetValue v.Id with
                | true, v' -> v'
                | _ -> v

            let freshLocal (v: Var) =
                let v' = state.NewVar(v.Base, instTy inst v.Ty, v.Kind, v.FMutable)
                varMap[v.Id] <- v'
                v'

            let rec clone (e: Expr) : Expr =
                match e with
                | EVar v -> EVar(mapVar v)
                | ELit(s, t) -> ELit(substStr inst s, instTy inst t)
                | EUnit -> EUnit
                | EPrim(op, xs, t) -> EPrim(op, xs |> List.map clone, instTy inst t)
                | ECall(f, recTypeArgs, recArgs, recRetTy) when
                    f = callee.Name
                    && recTypeArgs.Length = callee.TypeParams.Length
                    && (recTypeArgs |> List.map (instTy inst)) = callTypeArgs
                    && recArgs.Length = callee.Params.Length
                    && (specMap
                        |> Map.forall (fun idx _ ->
                            match recArgs[idx] with
                            | EVar v -> v.Id = callee.Params[idx].Id
                            | _ -> false
                        ))
                    ->
                    let expandedRecArgs =
                        recArgs
                        |> List.indexed
                        |> List.collect (fun (idx, a) ->
                            match capVarsByIdx.TryGetValue idx with
                            | true, caps -> caps |> List.map EVar
                            | _ -> [ clone a ]
                        )

                    ECall(specName, specTypeParams |> List.map TGen, expandedRecArgs, instTy inst recRetTy)
                | ECall(f, tys, xs, t) -> ECall(f, tys |> List.map (instTy inst), xs |> List.map clone, instTy inst t)
                | ECallClo(f, xs, t) -> ECallClo(clone f, xs |> List.map clone, instTy inst t)
                | ECallVt(f, s, xs, t) -> ECallVt(clone f, clone s, xs |> List.map clone, instTy inst t)
                | EClosure(f, tys, xs, t) ->
                    EClosure(f, tys |> List.map (instTy inst), xs |> List.map clone, instTy inst t)
                | EKnown(f, tys, xs, t) -> EKnown(f, tys |> List.map (instTy inst), xs |> List.map clone, instTy inst t)
                | EUse(u, x) -> EUse(u, clone x)
                | EAssumedRet(js, call) -> EAssumedRet(js, clone call)
                | EIface(t, src, slots) ->
                    let src' =
                        match src with
                        | ISrcValue x -> ISrcValue(clone x)
                        | ISrcCaptures xs -> ISrcCaptures(xs |> List.map clone)
                        | ISrcUpcast x -> ISrcUpcast(clone x)

                    let slots' =
                        slots |> List.map (fun (s, (f, tys)) -> s, (f, tys |> List.map (instTy inst)))

                    EIface(instTy inst t, src', slots')
                | EKnownIface(t, src, slots, isOpt) ->
                    let src' =
                        match src with
                        | ISrcValue x -> ISrcValue(clone x)
                        | ISrcCaptures xs -> ISrcCaptures(xs |> List.map clone)
                        | ISrcUpcast x -> ISrcUpcast(clone x)

                    let slots' =
                        slots |> List.map (fun (s, (f, tys)) -> s, (f, tys |> List.map (instTy inst)))

                    EKnownIface(instTy inst t, src', slots', isOpt)
                | ECallIface(r, slot, xs, t) -> ECallIface(clone r, slot, xs |> List.map clone, instTy inst t)
                | ECon(t, c, xs, tok) -> ECon(instTy inst t, c, xs |> List.map clone, tok |> Option.map mapVar)
                | EGet(x, p, t) -> EGet(clone x, p, instTy inst t)
                | ETest(x, c, t) -> ETest(clone x, c, instTy inst t)
                | EAddr(x, c) -> EAddr(clone x, c)
                | EDeref(x, t) -> EDeref(clone x, instTy inst t)
                | EIndex(a, b, t) -> EIndex(clone a, clone b, instTy inst t)
                | EEmit(m, xs, t) -> EEmit(substStr inst m, xs |> List.map clone, instTy inst t)
                | ERt(m, xs, t) -> ERt(substStr inst m, xs |> List.map clone, instTy inst t)
                | EExnNew(ent, xs) -> EExnNew(ent, xs |> List.map clone)
                | EExnTest(x, ent) -> EExnTest(clone x, ent)
                | EExnGet(x, ent, f, t) -> EExnGet(clone x, ent, f, instTy inst t)
                | EOnRaise(x, ds) -> EOnRaise(clone x, ds |> List.map mapVar)
                | EDup(x, t) -> EDup(clone x, instTy inst t)
                | ELet(v, r, b) ->
                    let r' = clone r
                    let v' = freshLocal v
                    ELet(v', r', clone b)
                | ESeq(a, b) -> ESeq(clone a, clone b)
                | EIf(c, t, f, ty) -> EIf(clone c, clone t, clone f, instTy inst ty)
                | EWhile(c, b) -> EWhile(clone c, clone b)
                | EFor(i, a, b, up, body) ->
                    let a' = clone a
                    let b' = clone b
                    let i' = freshLocal i
                    EFor(i', a', b', up, clone body)
                | EAssign(v, r) -> EAssign(mapVar v, clone r)
                | EStore(lv, r) -> EStore(clone lv, clone r)
                | EDrop(v, k) -> EDrop(mapVar v, clone k)
                | EUnpack(u, k) ->
                    let u' =
                        { u with
                            Scrut = mapVar u.Scrut
                            Moves = u.Moves |> List.map (fun (s, v) -> s, freshLocal v)
                            Token = u.Token |> Option.map freshLocal
                        }

                    EUnpack(u', clone k)
                | EPromote(v, k) -> EPromote(mapVar v, clone k)
                | ERaise(x, t) -> ERaise(clone x, instTy inst t)
                | ETry(b, v, h, t) ->
                    let b' = clone b
                    let v' = freshLocal v
                    ETry(b', v', clone h, instTy inst t)

            let wrappedBody =
                Seq.foldBack (fun (v, cExpr) acc -> ELet(v, cExpr, acc)) localCloWrappers (clone callee.Body)
                |> foldKnownClosures fns state.Curried2 Map.empty
                |> dropDeadClosures
                |> cleanup

            match state.Arenas.TryGetValue callee.Name with
            | true, bytes -> state.Arenas[specName] <- bytes
            | _ -> ()

            let psList = List.ofSeq specParams

            let specFn =
                {
                    Name = specName
                    TypeParams = specTypeParams
                    Params = psList
                    Modes = psList |> List.map (fun _ -> MPlain)
                    Ret = instTy inst callee.Ret
                    Body = wrappedBody
                    RetFrom = None
                    Raises = RNever
                    Stores = false
                    IsLocal = true
                    IsEntryPoint = false
                    Range = callee.Range
                    NoEscape = []
                    BodyK = None
                    StoreFacts = [], false, false
                    AssertedNoRaise = []
                    AssertedStores = []
                    NeedsChain = false
                    PendingChainDeps = []
                    BodyTc = None
                }

            state.Fns.Add specFn
            fns[specName] <- specFn
            specName

    let rec rewriteCalls (round: int) (env: Map<int, string * Ty list * Expr list * Ty>) (e: Expr) : Expr =
        let go = rewriteCalls round env

        match e with
        | ELet(v, r, b) ->
            let r' = go r

            let env' =
                match r' with
                | EClosure(target, cTypeArgs, caps, cloTy) when not v.FMutable && capsAreImmutableVars caps ->
                    env.Add(v.Id, (target, cTypeArgs, caps, cloTy))
                | _ -> env

            ELet(v, r', rewriteCalls round env' b)
        | ESeq(a, b) -> ESeq(go a, go b)
        | EIf(c, t, f, ty) -> EIf(go c, go t, go f, ty)
        | EWhile(c, b) -> EWhile(go c, go b)
        | EFor(i, a, b, up, body) -> EFor(i, go a, go b, up, go body)
        | EAssign(v, r) -> EAssign(v, go r)
        | EStore(lv, r) -> EStore(go lv, go r)
        | ETry(b, v, h, ty) -> ETry(go b, v, go h, ty)
        | ERaise(x, ty) -> ERaise(go x, ty)
        | _ ->
            let e' =
                match flatKids e with
                | [] -> e
                | ks -> withFlatKids e (List.map go ks)

            match e' with
            | ECall(calleeName, callTypeArgs, callArgs, callRetTy) ->
                match fns.TryGetValue calleeName with
                | true, callee when
                    not (hooks.Contains calleeName)
                    && not callee.IsEntryPoint
                    && callee.Params.Length = callArgs.Length
                    && callee.TypeParams.Length = callTypeArgs.Length
                    && exprSize callee.Body <= 250
                    && (round = 0 || not (calleeName.Contains("$spec")))
                    ->
                    let assigned = assignedIn callee.Body

                    let specEntries =
                        List.zip callee.Params callArgs
                        |> List.indexed
                        |> List.choose (fun (idx, (p, a)) ->
                            match p.Ty with
                            | TFn _ when not (assigned.Contains p.Id) ->
                                match resolveKnownClosure env a with
                                | Some(cloTarget, _, _, _) as found when
                                    fns.ContainsKey cloTarget && calleeUsesFnParam calleeName p.Id callee.Body
                                    ->
                                    Some(idx, found.Value)
                                | _ -> None
                            | _ -> None
                        )

                    if specEntries.IsEmpty then
                        e'
                    else
                        let specMap = Map.ofList specEntries

                        let inst =
                            if callee.TypeParams.IsEmpty then
                                Map.empty
                            else
                                Map.ofList (List.zip callee.TypeParams callTypeArgs)

                        let specTypeParams =
                            freeGens (
                                callTypeArgs
                                @ [ callRetTy; instTy inst callee.Ret ]
                                @ (callArgs
                                   |> List.indexed
                                   |> List.collect (fun (idx, a) ->
                                       match specMap.TryFind idx with
                                       | Some(_, cTys, cCaps, _) -> cTys @ (cCaps |> List.map typeOf)
                                       | None -> [ typeOf a ]
                                   ))
                            )

                        let typeKeyStr = callTypeArgs |> List.map tyKey |> String.concat ","

                        let cloKeyStr =
                            specEntries
                            |> List.map (fun (idx, (t, tys, caps, cty)) ->
                                let cTys = tys |> List.map tyKey |> String.concat ","
                                let capTys = caps |> List.map (typeOf >> tyKey) |> String.concat ","
                                $"%d{idx}:%s{t}<%s{cTys}>(%s{capTys}):%s{tyKey cty}"
                            )
                            |> String.concat ";"

                        let specParamsStr = String.concat "," specTypeParams

                        let specKey = $"%s{calleeName}|<%s{specParamsStr}>|<%s{typeKeyStr}>|%s{cloKeyStr}"

                        let specName = cloneSpecializedFn callee callTypeArgs specTypeParams specMap specKey

                        let expandedArgs =
                            callArgs
                            |> List.indexed
                            |> List.collect (fun (idx, a) ->
                                match specMap.TryFind idx with
                                | Some(_, _, caps, _) -> caps
                                | None -> [ a ]
                            )

                        ECall(specName, specTypeParams |> List.map TGen, expandedArgs, callRetTy)
                | _ -> e'
            | _ -> e'

    for round in 0..1 do
        for fn in List.ofSeq state.Fns do
            fn.Body <-
                rewriteCalls round Map.empty fn.Body
                |> foldKnownClosures fns state.Curried2 Map.empty
                |> dropDeadClosures
                |> cleanup

    for fn in state.Fns do
        polishFn fn

    // Prune local helper functions left dead after specialization / closure folding.
    let stripRaw (s: string) =
        if s.StartsWith("@raw:", System.StringComparison.Ordinal) then
            s.Substring 5
        else
            s

    let live = HashSet<string>()
    let work = Queue<string>()

    let enqueue name =
        if fns.ContainsKey name && live.Add name then
            work.Enqueue name

    for fn in state.Fns do
        if not fn.IsLocal || fn.IsEntryPoint || hooks.Contains fn.Name then
            enqueue fn.Name

    for (_, _, name) in state.Values do
        enqueue name

    for (_, name) in state.Tests do
        enqueue name

    for objDecl in state.Objs do
        for table in objDecl.Tables do
            match table with
            | Some(_, entries) ->
                for (_, target, _, _) in entries do
                    enqueue (stripRaw target)
            | None -> ()

        match objDecl.ToString with
        | Some(target, _) -> enqueue (stripRaw target)
        | None -> ()

        for (_, fn) in objDecl.Overrides do
            enqueue fn

    while work.Count > 0 do
        let fn = fns[work.Dequeue()]

        exists
            (fun x ->
                match x with
                | ECall(f, _, _, _) -> enqueue f
                | EClosure(f, _, _, ty) ->
                    enqueue f

                    match ty with
                    | TFn([ _ ], TFn([ _ ], _)) ->
                        match state.Curried2.TryGetValue f with
                        | true, f2 -> enqueue f2
                        | _ -> ()
                    | _ -> ()
                | EIface(_, _, slots)
                | EKnownIface(_, _, slots, _) ->
                    for (_, (f, _)) in slots do
                        enqueue (stripRaw f)
                | _ -> ()

                false
            )
            fn.Body
        |> ignore

    let kept =
        state.Fns
        |> Seq.filter (fun fn -> not fn.IsLocal || live.Contains fn.Name)
        |> List.ofSeq

    state.Fns.Clear()
    state.Fns.AddRange kept

let rec totalCurriedArgs (t: Ty) : int =
    match t with
    | TFn([ _ ], (TFn _ as inner)) -> 1 + totalCurriedArgs inner
    | TFn(ps, _) -> ps.Length
    | _ -> 0

let directFullArity (t: Ty) : int option =
    match t with
    | TFn([ _ ], TFn([ _ ], innerRet)) ->
        match innerRet with
        | TFn _ -> None
        | _ -> Some 2
    | TFn(ps, innerRet) ->
        match innerRet with
        | TFn _ -> None
        | _ -> Some ps.Length
    | _ -> None

let rec isChainConsumer (vId: int) (remArgs: int) (e: Expr) : bool =
    let has v = (fv v).Contains vId

    match e with
    | ELet(v2, ECallClo(EVar v, args2, _), rest) when v.Id = vId && not v2.FMutable ->
        args2.Length > 0
        && args2.Length < remArgs
        && List.forall (not << has) args2
        && not (has rest)
        && isChainConsumer v2.Id (remArgs - args2.Length) rest
    | ELet(_, r, b) ->
        if has r then
            not (has b) && isChainConsumer vId remArgs r
        else
            isChainConsumer vId remArgs b
    | ESeq(a, b) ->
        if has a then
            not (has b) && isChainConsumer vId remArgs a
        else
            isChainConsumer vId remArgs b
    | EIf(c, t, f, _) ->
        not (has c)
        && (not (has t) || isChainConsumer vId remArgs t)
        && (not (has f) || isChainConsumer vId remArgs f)
    | EWhile _
    | EFor _
    | EAssign _
    | EStore _
    | ERaise _
    | ETry _ -> false
    | EDrop(v, k)
    | EPromote(v, k) -> v.Id <> vId && isChainConsumer vId remArgs k
    | EUnpack(u, k) ->
        u.Scrut.Id <> vId
        && (u.Moves |> List.forall (fun (_, mv) -> mv.Id <> vId))
        && isChainConsumer vId remArgs k
    | ECallClo(EVar v, args2, _) when v.Id = vId -> args2.Length = remArgs && List.forall (not << has) args2
    | EVar v when v.Id = vId -> false
    | _ ->
        flatKids e
        |> List.forall (fun k -> not (has k) || isChainConsumer vId remArgs k)

let rec alwaysRaisesExpr (e: Expr) =
    match e with
    | ERaise _ -> true
    | ELet(_, _, b)
    | ESeq(_, b) -> alwaysRaisesExpr b
    | EIf(_, t, f, _) -> alwaysRaisesExpr t && alwaysRaisesExpr f
    | _ -> false

let rec peelDropsToCon (e: Expr) : (Ty * Expr list) option =
    match e with
    | ECon(conTy, _, conArgs, _) -> Some(conTy, conArgs)
    | EDrop(_, rest) -> peelDropsToCon rest
    | ELet(tmp, ECon(conTy, _, conArgs, _), body) ->
        let rec endsInTmp b =
            match b with
            | EDrop(_, rest) -> endsInTmp rest
            | EVar v when v.Id = tmp.Id -> true
            | _ -> false

        if endsInTmp body then
            Some(conTy, conArgs)
        else
            None
    | _ -> None

let tryMatchTrmcHole (r: Var) (conBody: Expr) : Ty option =
    match peelDropsToCon conBody with
    | Some(TEnt(ent, _) as conTy, conArgs) when (ent.Kind = KHeapUnion || ent.Kind = KValueUnion) && not conArgs.IsEmpty ->
        let hits =
            conArgs
            |> List.indexed
            |> List.filter (fun (_, a) ->
                match a with
                | EVar v -> v.Id = r.Id
                | _ -> false
            )

        match hits with
        | [ (holeIdx, _) ] when
            conArgs
            |> List.indexed
            |> List.forall (fun (j, a) -> j = holeIdx || not (Set.contains r.Id (fv a)))
            ->
            Some conTy
        | _ -> None
    | _ -> None

let rec unwrapTailCallExpr (e: Expr) =
    match e with
    | EAssumedRet(_, x)
    | EOnRaise(x, _)
    | EDup(x, _) -> unwrapTailCallExpr x
    | _ -> e

/// Functions whose tail or TRMC cycles cannot execute as stack-neutral loops inside a `$k`
/// clone (polymorphic/arity-mismatched self recursion, non-heap TRMC, or intra-file SCCs).
let noEscapeExcludedTailFns (fns: FnInfo seq) : HashSet<string> =
    let byName = Dictionary<string, FnInfo>()

    for fn in fns do
        byName[fn.Name] <- fn

    let excluded = HashSet<string>()
    let edges = Dictionary<string, string list>()

    for fn in fns do
        let rec collect (trmcConOpt: Ty option) (e: Expr) : string list =
            match e with
            | ELet(_, rhs, _) when alwaysRaisesExpr rhs -> []
            | ELet(v, rhs, EVar v2) when v.Id = v2.Id -> collect trmcConOpt rhs
            | ELet(r, callRhs, conBody) when not (alwaysRaisesExpr callRhs) ->
                match tryMatchTrmcHole r conBody with
                | Some conTy -> collect (Some conTy) callRhs
                | None -> collect None conBody
            | ELet(_, _, b)
            | ESeq(_, b)
            | EDrop(_, b)
            | EUnpack(_, b)
            | EPromote(_, b) -> collect trmcConOpt b
            | EIf(_, t, f, _) -> collect trmcConOpt t @ collect trmcConOpt f
            | ETry _ -> []
            | _ ->
                match unwrapTailCallExpr e with
                | ECall(g, tArgs, args, _) when byName.ContainsKey g && args.Length = byName[g].Params.Length ->
                    if g = fn.Name then
                        if
                            tArgs <> (fn.TypeParams |> List.map TGen)
                            || (
                                match trmcConOpt with
                                | Some conTy -> not (isHeapTy conTy) || fn.RetFrom.IsSome
                                | None -> false
                            )
                        then
                            excluded.Add fn.Name |> ignore

                        []
                    else
                        [ g ]
                | _ -> []

        edges[fn.Name] <- collect None fn.Body |> List.distinct

    let index = Dictionary<string, int>()
    let low = Dictionary<string, int>()
    let onStack = HashSet<string>()
    let stack = Stack<string>()
    let mutable next = 0

    let rec connect (v: string) =
        index[v] <- next
        low[v] <- next
        next <- next + 1
        stack.Push v
        onStack.Add v |> ignore

        for w in edges[v] do
            if not (index.ContainsKey w) then
                connect w
                low[v] <- min low[v] low[w]
            elif onStack.Contains w then
                low[v] <- min low[v] index[w]

        if low[v] = index[v] then
            let comp = List<string>()
            let mutable stop = false

            while not stop do
                let w = stack.Pop()
                onStack.Remove w |> ignore
                comp.Add w
                stop <- (w = v)

            if comp.Count >= 2 then
                for w in comp do
                    excluded.Add w |> ignore

    for fn in fns do
        if not (index.ContainsKey fn.Name) then
            connect fn.Name

    excluded

let inferNoEscape (p: P) (hooks: HashSet<string>) : unit =
    let fns = p.State.Fns
    let tailExcluded = noEscapeExcludedTailFns fns
    let noEscape = Dictionary<string, bool[]>()

    for fn in fns do
        let excluded =
            fn.IsEntryPoint || hooks.Contains fn.Name || tailExcluded.Contains fn.Name

        let assigned =
            if excluded then
                Set.empty
            else
                assignedIn fn.Body

        noEscape[fn.Name] <-
            fn.Params
            |> List.map (fun q ->
                if excluded then
                    false
                else
                    match q.Ty with
                    | TFn _ -> not (assigned.Contains q.Id)
                    | t when isIfaceParamTy t -> not (assigned.Contains q.Id)
                    | _ -> false
            )
            |> Array.ofList

    let paramOk (fn: FnInfo) (pIdx: int) (q: Var) : bool =
        if isIfaceParamTy q.Ty then
            let rec checkIface (sameIds: Set<int>) (unwrappedIds: Set<int>) (e: Expr) : bool =
                let go s u x = checkIface s u x
                let checkSub = go sameIds unwrappedIds

                match e with
                | EVar v -> not (sameIds.Contains v.Id || unwrappedIds.Contains v.Id)
                | ERt("fable_rt.checkNonNull($0)", [ EVar pv ], _) when sameIds.Contains pv.Id -> true
                | ECallIface(EVar pv, _, args, _) when sameIds.Contains pv.Id || unwrappedIds.Contains pv.Id ->
                    List.forall checkSub args
                | ECallIface(EGet(EVar pv, PSome, _), _, args, _) when sameIds.Contains pv.Id ->
                    List.forall checkSub args
                | ELet(v, EVar pv, scope) when not v.FMutable && sameIds.Contains pv.Id ->
                    go (Set.add v.Id sameIds) unwrappedIds scope
                | ELet(v, EVar pv, scope) when not v.FMutable && unwrappedIds.Contains pv.Id ->
                    go sameIds (Set.add v.Id unwrappedIds) scope
                | ELet(v, EGet(EVar pv, PSome, _), scope) when not v.FMutable && sameIds.Contains pv.Id ->
                    go sameIds (Set.add v.Id unwrappedIds) scope
                | ECall(g, tArgs, args, _) when g = fn.Name ->
                    tArgs = (fn.TypeParams |> List.map TGen)
                    && args.Length = fn.Params.Length
                    && (
                        match args[pIdx] with
                        | EVar pv -> pv.Id = q.Id
                        | _ -> false
                    )
                    && (args |> List.indexed |> List.forall (fun (j, a) -> j = pIdx || checkSub a))
                | ECall(g, _, args, _) ->
                    let matchFlags (gFlags: bool list) =
                        args.Length = gFlags.Length
                        && (args
                            |> List.indexed
                            |> List.forall (fun (j, a) ->
                                match a with
                                | EVar pv when sameIds.Contains pv.Id -> gFlags[j]
                                | _ -> checkSub a
                            ))

                    match p.Fns.TryGetValue g with
                    | true, _ -> matchFlags (Array.toList noEscape[g])
                    | _ ->
                        match p.Ext g with
                        | Some ff -> matchFlags ff.FnParamsNoEscape
                        | None -> List.forall checkSub args
                | ELet(_, r, b)
                | ESeq(r, b)
                | EWhile(r, b)
                | EStore(r, b) -> checkSub r && checkSub b
                | EIf(c, t, f, _) -> checkSub c && checkSub t && checkSub f
                | EFor(_, a, b, _, bd) -> checkSub a && checkSub b && checkSub bd
                | EAssign(_, r) -> checkSub r
                | ERaise(x, _) -> checkSub x
                | ETry(b, _, h, _) -> checkSub b && checkSub h
                | EDrop(_, k)
                | EUnpack(_, k)
                | EPromote(_, k) -> checkSub k
                | _ -> flatKids e |> List.forall checkSub

            checkIface (Set.singleton q.Id) Set.empty fn.Body
        else
            let tot = totalCurriedArgs q.Ty
            let fullArity = directFullArity q.Ty

            let rec check (e: Expr) : bool =
                match e with
                | EVar v -> v.Id <> q.Id
                | ELet(vMid, ECallClo(EVar pv, args1, _), scope) when
                    pv.Id = q.Id
                    && not vMid.FMutable
                    && args1.Length > 0
                    && args1.Length < tot
                    && isChainConsumer vMid.Id (tot - args1.Length) scope
                    ->
                    List.forall check args1 && check scope
                | ECallClo(EVar pv, args, _) when pv.Id = q.Id -> fullArity = Some args.Length && List.forall check args
                | ECall(g, tArgs, args, _) when g = fn.Name ->
                    tArgs = (fn.TypeParams |> List.map TGen)
                    && args.Length = fn.Params.Length
                    && (
                        match args[pIdx] with
                        | EVar pv -> pv.Id = q.Id
                        | _ -> false
                    )
                    && (args |> List.indexed |> List.forall (fun (j, a) -> j = pIdx || check a))
                | ECall(g, _, args, _) ->
                    let matchFlags (gFlags: bool list) =
                        args.Length = gFlags.Length
                        && (args
                            |> List.indexed
                            |> List.forall (fun (j, a) ->
                                match a with
                                | EVar pv when pv.Id = q.Id -> gFlags[j]
                                | _ -> check a
                            ))

                    match p.Fns.TryGetValue g with
                    | true, _ -> matchFlags (Array.toList noEscape[g])
                    | _ ->
                        match p.Ext g with
                        | Some ff -> matchFlags ff.FnParamsNoEscape
                        | None -> List.forall check args
                | ELet(_, r, b)
                | ESeq(r, b)
                | EWhile(r, b)
                | EStore(r, b) -> check r && check b
                | EIf(c, t, f, _) -> check c && check t && check f
                | EFor(_, a, b, _, bd) -> check a && check b && check bd
                | EAssign(_, r) -> check r
                | ERaise(x, _) -> check x
                | ETry(b, _, h, _) -> check b && check h
                | EDrop(_, k)
                | EUnpack(_, k)
                | EPromote(_, k) -> check k
                | _ -> flatKids e |> List.forall check

            check fn.Body

    let mutable changed = true

    while changed do
        changed <- false

        for fn in fns do
            let flags = noEscape[fn.Name]

            fn.Params
            |> List.iteri (fun idx q ->
                if flags[idx] && not (paramOk fn idx q) then
                    flags[idx] <- false
                    changed <- true
            )

    for fn in fns do
        fn.NoEscape <- Array.toList noEscape[fn.Name]

/// Rewrite calls to intra-file and eligible cross-file HOFs when given a known closure in a
/// parameter position, passing a stack-allocated `EKnown` struct instead of a heap closure.
let specializeCallKHofs (p: P) : unit =
    let userAliases = HashSet<string>(p.State.UserImports.Values)
    let importAliases = HashSet<string>(p.State.Imports.Values)

    let canSpecializeTarget (target: string) =
        if p.Fns.ContainsKey target then
            true
        else
            match target.IndexOf '.' with
            | -1 -> false
            | i -> not (userAliases.Contains(target.Substring(0, i)))

    let canSpecIface (ifaceTy: Ty) (src: IfaceSource) (slots: (string * (string * Ty list)) list) =
        not slots.IsEmpty
        && ifaceSourceVarsOk src
        && (let slotMap = caseFields ifaceTy "" |> Map.ofList

            slots
            |> List.forall (fun (slotName, (targetFn, slotTArgs)) ->
                not (targetFn.StartsWith("@raw:", System.StringComparison.Ordinal))
                && canSpecializeTarget targetFn
                && (
                    match slotMap.TryFind slotName with
                    | Some(TSlot(argTys, _) | TFn(argTys, _)) ->
                        let prefixLen =
                            match src with
                            | ISrcCaptures caps -> caps.Length
                            | ISrcValue _ -> 1
                            | ISrcUpcast _ -> 0

                        match p.Fns.TryGetValue targetFn with
                        | true, fn ->
                            fn.Params.Length = prefixLen + argTys.Length
                            && fn.TypeParams.Length = slotTArgs.Length
                            && (
                                match src with
                                | ISrcValue v when typeOf v <> TPrim "fable_rt.Obj" ->
                                    let inst =
                                        if fn.TypeParams.Length = slotTArgs.Length then
                                            Map.ofList (List.zip fn.TypeParams slotTArgs)
                                        else
                                            Map.empty

                                    match substTy inst fn.Params[0].Ty with
                                    | TPtr(_, false) -> false
                                    | _ -> true
                                | _ -> true
                            )
                        | _ ->
                            match src with
                            | ISrcCaptures _ -> true
                            | ISrcValue v -> typeOf v = TPrim "fable_rt.Obj"
                            | ISrcUpcast _ -> false
                    | _ -> false
                )
            ))

    let resolveKnownIface (ifaceEnv: Map<int, Ty * IfaceSource * (string * (string * Ty list)) list * bool>) (e: Expr) =
        match e with
        | EIface(ifaceTy, src, slots) when canSpecIface ifaceTy src slots -> Some(ifaceTy, src, slots, false)
        | ECon(TOpt _, "Some", [ inner ], None) ->
            match inner with
            | EIface(ifaceTy, src, slots) when canSpecIface ifaceTy src slots -> Some(ifaceTy, src, slots, true)
            | EVar u ->
                match ifaceEnv.TryFind u.Id with
                | Some(ifaceTy, src, slots, false) -> Some(ifaceTy, src, slots, true)
                | _ -> None
            | _ -> None
        | EVar v -> ifaceEnv.TryFind v.Id
        | _ -> None

    let rec rw
        (env: Map<int, string * Ty list * Expr list * Ty>)
        (ifaceEnv: Map<int, Ty * IfaceSource * (string * (string * Ty list)) list * bool>)
        (e: Expr)
        : Expr
        =
        let go = rw env ifaceEnv

        match e with
        | ELet(v, r, b) ->
            let r' = go r

            let env' =
                match r' with
                | EClosure(target, cTypeArgs, caps, cloTy) when not v.FMutable && capsAreImmutableVars caps ->
                    env.Add(v.Id, (target, cTypeArgs, caps, cloTy))
                | _ -> env

            let ifaceEnv' =
                if not v.FMutable then
                    match resolveKnownIface ifaceEnv r' with
                    | Some spec -> ifaceEnv.Add(v.Id, spec)
                    | None -> ifaceEnv
                else
                    ifaceEnv

            ELet(v, r', rw env' ifaceEnv' b)
        | ESeq(a, b) -> ESeq(go a, go b)
        | EIf(c, t, f, ty) -> EIf(go c, go t, go f, ty)
        | EWhile(c, b) -> EWhile(go c, go b)
        | EFor(i, a, b, up, body) -> EFor(i, go a, go b, up, go body)
        | EAssign(v, r) -> EAssign(v, go r)
        | EStore(lv, r) -> EStore(go lv, go r)
        | ETry(b, v, h, ty) -> ETry(go b, v, go h, ty)
        | ERaise(x, ty) -> ERaise(go x, ty)
        | _ ->
            let e' =
                match flatKids e with
                | [] -> e
                | ks -> withFlatKids e (List.map go ks)

            match e' with
            | ECall(calleeName, callTypeArgs, callArgs, callRetTy) ->
                let tryWrapArgs (flagsOpt: bool list option) =
                    match flagsOpt with
                    | Some flags when flags.Length = callArgs.Length && List.exists id flags ->
                        let mutable anyKnown = false

                        let callArgs' =
                            List.zip flags callArgs
                            |> List.map (fun (noEsc, a) ->
                                if noEsc then
                                    match resolveKnownClosure env a with
                                    | Some(target, cTypeArgs, caps, cloTy) when canSpecializeTarget target ->
                                        anyKnown <- true
                                        EKnown(target, cTypeArgs, caps, cloTy)
                                    | _ ->
                                        match resolveKnownIface ifaceEnv a with
                                        | Some(ifaceTy, src, slots, isOpt) ->
                                            anyKnown <- true
                                            EKnownIface(ifaceTy, src, slots, isOpt)
                                        | _ -> a
                                else
                                    a
                            )

                        if anyKnown then
                            Some(ECall(calleeName, callTypeArgs, callArgs', callRetTy))
                        else
                            None
                    | _ -> None

                match p.Fns.TryGetValue calleeName with
                | true, callee -> tryWrapArgs (Some callee.NoEscape) |> Option.defaultValue e'
                | false, _ when
                    (let dot = calleeName.IndexOf '.'

                     dot > 0
                     && importAliases.Contains(calleeName.Substring(0, dot))
                     && not (userAliases.Contains(calleeName.Substring(0, dot))))
                    ->
                    match p.Ext calleeName with
                    | Some ff -> tryWrapArgs (Some ff.FnParamsNoEscape) |> Option.defaultValue e'
                    | None ->
                        let flags =
                            callArgs
                            |> List.map (fun a ->
                                match typeOf a with
                                | TFn _ -> true
                                | t -> isIfaceParamTy t
                            )

                        tryWrapArgs (Some flags) |> Option.defaultValue e'
                | _ -> e'
            | _ -> e'

    for fn in p.State.Fns do
        fn.Body <- fn.Body |> rw Map.empty Map.empty |> dropDeadClosures |> cleanup

/// Mark functions that need a full chaining `$tc` entry (`NeedsChain = true`): functions whose
/// tail calls can reach an unknown callee (`ECallClo`, `ECallVt`, `ECallIface`) or an unfused
/// intra-file tail cycle. Excludes entries/hooks/arenas/stackalloc/byref frames.
let inferNeedsChain (p: P) (hooks: HashSet<string>) : unit =
    let state = p.State
    let exportSet = state.Exports |> Seq.map fst |> HashSet
    let testSet = state.Tests |> Seq.map snd |> HashSet
    let valueSet = state.Values |> Seq.map (fun (_, _, n) -> n) |> HashSet

    let usesLocalStackPtr (e: Expr) =
        exists
            (function
            | EAddr(_, false) -> true
            | EEmit(m, _, _)
            | ERt(m, _, _) -> m.StartsWith("fable_stack.alloc(", System.StringComparison.Ordinal)
            | _ -> false)
            e

    let isExcluded (fn: FnInfo) =
        fn.IsEntryPoint
        || hooks.Contains fn.Name
        || state.Arenas.ContainsKey fn.Name
        || state.NoTailCallsFile
        || state.NoTailCalls.Contains fn.Name
        || exportSet.Contains fn.Name
        || testSet.Contains fn.Name
        || valueSet.Contains fn.Name
        || usesLocalStackPtr fn.Body

    let rec tailExprs (e: Expr) : Expr list =
        match e with
        | ELet(_, rhs, _) when alwaysRaisesExpr rhs -> []
        | ELet(v, rhs, EVar v2) when v.Id = v2.Id -> tailExprs rhs
        | ELet(r, callRhs, conBody) when not (alwaysRaisesExpr callRhs) ->
            match tryMatchTrmcHole r conBody with
            | Some _ -> tailExprs callRhs
            | None -> tailExprs conBody
        | ELet(_, _, b)
        | ESeq(_, b)
        | EDrop(_, b)
        | EUnpack(_, b)
        | EPromote(_, b) -> tailExprs b
        | EIf(_, t, f, _) -> tailExprs t @ tailExprs f
        | ETry _ -> []
        | _ -> [ e ]

    let unwrapTail = unwrapTailCallExpr

    let rec isScalarTy (t: Ty) =
        match t with
        | TPrim _ -> true
        | _ -> false

    let fns = state.Fns
    let fableAliases = HashSet<string>(state.Imports.Values)

    for fn in fns do
        fn.NeedsChain <- false
        fn.PendingChainDeps <- []

    let excluded =
        fns |> Seq.filter isExcluded |> Seq.map (fun fn -> fn.Name) |> HashSet

    let sameFileEdges = Dictionary<string, (string * Ty list * int) list>()
    let pendingExt = Dictionary<string, HashSet<string>>()

    for fn in fns do
        let pSet = HashSet<string>()
        pendingExt[fn.Name] <- pSet

        if not (excluded.Contains fn.Name) then
            let edges = List<string * Ty list * int>()

            for rawT in tailExprs fn.Body do
                match unwrapTail rawT with
                | ECallClo _
                | ECallVt _
                | ECallIface _ -> fn.NeedsChain <- true
                | ECall(g, tArgs, args, _) when p.Fns.ContainsKey g && not (excluded.Contains g) ->
                    if g = fn.Name then
                        if tArgs <> (fn.TypeParams |> List.map TGen) || args.Length <> fn.Params.Length then
                            // Polymorphic or arity-mismatched self recursion cannot loop in place.
                            fn.NeedsChain <- true
                    else
                        edges.Add(g, tArgs, args.Length)
                | ECall(extF, _, _, _) when not (p.Fns.ContainsKey extF) ->
                    let dot = extF.IndexOf '.'

                    if dot > 0 && fableAliases.Contains(extF.Substring(0, dot)) then
                        match p.Ext extF with
                        | Some ff ->
                            if ff.NeedsChain then
                                fn.NeedsChain <- true
                        | None -> pSet.Add extF |> ignore
                | _ -> ()

            sameFileEdges[fn.Name] <- List.ofSeq edges
        else
            sameFileEdges[fn.Name] <- []

    // Find all non-self strongly connected components in `sameFileEdges` (even with mismatched
    // signatures/type args) and check whether `Emit`'s `emitScc` or scalar sibling `tailTarget`
    // already fuses each SCC into O(1) stack.
    let sccs = List<FnInfo list>()

    do
        let idx = ref 0
        let indexOf = Dictionary<string, int>()
        let lowOf = Dictionary<string, int>()
        let onStack = HashSet<string>()
        let stack = Stack<string>()

        let rec strongconnect (v: string) =
            indexOf[v] <- idx.Value
            lowOf[v] <- idx.Value
            idx.Value <- idx.Value + 1
            stack.Push v
            onStack.Add v |> ignore

            for (w, _, _) in sameFileEdges[v] do
                if not (indexOf.ContainsKey w) then
                    strongconnect w
                    lowOf[v] <- min lowOf[v] lowOf[w]
                elif onStack.Contains w then
                    lowOf[v] <- min lowOf[v] indexOf[w]

            if lowOf[v] = indexOf[v] then
                let comp = List<FnInfo>()
                let mutable stop = false

                while not stop do
                    let w = stack.Pop()
                    onStack.Remove w |> ignore
                    comp.Add p.Fns[w]

                    if w = v then
                        stop <- true

                if comp.Count >= 2 then
                    sccs.Add(List.ofSeq comp)

        for fn in fns do
            if not (excluded.Contains fn.Name) && not (indexOf.ContainsKey fn.Name) then
                strongconnect fn.Name

    let mayHaveReuseToken (fn: FnInfo) =
        exists
            (function
            | ETest(_, _, ty) -> isHeapTy ty
            | _ -> false)
            fn.Body

    let fusedSccs = List<FnInfo list>()

    for scc in sccs do
        let rep = scc.Head
        let repRet = zigType rep.Ret
        let memberNames = scc |> List.map (fun fn -> fn.Name) |> Set.ofList

        let allEdgesDirect =
            scc
            |> List.forall (fun fn ->
                let expectedTArgs = fn.TypeParams |> List.map TGen

                sameFileEdges[fn.Name]
                |> List.forall (fun (g, tArgs, nArgs) ->
                    not (memberNames.Contains g)
                    || (tArgs = expectedTArgs && nArgs = p.Fns[g].Params.Length)
                )
            )

        let allScalarSameSig =
            allEdgesDirect
            && rep.Raises = RNever
            && (scc
                |> List.forall (fun fn ->
                    (fn.Ret :: (fn.Params |> List.map (fun q -> q.Ty))) |> List.forall isScalarTy
                    && (fn.Params |> List.map (fun q -> zigType q.Ty)) =
                        (rep.Params |> List.map (fun q -> zigType q.Ty))
                ))

        let fusedScc =
            allEdgesDirect
            && not allScalarSameSig
            && (scc
                |> List.forall (fun fn ->
                    not (state.Arenas.ContainsKey fn.Name)
                    && fn.RetFrom.IsNone
                    && fn.TypeParams = rep.TypeParams
                    && zigType fn.Ret = repRet
                    && fn.Raises = rep.Raises
                ))

        let fusedScalar =
            allScalarSameSig && (scc |> List.forall (fun fn -> not (mayHaveReuseToken fn)))

        if fusedScc then
            fusedSccs.Add scc
        elif not fusedScalar then
            for fn in scc do
                fn.NeedsChain <- true

    let mutable changed = true

    while changed do
        changed <- false

        for fn in fns do
            if not (excluded.Contains fn.Name) && not fn.NeedsChain then
                let hitsChain =
                    sameFileEdges[fn.Name] |> List.exists (fun (g, _, _) -> p.Fns[g].NeedsChain)

                if hitsChain then
                    fn.NeedsChain <- true
                    changed <- true

        for scc in fusedSccs do
            if scc |> List.exists (fun m -> m.NeedsChain) then
                for m in scc do
                    if not m.NeedsChain && not (excluded.Contains m.Name) then
                        m.NeedsChain <- true
                        changed <- true

    for fn in fns do
        if excluded.Contains fn.Name || fn.NeedsChain then
            pendingExt[fn.Name].Clear()

    let mutable pendingChanged = true

    while pendingChanged do
        pendingChanged <- false

        for fn in fns do
            if not (excluded.Contains fn.Name) && not fn.NeedsChain then
                let dst = pendingExt[fn.Name]

                for (g, _, _) in sameFileEdges[fn.Name] do
                    for extF in pendingExt[g] do
                        if dst.Add extF then
                            pendingChanged <- true

        for scc in fusedSccs do
            if scc |> List.forall (fun m -> not m.NeedsChain && not (excluded.Contains m.Name)) then
                for m in scc do
                    let dst = pendingExt[m.Name]

                    for other in scc do
                        if other.Name <> m.Name then
                            for extF in pendingExt[other.Name] do
                                if dst.Add extF then
                                    pendingChanged <- true

    for fn in fns do
        if not fn.NeedsChain && pendingExt[fn.Name].Count > 0 then
            fn.PendingChainDeps <- pendingExt[fn.Name] |> Seq.sort |> Seq.toList
