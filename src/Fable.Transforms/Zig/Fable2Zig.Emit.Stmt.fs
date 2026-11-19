/// Emission of statements, values, and `$tc` tail-call blocks.
module internal Fable.Transforms.Zig.EmitStmt

open System.Collections.Generic
open System.Text
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.EmitExpr

let rec tailSites (e: Expr) : Expr list =
    match e with
    | ELet(_, (ECall _ | EOnRaise(ECall _, _)), ECon _) -> [ e ]
    | ELet(_, _, b)
    | ESeq(_, b)
    | EDrop(_, b)
    | EUnpack(_, b)
    | EPromote(_, b) -> tailSites b
    | EIf(_, t, f, _) -> tailSites t @ tailSites f
    | _ -> [ e ]

let countUses (id: int) (es: Expr list) =
    let mutable n = 0

    let rec go e =
        match e with
        | EVar v when v.Id = id -> n <- n + 1
        | _ -> List.iter go (flatKids e)

    List.iter go es
    n

/// `let r = target(args) in Case(..., r, ...)` at the end of a function or SCC arm:
/// the cell is made first with a hole where `r` goes, and the call becomes the next turn of the
/// loop that fills the hole.
let trmcSiteOf (isTarget: string -> bool) (e: Expr) =
    match e with
    // (a recursive call that may raise needs no error edge of its own once it is the next
    // turn of the loop)
    | ELet(r, (ECall(f, tArgs, args, _) | EOnRaise(ECall(f, tArgs, args, _), _)), ECon(conTy, case, conArgs, tok)) when
        isTarget f && isHeapTy conTy && not conArgs.IsEmpty
        ->
        let hits =
            conArgs
            |> List.indexed
            |> List.filter (fun (_, a) ->
                match a with
                | EVar v -> v.Id = r.Id
                | _ -> false
            )

        match hits with
        | [ (i, _) ] when countUses r.Id conArgs = 1 -> Some(f, tArgs, args, conTy, case, conArgs, tok, i)
        | _ -> None
    | _ -> None

let trmcSite (self: string) (e: Expr) =
    trmcSiteOf ((=) self) e
    |> Option.map (fun (_, _, args, conTy, case, conArgs, tok, i) -> args, conTy, case, conArgs, tok, i)

/// After a statement that has no value: leave through `dest` if that is where control goes.
let finishUnit (em: Em) (ind: string) (dest: Dest) =
    match dest with
    | DTcRet -> line em ind "return .{};"
    | DReturn when em.Loop.IsSome || em.Scc.IsSome -> line em ind "return;"
    | DBreak l -> line em ind $"break :%s{l} {{}};"
    | DReturn
    | DDiscard -> ()

/// A self tail call: give the parameters their new values and go round the loop again.
let emitTailJump (em: Em) (ind: string) (args: Expr list) =
    let loop = em.Loop.Value

    let changes =
        List.zip loop.Params args
        |> List.filter (fun (p, a) ->
            match a with
            | EVar v -> v.Id <> p.Id
            | _ -> true
        )

    match changes with
    | [ (p, a) ] -> line em ind $"%s{vname em p} = %s{ex em a};"
    | _ ->
        // every new argument is evaluated before any parameter is overwritten
        let temps =
            changes |> List.map (fun (p, a) -> p, freshName em ("next_" + p.Base), a)

        for (_, t, a) in temps do
            line em ind $"const %s{t} = %s{ex em a};"

        for (p, t, _) in temps do
            line em ind $"%s{vname em p} = %s{t};"

    line em ind "continue :tail;"

/// A dead value whose case is known: the fields that are still needed move out of it, the
/// others are dropped, and a cell is freed or kept to be built in again.
let emitUnpack (em: Em) (ind: string) (u: Unpack) =
    let L = line em ind
    let x = vname em u.Scrut

    let moves =
        u.Moves
        |> List.map (fun (f, v) -> $"%s{f} -> %s{vname em v}")
        |> String.concat ", "

    if u.Heap then
        // (a union's cell is its case's payload; a record by reference is a cell itself)
        let cell =
            if u.Case = "" then
                x
            else
                $"%s{x}.%s{fieldIdent u.Case}"

        let fate =
            if u.Token.IsSome then
                "the cell is kept to be built in again"
            else
                "the cell is freed"

        L $"// `%s{x}` is dead: [%s{moves}] move out and %s{fate}, if it is not shared"

        match u.Token with
        | Some tk ->
            let tn = vname em tk
            let dead = freshName em "dead"
            L $"var %s{tn}: %s{zigType tk.Ty} = null;"
            L $"defer if (%s{tn}) |%s{dead}| fable_rt.free(%s{dead});"
        | None -> ()

        let mayBeCyclic =
            match u.Scrut.Ty with
            | TEnt(ent, _) -> (cyclicDecl ent).IsSome
            | _ -> false

        L $"if (fable_rt.isUnique(%s{cell})) {{"

        // (the collector is told first: what the cell holds stops being held by its structure,
        // whether it is given up or moved out)
        if mayBeCyclic then
            L $"    fable_rt.forget(%s{cell});"

        for (f, _) in u.Drops do
            L("    " + dropCode $"%s{cell}.%s{fieldIdent f}")

        for (_, v) in u.Moves do
            if isManaged v.Ty && mayHoldCyclic v.Ty then
                L $"    fable_rt.touch(%s{vname em v});"

        match u.Token with
        | Some tk -> L $"    %s{vname em tk} = %s{cell};"
        | None -> L $"    fable_rt.free(%s{cell});"

        L "} else {"

        for (_, v) in u.Moves do
            if isManaged v.Ty then
                L $"    _ = %s{dupCode (vname em v)};"

        // (a shared cell may lose its last reference here, another thread having dropped its
        // own since `isUnique` was asked: then it is freed, with the fields just dup'ed)
        L $"    fable_rt.drop(%s{cell});"
        L "}"
    elif not u.Drops.IsEmpty then
        L $"// `%s{x}` is dead: [%s{moves}] move out, the rest is dropped"

        for (f, _) in u.Drops do
            L(dropCode (projAccess u.Scrut.Ty u.Case f x))

/// Does this statement always raise (end in a `raise` on every path it can take)?
let rec alwaysRaises (e: Expr) : bool =
    match e with
    | ERaise _ -> true
    | ELet(_, _, b)
    | ESeq(_, b) -> alwaysRaises b
    | EIf(_, t, f, _) -> alwaysRaises t && alwaysRaises f
    | _ -> false

let rec peelDropSpine (targetVarId: int option) (e: Expr) : Var list option =
    match e with
    | EDrop(d, rest) -> peelDropSpine targetVarId rest |> Option.map (fun ds -> d :: ds)
    | EVar v when targetVarId = Some v.Id -> Some []
    | EUnit when targetVarId.IsNone -> Some []
    | _ -> None

let peelTailCall (e: Expr) : (Expr * Var list) option =
    match e with
    | ELet(tmp, inner, body) -> peelDropSpine (Some tmp.Id) body |> Option.map (fun ds -> inner, ds)
    | ESeq(inner, body) when isVoid (typeOf inner) -> peelDropSpine None body |> Option.map (fun ds -> inner, ds)
    | _ -> Some(e, [])

let rec unwrapTailCallInfo (e: Expr) : Expr * int list option * bool =
    match e with
    | EDup(x, _) ->
        let inner, assumed, _ = unwrapTailCallInfo x
        inner, assumed, true
    | EOnRaise(x, _) -> unwrapTailCallInfo x
    | EAssumedRet(js, x) ->
        let inner, prev, hadDup = unwrapTailCallInfo x

        inner,
        (if prev.IsSome then
             prev
         else
             Some js),
        hadDup
    | _ -> e, None, false

let emitArgAsTcVal (em: Em) (x: Expr) : string =
    match x with
    | EKnown(target, kTys, caps, cloTy)
    | EUse(_, EKnown(target, kTys, caps, cloTy)) ->
        let kn = ensureKnownDecl em target kTys caps cloTy
        kn.NeedsToFunc <- true
        $"(%s{ex em x}).toFunc()"
    | EKnownIface(ifaceTy, src, slots, isOpt)
    | EUse(_, EKnownIface(ifaceTy, src, slots, isOpt)) ->
        let ki = ensureKnownIfaceDecl em ifaceTy src slots isOpt
        ki.NeedsToFunc <- true
        $"(%s{ex em x}).toFunc()"
    | _ -> ex em x

let isSameFileTcTarget (em: Em) (inTrmc: bool) (g: string) (typeArgs: Ty list) (argCount: int) =
    match em.Fns.TryGetValue g with
    | true, gFn ->
        not (em.NoTcFns.Contains g)
        && fnHasTcBody gFn
        && argCount = gFn.Params.Length
        && (inTrmc
            || (not (em.Loop.IsSome && g = em.Loop.Value.Self)
                && not (
                    em.Scc.IsSome
                    && em.Scc.Value.TagOf.ContainsKey g
                    && typeArgs = (em.Self.TypeParams |> List.map TGen)
                )))
    | _ -> false

let isExtTcAlias (aliases: HashSet<string>) (fns: Dictionary<string, FnInfo>) (f: string) =
    if fns.ContainsKey f then
        false
    else
        let dot = f.IndexOf '.'
        dot > 0 && aliases.Contains(f.Substring(0, dot))

type TrmcTailInfo =
    {
        RetVar: Var
        InnerCall: Expr
        CallDrops: Var list
        MidDrops: Var list
        PostDrops: Var list
        ConTy: Ty
        Case: string
        ConArgs: Expr list
        Tok: Var option
        HoleIdx: int
        IsHeapUnion: bool
        NonHoleConFv: Set<int>
    }

let rec hasMutableOrCallExpr (e: Expr) =
    match e with
    | ECall _
    | ECallClo _
    | ECallVt _
    | ECallIface _
    | ERt _ -> true
    | EVar v -> v.FMutable
    | _ -> false

let peelTailTrmc (em: Em) (e: Expr) : TrmcTailInfo option =
    if em.Self.RetFrom.IsSome then
        None
    else
        match e with
        | ELet(r, callPart, afterCall) ->
            match peelTailCall callPart with
            | None -> None
            | Some(innerCall, callDrops) ->
                let _, assumedFrom, hadDup = unwrapTailCallInfo innerCall

                if assumedFrom.IsSome && not hadDup then
                    None
                else
                    let rec peelMidDrops (x: Expr) =
                        match x with
                        | EDrop(d, rest) ->
                            let ds, core = peelMidDrops rest
                            d :: ds, core
                        | _ -> [], x

                    let midDrops, conCore = peelMidDrops afterCall

                    let conOpt =
                        match conCore with
                        | ECon(conTy, case, conArgs, tok) -> Some(conTy, case, conArgs, tok, [])
                        | ELet(conTmp, ECon(conTy, case, conArgs, tok), tailBody) ->
                            peelDropSpine (Some conTmp.Id) tailBody
                            |> Option.map (fun postDrops -> conTy, case, conArgs, tok, postDrops)
                        | _ -> None

                    match conOpt with
                    | Some(TEnt(ent, _) as conTy, case, conArgs, tok, postDrops) when
                        (ent.Kind = KHeapUnion || ent.Kind = KValueUnion) && not conArgs.IsEmpty
                        ->
                        let allDrops = callDrops @ midDrops @ postDrops

                        if allDrops |> List.exists (fun d -> d.Id = r.Id) then
                            None
                        else
                            let hits =
                                conArgs
                                |> List.indexed
                                |> List.filter (fun (_, a) ->
                                    match a with
                                    | EVar v -> v.Id = r.Id
                                    | _ -> false
                                )

                            match hits with
                            | [ (holeIdx, _) ] when countUses r.Id conArgs = 1 ->
                                let nonHoleSafe =
                                    conArgs
                                    |> List.indexed
                                    |> List.forall (fun (j, a) ->
                                        if j = holeIdx then
                                            true
                                        elif not (isFlat a) then
                                            false
                                        elif j > holeIdx then
                                            Set.isEmpty (Set.intersect (fv a) em.Mutated)
                                            && not (touchesMutable a)
                                            && not (exists hasMutableOrCallExpr a)
                                        else
                                            true
                                    )

                                if nonHoleSafe then
                                    let nonHoleConFv =
                                        conArgs
                                        |> List.indexed
                                        |> List.choose (fun (j, a) ->
                                            if j <> holeIdx then
                                                Some(fv a)
                                            else
                                                None
                                        )
                                        |> Set.unionMany

                                    Some
                                        {
                                            RetVar = r
                                            InnerCall = innerCall
                                            CallDrops = callDrops
                                            MidDrops = midDrops
                                            PostDrops = postDrops
                                            ConTy = conTy
                                            Case = case
                                            ConArgs = conArgs
                                            Tok = tok
                                            HoleIdx = holeIdx
                                            IsHeapUnion = ent.Kind = KHeapUnion
                                            NonHoleConFv = nonHoleConFv
                                        }
                                else
                                    None
                            | _ -> None
                    | _ -> None
        | _ -> None

let classifyTailTc (em: Em) (e: Expr) =
    match peelTailTrmc em e with
    | Some trmc ->
        let allDrops = trmc.CallDrops @ trmc.MidDrops @ trmc.PostDrops
        Some(trmc.InnerCall, allDrops, Some trmc)
    | None ->
        match peelTailCall e with
        | Some(inner, drops) -> Some(inner, drops, None)
        | None -> None

let hasKParamInCall (kParams: Set<int>) (inner: Expr) : bool =
    if kParams.IsEmpty then
        false
    else
        let call, _, _ = unwrapTailCallInfo inner

        match call with
        | ECallClo(EVar v, _, _) when kParams.Contains v.Id -> true
        | ECall(_, _, xs, _)
        | ECallClo(_, xs, _)
        | ECallVt(_, _, xs, _) -> xs |> List.exists (hasKnownOrKArg kParams)
        | ECallIface(r, _, xs, _) -> (r :: xs) |> List.exists (hasKnownOrKArg kParams)
        | _ -> false

let isTcBoundaryCall (em: Em) (inTrmc: bool) (inner: Expr) : bool =
    if hasKParamInCall em.KParams inner then
        false
    else
        let call, _, _ = unwrapTailCallInfo inner

        match call with
        | ECallClo(fExpr, _, _) ->
            match fExpr with
            | EVar v -> not (em.KParams.Contains v.Id)
            | _ -> true
        | ECallVt _
        | ECallIface _ -> true
        | ECall(g, typeArgs, xs, _) ->
            isSameFileTcTarget em inTrmc g typeArgs xs.Length
            || isExtTcAlias em.FableAliases em.Fns g
        | _ -> false

let isTcBoundaryExpr (em: Em) (e: Expr) : bool =
    if
        em.NoTailCalls.Contains em.Self.Name
        || (em.IsTc && not em.KParams.IsEmpty)
        || em.TryLabels.Count > 0
        || (not em.IsTc && em.Self.RetFrom.IsSome)
    then
        false
    else
        match classifyTailTc em e with
        | None -> false
        | Some(inner, _, trmcOpt) -> isTcBoundaryCall em trmcOpt.IsSome inner

let floatTrmcCall (em: Em) (r: Var) (callExpr: Expr) (afterCall: Expr) : Expr option =
    let afterFv = fv afterCall

    let rec step (x: Expr) : Expr option =
        let cand = ELet(r, x, afterCall)

        match peelTailTrmc em cand with
        | Some t when isTcBoundaryCall em true t.InnerCall -> Some cand
        | _ ->
            match x with
            | ELet(v, rhs, body) when v.Id <> r.Id && not (afterFv.Contains v.Id) ->
                step body |> Option.map (fun res -> ELet(v, rhs, res))
            | ESeq(a, body) -> step body |> Option.map (fun res -> ESeq(a, res))
            | EDrop(d, body) when not (afterFv.Contains d.Id) -> step body |> Option.map (fun res -> EDrop(d, res))
            | EUnpack(u, body) when u.Token.IsNone -> step body |> Option.map (fun res -> EUnpack(u, res))
            | EPromote(v, body) -> step body |> Option.map (fun res -> EPromote(v, res))
            | _ -> None

    match peelTailTrmc em (ELet(r, callExpr, afterCall)) with
    | Some t when isTcBoundaryCall em true t.InnerCall -> None
    | _ -> step callExpr

let (|FloatedTrmc|_|) (em: Em) (dest: Dest) (e: Expr) : Expr option =
    if
        (dest = DTcRet || dest = DReturn)
        && not (dest = DReturn && em.Self.RetFrom.IsSome)
        && not (em.NoTailCalls.Contains em.Self.Name)
        && not (em.IsTc && not em.KParams.IsEmpty)
        && em.TryLabels.Count = 0
        && not (em.Loop.IsSome && em.Loop.Value.Trmc)
        && not (em.Scc.IsSome && em.Scc.Value.Trmc)
    then
        match e with
        | ELet(r, callPart, afterCall) -> floatTrmcCall em r callPart afterCall
        | _ -> None
    else
        None

/// Emit a `$tc` tail jump (inside `DTcRet` `$tcbody`) or `$tc` boundary (at normal `DReturn`)
/// when `e` ends in an unknown `ECallClo`, `ECallVt`, `ECallIface`, same-file `$tc`, or cross-file `$tc`
/// (directly or wrapped inside a TRMC `KHeapUnion` / `KValueUnion` constructor hole).
let rec tryEmitTailTc (em: Em) (ind: string) (e: Expr) (dest: Dest) : bool =
    if
        (dest <> DTcRet && dest <> DReturn)
        || (dest = DReturn && em.Self.RetFrom.IsSome)
        || em.NoTailCalls.Contains em.Self.Name
        || (em.IsTc && not em.KParams.IsEmpty)
        || em.TryLabels.Count > 0
        || (em.Loop.IsSome && em.Loop.Value.Trmc)
        || (em.Scc.IsSome && em.Scc.Value.Trmc)
    then
        false
    else
        match classifyTailTc em e with
        | None -> false
        | Some(inner, _, _) when hasKParamInCall em.KParams inner -> false
        | Some(inner, drops, trmcOpt) ->
            let L = line em ind
            let retZig = zigType em.Self.Ret
            let voidRet = isVoid em.Self.Ret

            let nonHoleConFv =
                trmcOpt |> Option.map (fun t -> t.NonHoleConFv) |> Option.defaultValue Set.empty

            let leaveOnErr () =
                if dest = DTcRet then
                    "return error.Raised;"
                else
                    match em.Self.Raises with
                    | RNever -> "unreachable;"
                    | RAlways -> leaveText em
                    | RDepends _ ->
                        $"if (comptime fable_rt.isRaised(%s{retType em.Self})) {{ %s{leaveText em} }} else {{ unreachable; }}"

            let emitTrampolineRaised (tInd: string) (tresVar: string) =
                let RL = line em tInd

                match em.Self.Raises with
                | RNever -> RL "unreachable;"
                | RAlways ->
                    if not voidRet then
                        RL $"if (comptime fable_rt.canPlugRet(%s{retZig})) fable_rt.drop(%s{tresVar});"

                    RL(leaveText em)
                | RDepends _ ->
                    RL $"if (comptime fable_rt.isRaised(%s{retType em.Self})) {{"

                    if not voidRet then
                        RL $"    if (comptime fable_rt.canPlugRet(%s{retZig})) fable_rt.drop(%s{tresVar});"

                    RL $"    %s{leaveText em}"
                    RL "} else {"
                    RL "    unreachable;"
                    RL "}"

            let trmcPlugCond, emitTrmcTemps =
                match trmcOpt with
                | None -> "", (fun () -> None)
                | Some t ->
                    let conZig = zigType t.ConTy
                    let fields = caseFields t.ConTy t.Case
                    let _, holeFieldTy = fields[t.HoleIdx]
                    let holeFieldZig = zigType holeFieldTy

                    let cond =
                        $" and fable_rt.canPlugRet(%s{holeFieldZig}) and fable_rt.canPlugRet(%s{conZig})"

                    let emitTemps () =
                        let tmpList =
                            List.zip fields t.ConArgs
                            |> List.mapi (fun i ((f, fTy), a) ->
                                if i = t.HoleIdx then
                                    f, fTy, None
                                else
                                    let tmp = freshName em ("trmc_" + cleanIdent f)
                                    L $"const %s{tmp}: %s{zigType fTy} = %s{ex em a};"
                                    f, fTy, Some tmp
                            )

                        Some(t, conZig, fields, tmpList)

                    cond, emitTemps

            let fieldInits (holeIdx: int) (conTemps: (string * Ty * string option) list) (holeVal: string) =
                conTemps
                |> List.mapi (fun i (f, _, tmpOpt) ->
                    let v =
                        if i = holeIdx then
                            holeVal
                        else
                            Option.get tmpOpt

                    $".%s{fieldIdent f} = %s{v}"
                )
                |> String.concat ", "

            let emitTcJump
                (trmcStateOpt: (TrmcTailInfo * string * (string * Ty) list * (string * Ty * string option) list) option)
                (jInd: string)
                (tcfnTarget: string)
                (takeAddr: bool)
                (paramTysStr: string)
                (storeValsStr: string)
                (selfPtr: string)
                (selfOwned: bool)
                =
                let JL = line em jInd

                let tcfnPtr =
                    if takeAddr then
                        "&" + tcfnTarget
                    else
                        tcfnTarget

                match trmcStateOpt with
                | None ->
                    if dest = DTcRet then
                        if paramTysStr <> "" then
                            JL $"fable_rt.tailStore(&.{{ %s{paramTysStr} }}, ctx, .{{ %s{storeValsStr} }});"

                        JL $"ctx.self = %s{selfPtr};"
                        JL "ctx.self_owned = true;"
                        JL $"return .{{ .func = %s{tcfnPtr}, .ret = ret }};"
                    else
                        let tctxVar = freshName em "tctx"
                        let tresVar = freshName em "tcres"

                        let resDeclTy =
                            if voidRet then
                                "u8"
                            else
                                retZig

                        JL $"var %s{tctxVar}: fable_rt.TailCtx = .{{}};"
                        JL $"var %s{tresVar}: %s{resDeclTy} = undefined;"

                        if paramTysStr <> "" then
                            JL $"fable_rt.tailStore(&.{{ %s{paramTysStr} }}, &%s{tctxVar}, .{{ %s{storeValsStr} }});"

                        JL $"%s{tctxVar}.self = %s{selfPtr};"

                        let ownedLit =
                            if selfOwned then
                                "true"
                            else
                                "false"

                        JL $"%s{tctxVar}.self_owned = %s{ownedLit};"
                        JL $"if (%s{tcfnTarget}(&%s{tctxVar}, @ptrCast(&%s{tresVar})) == .raised) {{"
                        emitTrampolineRaised (jInd + "    ") tresVar
                        JL "}"

                        if voidRet then
                            JL "return;"
                        else
                            JL $"return %s{tresVar};"
                | Some(t, conZig, fields, conTemps) ->
                    let caseIdent = fieldIdent t.Case
                    let holeFieldIdent = fieldIdent (fst fields[t.HoleIdx])
                    let initStr = fieldInits t.HoleIdx conTemps "undefined"

                    if t.IsHeapUnion then
                        let cellVar = freshName em "trmc_cell"

                        match t.Tok with
                        | Some tk ->
                            JL
                                $"const %s{cellVar} = fable_rt.cellReuse(%s{conZig}, .%s{caseIdent}, &%s{vname em tk}, .{{ %s{initStr} }});"
                        | None ->
                            JL $"const %s{cellVar} = fable_rt.cell(%s{conZig}, .%s{caseIdent}, .{{ %s{initStr} }});"

                        let nextRet = $"@ptrCast(&%s{cellVar}.%s{holeFieldIdent})"

                        if dest = DTcRet then
                            JL $"@as(*%s{conZig}, @ptrCast(@alignCast(ret))).* = .{{ .%s{caseIdent} = %s{cellVar} }};"

                            if paramTysStr <> "" then
                                JL $"fable_rt.tailStore(&.{{ %s{paramTysStr} }}, ctx, .{{ %s{storeValsStr} }});"

                            JL $"ctx.self = %s{selfPtr};"
                            JL "ctx.self_owned = true;"
                            JL $"return .{{ .func = %s{tcfnPtr}, .ret = %s{nextRet} }};"
                        else
                            let tctxVar = freshName em "tctx"
                            let tresVar = freshName em "tcres"
                            JL $"var %s{tctxVar}: fable_rt.TailCtx = .{{}};"
                            JL $"const %s{tresVar}: %s{conZig} = .{{ .%s{caseIdent} = %s{cellVar} }};"

                            if paramTysStr <> "" then
                                JL
                                    $"fable_rt.tailStore(&.{{ %s{paramTysStr} }}, &%s{tctxVar}, .{{ %s{storeValsStr} }});"

                            JL $"%s{tctxVar}.self = %s{selfPtr};"

                            let ownedLit =
                                if selfOwned then
                                    "true"
                                else
                                    "false"

                            JL $"%s{tctxVar}.self_owned = %s{ownedLit};"
                            JL $"if (%s{tcfnTarget}(&%s{tctxVar}, %s{nextRet}) == .raised) {{"
                            emitTrampolineRaised (jInd + "    ") tresVar
                            JL "}"
                            JL $"return %s{tresVar};"
                    else if dest = DTcRet then
                        let retPtrVar = freshName em "ret_ptr"
                        JL $"const %s{retPtrVar}: *%s{conZig} = @ptrCast(@alignCast(ret));"
                        JL $"%s{retPtrVar}.* = .{{ .%s{caseIdent} = .{{ %s{initStr} }} }};"
                        let nextRet = $"@ptrCast(&%s{retPtrVar}.%s{caseIdent}.%s{holeFieldIdent})"

                        if paramTysStr <> "" then
                            JL $"fable_rt.tailStore(&.{{ %s{paramTysStr} }}, ctx, .{{ %s{storeValsStr} }});"

                        JL $"ctx.self = %s{selfPtr};"
                        JL "ctx.self_owned = true;"
                        JL $"return .{{ .func = %s{tcfnPtr}, .ret = %s{nextRet} }};"
                    else
                        let tctxVar = freshName em "tctx"
                        let tresVar = freshName em "tcres"
                        JL $"var %s{tctxVar}: fable_rt.TailCtx = .{{}};"
                        JL $"var %s{tresVar}: %s{conZig} = .{{ .%s{caseIdent} = .{{ %s{initStr} }} }};"
                        let nextRet = $"@ptrCast(&%s{tresVar}.%s{caseIdent}.%s{holeFieldIdent})"

                        if paramTysStr <> "" then
                            JL $"fable_rt.tailStore(&.{{ %s{paramTysStr} }}, &%s{tctxVar}, .{{ %s{storeValsStr} }});"

                        JL $"%s{tctxVar}.self = %s{selfPtr};"

                        let ownedLit =
                            if selfOwned then
                                "true"
                            else
                                "false"

                        JL $"%s{tctxVar}.self_owned = %s{ownedLit};"
                        JL $"if (%s{tcfnTarget}(&%s{tctxVar}, %s{nextRet}) == .raised) {{"
                        emitTrampolineRaised (jInd + "    ") tresVar
                        JL "}"
                        JL $"return %s{tresVar};"

            let emitFallbackCall
                (trmcStateOpt: (TrmcTailInfo * string * (string * Ty) list * (string * Ty * string option) list) option)
                (fInd: string)
                (rawCall: string)
                (alwaysErrorUnion: bool)
                (dupResult: bool)
                =
                let FL = line em fInd

                match trmcStateOpt with
                | None ->
                    if
                        alwaysErrorUnion
                        && drops.IsEmpty
                        && not dupResult
                        && dest = DReturn
                        && canPlainTry em
                        && em.Self.Raises = RAlways
                    then
                        if voidRet then
                            FL $"_ = try %s{rawCall};"
                            FL "return;"
                        else
                            FL $"return try %s{rawCall};"
                    else
                        let rawVar = freshName em "tc_raw"
                        let rVar = freshName em "tc_r"

                        let dropErr =
                            drops |> List.map (fun d -> dropCode (vname em d) + " ") |> String.concat ""

                        FL $"const %s{rawVar} = %s{rawCall};"

                        FL
                            $"const %s{rVar} = if (comptime fable_rt.isRaised(@TypeOf(%s{rawVar}))) %s{rawVar} catch {{ %s{dropErr}%s{leaveOnErr ()} }} else %s{rawVar};"

                        let resVar =
                            if dupResult && not voidRet then
                                let rv = freshName em "tc_res"
                                FL $"const %s{rv} = %s{dupCode rVar};"
                                rv
                            else
                                rVar

                        for d in drops do
                            FL(dropCode (vname em d))

                        if dest = DTcRet then
                            if voidRet then
                                FL $"_ = %s{resVar};"
                            else
                                FL $"@as(*%s{retZig}, @ptrCast(@alignCast(ret))).* = %s{resVar};"

                            FL "return .{};"
                        elif voidRet then
                            FL $"_ = %s{resVar};"
                            FL "return;"
                        else
                            FL $"return %s{resVar};"
                | Some(t, conZig, _, conTemps) ->
                    let conTmpDrops =
                        conTemps
                        |> List.choose (fun (_, fTy, tmpOpt) ->
                            match tmpOpt with
                            | Some tmp when isManaged fTy -> Some(dropCode tmp)
                            | _ -> None
                        )

                    let allErrDrops =
                        conTmpDrops @ (drops |> List.map (fun d -> dropCode (vname em d)))
                        |> String.concat " "

                    let errPrefix =
                        if allErrDrops = "" then
                            ""
                        else
                            allErrDrops + " "

                    let rawVar = freshName em "tc_raw"
                    let rVar = freshName em "tc_r"
                    FL $"const %s{rawVar} = %s{rawCall};"

                    FL
                        $"const %s{rVar} = if (comptime fable_rt.isRaised(@TypeOf(%s{rawVar}))) %s{rawVar} catch {{ %s{errPrefix}%s{leaveOnErr ()} }} else %s{rawVar};"

                    let holeVal =
                        if dupResult then
                            let hv = freshName em "tc_hole"
                            let dupR = dupCode rVar
                            FL $"const %s{hv} = %s{dupR};"
                            hv
                        else
                            rVar

                    let caseIdent = fieldIdent t.Case
                    let builtVar = freshName em "tc_built"
                    let initStr = fieldInits t.HoleIdx conTemps holeVal

                    if t.IsHeapUnion then
                        let cellVar = freshName em "tc_cell"

                        match t.Tok with
                        | Some tk ->
                            FL
                                $"const %s{cellVar} = fable_rt.cellReuse(%s{conZig}, .%s{caseIdent}, &%s{vname em tk}, .{{ %s{initStr} }});"
                        | None ->
                            FL $"const %s{cellVar} = fable_rt.cell(%s{conZig}, .%s{caseIdent}, .{{ %s{initStr} }});"

                        FL $"const %s{builtVar}: %s{conZig} = .{{ .%s{caseIdent} = %s{cellVar} }};"
                    else
                        FL $"const %s{builtVar}: %s{conZig} = .{{ .%s{caseIdent} = .{{ %s{initStr} }} }};"

                    for d in drops do
                        FL(dropCode (vname em d))

                    if dest = DTcRet then
                        FL $"@as(*%s{conZig}, @ptrCast(@alignCast(ret))).* = %s{builtVar};"
                        FL "return .{};"
                    else
                        FL $"return %s{builtVar};"

            let recvPlan (recvExpr: Expr) (xs: Expr list) =
                let moveId =
                    match recvExpr with
                    | EVar kv when
                        drops |> List.exists (fun d -> d.Id = kv.Id)
                        && not (nonHoleConFv.Contains kv.Id)
                        && not (xs |> List.exists (fun x -> Set.contains kv.Id (fv x)))
                        ->
                        Some kv.Id
                    | EGet(EVar kv, PSome, _) when
                        drops |> List.exists (fun d -> d.Id = kv.Id)
                        && not (nonHoleConFv.Contains kv.Id)
                        && not (xs |> List.exists (fun x -> Set.contains kv.Id (fv x)))
                        ->
                        Some kv.Id
                    | _ -> None

                let rem =
                    match moveId with
                    | Some id -> drops |> List.filter (fun d -> d.Id <> id)
                    | None -> drops

                let canLend =
                    dest = DReturn
                    && moveId.IsNone
                    && rem.IsEmpty
                    && (
                        match recvExpr with
                        | EVar _ -> true
                        | EGet(EVar _, (PField _ | PSome | PItem _ | PCase _), _) -> true
                        | _ -> false
                    )

                moveId, rem, canLend

            let callExpr, assumedFrom, hadDup = unwrapTailCallInfo inner
            let inTrmc = trmcOpt.IsSome

            match callExpr with
            | ECallClo(fExpr, xs, _) ->
                let trmcState = emitTrmcTemps ()

                let isCurried2 =
                    match typeOf fExpr, xs with
                    | TFn([ _ ], TFn([ _ ], _)), [ _; _ ] -> true
                    | _ -> false

                let argTys =
                    match isCurried2, typeOf fExpr with
                    | true, TFn([ tyA ], TFn([ tyB ], _)) -> [ tyA; tyB ]
                    | _ -> xs |> List.map typeOf

                let argTysStr = argTys |> List.map zigType |> String.concat ", "
                let moveSelfId, remDrops, canLendSelf = recvPlan fExpr xs

                let fVar = freshName em "tc_f"
                L $"const %s{fVar}: %s{zigType (typeOf fExpr)} = %s{ex em fExpr};"

                let argVars =
                    List.zip xs argTys
                    |> List.mapi (fun i (x, ty) ->
                        let av = freshName em $"tc_a%d{i}"
                        L $"const %s{av}: %s{zigType ty} = %s{emitArgAsTcVal em x};"
                        av
                    )

                let cloRetZig = zigType (typeOf callExpr)

                let fallbackCall =
                    if isCurried2 then
                        $"fable_rt.apply2(%s{cloRetZig}, %s{fVar}, %s{argVars[0]}, %s{argVars[1]})"
                    else
                        let callArgs = $"%s{fVar}.env" :: argVars |> String.concat ", "
                        $"%s{fVar}.code(%s{callArgs})"

                let tcodeField =
                    if isCurried2 then
                        $"%s{fVar}.tcode2"
                    else
                        $"%s{fVar}.tcode"

                let tcFnVar = freshName em "tcfn"
                let fitsExpr = $"fable_rt.fitsTailArgs(&.{{ %s{argTysStr} }})%s{trmcPlugCond}"
                let storeVals = argVars |> String.concat ", "
                L $"if (comptime (%s{fitsExpr})) {{"
                L $"    if (%s{tcodeField}) |%s{tcFnVar}| {{"

                let selfPtr, selfOwned =
                    match moveSelfId with
                    | Some _ -> $"@ptrCast(%s{fVar}.env)", true
                    | None when canLendSelf -> $"@ptrCast(%s{fVar}.env)", false
                    | None ->
                        let fOwn = freshName em "tc_fown"
                        L $"        const %s{fOwn} = fable_rt.dup(%s{fVar});"
                        $"@ptrCast(%s{fOwn}.env)", true

                for d in remDrops do
                    L("        " + dropCode (vname em d))

                emitTcJump trmcState (ind + "        ") tcFnVar false argTysStr storeVals selfPtr selfOwned
                L "    } else {"
                emitFallbackCall trmcState (ind + "        ") fallbackCall true hadDup
                L "    }"
                L "} else {"
                emitFallbackCall trmcState (ind + "    ") fallbackCall true hadDup
                L "}"
                true

            | ECallVt(fExpr, sExpr, xs, _) ->
                let trmcState = emitTrmcTemps ()
                let argTys = xs |> List.map typeOf
                let argTysStr = argTys |> List.map zigType |> String.concat ", "
                let moveSelfId, remDrops, canLendSelf = recvPlan sExpr xs

                let fVar = freshName em "tc_f"
                L $"const %s{fVar}: %s{zigType (typeOf fExpr)} = %s{ex em fExpr};"
                let sVar = freshName em "tc_s"
                L $"const %s{sVar}: %s{zigType (typeOf sExpr)} = %s{ex em sExpr};"

                let argVars =
                    List.zip xs argTys
                    |> List.mapi (fun i (x, ty) ->
                        let av = freshName em $"tc_a%d{i}"
                        L $"const %s{av}: %s{zigType ty} = %s{emitArgAsTcVal em x};"
                        av
                    )

                let fallbackArgs = $"%s{fVar}.env" :: sVar :: argVars |> String.concat ", "
                let fallbackCall = $"%s{fVar}.code(%s{fallbackArgs})"
                let tcFnVar = freshName em "tcfn"
                let fitsExpr = $"fable_rt.fitsTailArgs(&.{{ %s{argTysStr} }})%s{trmcPlugCond}"
                let storeVals = argVars |> String.concat ", "

                L $"if (comptime (%s{fitsExpr})) {{"
                L $"    if (%s{fVar}.tcode) |%s{tcFnVar}| {{"

                let selfPtr, selfOwned =
                    match moveSelfId with
                    | Some _ -> $"@ptrCast(%s{sVar})", true
                    | None when canLendSelf -> $"@ptrCast(%s{sVar})", false
                    | None ->
                        let sOwn = freshName em "tc_sown"
                        L $"        const %s{sOwn} = fable_rt.dup(%s{sVar});"
                        $"@ptrCast(%s{sOwn})", true

                for d in remDrops do
                    L("        " + dropCode (vname em d))

                emitTcJump trmcState (ind + "        ") tcFnVar false argTysStr storeVals selfPtr selfOwned
                L "    } else {"
                emitFallbackCall trmcState (ind + "        ") fallbackCall true hadDup
                L "    }"
                L "} else {"
                emitFallbackCall trmcState (ind + "    ") fallbackCall true hadDup
                L "}"
                true

            | ECallIface(rExpr, slot, xs, _) ->
                let trmcState = emitTrmcTemps ()
                let argTys = xs |> List.map typeOf
                let argTysStr = argTys |> List.map zigType |> String.concat ", "
                let moveSelfId, remDrops, canLendSelf = recvPlan rExpr xs

                let rVar = freshName em "tc_r"
                L $"const %s{rVar}: %s{zigType (typeOf rExpr)} = %s{ex em rExpr};"

                let argVars =
                    List.zip xs argTys
                    |> List.mapi (fun i (x, ty) ->
                        let av = freshName em $"tc_a%d{i}"
                        L $"const %s{av}: %s{zigType ty} = %s{emitArgAsTcVal em x};"
                        av
                    )

                let fallbackArgs = $"%s{rVar}.data" :: argVars |> String.concat ", "
                let fallbackCall = $"%s{rVar}.vt.%s{fieldIdent slot}(%s{fallbackArgs})"
                let tcFnVar = freshName em "tcfn"
                let fitsExpr = $"fable_rt.fitsTailArgs(&.{{ %s{argTysStr} }})%s{trmcPlugCond}"
                let storeVals = argVars |> String.concat ", "

                L $"if (comptime (%s{fitsExpr})) {{"
                L $"    if (%s{rVar}.vt.@\"%s{cleanIdent slot}$tc\") |%s{tcFnVar}| {{"

                let selfPtr, selfOwned =
                    match moveSelfId with
                    | Some _ -> $"%s{rVar}.data", true
                    | None when canLendSelf -> $"%s{rVar}.data", false
                    | None ->
                        let rOwn = freshName em "tc_rown"
                        L $"        const %s{rOwn} = fable_rt.dup(%s{rVar});"
                        $"%s{rOwn}.data", true

                for d in remDrops do
                    L("        " + dropCode (vname em d))

                emitTcJump trmcState (ind + "        ") tcFnVar false argTysStr storeVals selfPtr selfOwned
                L "    } else {"
                emitFallbackCall trmcState (ind + "        ") fallbackCall true hadDup
                L "    }"
                L "} else {"
                emitFallbackCall trmcState (ind + "    ") fallbackCall true hadDup
                L "}"
                true

            | ECall(g, typeArgs, xs, _) when isSameFileTcTarget em inTrmc g typeArgs xs.Length ->
                let trmcState = emitTrmcTemps ()
                let gFn = em.Fns[g]

                let inst =
                    if gFn.TypeParams.Length = typeArgs.Length then
                        Map.ofList (List.zip gFn.TypeParams typeArgs)
                    else
                        Map.empty

                let gParamTys = gFn.Params |> List.map (fun p -> substTy inst p.Ty |> zigType)

                let paramTysStr = String.concat ", " gParamTys

                let comptimeCond =
                    if gFn.NeedsChain then
                        $"fable_rt.fitsTailArgs(&.{{ %s{paramTysStr} }})%s{trmcPlugCond}"
                    else
                        $"%s{chainName g} and fable_rt.fitsTailArgs(&.{{ %s{paramTysStr} }})%s{trmcPlugCond}"

                L $"if (comptime (%s{comptimeCond})) {{"
                let TI = ind + "    "
                let TL = line em TI
                let movedIds = HashSet<int>()

                let tcArgVars =
                    xs
                    |> List.mapi (fun i x ->
                        let pMode = gFn.Modes[i]
                        let av = freshName em $"tc_a%d{i}"

                        let laterUses vId =
                            xs |> List.skip (i + 1) |> List.exists (fun y -> Set.contains vId (fv y))

                        let rawText = emitArgAsTcVal em x

                        let moved =
                            pMode = MBorrowed
                            && (
                                match x with
                                | EVar v when
                                    drops |> List.exists (fun d -> d.Id = v.Id)
                                    && not (nonHoleConFv.Contains v.Id)
                                    && not (movedIds.Contains v.Id)
                                    && not (laterUses v.Id)
                                    ->
                                    movedIds.Add v.Id |> ignore
                                    true
                                | _ -> false
                            )

                        let isKnownArg =
                            match x with
                            | EKnown _
                            | EKnownIface _
                            | EUse(_, EKnown _)
                            | EUse(_, EKnownIface _) -> true
                            | _ -> false

                        if pMode = MBorrowed && not moved && not isKnownArg then
                            TL $"const %s{av}: %s{gParamTys[i]} = %s{dupCode rawText};"
                        else
                            TL $"const %s{av}: %s{gParamTys[i]} = %s{rawText};"

                        av
                    )

                for d in drops do
                    if not (movedIds.Contains d.Id) then
                        TL(dropCode (vname em d))

                let storeVals = String.concat ", " tcArgVars
                let gTcRef = fnRefTc g typeArgs
                emitTcJump trmcState TI gTcRef true paramTysStr storeVals "null" true

                L "} else {"

                let rawCallee =
                    if xs |> List.exists (hasKnownOrKArg em.KParams) then
                        kRef g typeArgs
                    else
                        fnRef g typeArgs

                let rawArgs = xs |> List.map (ex em) |> String.concat ", "
                let rawCall = $"%s{rawCallee}(%s{rawArgs})"
                emitFallbackCall trmcState (ind + "    ") rawCall false gFn.RetFrom.IsSome
                L "}"
                true

            | ECall(extF, typeArgs, xs, resTy) when isExtTcAlias em.FableAliases em.Fns extF ->
                let trmcState = emitTrmcTemps ()
                let extParamTys = xs |> List.map (typeOf >> zigType)
                let paramTysStr = String.concat ", " extParamTys

                let fitsExpr =
                    $"%s{extChainCheck extF} and fable_rt.fitsTailArgs(&.{{ %s{paramTysStr} }})%s{trmcPlugCond}"

                L $"if (comptime (%s{fitsExpr})) {{"
                let TI = ind + "    "
                let TL = line em TI
                let movedIds = HashSet<int>()

                let tcArgVars =
                    xs
                    |> List.mapi (fun i x ->
                        let av = freshName em $"tc_a%d{i}"

                        let laterUses vId =
                            xs |> List.skip (i + 1) |> List.exists (fun y -> Set.contains vId (fv y))

                        let needsDup =
                            match x with
                            | EUse(UKeep, inner) when isManaged (typeOf inner) ->
                                let moved =
                                    match inner with
                                    | EVar v when
                                        drops |> List.exists (fun d -> d.Id = v.Id)
                                        && not (nonHoleConFv.Contains v.Id)
                                        && not (movedIds.Contains v.Id)
                                        && not (laterUses v.Id)
                                        ->
                                        movedIds.Add v.Id |> ignore
                                        true
                                    | _ -> false

                                not moved
                            | _ -> false

                        let rawText = emitArgAsTcVal em x

                        let argExpr =
                            if needsDup then
                                dupCode rawText
                            else
                                rawText

                        TL $"const %s{av}: %s{extParamTys[i]} = %s{argExpr};"
                        av
                    )

                for d in drops do
                    if not (movedIds.Contains d.Id) then
                        TL(dropCode (vname em d))

                let storeVals = String.concat ", " tcArgVars
                let extTcRef = fnRefTc extF typeArgs
                emitTcJump trmcState TI extTcRef true paramTysStr storeVals "null" true

                L "} else {"

                let fallbackCall =
                    match formatCrossCall em extF typeArgs xs resTy None assumedFrom with
                    | Some s -> s
                    | None ->
                        let rawArgs = xs |> List.map (ex em) |> String.concat ", "
                        $"%s{fnRef extF typeArgs}(%s{rawArgs})"

                emitFallbackCall trmcState (ind + "    ") fallbackCall false hadDup
                L "}"
                true

            | _ -> false


let tailTarget (em: Em) (e: Expr) : string option =
    let isScalar (t: Ty) =
        match t with
        | TPrim _ -> true
        | _ -> false

    match e with
    | ECall(f, typeArgs, args, _) when em.CanTail && f <> em.Self.Name ->
        match em.Fns.TryGetValue f with
        | true, g ->
            let inst =
                if g.TypeParams.Length = typeArgs.Length then
                    Map.ofList (List.zip g.TypeParams typeArgs)
                else
                    Map.empty

            let calleeParams = g.Params |> List.map (fun p -> substTy inst p.Ty)
            let callerParams = em.Self.Params |> List.map (fun p -> p.Ty)
            let calleeRet = substTy inst g.Ret

            let same =
                g.Raises = RNever
                && List.forall isScalar (calleeRet :: calleeParams)
                && List.map zigType calleeParams = List.map zigType callerParams
                && zigType calleeRet = zigType em.Self.Ret

            if same then
                let tuple =
                    match args with
                    | [] -> ".{}"
                    | _ -> args |> List.map (ex em) |> String.concat ", " |> sprintf ".{ %s }"

                Some $"@call(fable_rt.tail_call, %s{fnRef f typeArgs}, %s{tuple})"
            else
                None
        | _ -> None
    | _ -> None

let emitValue (em: Em) (ind: string) (e: Expr) (dest: Dest) =
    let L = line em ind

    let effect () =
        match e with
        | EUnit -> ()
        | _ -> L(ex em e + ";")

    match dest with
    | DTcRet ->
        let retZig = zigType em.Self.Ret

        match em.Loop, em.Scc, e with
        | Some loop, _, (ECall(f, _, args, _) | EOnRaise(ECall(f, _, args, _), _)) when f = loop.Self ->
            emitTailJump em ind args
        | Some loop, _, _ when loop.Trmc ->
            L $"hole.* = %s{ex em e};"
            L $"@as(*%s{retZig}, @ptrCast(@alignCast(ret))).* = result;"
            L "return .{};"
        | _, Some scc, (ECall(g, tArgs, args, _) | EOnRaise(ECall(g, tArgs, args, _), [])) when
            em.TryLabels.Count = 0
            && tArgs = (em.Self.TypeParams |> List.map TGen)
            && scc.TagOf.ContainsKey g
            ->
            let tag = scc.TagOf[g]

            if args.IsEmpty then
                L $"_st = .%s{tag};"
            else
                let inits =
                    args |> List.mapi (fun i a -> $".a%d{i} = %s{ex em a}") |> String.concat ", "

                L $"const _next: %s{scc.StateTypeName} = .{{ .%s{tag} = .{{ %s{inits} }} }};"
                L "_st = _next;"

            L "continue :tail;"
        | _, Some scc, _ when scc.Trmc ->
            L $"hole.* = %s{ex em e};"
            L $"@as(*%s{retZig}, @ptrCast(@alignCast(ret))).* = result;"
            L "return .{};"
        | _ when tryEmitTailTc em ind e DTcRet -> ()
        | _ ->
            if isVoid em.Self.Ret then
                effect ()
                L "return .{};"
            else
                L $"@as(*%s{retZig}, @ptrCast(@alignCast(ret))).* = %s{ex em e};"
                L "return .{};"
    | DReturn ->
        match em.Loop, em.Scc, e with
        | Some loop, _, (ECall(f, _, args, _) | EOnRaise(ECall(f, _, args, _), _)) when f = loop.Self ->
            emitTailJump em ind args
        | Some loop, _, _ when loop.Trmc ->
            L $"hole.* = %s{ex em e};"
            L "return result;"
        | _, Some scc, (ECall(g, tArgs, args, _) | EOnRaise(ECall(g, tArgs, args, _), [])) when
            em.TryLabels.Count = 0
            && tArgs = (em.Self.TypeParams |> List.map TGen)
            && scc.TagOf.ContainsKey g
            ->
            let tag = scc.TagOf[g]

            if args.IsEmpty then
                L $"_st = .%s{tag};"
            else
                let inits =
                    args |> List.mapi (fun i a -> $".a%d{i} = %s{ex em a}") |> String.concat ", "

                L $"const _next: %s{scc.StateTypeName} = .{{ .%s{tag} = .{{ %s{inits} }} }};"
                L "_st = _next;"

            L "continue :tail;"
        | _, Some scc, _ when scc.Trmc ->
            L $"hole.* = %s{ex em e};"
            L "return result;"
        | _ when (tailTarget em e).IsSome -> L $"return %s{(tailTarget em e).Value};"
        | _ ->
            if isVoid (typeOf e) then
                effect ()

                if em.Loop.IsSome then
                    L "return;"
            else
                L $"return %s{ex em e};"
    | DBreak l ->
        if isVoid (typeOf e) then
            effect ()
            L $"break :%s{l} {{}};"
        else
            L $"break :%s{l} %s{ex em e};"
    | DDiscard ->
        match e with
        | EUnit -> ()
        | _ when isVoid (typeOf e) -> L(ex em e + ";")
        // (a local that is only discarded is still used, or Zig would reject it; a mutable one
        // is used by its assignments, and discarding it as well is an error to Zig)
        | EVar v when v.FMutable -> ()
        | EVar _ -> L $"_ = %s{ex em e};"
        | _ when isPure e -> ()
        | _ -> L $"_ = %s{ex em e};"


let rec stmt (em: Em) (ind: string) (e: Expr) (dest: Dest) : unit =
    let L = line em ind

    let block (rhs: Expr) (openLine: string -> string) =
        em.Counter <- em.Counter + 1
        let lbl = $"blk%d{em.Counter}"
        L(openLine lbl)
        stmt em (ind + "    ") rhs (DBreak lbl)
        L "};"

    match e with
    | ELet _ when
        dest = DReturn
        && em.Loop.IsSome
        && em.Loop.Value.Trmc
        && (trmcSite em.Loop.Value.Self e).IsSome
        ->
        let (args, conTy, case, conArgs, tok, holeIdx) =
            (trmcSite em.Loop.Value.Self e).Value

        let t = zigType conTy
        let c = fieldIdent case
        let fields = caseFields conTy case

        let inits =
            List.zip fields conArgs
            |> List.mapi (fun i ((f, _), a) ->
                let value =
                    if i = holeIdx then
                        "undefined"
                    else
                        ex em a

                $".%s{fieldIdent f} = %s{value}"
            )
            |> String.concat ", "

        let cell = freshName em "cell"

        match tok with
        | Some tk -> L $"const %s{cell} = fable_rt.cellReuse(%s{t}, .%s{c}, &%s{vname em tk}, .{{ %s{inits} }});"
        | None -> L $"const %s{cell} = fable_rt.cell(%s{t}, .%s{c}, .{{ %s{inits} }});"

        L "// link the new cell into the hole, then loop on the recursive call"
        L $"hole.* = .{{ .%s{c} = %s{cell} }};"
        L $"hole = &%s{cell}.%s{fieldIdent (fst fields[holeIdx])};"
        emitTailJump em ind args
    | ELet _ when
        dest = DReturn
        && em.Scc.IsSome
        && em.Scc.Value.Trmc
        && em.TryLabels.Count = 0
        && (
            match trmcSiteOf em.Scc.Value.TagOf.ContainsKey e with
            | Some(g, tArgs, args, _, _, _, _, _) ->
                tArgs = (em.Self.TypeParams |> List.map TGen)
                && args.Length = em.Fns[g].Params.Length
            | None -> false
        )
        ->
        let scc = em.Scc.Value

        let (g, _, args, conTy, case, conArgs, tok, holeIdx) =
            (trmcSiteOf scc.TagOf.ContainsKey e).Value

        let t = zigType conTy
        let c = fieldIdent case
        let fields = caseFields conTy case
        // evaluate non-hole constructor fields and callee arguments before mutating `hole` or `_st`
        let conTemps =
            List.zip fields conArgs
            |> List.mapi (fun i ((f, fTy), a) ->
                if i = holeIdx then
                    f, None
                else
                    let tmp = freshName em ("trmc_" + cleanIdent f)
                    L $"const %s{tmp}: %s{zigType fTy} = %s{ex em a};"
                    f, Some tmp
            )

        let argTemps =
            List.zip em.Fns[g].Params args
            |> List.mapi (fun i (p, a) ->
                let tmp = freshName em ("next_" + cleanIdent p.Base)
                L $"const %s{tmp}: %s{zigType p.Ty} = %s{ex em a};"
                i, tmp
            )

        let inits =
            conTemps
            |> List.map (fun (f, tmpOpt) ->
                let value = defaultArg tmpOpt "undefined"
                $".%s{fieldIdent f} = %s{value}"
            )
            |> String.concat ", "

        let cell = freshName em "cell"

        match tok with
        | Some tk -> L $"const %s{cell} = fable_rt.cellReuse(%s{t}, .%s{c}, &%s{vname em tk}, .{{ %s{inits} }});"
        | None -> L $"const %s{cell} = fable_rt.cell(%s{t}, .%s{c}, .{{ %s{inits} }});"

        L "// link the new cell into the hole, then transition to the next SCC state"
        L $"hole.* = .{{ .%s{c} = %s{cell} }};"
        L $"hole = &%s{cell}.%s{fieldIdent (fst fields[holeIdx])};"
        let tag = scc.TagOf[g]

        if argTemps.IsEmpty then
            L $"_st = .%s{tag};"
        else
            let stInits =
                argTemps
                |> List.map (fun (i, tmp) -> $".a%d{i} = %s{tmp}")
                |> String.concat ", "

            L $"const _next: %s{scc.StateTypeName} = .{{ .%s{tag} = .{{ %s{stInits} }} }};"
            L "_st = _next;"

        L "continue :tail;"
    | FloatedTrmc em dest floated -> stmt em ind floated dest
    | _ when tryEmitTailTc em ind e dest -> ()
    // (a value that always raises: the raise, and nothing after it, which could not run)
    | ELet(_, rhs, _) when alwaysRaises rhs -> stmt em ind rhs DDiscard
    | ELet(v, rhs, body) ->
        let isKParamAlias =
            not v.FMutable
            && (
                match rhs with
                | EVar u -> em.KParams.Contains u.Id
                | EGet(EVar u, PSome, _) -> em.KParams.Contains u.Id
                | _ -> false
            )

        if not ((fv body).Contains v.Id) then
            if isFlat rhs then
                let s = ex em rhs

                if isVoid (typeOf rhs) then
                    (match rhs with
                     | EUnit -> ()
                     | _ -> L(s + ";"))
                elif not (isPure rhs) then
                    L $"_ = %s{s};"
            else
                stmt em ind rhs DDiscard

            stmt em ind body dest
        else
            let name = vname em v

            let kw =
                if em.Mutated.Contains v.Id then
                    "var"
                else
                    "const"

            if isKParamAlias then
                L $"%s{kw} %s{name} = %s{ex em rhs};"
                stmt { em with KParams = em.KParams.Add v.Id } ind body dest
            else
                // (a unit made by a statement, a loop: the statement, then the unit)
                match rhs with
                | EFor _
                | EWhile _ when isVoid v.Ty ->
                    stmt em ind rhs DDiscard
                    L $"%s{kw} %s{name}: void = {{}};"
                | _ when isFlat rhs || isSimpleIf rhs -> L $"%s{kw} %s{name}: %s{zigType v.Ty} = %s{ex em rhs};"
                | _ -> block rhs (fun lbl -> $"%s{kw} %s{name}: %s{zigType v.Ty} = %s{lbl}: {{")

                stmt em ind body dest
    // (after what always raises, nothing runs: Zig refuses code after its jump)
    | ESeq(a, _) when alwaysRaises a -> stmt em ind a DDiscard
    | ESeq(a, b) ->
        stmt em ind a DDiscard
        stmt em ind b dest
    // (where a function ends, each branch is a statement if one of them may be a jump)
    | EIf(_, t, f, _) when
        isSimpleIf e
        && dest <> DDiscard
        && dest <> DTcRet
        && not (
            dest = DReturn
            && (em.Loop.IsSome
                || em.Scc.IsSome
                || (tailTarget em t).IsSome
                || (tailTarget em f).IsSome
                || isTcBoundaryExpr em t
                || isTcBoundaryExpr em f)
        )
        ->
        emitValue em ind e dest
    | EIf(c, t, f, _) ->
        L $"if (%s{unparen (ex em c)}) {{"
        stmt em (ind + "    ") t dest

        match f, dest with
        | EUnit, DDiscard -> L "}"
        | _ ->
            L "} else {"
            stmt em (ind + "    ") f dest
            L "}"
    | EWhile(c, b) ->
        L $"while (%s{unparen (ex em c)}) {{"
        stmt em (ind + "    ") b DDiscard
        L "}"
        finishUnit em ind dest
    | EFor(i, a, b, up, body) ->
        let iname = vname em i
        let endName = freshName em (iname + "_end")

        let cmp, step =
            if up then
                "<=", "+="
            else
                ">=", "-="

        // the bound is evaluated once; the loop variable does not overflow past it
        L "{"
        L $"    const %s{endName}: %s{zigType i.Ty} = %s{ex em b};"
        L $"    var %s{iname}: %s{zigType i.Ty} = %s{ex em a};"
        L $"    while (%s{iname} %s{cmp} %s{endName}) {{"
        stmt em (ind + "        ") body DDiscard
        L $"        if (%s{iname} == %s{endName}) break;"
        L $"        %s{iname} %s{step} 1;"
        L "    }"
        L "}"
        finishUnit em ind dest
    | EAssign(v, rhs) ->
        if isFlat rhs || isSimpleIf rhs then
            L(assignText em (vname em v) rhs)
        else
            block rhs (fun lbl -> $"%s{vname em v} = %s{lbl}: {{")

        finishUnit em ind dest
    // A field that owns its value: the old value is given up once the new one is in place.
    | EStore(EGet(EEmit(m, [ o ], TPtr(part, false)), PField _, _) as lv, rhs) when
        m.StartsWith("objInit:", System.StringComparison.Ordinal)
        ->
        let rest = m.Substring 8
        let colon = rest.IndexOf ':'
        let fieldIdx = rest.Substring(0, colon)
        let parts = rest.Substring(colon + 1)

        let value =
            if isFlat rhs || isSimpleIf rhs then
                ex em rhs
            else
                let stored = freshName em "stored"
                block rhs (fun lbl -> $"const %s{stored}: %s{zigType (typeOf lv)} = %s{lbl}: {{")
                stored

        L $"fable_rt.objInitField(%s{zigType part}, &[_]type{{ %s{parts} }}, %s{fieldIdx}, %s{ex em o}, %s{value});"
        finishUnit em ind dest
    | EStore(lv, rhs) ->
        let place = ex em lv

        let value =
            if isFlat rhs || isSimpleIf rhs then
                ex em rhs
            else
                let stored = freshName em "stored"
                block rhs (fun lbl -> $"const %s{stored}: %s{zigType (typeOf lv)} = %s{lbl}: {{")
                stored

        match lv with
        // (a field of an object: the collector is told through the object's header)
        | EGet(EEmit(m, [ o ], TPtr _), PField _, _) when
            isManaged (typeOf lv)
            && m.StartsWith("fable_rt.objPart(", System.StringComparison.Ordinal)
            ->
            L $"fable_rt.objStore(%s{ex em o}, &%s{place}, %s{value});"
        // (a field of a reference record: the collector is told, a cycle may be closed here)
        | EGet(owner, PField f, _) when
            isManaged (typeOf lv)
            && (
                match typeOf owner with
                | TEnt({ Kind = KRefRecord }, _) -> true
                | _ -> false
            )
            ->
            L $"fable_rt.storeIn(%s{ex em owner}, \"%s{f}\", %s{value});"
        | _ when isManaged (typeOf lv) -> L $"fable_rt.store(&%s{place}, %s{value});"
        | _ -> L $"%s{place} = %s{value};"

        finishUnit em ind dest
    | EDrop(v, k) ->
        L(dropCode (vname em v))
        stmt em ind k dest
    | EUnpack(u, k) ->
        emitUnpack em ind u
        stmt em ind k dest
    | EPromote(v, k) ->
        L $"_ = %s{dupCode (vname em v)}; // this borrow outlives its owner"
        stmt em ind k dest
    | ERaise(x, _) ->
        L $"fable_rt.throw(%s{ex em x});"
        L(leaveText em)
    | ETry(body, exV, handler, ty) ->
        em.Counter <- em.Counter + 1
        let okL = $"try%d{em.Counter}"
        let errL = $"raised%d{em.Counter}"
        // (the body and the handler go to a buffer first, to see which labels are used)
        let inner = { em with Out = StringBuilder() }
        em.TryLabels.Push errL

        try
            stmt inner (ind + "        ") body (DBreak okL)
        finally
            em.TryLabels.Pop() |> ignore

        let bodyText = inner.Out.ToString()
        let raises = bodyText.Contains $"break :%s{errL};"
        inner.Out.Clear() |> ignore

        if raises then
            line inner ind $"    %s{errL}: {{"
            inner.Out.Append(bodyText) |> ignore
            line inner ind "    }"
            // the handler owns the exception
            line inner ind $"    const %s{vname inner exV}: fable_rt.Exn = fable_rt.take();"
            stmt inner (ind + "    ") handler (DBreak okL)
        else
            inner.Out.Append(bodyText) |> ignore

        em.Counter <- inner.Counter
        let text = inner.Out.ToString()

        if not (text.Contains $"break :%s{okL} ") then
            // (every path raises again or returns: nothing comes after the `try`)
            L "{"
            em.Out.Append(text) |> ignore
            L "}"
        elif isVoid ty then
            L $"%s{okL}: {{"
            em.Out.Append(text) |> ignore
            L "}"
            finishUnit em ind dest
        else
            let tried = freshName em "tried"
            L $"const %s{tried}: %s{zigType ty} = %s{okL}: {{"
            em.Out.Append(text) |> ignore
            L "};"
            emitValue em ind (ELit(tried, ty)) dest
    | _ -> emitValue em ind e dest

/// A call of another function of the file that ends this one can be a jump instead of a call
/// when nothing is left to do after it (no result to store through a destination pointer, no
/// dead cell waiting to be freed) and the two functions have the same parameter and result
/// types, all of them numbers, booleans or chars: the callee then runs in the caller's frame.
/// (Zig passes and returns records and unions through pointers into the caller's frame, which
/// a jump would leave dangling, so such signatures stay calls.) Functions that call each other
/// last (`even`/`odd`, state machines over numbers) then run in constant stack, as on .NET.
