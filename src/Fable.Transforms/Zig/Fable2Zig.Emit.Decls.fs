/// Emission of closure adapters, `$known` records, and interface vtables.
module internal Fable.Transforms.Zig.EmitDecls

open System.Collections.Generic
open System.Text
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.EmitExpr
open Fable.Transforms.Zig.EmitStmt

/// The code of a function value. A function value owns its arguments and its result, and what
/// it captured stays in its environment; the function it calls may have been inferred to
/// borrow some of that, so this is where the two are brought together.
let emitAdapter
    (out: StringBuilder)
    (fableAliases: HashSet<string>)
    (noTcFns: HashSet<string>)
    (fns: Dictionary<string, FnInfo>)
    (a: Adapter)
    =
    let argTys, ret =
        match a.FnTy with
        | TFn(args, ret) -> args, ret
        | _ -> fail None "internal: not a function type"

    let ps = argTys |> List.mapi (fun i t -> $"a%d{i}", t)

    let sigParams =
        "env: ?*fable_rt.Env"
        :: (ps |> List.map (fun (n, t) -> $"%s{n}: %s{zigType t}"))
        |> String.concat ", "

    let line (text: string) = out.AppendLine(text) |> ignore

    match a.Gens with
    | [] -> line $"const %s{a.Name} = struct {{"
    | gens ->
        let comptimeParams =
            gens
            |> List.map (fun g -> $"comptime %s{genName g}: type")
            |> String.concat ", "

        line $"fn %s{a.Name}(%s{comptimeParams}) type {{"
        line "    return struct {"

    let ind =
        if a.Gens.IsEmpty then
            "    "
        else
            "        "

    let line (text: string) = line (ind + text)

    // (The function behind the value may raise or not; a function value always may. If the call
    // raised, what the function only borrowed is given up here, like after a call that did not.)
    let finish (call: string) (resultBorrowed: bool) (dropAfter: string list) =
        let drops = dropAfter |> List.map (fun n -> dropCode n + " ") |> String.concat ""
        line $"    const raw = %s{call};"

        line
            $"    const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch |err| {{ %s{drops}return err; }} else raw;"

        let result =
            if resultBorrowed then
                dupCode "r"
            else
                "r"

        if dropAfter.IsEmpty then
            line $"    return %s{result};"
        else
            line $"    const result = %s{result};"

            for name in dropAfter do
                line ("    " + dropCode name)

            line "    return result;"

    match fns.TryGetValue a.Target with
    | true, fn ->
        let inst =
            if fn.TypeParams.Length = a.TypeArgs.Length then
                Map.ofList (List.zip fn.TypeParams a.TypeArgs)
            else
                Map.empty

        let captured, rest = List.splitAt a.NCaptures (List.zip fn.Params fn.Modes)

        if a.NCaptures > 0 then
            let fields =
                captured
                |> List.mapi (fun i (p, _) -> $"c%d{i}: %s{zigType (substTy inst p.Ty)}")
                |> String.concat ", "

            line $"const Env = struct {{ %s{fields} }};"

        line $"fn code(%s{sigParams}) fable_rt.Raised!%s{zigType ret} {{"

        if a.NCaptures > 0 then
            line "    const c = fable_rt.captured(Env, env);"
        else
            line "    _ = env;"

        // (the environment keeps what it captured: a function that takes ownership gets a
        // reference of its own)
        let capturedArgs =
            captured
            |> List.mapi (fun i (_, m) ->
                if m = MOwned then
                    dupCode $"c.c%d{i}"
                else
                    $"c.c%d{i}"
            )

        let callPs =
            match ps, rest with
            | (n0, _) :: psTail, (_, m0) :: _ when a.BorrowFirst ->
                let a0 =
                    if m0 = MOwned then
                        dupCode n0
                    else
                        n0

                a0 :: (psTail |> List.map fst)
            | _ -> ps |> List.map fst

        let args = capturedArgs @ callPs |> String.concat ", "

        let dropPairs =
            match List.zip ps rest with
            | _ :: tail when a.BorrowFirst -> tail
            | all -> all

        let dropAfter =
            dropPairs
            |> List.choose (fun ((n, _), (_, m)) ->
                if m = MBorrowed then
                    Some n
                else
                    None
            )

        finish $"%s{fnRef a.Target a.TypeArgs}(%s{args})" fn.RetFrom.IsSome dropAfter

        match a.Target2, a.FnTy with
        | Some t2, TFn([ tyA ], TFn([ tyB ], tyR)) ->
            match fns.TryGetValue t2 with
            | true, fn2 ->
                line "}"
                let captured2, rest2 = List.splitAt a.NCaptures (List.zip fn2.Params fn2.Modes)

                line
                    $"fn code2(env: ?*fable_rt.Env, a0: %s{zigType tyA}, a1: %s{zigType tyB}) fable_rt.Raised!%s{zigType tyR} {{"

                if a.NCaptures > 0 then
                    line "    const c = fable_rt.captured(Env, env);"
                else
                    line "    _ = env;"

                let capturedArgs2 =
                    captured2
                    |> List.mapi (fun i (_, m) ->
                        if m = MOwned then
                            dupCode $"c.c%d{i}"
                        else
                            $"c.c%d{i}"
                    )

                let args2 = capturedArgs2 @ [ "a0"; "a1" ] |> String.concat ", "

                let dropAfter2 =
                    List.zip [ "a0"; "a1" ] rest2
                    |> List.choose (fun (n, (_, m)) ->
                        if m = MBorrowed then
                            Some n
                        else
                            None
                    )

                finish $"%s{fnRef t2 a.TypeArgs}(%s{args2})" fn2.RetFrom.IsSome dropAfter2
            | _ -> ()
        | _ -> ()
    | _ ->
        // a function of another file: what it borrows is settled when the Zig is compiled
        if a.NCaptures > 0 then
            let fields =
                a.CaptureTys
                |> List.mapi (fun i t -> $"c%d{i}: %s{zigType t}")
                |> String.concat ", "

            line $"const Env = struct {{ %s{fields} }};"

        line $"fn code(%s{sigParams}) fable_rt.Raised!%s{zigType ret} {{"

        if a.NCaptures > 0 then
            line "    const c = fable_rt.captured(Env, env);"
        else
            line "    _ = env;"

        let tuple (items: string list) =
            match items with
            | [] -> ".{}"
            | _ -> items |> String.concat ", " |> sprintf ".{ %s }"

        let capturedArgs = a.CaptureTys |> List.mapi (fun i _ -> $"c.c%d{i}")

        if
            isManaged ret
            || argTys |> List.exists isManaged
            || a.CaptureTys |> List.exists isManaged
        then
            // (the environment keeps what it captured; the arguments are given unless BorrowFirst borrows a0)
            let uses =
                (a.CaptureTys
                 |> List.map (fun t ->
                     if isManaged t then
                         ".keep"
                     else
                         ".plain"
                 ))
                @ (argTys
                   |> List.mapi (fun i t ->
                       if isManaged t then
                           if a.BorrowFirst && i = 0 then
                               ".keep"
                           else
                               ".give"
                       else
                           ".plain"
                   ))

            finish
                $"fable_rt.across(%s{fnRef a.Target a.TypeArgs}, %s{sigName a.Target}, %s{tuple uses}, %s{tuple (capturedArgs @ (ps |> List.map fst))})"
                false
                []
        else
            let args = capturedArgs @ (ps |> List.map fst) |> String.concat ", "
            finish $"%s{fnRef a.Target a.TypeArgs}(%s{args})" false []

    line "}"

    if a.NeedsTcode && not a.BorrowFirst then
        let emitTcodeFn (tcFnName: string) (target: string) (tArgTys: Ty list) (tRetTy: Ty) =
            let tParamTysStr = tArgTys |> List.map zigType |> String.concat ", "
            let tRetZig = zigType tRetTy
            let tVoidRet = isVoid tRetTy
            line $"pub fn %s{tcFnName}(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {{"
            line $"    if (comptime fable_rt.fitsTailArgs(&.{{ %s{tParamTysStr} }})) {{"
            line $"        const _tca = fable_rt.tailLoad(&.{{ %s{tParamTysStr} }}, ctx);"
            line "        const _ts = fable_rt.takeSelfBorrowed(ctx);"
            line "        const env: ?*fable_rt.Env = @ptrCast(@alignCast(_ts.ptr));"

            let emitTcBodyDispatch (fn: FnInfo) (pad: string) =
                let inst =
                    if fn.TypeParams.Length = a.TypeArgs.Length then
                        Map.ofList (List.zip fn.TypeParams a.TypeArgs)
                    else
                        Map.empty

                let capParams = List.take a.NCaptures fn.Params

                let capArgs =
                    if a.NCaptures > 0 then
                        line $"%s{pad}const c = fable_rt.captured(Env, env);"
                        line $"%s{pad}var _tc_reuse_e: ?*fable_rt.EnvOf(Env) = null;"

                        let capInfo =
                            capParams
                            |> List.mapi (fun i p ->
                                let capTy = substTy inst p.Ty
                                let cv = $"_tc_cap%d{i}"
                                line $"%s{pad}var %s{cv}: %s{zigType capTy} = undefined;"
                                i, capTy, cv
                            )

                        line $"%s{pad}if (_ts.owned and fable_rt.isUnique(env.?)) {{"
                        line $"%s{pad}    fable_rt.forgetEnv(env.?);"

                        for (i, capTy, cv) in capInfo do
                            line $"%s{pad}    %s{cv} = c.c%d{i};"

                            if isManaged capTy && mayHoldCyclic capTy then
                                line $"%s{pad}    if (comptime fable_rt.EnvOf(Env).cyclic) fable_rt.touch(%s{cv});"

                        line
                            $"%s{pad}    const _re: *fable_rt.EnvOf(Env) = @alignCast(@fieldParentPtr(\"header\", env.?));"

                        line $"%s{pad}    _tc_reuse_e = _re;"
                        line $"%s{pad}    ctx.reuse_env = @ptrCast(_re);"
                        line $"%s{pad}    ctx.reuse_env_size = @sizeOf(fable_rt.EnvOf(Env));"
                        line $"%s{pad}    ctx.reuse_env_align = @alignOf(fable_rt.EnvOf(Env));"
                        line $"%s{pad}}} else {{"

                        for (i, capTy, cv) in capInfo do
                            let src = $"c.c%d{i}"

                            let initExpr =
                                if isManaged capTy then
                                    dupCode src
                                else
                                    src

                            line $"%s{pad}    %s{cv} = %s{initExpr};"

                        line $"%s{pad}    if (_ts.owned) fable_rt.dropEnv(env);"
                        line $"%s{pad}}}"
                        capInfo |> List.map (fun (_, _, cv) -> cv)
                    else
                        line $"%s{pad}if (_ts.owned) fable_rt.dropEnv(env);"
                        []

                let emitReuseCleanup (cpad: string) =
                    if a.NCaptures > 0 then
                        line $"%s{cpad}if (_tc_reuse_e) |_re| {{"
                        line $"%s{cpad}    if (ctx.reuse_env != null) {{"
                        line $"%s{cpad}        ctx.reuse_env = null;"
                        line $"%s{cpad}        fable_rt.free(_re);"
                        line $"%s{cpad}    }}"
                        line $"%s{cpad}}}"

                let loadArgs = tArgTys |> List.mapi (fun i _ -> $"_tca[%d{i}]")
                let allArgs = capArgs @ loadArgs |> String.concat ", "

                line $"%s{pad}const _next = %s{fnTcBodyRef target a.TypeArgs}(ctx, ret, %s{allArgs}) catch {{"
                emitReuseCleanup (pad + "    ")
                line $"%s{pad}    fable_rt.plugRet(%s{tRetZig}, ret);"
                line $"%s{pad}    return .raised;"
                line $"%s{pad}}};"
                emitReuseCleanup pad
                line $"%s{pad}if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{{ ctx, _next.ret }});"
                line $"%s{pad}return .ok;"

            let emitKnownNonTc (fn: FnInfo) (pad: string) =
                if a.NCaptures > 0 then
                    line $"%s{pad}const c = fable_rt.captured(Env, env);"

                let captured, rest = List.splitAt a.NCaptures (List.zip fn.Params fn.Modes)

                let capArgs =
                    captured
                    |> List.mapi (fun i (_, m) ->
                        if m = MOwned then
                            dupCode $"c.c%d{i}"
                        else
                            $"c.c%d{i}"
                    )

                let callArgs = tArgTys |> List.mapi (fun i _ -> $"_tca[%d{i}]")
                let args = capArgs @ callArgs |> String.concat ", "

                let dropAfter =
                    List.zip callArgs rest
                    |> List.choose (fun (n, (_, m)) ->
                        if m = MBorrowed then
                            Some n
                        else
                            None
                    )

                line $"%s{pad}const raw = %s{fnRef target a.TypeArgs}(%s{args});"
                line $"%s{pad}const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"

                for d in dropAfter do
                    line ($"%s{pad}    " + dropCode d)

                line $"%s{pad}    if (_ts.owned) fable_rt.dropEnv(env);"
                line $"%s{pad}    fable_rt.plugRet(%s{tRetZig}, ret);"
                line $"%s{pad}    return .raised;"
                line $"%s{pad}}} else raw;"

                if tVoidRet then
                    line $"%s{pad}_ = r;"

                    for d in dropAfter do
                        line ($"%s{pad}" + dropCode d)

                    line $"%s{pad}if (_ts.owned) fable_rt.dropEnv(env);"
                    line $"%s{pad}return .ok;"
                else
                    let resExpr =
                        if fn.RetFrom.IsSome then
                            dupCode "r"
                        else
                            "r"

                    line $"%s{pad}const res = %s{resExpr};"

                    for d in dropAfter do
                        line ($"%s{pad}" + dropCode d)

                    line $"%s{pad}if (_ts.owned) fable_rt.dropEnv(env);"
                    line $"%s{pad}@as(*%s{tRetZig}, @ptrCast(@alignCast(ret))).* = res;"
                    line $"%s{pad}return .ok;"

            match fns.TryGetValue target with
            | true, fn when not (noTcFns.Contains target) && fnHasTcBody fn ->
                if fn.NeedsChain then
                    emitTcBodyDispatch fn "        "
                else
                    line $"        if (comptime %s{chainName target}) {{"
                    emitTcBodyDispatch fn "            "
                    line "        } else {"
                    emitKnownNonTc fn "            "
                    line "        }"
            | true, fn -> emitKnownNonTc fn "        "
            | _ ->
                let emitExtFallback (pad: string) =
                    if a.NCaptures > 0 then
                        line $"%s{pad}const c = fable_rt.captured(Env, env);"

                    let tuple (items: string list) =
                        match items with
                        | [] -> ".{}"
                        | _ -> items |> String.concat ", " |> sprintf ".{ %s }"

                    let capArgs = a.CaptureTys |> List.mapi (fun i _ -> $"c.c%d{i}")
                    let callArgs = tArgTys |> List.mapi (fun i _ -> $"_tca[%d{i}]")

                    let callExpr =
                        if
                            isManaged tRetTy
                            || tArgTys |> List.exists isManaged
                            || a.CaptureTys |> List.exists isManaged
                        then
                            let uses =
                                (a.CaptureTys
                                 |> List.map (fun t ->
                                     if isManaged t then
                                         ".keep"
                                     else
                                         ".plain"
                                 ))
                                @ (tArgTys
                                   |> List.map (fun t ->
                                       if isManaged t then
                                           ".give"
                                       else
                                           ".plain"
                                   ))

                            $"fable_rt.across(%s{fnRef target a.TypeArgs}, %s{sigName target}, %s{tuple uses}, %s{tuple (capArgs @ callArgs)})"
                        else
                            let args = capArgs @ callArgs |> String.concat ", "
                            $"%s{fnRef target a.TypeArgs}(%s{args})"

                    line $"%s{pad}const raw = %s{callExpr};"
                    line $"%s{pad}const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"
                    line $"%s{pad}    if (_ts.owned) fable_rt.dropEnv(env);"
                    line $"%s{pad}    fable_rt.plugRet(%s{tRetZig}, ret);"
                    line $"%s{pad}    return .raised;"
                    line $"%s{pad}}} else raw;"

                    if tVoidRet then
                        line $"%s{pad}_ = r;"
                    else
                        line $"%s{pad}@as(*%s{tRetZig}, @ptrCast(@alignCast(ret))).* = r;"

                    line $"%s{pad}if (_ts.owned) fable_rt.dropEnv(env);"
                    line $"%s{pad}return .ok;"

                if isExtTcAlias fableAliases fns target then
                    let allParamTysStr =
                        a.CaptureTys @ tArgTys |> List.map zigType |> String.concat ", "

                    line
                        $"        if (comptime (%s{extChainCheck target} and fable_rt.fitsTailArgs(&.{{ %s{allParamTysStr} }}))) {{"

                    let capArgs =
                        if a.NCaptures > 0 then
                            line "            const c = fable_rt.captured(Env, env);"

                            a.CaptureTys
                            |> List.mapi (fun i capTy ->
                                let cv = $"_tc_cap%d{i}"

                                if isManaged capTy then
                                    let dupCap = dupCode $"c.c%d{i}"
                                    line $"            const %s{cv}: %s{zigType capTy} = %s{dupCap};"
                                else
                                    line $"            const %s{cv}: %s{zigType capTy} = c.c%d{i};"

                                cv
                            )
                        else
                            []

                    line "            if (_ts.owned) fable_rt.dropEnv(env);"
                    let loadArgs = tArgTys |> List.mapi (fun i _ -> $"_tca[%d{i}]")
                    let allArgs = capArgs @ loadArgs |> String.concat ", "

                    if allParamTysStr <> "" then
                        line $"            fable_rt.tailStore(&.{{ %s{allParamTysStr} }}, ctx, .{{ %s{allArgs} }});"

                    line
                        $"            return @call(fable_rt.tail_call, &%s{fnRefTc target a.TypeArgs}, .{{ ctx, ret }});"

                    line "        } else {"
                    emitExtFallback "            "
                    line "        }"
                else
                    emitExtFallback "        "

            line "    } else {"
            line "        unreachable;"
            line "    }"
            line "}"

        emitTcodeFn "tcode" a.Target argTys ret

        match a.Target2, a.FnTy with
        | Some t2, TFn([ tyA ], TFn([ tyB ], tyR)) -> emitTcodeFn "tcode2" t2 [ tyA; tyB ] tyR
        | _ -> ()
    elif a.NeedsTcode then
        let thisTy, restArgTys =
            match argTys with
            | t :: rs -> t, rs
            | [] -> fail None "internal: borrow-first adapter without self parameter"

        let thisZig = zigType thisTy
        let restParamTysStr = restArgTys |> List.map zigType |> String.concat ", "
        let retZig = zigType ret
        let voidRet = isVoid ret

        line "pub fn tcode(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {"

        let emitVtTcodeBody (pad: string) =
            let loadArgs = restArgTys |> List.mapi (fun i _ -> $"_tca[%d{i}]")
            let dupSelf = dupCode "self"
            let dropSelf = dropCode "self"
            line $"%s{pad}const _ts = fable_rt.takeSelfBorrowed(ctx);"
            line $"%s{pad}const self: %s{thisZig} = @ptrCast(@alignCast(_ts.ptr.?));"

            let emitTcBodyVt (p: string) =
                line $"%s{p}const _self_own: %s{thisZig} = if (_ts.owned) self else %s{dupSelf};"
                let allArgs = "_self_own" :: loadArgs |> String.concat ", "
                line $"%s{p}const _next = %s{fnTcBodyRef a.Target a.TypeArgs}(ctx, ret, %s{allArgs}) catch {{"
                line $"%s{p}    fable_rt.plugRet(%s{retZig}, ret);"
                line $"%s{p}    return .raised;"
                line $"%s{p}}};"
                line $"%s{p}if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{{ ctx, _next.ret }});"
                line $"%s{p}return .ok;"

            let emitKnownNonTcVt (fn: FnInfo) (p: string) =
                match List.zip fn.Params fn.Modes with
                | (_, thisMode) :: restModes ->
                    let a0 =
                        if thisMode = MOwned then
                            $"if (_ts.owned) self else %s{dupSelf}"
                        else
                            "self"

                    let args = a0 :: loadArgs |> String.concat ", "

                    let dropAfter =
                        List.zip loadArgs restModes
                        |> List.choose (fun (n, (_, m)) ->
                            if m = MBorrowed then
                                Some n
                            else
                                None
                        )

                    let selfDropLine =
                        if thisMode <> MOwned && isManaged thisTy then
                            Some $"if (_ts.owned) %s{dropSelf}"
                        else
                            None

                    line $"%s{p}const raw = %s{fnRef a.Target a.TypeArgs}(%s{args});"
                    line $"%s{p}const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"

                    for d in dropAfter do
                        line ($"%s{p}    " + dropCode d)

                    Option.iter (fun s -> line $"%s{p}    %s{s}") selfDropLine
                    line $"%s{p}    fable_rt.plugRet(%s{retZig}, ret);"
                    line $"%s{p}    return .raised;"
                    line $"%s{p}}} else raw;"

                    if voidRet then
                        line $"%s{p}_ = r;"

                        for d in dropAfter do
                            line ($"%s{p}" + dropCode d)

                        Option.iter (fun s -> line $"%s{p}%s{s}") selfDropLine
                        line $"%s{p}return .ok;"
                    else
                        let resExpr =
                            if fn.RetFrom.IsSome then
                                dupCode "r"
                            else
                                "r"

                        line $"%s{p}const res = %s{resExpr};"

                        for d in dropAfter do
                            line ($"%s{p}" + dropCode d)

                        Option.iter (fun s -> line $"%s{p}%s{s}") selfDropLine
                        line $"%s{p}@as(*%s{retZig}, @ptrCast(@alignCast(ret))).* = res;"
                        line $"%s{p}return .ok;"
                | [] -> fail None "internal: vtable method `%s` has no self parameter" a.Target

            match fns.TryGetValue a.Target with
            | true, fn when not (noTcFns.Contains a.Target) && fnHasTcBody fn ->
                if fn.NeedsChain then
                    emitTcBodyVt pad
                else
                    line $"%s{pad}if (comptime %s{chainName a.Target}) {{"
                    emitTcBodyVt (pad + "    ")
                    line $"%s{pad}}} else {{"
                    emitKnownNonTcVt fn (pad + "    ")
                    line $"%s{pad}}}"
            | true, fn -> emitKnownNonTcVt fn pad
            | _ ->
                let emitExtFallbackVt (p: string) =
                    let tuple (items: string list) =
                        match items with
                        | [] -> ".{}"
                        | _ -> items |> String.concat ", " |> sprintf ".{ %s }"

                    let callExpr =
                        if isManaged ret || argTys |> List.exists isManaged then
                            let uses =
                                (if isManaged thisTy then
                                     ".keep"
                                 else
                                     ".plain")
                                :: (restArgTys
                                    |> List.map (fun t ->
                                        if isManaged t then
                                            ".give"
                                        else
                                            ".plain"
                                    ))

                            let usesTuple = tuple uses
                            let argsTuple = tuple ("self" :: loadArgs)
                            $"fable_rt.across(%s{fnRef a.Target a.TypeArgs}, %s{sigName a.Target}, %s{usesTuple}, %s{argsTuple})"
                        else
                            let args = "self" :: loadArgs |> String.concat ", "
                            $"%s{fnRef a.Target a.TypeArgs}(%s{args})"

                    let selfDrop =
                        if isManaged thisTy then
                            Some $"if (_ts.owned) %s{dropSelf}"
                        else
                            None

                    line $"%s{p}const raw = %s{callExpr};"
                    line $"%s{p}const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"
                    Option.iter (fun s -> line $"%s{p}    %s{s}") selfDrop
                    line $"%s{p}    fable_rt.plugRet(%s{retZig}, ret);"
                    line $"%s{p}    return .raised;"
                    line $"%s{p}}} else raw;"

                    if voidRet then
                        line $"%s{p}_ = r;"
                    else
                        line $"%s{p}@as(*%s{retZig}, @ptrCast(@alignCast(ret))).* = r;"

                    Option.iter (fun s -> line $"%s{p}%s{s}") selfDrop
                    line $"%s{p}return .ok;"

                if isExtTcAlias fableAliases fns a.Target then
                    let fullParamTysStr = argTys |> List.map zigType |> String.concat ", "

                    line
                        $"%s{pad}if (comptime (%s{extChainCheck a.Target} and fable_rt.fitsTailArgs(&.{{ %s{fullParamTysStr} }}))) {{"

                    line $"%s{pad}    const _self_own: %s{thisZig} = if (_ts.owned) self else %s{dupSelf};"
                    let allArgs = "_self_own" :: loadArgs |> String.concat ", "
                    line $"%s{pad}    fable_rt.tailStore(&.{{ %s{fullParamTysStr} }}, ctx, .{{ %s{allArgs} }});"

                    line
                        $"%s{pad}    return @call(fable_rt.tail_call, &%s{fnRefTc a.Target a.TypeArgs}, .{{ ctx, ret }});"

                    line $"%s{pad}}} else {{"
                    emitExtFallbackVt (pad + "    ")
                    line $"%s{pad}}}"
                else
                    emitExtFallbackVt pad

        if restArgTys.IsEmpty then
            emitVtTcodeBody "    "
        else
            line $"    if (comptime fable_rt.fitsTailArgs(&.{{ %s{restParamTysStr} }})) {{"
            line $"        const _tca = fable_rt.tailLoad(&.{{ %s{restParamTysStr} }}, ctx);"
            emitVtTcodeBody "        "
            line "    } else {"
            line "        unreachable;"
            line "    }"

        line "}"

    if a.Gens.IsEmpty then
        out.AppendLine("};") |> ignore
    else
        out.AppendLine("    };").AppendLine("}") |> ignore

    out.AppendLine() |> ignore

/// Emit a stack-allocated `Known` lambda struct descriptor for `callK` / `callHof`.
let emitKnownDecl
    (out: StringBuilder)
    (fns: Dictionary<string, FnInfo>)
    (noTcFile: bool)
    (noTailCalls: HashSet<string>)
    (adapters: Dictionary<string, Adapter>)
    (k: KnownDecl)
    =
    let argTys, ret =
        match k.FnTy with
        | TFn(args, ret) -> args, ret
        | _ -> fail None "internal: not a function type"

    let ps =
        argTys |> List.mapi (fun i t -> $"a%d{i}: %s{zigType t}") |> String.concat ", "

    let pNames = argTys |> List.mapi (fun i _ -> $"a%d{i}")

    let selfParam =
        if pNames.IsEmpty then
            "self: *const @This()"
        else
            "self: *const @This(), " + ps

    let line (text: string) = out.AppendLine(text) |> ignore

    match k.Gens with
    | [] -> line $"const %s{k.Name} = struct {{"
    | gens ->
        let comptimeParams =
            gens
            |> List.map (fun g -> $"comptime %s{genName g}: type")
            |> String.concat ", "

        line $"fn %s{k.Name}(%s{comptimeParams}) type {{"
        line "    return struct {"

    let ind =
        if k.Gens.IsEmpty then
            "    "
        else
            "        "

    let line (text: string) = line (ind + text)

    line "pub const fable_known = {};"
    line $"pub const FuncType = %s{zigType k.FnTy};"

    if k.NCaptures > 0 then
        let capFields =
            match fns.TryGetValue k.Target with
            | true, fn ->
                let inst =
                    if fn.TypeParams.Length = k.TypeArgs.Length then
                        Map.ofList (List.zip fn.TypeParams k.TypeArgs)
                    else
                        Map.empty

                fn.Params
                |> List.take k.NCaptures
                |> List.mapi (fun i p -> $"c%d{i}: %s{zigType (substTy inst p.Ty)}")
            | _ -> k.CaptureTys |> List.mapi (fun i t -> $"c%d{i}: %s{zigType t}")

        let capDecls = capFields |> String.concat ", "
        line $"caps: struct {{ %s{capDecls} }},"

    let boolTuple (ms: Mode list) =
        match ms with
        | [] -> ".{}"
        | _ ->
            ms
            |> List.map (fun m ->
                if m = MBorrowed then
                    "true"
                else
                    "false"
            )
            |> String.concat ", "
            |> sprintf ".{ %s }"

    match fns.TryGetValue k.Target with
    | true, fn ->
        let captured, rest = List.splitAt k.NCaptures (List.zip fn.Params fn.Modes)
        line $"pub const borrows = %s{boolTuple (rest |> List.map snd)};"

        let rb =
            if fn.RetFrom.IsSome then
                "true"
            else
                "false"

        line $"pub const result_borrowed = %s{rb};"

        let targetRef = fnRef k.Target k.TypeArgs

        line $"pub inline fn call(%s{selfParam}) @typeInfo(@TypeOf(%s{targetRef})).@\"fn\".return_type.? {{"

        if k.NCaptures = 0 then
            line "    _ = self;"

        let capturedArgs =
            captured
            |> List.mapi (fun i (_, m) ->
                if m = MOwned then
                    dupCode $"self.caps.c%d{i}"
                else
                    $"self.caps.c%d{i}"
            )

        let callArgs = capturedArgs @ pNames |> String.concat ", "
        line $"    return %s{targetRef}(%s{callArgs});"
        line "}"

        match k.Target2, k.FnTy with
        | Some t2, TFn([ tyA ], TFn([ tyB ], _)) ->
            match fns.TryGetValue t2 with
            | true, fn2 ->
                let captured2, rest2 = List.splitAt k.NCaptures (List.zip fn2.Params fn2.Modes)
                line $"pub const borrows2 = %s{boolTuple (rest2 |> List.map snd)};"

                let rb2 =
                    if fn2.RetFrom.IsSome then
                        "true"
                    else
                        "false"

                line $"pub const result_borrowed2 = %s{rb2};"

                let target2Ref = fnRef t2 k.TypeArgs

                line
                    $"pub inline fn call2(self: *const @This(), a0: %s{zigType tyA}, a1: %s{zigType tyB}) @typeInfo(@TypeOf(%s{target2Ref})).@\"fn\".return_type.? {{"

                if k.NCaptures = 0 then
                    line "    _ = self;"

                let capturedArgs2 =
                    captured2
                    |> List.mapi (fun i (_, m) ->
                        if m = MOwned then
                            dupCode $"self.caps.c%d{i}"
                        else
                            $"self.caps.c%d{i}"
                    )

                let callArgs2 = capturedArgs2 @ [ "a0"; "a1" ] |> String.concat ", "
                line $"    return %s{target2Ref}(%s{callArgs2});"
                line "}"
            | _ -> ()
        | _ -> ()
    | _ ->
        let falseBorrows =
            match argTys with
            | [] -> ".{}"
            | _ -> argTys |> List.map (fun _ -> "false") |> String.concat ", " |> sprintf ".{ %s }"

        line $"pub const borrows = %s{falseBorrows};"
        line "pub const result_borrowed = false;"
        let targetRef = fnRef k.Target k.TypeArgs

        line $"pub inline fn call(%s{selfParam}) @typeInfo(@TypeOf(%s{targetRef})).@\"fn\".return_type.? {{"

        if k.NCaptures = 0 then
            line "    _ = self;"

        let capturedArgs = k.CaptureTys |> List.mapi (fun i _ -> $"self.caps.c%d{i}")

        if
            isManaged ret
            || argTys |> List.exists isManaged
            || k.CaptureTys |> List.exists isManaged
        then
            let uses =
                (k.CaptureTys
                 |> List.map (fun t ->
                     if isManaged t then
                         ".keep"
                     else
                         ".plain"
                 ))
                @ (argTys
                   |> List.map (fun t ->
                       if isManaged t then
                           ".give"
                       else
                           ".plain"
                   ))
                |> String.concat ", "
                |> sprintf ".{ %s }"

            let allArgs = capturedArgs @ pNames

            let argsTuple =
                match allArgs with
                | [] -> ".{}"
                | _ -> allArgs |> String.concat ", " |> sprintf ".{ %s }"

            line $"    return fable_rt.across(%s{targetRef}, %s{sigName k.Target}, %s{uses}, %s{argsTuple});"
        else
            let argList = String.concat ", " (capturedArgs @ pNames)
            line $"    return %s{targetRef}(%s{argList});"

        line "}"

    if k.NeedsToFunc then
        let adapter =
            adapterForClosure adapters k.Target k.Target2 k.TypeArgs k.CaptureTys k.FnTy

        let ans = adapterRef adapter
        let suppressTcode = noTcFile || noTailCalls.Contains k.Target
        line "pub fn toFunc(self: @This()) FuncType {"

        if suppressTcode then
            if k.NCaptures = 0 then
                line "    _ = self;"

                if adapter.Target2.IsSome then
                    line $"    return .{{ .env = null, .code = %s{ans}.code, .code2 = %s{ans}.code2 }};"
                else
                    line $"    return .{{ .env = null, .code = %s{ans}.code }};"
            else
                let inits =
                    k.CaptureTys
                    |> List.mapi (fun i t ->
                        let v =
                            if isManaged t then
                                dupCode $"self.caps.c%d{i}"
                            else
                                $"self.caps.c%d{i}"

                        $".c%d{i} = %s{v}"
                    )
                    |> String.concat ", "

                if adapter.Target2.IsSome then
                    line
                        $"    return fable_rt.closure2(FuncType, %s{ans}.Env, .{{ %s{inits} }}, %s{ans}.code, %s{ans}.code2);"
                else
                    line $"    return fable_rt.closure(FuncType, %s{ans}.Env, .{{ %s{inits} }}, %s{ans}.code);"
        else
            adapter.NeedsTcode <- true
            let paramTysStr = argTys |> List.map zigType |> String.concat ", "

            let tcodeExpr =
                $"if (comptime fable_rt.fitsTailArgs(&.{{ %s{paramTysStr} }})) &%s{ans}.tcode else null"

            if k.NCaptures = 0 then
                line "    _ = self;"

                if adapter.Target2.IsSome then
                    let tcode2Expr =
                        match k.FnTy with
                        | TFn([ tyA ], TFn([ tyB ], _)) ->
                            $"if (comptime fable_rt.fitsTailArgs(&.{{ %s{zigType tyA}, %s{zigType tyB} }})) &%s{ans}.tcode2 else null"
                        | _ -> "null"

                    line
                        $"    return .{{ .env = null, .code = %s{ans}.code, .code2 = %s{ans}.code2, .tcode = %s{tcodeExpr}, .tcode2 = %s{tcode2Expr} }};"
                else
                    line $"    return .{{ .env = null, .code = %s{ans}.code, .tcode = %s{tcodeExpr} }};"
            else
                let inits =
                    k.CaptureTys
                    |> List.mapi (fun i t ->
                        let v =
                            if isManaged t then
                                dupCode $"self.caps.c%d{i}"
                            else
                                $"self.caps.c%d{i}"

                        $".c%d{i} = %s{v}"
                    )
                    |> String.concat ", "

                if adapter.Target2.IsSome then
                    let tcode2Expr =
                        match k.FnTy with
                        | TFn([ tyA ], TFn([ tyB ], _)) ->
                            $"if (comptime fable_rt.fitsTailArgs(&.{{ %s{zigType tyA}, %s{zigType tyB} }})) &%s{ans}.tcode2 else null"
                        | _ -> "null"

                    line
                        $"    return fable_rt.closure2Tc(FuncType, %s{ans}.Env, .{{ %s{inits} }}, %s{ans}.code, %s{ans}.code2, %s{tcodeExpr}, %s{tcode2Expr});"
                else
                    line
                        $"    return fable_rt.closureTc(FuncType, %s{ans}.Env, .{{ %s{inits} }}, %s{ans}.code, %s{tcodeExpr});"

        line "}"

    if k.Gens.IsEmpty then
        out.AppendLine("};") |> ignore
    else
        out.AppendLine("    };").AppendLine("}") |> ignore

    out.AppendLine() |> ignore

/// Emit a stack-allocated `KnownIface` descriptor for non-escaping interface / object-expression HOF parameters.
let emitKnownIfaceDecl
    (out: StringBuilder)
    (fns: Dictionary<string, FnInfo>)
    (ifaceVts: Dictionary<string, IfaceVt>)
    (k: KnownIfaceDecl)
    =
    let line (text: string) = out.AppendLine(text) |> ignore

    match k.Gens with
    | [] -> line $"const %s{k.Name} = struct {{"
    | gens ->
        let comptimeParams =
            gens
            |> List.map (fun g -> $"comptime %s{genName g}: type")
            |> String.concat ", "

        line $"fn %s{k.Name}(%s{comptimeParams}) type {{"
        line "    return struct {"

    let ind =
        if k.Gens.IsEmpty then
            "    "
        else
            "        "

    let line (text: string) = line (ind + text)

    let funcTypeZig =
        if k.IsOpt then
            "?" + zigType k.IfaceTy
        else
            zigType k.IfaceTy

    line "pub const fable_known = {};"
    line "pub const fable_known_iface = {};"
    line $"pub const FuncType = %s{funcTypeZig};"

    match k.Kind with
    | IVtObj -> line "val: fable_rt.Obj,"
    | IVtBox valTy -> line $"val: %s{zigType valTy},"
    | IVtCaptures [] -> ()
    | IVtCaptures capTys ->
        let capDecls =
            capTys |> List.mapi (fun i t -> $"c%d{i}: %s{zigType t}") |> String.concat ", "

        line $"caps: struct {{ %s{capDecls} }},"
    | IVtUpcast _ -> fail None "internal: KnownIface cannot wrap upcast"

    let boolTuple (ms: Mode list) =
        match ms with
        | [] -> ".{}"
        | _ ->
            ms
            |> List.map (fun m ->
                if m = MBorrowed then
                    "true"
                else
                    "false"
            )
            |> String.concat ", "
            |> sprintf ".{ %s }"

    let slotTys = caseFields k.IfaceTy "" |> dict

    let prefixCount =
        match k.Kind with
        | IVtObj
        | IVtBox _ -> 1
        | IVtCaptures capTys -> capTys.Length
        | IVtUpcast _ -> 0

    for (slotName, (targetFn, typeArgs)) in k.Slots do
        let argTys, ret =
            match slotTys.TryGetValue slotName with
            | true, (TSlot(argTys, ret) | TFn(argTys, ret)) -> argTys, ret
            | _ -> fail None "internal: missing slot `%s` on interface `%A`" slotName k.IfaceTy

        let cleanSlot = cleanIdent slotName
        let ps = argTys |> List.mapi (fun i t -> $"a%d{i}", t)
        let pNames = ps |> List.map fst

        let paramDecls = ps |> List.map (fun (n, t) -> $"%s{n}: %s{zigType t}")

        let selfParam = "self: *const @This()" :: paramDecls |> String.concat ", "
        let targetRef = fnRef targetFn typeArgs
        let slotPubName = $"@\"slot_%s{cleanSlot}\""
        let borrowsPubName = $"@\"slot_%s{cleanSlot}$borrows\""
        let resBorrowedPubName = $"@\"slot_%s{cleanSlot}$result_borrowed\""

        match fns.TryGetValue targetFn with
        | true, fn ->
            let inst =
                if fn.TypeParams.Length = typeArgs.Length then
                    Map.ofList (List.zip fn.TypeParams typeArgs)
                else
                    Map.empty

            let captured, rest = List.splitAt prefixCount (List.zip fn.Params fn.Modes)
            line $"pub const %s{borrowsPubName} = %s{boolTuple (rest |> List.map snd)};"

            let rb =
                if fn.RetFrom.IsSome then
                    "true"
                else
                    "false"

            line $"pub const %s{resBorrowedPubName} = %s{rb};"

            line
                $"pub inline fn %s{slotPubName}(%s{selfParam}) @typeInfo(@TypeOf(%s{targetRef})).@\"fn\".return_type.? {{"

            let prefixArgs =
                match k.Kind with
                | IVtObj ->
                    let (_, thisMode) = captured.Head

                    [
                        if thisMode = MOwned then
                            dupCode "self.val"
                        else
                            "self.val"
                    ]
                | IVtBox _ ->
                    let (thisParam, thisMode) = captured.Head

                    let thisIsPtr =
                        match substTy inst thisParam.Ty with
                        | TPtr _ -> true
                        | _ -> false

                    [
                        if thisIsPtr then
                            "&self.val"
                        elif thisMode = MOwned then
                            dupCode "self.val"
                        else
                            "self.val"
                    ]
                | IVtCaptures [] ->
                    line "    _ = self;"
                    []
                | IVtCaptures _ ->
                    captured
                    |> List.mapi (fun i (_, m) ->
                        if m = MOwned then
                            dupCode $"self.caps.c%d{i}"
                        else
                            $"self.caps.c%d{i}"
                    )
                | IVtUpcast _ -> []

            let callArgs = prefixArgs @ pNames |> String.concat ", "
            line $"    return %s{targetRef}(%s{callArgs});"
            line "}"
        | _ ->
            let falseBorrows =
                match argTys with
                | [] -> ".{}"
                | _ -> argTys |> List.map (fun _ -> "false") |> String.concat ", " |> sprintf ".{ %s }"

            line $"pub const %s{borrowsPubName} = %s{falseBorrows};"
            line $"pub const %s{resBorrowedPubName} = false;"

            line
                $"pub inline fn %s{slotPubName}(%s{selfParam}) @typeInfo(@TypeOf(%s{targetRef})).@\"fn\".return_type.? {{"

            let prefixArgs, prefixTys =
                match k.Kind with
                | IVtObj -> [ "self.val" ], [ TPrim "fable_rt.Obj" ]
                | IVtCaptures [] ->
                    line "    _ = self;"
                    [], []
                | IVtCaptures capTys -> (capTys |> List.mapi (fun i _ -> $"self.caps.c%d{i}")), capTys
                | IVtBox _
                | IVtUpcast _ -> fail None "internal: cross-file boxed/upcast KnownIface not supported"

            if
                isManaged ret
                || argTys |> List.exists isManaged
                || prefixTys |> List.exists isManaged
            then
                let uses =
                    (prefixTys
                     |> List.map (fun t ->
                         if isManaged t then
                             ".keep"
                         else
                             ".plain"
                     ))
                    @ (argTys
                       |> List.map (fun t ->
                           if isManaged t then
                               ".give"
                           else
                               ".plain"
                       ))
                    |> String.concat ", "
                    |> sprintf ".{ %s }"

                let allArgs = prefixArgs @ pNames

                let argsTuple =
                    match allArgs with
                    | [] -> ".{}"
                    | _ -> allArgs |> String.concat ", " |> sprintf ".{ %s }"

                line $"    return fable_rt.across(%s{targetRef}, %s{sigName targetFn}, %s{uses}, %s{argsTuple});"
            else
                let argList = String.concat ", " (prefixArgs @ pNames)
                line $"    return %s{targetRef}(%s{argList});"

            line "}"

    if k.NeedsToFunc then
        let srcKey, srcTys =
            match k.Kind with
            | IVtObj -> "obj", []
            | IVtBox valTy -> "box:" + tyKey valTy, [ valTy ]
            | IVtCaptures capTys -> "cap:" + (capTys |> List.map tyKey |> String.concat ","), capTys
            | IVtUpcast _ -> "", []

        let vt = ifaceVtFor ifaceVts k.IfaceTy k.Kind srcKey srcTys k.Slots
        let vns = ifaceVtRef vt
        let ifaceZ = zigType k.IfaceTy
        line "pub fn toFunc(self: @This()) FuncType {"

        match k.Kind with
        | IVtObj -> line $"    return %s{ifaceZ}{{ .data = @ptrCast(fable_rt.dup(self.val)), .vt = &%s{vns}.vt }};"
        | IVtBox valTy ->
            let valExpr =
                if isManaged valTy then
                    dupCode "self.val"
                else
                    "self.val"

            line $"    return fable_rt.ifaceBox(%s{ifaceZ}, %s{zigType valTy}, %s{valExpr}, &%s{vns}.vt);"
        | IVtCaptures [] ->
            line "    _ = self;"
            line $"    return %s{ifaceZ}{{ .data = null, .vt = &%s{vns}.vt }};"
        | IVtCaptures capTys ->
            let inits =
                capTys
                |> List.mapi (fun i t ->
                    let v =
                        if isManaged t then
                            dupCode $"self.caps.c%d{i}"
                        else
                            $"self.caps.c%d{i}"

                    $".c%d{i} = %s{v}"
                )
                |> String.concat ", "

            line $"    return fable_rt.ifaceClosure(%s{ifaceZ}, %s{vns}.Env, .{{ %s{inits} }}, &%s{vns}.vt);"
        | IVtUpcast _ -> ()

        line "}"

    if k.Gens.IsEmpty then
        out.AppendLine("};") |> ignore
    else
        out.AppendLine("    };").AppendLine("}") |> ignore

    out.AppendLine() |> ignore

/// Emit a static vtable struct (and optional captured `Env`) for a fat-pointer interface.
let emitIfaceVt
    (out: StringBuilder)
    (fableAliases: HashSet<string>)
    (noTcFile: bool)
    (noTcFns: HashSet<string>)
    (fns: Dictionary<string, FnInfo>)
    (vt: IfaceVt)
    =
    let line (text: string) = out.AppendLine(text) |> ignore

    match vt.Gens with
    | [] -> line $"const %s{vt.Name} = struct {{"
    | gens ->
        let comptimeParams =
            gens
            |> List.map (fun g -> $"comptime %s{genName g}: type")
            |> String.concat ", "

        line $"fn %s{vt.Name}(%s{comptimeParams}) type {{"
        line "    return struct {"

    let ind =
        if vt.Gens.IsEmpty then
            "    "
        else
            "        "

    let line (text: string) = line (ind + text)

    let finishInd (extra: string) (call: string) (resultBorrowed: bool) (dropAfter: string list) =
        let drops = dropAfter |> List.map (fun n -> dropCode n + " ") |> String.concat ""
        line $"%s{extra}    const raw = %s{call};"

        line
            $"%s{extra}    const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch |err| {{ %s{drops}return err; }} else raw;"

        let result =
            if resultBorrowed then
                dupCode "r"
            else
                "r"

        if dropAfter.IsEmpty then
            line $"%s{extra}    return %s{result};"
        else
            line $"%s{extra}    const result = %s{result};"

            for name in dropAfter do
                line ($"%s{extra}    " + dropCode name)

            line $"%s{extra}    return result;"

    let tuple (items: string list) =
        match items with
        | [] -> ".{}"
        | _ -> items |> String.concat ", " |> sprintf ".{ %s }"

    match vt.Kind with
    | IVtCaptures capTys when not capTys.IsEmpty ->
        let fields =
            capTys |> List.mapi (fun i t -> $"c%d{i}: %s{zigType t}") |> String.concat ", "

        line $"const Env = struct {{ %s{fields} }};"
    | _ -> ()

    let slotTys = caseFields vt.IfaceTy "" |> dict

    for (slotIdx, (slotName, (targetFn, typeArgs))) in List.indexed vt.Slots do
        let argTys, ret =
            match slotTys.TryGetValue slotName with
            | true, (TSlot(argTys, ret) | TFn(argTys, ret)) -> argTys, ret
            | _ -> fail None "internal: missing slot `%s` on interface `%A`" slotName vt.IfaceTy

        let wrapperName = $"@\"slot_%d{slotIdx}_%s{cleanIdent slotName}\""
        let ps = argTys |> List.mapi (fun i t -> $"a%d{i}", t)

        let sigParams =
            "d: ?*anyopaque" :: (ps |> List.map (fun (n, t) -> $"%s{n}: %s{zigType t}"))
            |> String.concat ", "

        line $"fn %s{wrapperName}(%s{sigParams}) fable_rt.Raised!%s{zigType ret} {{"

        match vt.Kind with
        | IVtUpcast subTy ->
            line $"    const sub = fable_rt.boxed(%s{zigType subTy}, @ptrCast(@alignCast(d.?))).value;"
            let callArgs = "sub.data" :: (ps |> List.map fst) |> String.concat ", "
            line $"    return sub.vt.%s{fieldIdent targetFn}(%s{callArgs});"
        | IVtObj ->
            line "    const self: fable_rt.Obj = @ptrCast(@alignCast(d.?));"

            match fns.TryGetValue targetFn with
            | true, fn ->
                let inst =
                    if fn.TypeParams.Length = typeArgs.Length then
                        Map.ofList (List.zip fn.TypeParams typeArgs)
                    else
                        Map.empty

                ignore inst

                match List.zip fn.Params fn.Modes with
                | (_, thisMode) :: rest ->
                    let a0 =
                        if thisMode = MOwned then
                            dupCode "self"
                        else
                            "self"

                    let args = a0 :: (ps |> List.map fst) |> String.concat ", "

                    let dropAfter =
                        List.zip ps rest
                        |> List.choose (fun ((n, _), (_, m)) ->
                            if m = MBorrowed then
                                Some n
                            else
                                None
                        )

                    finishInd "" $"%s{fnRef targetFn typeArgs}(%s{args})" fn.RetFrom.IsSome dropAfter
                | [] -> fail None "internal: object interface method `%s` has no self parameter" targetFn
            | _ ->
                let uses =
                    ".keep"
                    :: (argTys
                        |> List.map (fun t ->
                            if isManaged t then
                                ".give"
                            else
                                ".plain"
                        ))

                let callArgs = tuple ("self" :: (ps |> List.map fst))

                finishInd
                    ""
                    $"fable_rt.across(%s{fnRef targetFn typeArgs}, %s{sigName targetFn}, %s{tuple uses}, %s{callArgs})"
                    false
                    []
        | IVtBox valTy ->
            let valZ = zigType valTy
            line $"    const box_ptr = fable_rt.boxed(%s{valZ}, @ptrCast(@alignCast(d.?)));"

            match fns.TryGetValue targetFn with
            | true, fn ->
                let inst =
                    if fn.TypeParams.Length = typeArgs.Length then
                        Map.ofList (List.zip fn.TypeParams typeArgs)
                    else
                        Map.empty

                match List.zip fn.Params fn.Modes with
                | (thisParam, thisMode) :: rest ->
                    let thisIsPtr =
                        match substTy inst thisParam.Ty with
                        | TPtr _ -> true
                        | _ -> false

                    let a0 =
                        if thisIsPtr then
                            "&box_ptr.value"
                        elif thisMode = MOwned then
                            dupCode "box_ptr.value"
                        else
                            "box_ptr.value"

                    let args = a0 :: (ps |> List.map fst) |> String.concat ", "

                    let dropAfter =
                        List.zip ps rest
                        |> List.choose (fun ((n, _), (_, m)) ->
                            if m = MBorrowed then
                                Some n
                            else
                                None
                        )

                    finishInd "" $"%s{fnRef targetFn typeArgs}(%s{args})" fn.RetFrom.IsSome dropAfter
                | [] -> fail None "internal: boxed interface method `%s` has no self parameter" targetFn
            | _ ->
                let target = fnRef targetFn typeArgs
                line $"    const SelfP = @typeInfo(@TypeOf(%s{target})).@\"fn\".param_types[0].?;"
                line $"    if (comptime SelfP == *%s{valZ} or SelfP == *const %s{valZ}) {{"

                if isManaged ret || argTys |> List.exists isManaged then
                    let ptrUses =
                        ".plain"
                        :: (argTys
                            |> List.map (fun t ->
                                if isManaged t then
                                    ".give"
                                else
                                    ".plain"
                            ))

                    let callArgs = tuple ("&box_ptr.value" :: (ps |> List.map fst))

                    finishInd
                        "    "
                        $"fable_rt.across(%s{target}, %s{sigName targetFn}, %s{tuple ptrUses}, %s{callArgs})"
                        false
                        []
                else
                    let args = "&box_ptr.value" :: (ps |> List.map fst) |> String.concat ", "
                    finishInd "    " $"%s{target}(%s{args})" false []

                line "    } else {"

                if isManaged valTy || isManaged ret || argTys |> List.exists isManaged then
                    let valUses =
                        (if isManaged valTy then
                             ".keep"
                         else
                             ".plain")
                        :: (argTys
                            |> List.map (fun t ->
                                if isManaged t then
                                    ".give"
                                else
                                    ".plain"
                            ))

                    let callArgs = tuple ("box_ptr.value" :: (ps |> List.map fst))

                    finishInd
                        "    "
                        $"fable_rt.across(%s{target}, %s{sigName targetFn}, %s{tuple valUses}, %s{callArgs})"
                        false
                        []
                else
                    let args = "box_ptr.value" :: (ps |> List.map fst) |> String.concat ", "
                    finishInd "    " $"%s{target}(%s{args})" false []

                line "    }"
        | IVtCaptures capTys ->
            if capTys.IsEmpty then
                line "    _ = d;"
            else
                line "    const c = fable_rt.captured(Env, @ptrCast(@alignCast(d)));"

            match fns.TryGetValue targetFn with
            | true, fn ->
                let captured, rest = List.splitAt capTys.Length (List.zip fn.Params fn.Modes)

                let capturedArgs =
                    captured
                    |> List.mapi (fun i (_, m) ->
                        if m = MOwned then
                            dupCode $"c.c%d{i}"
                        else
                            $"c.c%d{i}"
                    )

                let args = capturedArgs @ (ps |> List.map fst) |> String.concat ", "

                let dropAfter =
                    List.zip ps rest
                    |> List.choose (fun ((n, _), (_, m)) ->
                        if m = MBorrowed then
                            Some n
                        else
                            None
                    )

                finishInd "" $"%s{fnRef targetFn typeArgs}(%s{args})" fn.RetFrom.IsSome dropAfter
            | _ ->
                let capturedArgs = capTys |> List.mapi (fun i _ -> $"c.c%d{i}")

                if
                    isManaged ret
                    || argTys |> List.exists isManaged
                    || capTys |> List.exists isManaged
                then
                    let uses =
                        (capTys
                         |> List.map (fun t ->
                             if isManaged t then
                                 ".keep"
                             else
                                 ".plain"
                         ))
                        @ (argTys
                           |> List.map (fun t ->
                               if isManaged t then
                                   ".give"
                               else
                                   ".plain"
                           ))

                    finishInd
                        ""
                        $"fable_rt.across(%s{fnRef targetFn typeArgs}, %s{sigName targetFn}, %s{tuple uses}, %s{tuple (capturedArgs @ (ps |> List.map fst))})"
                        false
                        []
                else
                    let args = capturedArgs @ (ps |> List.map fst) |> String.concat ", "
                    finishInd "" $"%s{fnRef targetFn typeArgs}(%s{args})" false []

        line "}"

        if not noTcFile then
            let tcWrapperName = $"@\"slot_%d{slotIdx}_%s{cleanIdent slotName}$tc\""
            let retZig = zigType ret
            let voidRet = isVoid ret
            let argTysStr = argTys |> List.map zigType |> String.concat ", "
            let loadArgs = ps |> List.mapi (fun i _ -> $"_tca[%d{i}]")

            let emitFailTailStatus (pad: string) (extraDrop: string option) =
                Option.iter (fun s -> line $"%s{pad}%s{s}") extraDrop
                line $"%s{pad}fable_rt.plugRet(%s{retZig}, ret);"
                line $"%s{pad}return .raised;"

            let emitOkTailStatus (pad: string) (resIdent: string) (dropsAfter: string list) (extraDrop: string option) =
                if voidRet then
                    line $"%s{pad}_ = %s{resIdent};"
                else
                    line $"%s{pad}const _tc_res = %s{resIdent};"

                for d in dropsAfter do
                    line ($"%s{pad}" + dropCode d)

                Option.iter (fun s -> line $"%s{pad}%s{s}") extraDrop

                if not voidRet then
                    line $"%s{pad}@as(*%s{retZig}, @ptrCast(@alignCast(ret))).* = _tc_res;"

                line $"%s{pad}return .ok;"

            let emitKnownBody
                (pad: string)
                (capArgsOwned: string list)
                (capArgsForDirect: (string * Mode) list)
                (selfDropOpt: string option)
                =
                let emitDirectFn (fn: FnInfo) (p: string) =
                    let directCaps =
                        capArgsForDirect
                        |> List.map (fun (expr, m) ->
                            if m = MOwned then
                                dupCode expr
                            else
                                expr
                        )

                    let allArgs = directCaps @ loadArgs |> String.concat ", "
                    let argModes = fn.Modes |> List.skip capArgsForDirect.Length

                    let dropAfter =
                        List.zip loadArgs argModes
                        |> List.choose (fun (n, m) ->
                            if m = MBorrowed then
                                Some n
                            else
                                None
                        )

                    line $"%s{p}const raw = %s{fnRef targetFn typeArgs}(%s{allArgs});"
                    line $"%s{p}const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"

                    for d in dropAfter do
                        line ($"%s{p}    " + dropCode d)

                    emitFailTailStatus (p + "    ") selfDropOpt
                    line $"%s{p}}} else raw;"

                    let resExpr =
                        if fn.RetFrom.IsSome && not voidRet then
                            dupCode "r"
                        else
                            "r"

                    if fn.RetFrom.IsSome && not voidRet then
                        line $"%s{p}const r_own = %s{resExpr};"
                        emitOkTailStatus p "r_own" dropAfter selfDropOpt
                    else
                        emitOkTailStatus p "r" dropAfter selfDropOpt

                let emitTcBodyCall (p: string) =
                    let capVars =
                        capArgsOwned
                        |> List.mapi (fun i expr ->
                            let cv = $"_tc_cap%d{i}"
                            line $"%s{p}const %s{cv} = %s{expr};"
                            cv
                        )

                    Option.iter (fun s -> line $"%s{p}%s{s}") selfDropOpt
                    let allArgs = capVars @ loadArgs |> String.concat ", "
                    line $"%s{p}const _next = %s{fnTcBodyRef targetFn typeArgs}(ctx, ret, %s{allArgs}) catch {{"
                    line $"%s{p}    fable_rt.plugRet(%s{retZig}, ret);"
                    line $"%s{p}    return .raised;"
                    line $"%s{p}}};"
                    line $"%s{p}if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{{ ctx, _next.ret }});"
                    line $"%s{p}return .ok;"

                match fns.TryGetValue targetFn with
                | true, fn when not (noTcFns.Contains targetFn) && fnHasTcBody fn ->
                    if fn.NeedsChain then
                        emitTcBodyCall pad
                    else
                        line $"%s{pad}if (comptime %s{chainName targetFn}) {{"
                        emitTcBodyCall (pad + "    ")
                        line $"%s{pad}}} else {{"
                        emitDirectFn fn (pad + "    ")
                        line $"%s{pad}}}"
                | true, fn -> emitDirectFn fn pad
                | _ -> fail None "internal: expected same-file fn"

            let emitWithArgs (bodyFn: string -> unit) =
                if argTys.IsEmpty then
                    bodyFn "    "
                else
                    line $"    if (comptime fable_rt.fitsTailArgs(&.{{ %s{argTysStr} }})) {{"
                    line $"        const _tca = fable_rt.tailLoad(&.{{ %s{argTysStr} }}, ctx);"
                    bodyFn "        "
                    line "    } else {"
                    line "        unreachable;"
                    line "    }"

            line $"fn %s{tcWrapperName}(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {{"

            match vt.Kind with
            | IVtUpcast subTy ->
                line "    const _ts = fable_rt.takeSelfBorrowed(ctx);"
                line $"    const sub = fable_rt.boxed(%s{zigType subTy}, @ptrCast(@alignCast(_ts.ptr.?))).value;"
                line $"    if (sub.vt.@\"%s{cleanIdent targetFn}$tc\") |tcfn| {{"
                line "        _ = fable_rt.dup(sub);"
                line "        if (_ts.owned) fable_rt.obj_iface_meta.drop(_ts.ptr);"
                line "        ctx.self = sub.data;"
                line "        ctx.self_owned = true;"
                line "        return @call(fable_rt.tail_call, tcfn, .{ ctx, ret });"
                line "    }"

                emitWithArgs (fun pad ->
                    let callArgs = "sub.data" :: loadArgs |> String.concat ", "
                    let selfDrop = Some "if (_ts.owned) fable_rt.obj_iface_meta.drop(_ts.ptr);"
                    line $"%s{pad}const raw = sub.vt.%s{fieldIdent targetFn}(%s{callArgs});"
                    line $"%s{pad}const r = raw catch {{"
                    emitFailTailStatus (pad + "    ") selfDrop
                    line $"%s{pad}}};"
                    emitOkTailStatus pad "r" [] selfDrop
                )
            | IVtObj ->
                line "    const _ts = fable_rt.takeSelfBorrowed(ctx);"
                line "    const self: fable_rt.Obj = @ptrCast(@alignCast(_ts.ptr.?));"

                emitWithArgs (fun pad ->
                    let dropSelf = dropCode "self"
                    let dupSelf = dupCode "self"
                    let dupR = dupCode "r"
                    let selfDrop = Some $"if (_ts.owned) %s{dropSelf}"

                    match fns.TryGetValue targetFn with
                    | true, fn ->
                        let thisMode =
                            match fn.Modes with
                            | m :: _ -> m
                            | [] -> fail None "internal: object interface method `%s` has no self parameter" targetFn

                        let ownSelfArg = $"if (_ts.owned) self else %s{dupSelf}"

                        if not (noTcFns.Contains targetFn) && fnHasTcBody fn then
                            if fn.NeedsChain then
                                line $"%s{pad}const _self_own: fable_rt.Obj = %s{ownSelfArg};"
                                let allArgs = "_self_own" :: loadArgs |> String.concat ", "

                                line
                                    $"%s{pad}const _next = %s{fnTcBodyRef targetFn typeArgs}(ctx, ret, %s{allArgs}) catch {{"

                                line $"%s{pad}    fable_rt.plugRet(%s{retZig}, ret);"
                                line $"%s{pad}    return .raised;"
                                line $"%s{pad}}};"

                                line
                                    $"%s{pad}if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{{ ctx, _next.ret }});"

                                line $"%s{pad}return .ok;"
                            else
                                line $"%s{pad}if (comptime %s{chainName targetFn}) {{"
                                line $"%s{pad}    const _self_own: fable_rt.Obj = %s{ownSelfArg};"
                                let allArgs = "_self_own" :: loadArgs |> String.concat ", "

                                line
                                    $"%s{pad}    const _next = %s{fnTcBodyRef targetFn typeArgs}(ctx, ret, %s{allArgs}) catch {{"

                                line $"%s{pad}        fable_rt.plugRet(%s{retZig}, ret);"
                                line $"%s{pad}        return .raised;"
                                line $"%s{pad}    }};"

                                line
                                    $"%s{pad}    if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{{ ctx, _next.ret }});"

                                line $"%s{pad}    return .ok;"
                                line $"%s{pad}}} else {{"

                                let a0 =
                                    if thisMode = MOwned then
                                        ownSelfArg
                                    else
                                        "self"

                                let directDrop =
                                    if thisMode = MOwned then
                                        None
                                    else
                                        selfDrop

                                let dropAfter =
                                    List.zip loadArgs (List.tail fn.Modes)
                                    |> List.choose (fun (n, m) ->
                                        if m = MBorrowed then
                                            Some n
                                        else
                                            None
                                    )

                                let args = a0 :: loadArgs |> String.concat ", "
                                line $"%s{pad}    const raw = %s{fnRef targetFn typeArgs}(%s{args});"
                                line $"%s{pad}    const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"

                                for d in dropAfter do
                                    line ($"%s{pad}        " + dropCode d)

                                emitFailTailStatus (pad + "        ") directDrop
                                line $"%s{pad}    }} else raw;"

                                if fn.RetFrom.IsSome && not voidRet then
                                    line $"%s{pad}    const r_own = %s{dupR};"
                                    emitOkTailStatus (pad + "    ") "r_own" dropAfter directDrop
                                else
                                    emitOkTailStatus (pad + "    ") "r" dropAfter directDrop

                                line $"%s{pad}}}"
                        else
                            let a0 =
                                if thisMode = MOwned then
                                    ownSelfArg
                                else
                                    "self"

                            let directDrop =
                                if thisMode = MOwned then
                                    None
                                else
                                    selfDrop

                            let dropAfter =
                                List.zip loadArgs (List.tail fn.Modes)
                                |> List.choose (fun (n, m) ->
                                    if m = MBorrowed then
                                        Some n
                                    else
                                        None
                                )

                            let args = a0 :: loadArgs |> String.concat ", "
                            line $"%s{pad}const raw = %s{fnRef targetFn typeArgs}(%s{args});"
                            line $"%s{pad}const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"

                            for d in dropAfter do
                                line ($"%s{pad}    " + dropCode d)

                            emitFailTailStatus (pad + "    ") directDrop
                            line $"%s{pad}}} else raw;"

                            if fn.RetFrom.IsSome && not voidRet then
                                line $"%s{pad}const r_own = %s{dupR};"
                                emitOkTailStatus pad "r_own" dropAfter directDrop
                            else
                                emitOkTailStatus pad "r" dropAfter directDrop
                    | _ ->
                        let uses =
                            ".keep"
                            :: (argTys
                                |> List.map (fun t ->
                                    if isManaged t then
                                        ".give"
                                    else
                                        ".plain"
                                ))

                        let usesTuple = tuple uses
                        let argsTuple = tuple ("self" :: loadArgs)

                        let callExpr =
                            $"fable_rt.across(%s{fnRef targetFn typeArgs}, %s{sigName targetFn}, %s{usesTuple}, %s{argsTuple})"

                        let emitExtFallbackObj (p: string) =
                            line $"%s{p}const raw = %s{callExpr};"
                            line $"%s{p}const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"
                            emitFailTailStatus (p + "    ") selfDrop
                            line $"%s{p}}} else raw;"
                            emitOkTailStatus p "r" [] selfDrop

                        if isExtTcAlias fableAliases fns targetFn then
                            let fullParamTysStr =
                                ("fable_rt.Obj" :: (argTys |> List.map zigType)) |> String.concat ", "

                            line
                                $"%s{pad}if (comptime (%s{extChainCheck targetFn} and fable_rt.fitsTailArgs(&.{{ %s{fullParamTysStr} }}))) {{"

                            line $"%s{pad}    const _self_own: fable_rt.Obj = if (_ts.owned) self else %s{dupSelf};"
                            let allArgs = "_self_own" :: loadArgs |> String.concat ", "

                            line
                                $"%s{pad}    fable_rt.tailStore(&.{{ %s{fullParamTysStr} }}, ctx, .{{ %s{allArgs} }});"

                            line
                                $"%s{pad}    return @call(fable_rt.tail_call, &%s{fnRefTc targetFn typeArgs}, .{{ ctx, ret }});"

                            line $"%s{pad}}} else {{"
                            emitExtFallbackObj (pad + "    ")
                            line $"%s{pad}}}"
                        else
                            emitExtFallbackObj pad
                )
            | IVtBox valTy ->
                let valZ = zigType valTy
                let dupR = dupCode "r"
                line "    const _ts = fable_rt.takeSelfBorrowed(ctx);"
                line $"    const box_ptr = fable_rt.boxed(%s{valZ}, @ptrCast(@alignCast(_ts.ptr.?)));"

                emitWithArgs (fun pad ->
                    let boxDrop = Some "if (_ts.owned) fable_rt.box_iface_meta.drop(_ts.ptr);"

                    match fns.TryGetValue targetFn with
                    | true, fn ->
                        let inst =
                            if fn.TypeParams.Length = typeArgs.Length then
                                Map.ofList (List.zip fn.TypeParams typeArgs)
                            else
                                Map.empty

                        match List.zip fn.Params fn.Modes with
                        | (thisParam, thisMode) :: rest ->
                            let thisIsPtr =
                                match substTy inst thisParam.Ty with
                                | TPtr _ -> true
                                | _ -> false

                            if thisIsPtr then
                                let args = "&box_ptr.value" :: loadArgs |> String.concat ", "

                                let dropAfter =
                                    List.zip loadArgs rest
                                    |> List.choose (fun (n, (_, m)) ->
                                        if m = MBorrowed then
                                            Some n
                                        else
                                            None
                                    )

                                line $"%s{pad}const raw = %s{fnRef targetFn typeArgs}(%s{args});"
                                line $"%s{pad}const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"

                                for d in dropAfter do
                                    line ($"%s{pad}    " + dropCode d)

                                emitFailTailStatus (pad + "    ") boxDrop
                                line $"%s{pad}}} else raw;"

                                if fn.RetFrom.IsSome && not voidRet then
                                    line $"%s{pad}const r_own = %s{dupR};"
                                    emitOkTailStatus pad "r_own" dropAfter boxDrop
                                else
                                    emitOkTailStatus pad "r" dropAfter boxDrop
                            else
                                let ownValExpr =
                                    if isManaged valTy then
                                        dupCode "box_ptr.value"
                                    else
                                        "box_ptr.value"

                                emitKnownBody pad [ ownValExpr ] [ "box_ptr.value", thisMode ] boxDrop
                        | [] -> fail None "internal: boxed interface method `%s` has no self parameter" targetFn
                    | _ ->
                        let target = fnRef targetFn typeArgs
                        line $"%s{pad}const SelfP = @typeInfo(@TypeOf(%s{target})).@\"fn\".param_types[0].?;"
                        line $"%s{pad}if (comptime SelfP == *%s{valZ} or SelfP == *const %s{valZ}) {{"

                        let ptrCall =
                            if isManaged ret || argTys |> List.exists isManaged then
                                let ptrUses =
                                    ".plain"
                                    :: (argTys
                                        |> List.map (fun t ->
                                            if isManaged t then
                                                ".give"
                                            else
                                                ".plain"
                                        ))

                                let ptrUsesTuple = tuple ptrUses
                                let ptrArgsTuple = tuple ("&box_ptr.value" :: loadArgs)
                                $"fable_rt.across(%s{target}, %s{sigName targetFn}, %s{ptrUsesTuple}, %s{ptrArgsTuple})"
                            else
                                let args = "&box_ptr.value" :: loadArgs |> String.concat ", "
                                $"%s{target}(%s{args})"

                        line $"%s{pad}    const raw = %s{ptrCall};"
                        line $"%s{pad}    const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"
                        emitFailTailStatus (pad + "        ") boxDrop
                        line $"%s{pad}    }} else raw;"
                        emitOkTailStatus (pad + "    ") "r" [] boxDrop
                        line $"%s{pad}}} else {{"

                        let emitBoxValFallback (p: string) =
                            let valCall =
                                if isManaged valTy || isManaged ret || argTys |> List.exists isManaged then
                                    let valUses =
                                        (if isManaged valTy then
                                             ".keep"
                                         else
                                             ".plain")
                                        :: (argTys
                                            |> List.map (fun t ->
                                                if isManaged t then
                                                    ".give"
                                                else
                                                    ".plain"
                                            ))

                                    let valUsesTuple = tuple valUses
                                    let valArgsTuple = tuple ("box_ptr.value" :: loadArgs)
                                    $"fable_rt.across(%s{target}, %s{sigName targetFn}, %s{valUsesTuple}, %s{valArgsTuple})"
                                else
                                    let args = "box_ptr.value" :: loadArgs |> String.concat ", "
                                    $"%s{target}(%s{args})"

                            line $"%s{p}const raw = %s{valCall};"
                            line $"%s{p}const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"
                            emitFailTailStatus (p + "    ") boxDrop
                            line $"%s{p}}} else raw;"
                            emitOkTailStatus p "r" [] boxDrop

                        if isExtTcAlias fableAliases fns targetFn then
                            let fullParamTysStr = valTy :: argTys |> List.map zigType |> String.concat ", "

                            line
                                $"%s{pad}    if (comptime (%s{extChainCheck targetFn} and fable_rt.fitsTailArgs(&.{{ %s{fullParamTysStr} }}))) {{"

                            let ownValExpr =
                                if isManaged valTy then
                                    dupCode "box_ptr.value"
                                else
                                    "box_ptr.value"

                            line $"%s{pad}        const _val_own: %s{valZ} = %s{ownValExpr};"
                            Option.iter (fun s -> line $"%s{pad}        %s{s}") boxDrop
                            let allArgs = "_val_own" :: loadArgs |> String.concat ", "

                            line
                                $"%s{pad}        fable_rt.tailStore(&.{{ %s{fullParamTysStr} }}, ctx, .{{ %s{allArgs} }});"

                            line
                                $"%s{pad}        return @call(fable_rt.tail_call, &%s{fnRefTc targetFn typeArgs}, .{{ ctx, ret }});"

                            line $"%s{pad}    }} else {{"
                            emitBoxValFallback (pad + "        ")
                            line $"%s{pad}    }}"
                        else
                            emitBoxValFallback (pad + "    ")

                        line $"%s{pad}}}"
                )
            | IVtCaptures capTys ->
                line "    const _ts = fable_rt.takeSelfBorrowed(ctx);"

                if capTys.IsEmpty then
                    line "    _ = _ts;"
                else
                    line "    const c = fable_rt.captured(Env, @ptrCast(@alignCast(_ts.ptr.?)));"

                emitWithArgs (fun pad ->
                    let envDrop =
                        if capTys.IsEmpty then
                            None
                        else
                            Some "if (_ts.owned) fable_rt.env_iface_meta.drop(_ts.ptr);"

                    match fns.TryGetValue targetFn with
                    | true, fn ->
                        let capModes = List.take capTys.Length fn.Modes

                        let ownedCaps =
                            List.zip capTys (List.indexed capModes)
                            |> List.map (fun (capTy, (i, _)) ->
                                if isManaged capTy then
                                    dupCode $"c.c%d{i}"
                                else
                                    $"c.c%d{i}"
                            )

                        let directCaps = capModes |> List.mapi (fun i m -> $"c.c%d{i}", m)

                        emitKnownBody pad ownedCaps directCaps envDrop
                    | _ ->
                        let capArgs = capTys |> List.mapi (fun i _ -> $"c.c%d{i}")

                        let emitCapExtFallback (p: string) =
                            let callExpr =
                                if
                                    isManaged ret
                                    || argTys |> List.exists isManaged
                                    || capTys |> List.exists isManaged
                                then
                                    let uses =
                                        (capTys
                                         |> List.map (fun t ->
                                             if isManaged t then
                                                 ".keep"
                                             else
                                                 ".plain"
                                         ))
                                        @ (argTys
                                           |> List.map (fun t ->
                                               if isManaged t then
                                                   ".give"
                                               else
                                                   ".plain"
                                           ))

                                    $"fable_rt.across(%s{fnRef targetFn typeArgs}, %s{sigName targetFn}, %s{tuple uses}, %s{tuple (capArgs @ loadArgs)})"
                                else
                                    let args = capArgs @ loadArgs |> String.concat ", "
                                    $"%s{fnRef targetFn typeArgs}(%s{args})"

                            line $"%s{p}const raw = %s{callExpr};"
                            line $"%s{p}const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {{"
                            emitFailTailStatus (p + "    ") envDrop
                            line $"%s{p}}} else raw;"
                            emitOkTailStatus p "r" [] envDrop

                        if isExtTcAlias fableAliases fns targetFn then
                            let fullParamTysStr = capTys @ argTys |> List.map zigType |> String.concat ", "

                            let tcCond =
                                if fullParamTysStr = "" then
                                    extChainCheck targetFn
                                else
                                    $"%s{extChainCheck targetFn} and fable_rt.fitsTailArgs(&.{{ %s{fullParamTysStr} }})"

                            line $"%s{pad}if (comptime (%s{tcCond})) {{"

                            let ownedCaps =
                                capTys
                                |> List.mapi (fun i capTy ->
                                    let cv = $"_tc_cap%d{i}"

                                    let capExpr =
                                        if isManaged capTy then
                                            let dupCap = dupCode $"c.c%d{i}"
                                            dupCap
                                        else
                                            $"c.c%d{i}"

                                    line $"%s{pad}        const %s{cv}: %s{zigType capTy} = %s{capExpr};"
                                    cv
                                )

                            Option.iter (fun s -> line $"%s{pad}    %s{s}") envDrop

                            if fullParamTysStr <> "" then
                                let allArgs = ownedCaps @ loadArgs |> String.concat ", "

                                line
                                    $"%s{pad}    fable_rt.tailStore(&.{{ %s{fullParamTysStr} }}, ctx, .{{ %s{allArgs} }});"

                            line
                                $"%s{pad}    return @call(fable_rt.tail_call, &%s{fnRefTc targetFn typeArgs}, .{{ ctx, ret }});"

                            line $"%s{pad}}} else {{"
                            emitCapExtFallback (pad + "    ")
                            line $"%s{pad}}}"
                        else
                            emitCapExtFallback pad
                )

            line "}"

    let vtSlots =
        vt.Slots
        |> List.mapi (fun i (slotName, _) -> $".%s{fieldIdent slotName} = @\"slot_%d{i}_%s{cleanIdent slotName}\"")

    let vtTcSlots =
        if noTcFile then
            []
        else
            vt.Slots
            |> List.mapi (fun i (slotName, _) ->
                $".@\"%s{cleanIdent slotName}$tc\" = &@\"slot_%d{i}_%s{cleanIdent slotName}$tc\""
            )

    let metaExpr =
        match vt.Kind with
        | IVtObj -> "&fable_rt.obj_iface_meta"
        | IVtBox _ -> "&fable_rt.box_iface_meta"
        | IVtCaptures [] -> "&fable_rt.empty_iface_meta"
        | IVtCaptures _ -> "&fable_rt.env_iface_meta"
        | IVtUpcast subTy -> $"fable_rt.upcastIfaceMeta(%s{zigType subTy})"

    let vtFields =
        $".@\"$meta\" = %s{metaExpr}" :: (vtSlots @ vtTcSlots) |> String.concat ", "

    line $"const Vt = @typeInfo(@FieldType(%s{zigType vt.IfaceTy}, \"vt\")).pointer.child;"
    line $"const vt: Vt = .{{ %s{vtFields} }};"

    if vt.Gens.IsEmpty then
        out.AppendLine("};") |> ignore
    else
        out.AppendLine("    };").AppendLine("}") |> ignore

    out.AppendLine() |> ignore
