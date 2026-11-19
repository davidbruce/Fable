/// Function emission, thin/full `$tc` entries, fact assertions, and mutual-tail-recursion SCC state machines.
module internal Fable.Transforms.Zig.EmitFunction

open System.Collections.Generic
open System.Text
open System.Text.RegularExpressions
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.EmitExpr
open Fable.Transforms.Zig.EmitStmt

/// A name given to a part of a value (`const Head: T = x.Cons.Head;`) for a pattern whose other
/// parts were then left out may be read nowhere, which Zig rejects: such lines are removed (they
/// only read, and the part is borrowed).
let dropUnreadPaths (body: string) =
    let decl = Regex(@"^\s*const (\w+): [^=]+ = [\w.\[\]@""]+;\s*$")

    let lines = body.Split('\n')
    // (what the comments say is not a use; a `//` inside a string literal is no comment)
    let code =
        Regex.Replace(
            body,
            @"""(?:[^""\\\n]|\\.)*""|//[^\n]*",
            fun m ->
                if m.Value.StartsWith "//" then
                    ""
                else
                    m.Value
        )

    // how often each name is written, not as a field (`.name`): one walk of the text
    let counts = Dictionary<string, int>()

    for m in Regex.Matches(code, @"(?<![\w.@""])\w+") do
        let n = m.Value

        match counts.TryGetValue n with
        | true, c -> counts[n] <- c + 1
        | _ -> counts[n] <- 1

    let unread =
        lines
        |> Array.choose (fun l ->
            let m = decl.Match l

            if
                m.Success
                && (
                    match counts.TryGetValue m.Groups[1].Value with
                    | true, 1 -> true
                    | _ -> false
                )
            then
                Some l
            else
                None
        )
        |> Set.ofArray

    if unread.IsEmpty then
        body
    else
        lines |> Array.filter (fun l -> not (unread.Contains l)) |> String.concat "\n"

/// Zig rejects a parameter that is never used.
let ensureUsed (names: string list) (body: string) =
    // (a name inside a string literal or comment is not a use of it)
    let code = Regex.Replace(body, "\"(?:[^\"\\\\]|\\\\.)*\"|//[^\\n]*", "\"\"")

    names
    |> List.filter (fun n -> not (Regex.IsMatch(code, $@"(?<![\w.])%s{Regex.Escape n}\b")))
    |> List.map (fun n -> $"    _ = %s{n};\n")
    |> String.concat ""

/// The variables that hold a value record of which a field is assigned (they are declared
/// with `var`; a reference record is assigned through its pointer).
let storedInto (body: Expr) : Set<int> =
    let found = HashSet<int>()

    let rec root (e: Expr) =
        match e with
        | EVar v ->
            match v.Ty with
            | TEnt({ Kind = KRefRecord }, _) -> ()
            | _ -> found.Add v.Id |> ignore
        | EGet(x, _, _) ->
            match typeOf x with
            | TEnt({ Kind = KRefRecord }, _) -> ()
            | _ -> root x
        | _ -> ()

    exists
        (function
        | EStore(lv, _) ->
            root lv
            false
        | _ -> false)
        body
    |> ignore

    Set.ofSeq found

let hasManaged (fn: FnInfo) =
    isManaged fn.Ret || fn.Params |> List.exists (fun p -> isManaged p.Ty)

let formatSigValue (fn: FnInfo) =
    let borrows =
        match fn.Modes with
        | [] -> ".{}"
        | modes ->
            modes
            |> List.map (fun m ->
                if m = MBorrowed then
                    "true"
                else
                    "false"
            )
            |> String.concat ", "
            |> sprintf ".{ %s }"

    let resultBorrowed =
        if fn.RetFrom.IsSome then
            "true"
        else
            "false"

    let resultFrom =
        match fn.RetFrom with
        | None
        | Some [] -> ".{}"
        | Some js ->
            js
            |> List.sort
            |> List.map string<int>
            |> String.concat ", "
            |> sprintf ".{ %s }"

    $".{{ .borrows = %s{borrows}, .result_borrowed = %s{resultBorrowed}, .result_from = %s{resultFrom} }}"

let zigStrLit (s: string) =
    let esc = s.Replace("\\", "\\\\").Replace("\"", "\\\"")
    $"\"%s{esc}\""

let formatStoresValue (fn: FnInfo) =
    let fields, cb, ext = fn.StoreFacts

    let fieldsTuple =
        match fields |> List.sort with
        | [] -> ".{}"
        | fs -> fs |> List.map zigStrLit |> String.concat ", " |> sprintf ".{ %s }"

    let bStr (b: bool) =
        if b then
            "true"
        else
            "false"

    $".{{ .fields = %s{fieldsTuple}, .calls_callback = %s{bStr cb}, .calls_ext_store = %s{bStr ext} }}"

let formatFactAssertions (fns: FnInfo list) : string =
    let noRaiseStmts =
        fns
        |> Seq.collect (fun fn -> fn.AssertedNoRaise)
        |> Seq.distinctBy (fun (f, tys) -> f + "<" + (tys |> List.map tyKey |> String.concat ",") + ">")
        |> Seq.map (fun (f, tys) -> $"        fable_rt.assertNoRaise(%s{fnRef f tys});")
        |> List.ofSeq

    let storeStmts =
        fns
        |> Seq.collect (fun fn -> fn.AssertedStores)
        |> Seq.groupBy (fun (extFn, _, _) -> extFn)
        |> Seq.choose (fun (extFn, items) ->
            match extFn.IndexOf '.' with
            | -1 -> None
            | dot ->
                let modAlias = extFn.Substring(0, dot)
                let memberName = topIdent (extFn.Substring(dot + 1))

                let fields =
                    items
                    |> Seq.collect (fun (_, fs, _) -> fs)
                    |> Set.ofSeq
                    |> Set.toList
                    |> List.sort

                let checkExt = items |> Seq.exists (fun (_, _, c) -> c)

                let fieldsTuple =
                    match fields with
                    | [] -> ".{}"
                    | fs -> fs |> List.map zigStrLit |> String.concat ", " |> sprintf ".{ %s }"

                let extFlag =
                    if checkExt then
                        "true"
                    else
                        "false"

                Some
                    $"        fable_rt.assertNoStore(%s{modAlias}, %s{zigStrLit memberName}, %s{fieldsTuple}, %s{extFlag});"
        )
        |> List.ofSeq

    let stmts = noRaiseStmts @ storeStmts

    if stmts.IsEmpty then
        ""
    else
        "    comptime {\n" + String.concat "\n" stmts + "\n    }\n"

/// The runtime's `cell` is inlined, so the work Zig does at compile time for each counts against
/// the function's quota of backward branches: a literal of many cells, a 9 by 9 list of lists,
/// runs out of it; and so does each inlined `dup` and `drop` (a state machine fusing many
/// functions has hundreds of them). The line that raises the quota, if the body needs it.
let branchQuota (bodyText: string) : string =
    let count (what: string) =
        let mutable n = 0
        let mutable i = bodyText.IndexOf(what, System.StringComparison.Ordinal)

        while i >= 0 do
            n <- n + 1
            i <- bodyText.IndexOf(what, i + 1, System.StringComparison.Ordinal)

        n

    let cells = count "fable_rt.cell("
    let counts = count "fable_rt.dup(" + count "fable_rt.drop("

    if cells > 32 || counts > 128 then
        "    @setEvalBranchQuota("
        + string (max 10000 (cells * 200 + counts * 50))
        + ");\n"
    else
        ""

/// The `[<StackArena>]` functions of the file being written.
let currentArenas =
    new System.Threading.ThreadLocal<Dictionary<string, int> ref>(fun () -> ref (Dictionary<string, int>()))

/// Emit a thin `$tc` adapter around an ordinary synchronous function whose body cannot enter an
/// unbounded tail chain (`NeedsChain = false`).
let emitThinTc
    (out: StringBuilder)
    (indent: string)
    (fnNameZig: string)
    (visibility: string)
    (targetFn: string)
    (fn: FnInfo)
    =
    let L (s: string) = out.AppendLine(indent + s) |> ignore
    let paramTys = fn.Params |> List.map (fun p -> zigType p.Ty)
    let paramTysStr = String.concat ", " paramTys
    let retZig = zigType fn.Ret
    let voidRet = isVoid fn.Ret

    let borrowedIdx =
        fn.Modes
        |> List.indexed
        |> List.choose (fun (i, m) ->
            if m = MBorrowed then
                Some i
            else
                None
        )

    let ctxParam =
        if fn.Params.IsEmpty then
            "_: *fable_rt.TailCtx"
        else
            "ctx: *fable_rt.TailCtx"

    L $"%s{visibility}fn %s{fnNameZig}(%s{ctxParam}, ret: *anyopaque) fable_rt.TailStatus {{"

    if fn.Params.IsEmpty then
        L $"    const raw = %s{targetFn}();"

        if voidRet then
            L "    const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {"
            L $"        fable_rt.plugRet(%s{retZig}, ret);"
            L "        return .raised;"
            L "    } else raw;"
            L "    _ = r;"
            L "    return .ok;"
        else
            L "    const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {"
            L $"        fable_rt.plugRet(%s{retZig}, ret);"
            L "        return .raised;"
            L "    } else raw;"

            let resExpr =
                if fn.RetFrom.IsSome then
                    dupCode "r"
                else
                    "r"

            L $"    const res = %s{resExpr};"
            L $"    @as(*%s{retZig}, @ptrCast(@alignCast(ret))).* = res;"
            L "    return .ok;"
    else
        L $"    if (comptime fable_rt.fitsTailArgs(&.{{ %s{paramTysStr} }})) {{"
        L $"        const _tca = fable_rt.tailLoad(&.{{ %s{paramTysStr} }}, ctx);"
        let args = fn.Params |> List.mapi (fun i _ -> $"_tca[%d{i}]") |> String.concat ", "
        L $"        const raw = %s{targetFn}(%s{args});"

        if voidRet then
            L "        const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {"

            for i in borrowedIdx do
                L("            " + dropCode $"_tca[%d{i}]")

            L $"            fable_rt.plugRet(%s{retZig}, ret);"
            L "            return .raised;"
            L "        } else raw;"
            L "        _ = r;"

            for i in borrowedIdx do
                L("        " + dropCode $"_tca[%d{i}]")

            L "        return .ok;"
        else
            L "        const r = if (comptime fable_rt.isRaised(@TypeOf(raw))) raw catch {"

            for i in borrowedIdx do
                L("            " + dropCode $"_tca[%d{i}]")

            L $"            fable_rt.plugRet(%s{retZig}, ret);"
            L "            return .raised;"
            L "        } else raw;"

            let resExpr =
                if fn.RetFrom.IsSome then
                    dupCode "r"
                else
                    "r"

            L $"        const res = %s{resExpr};"

            for i in borrowedIdx do
                L("        " + dropCode $"_tca[%d{i}]")

            L $"        @as(*%s{retZig}, @ptrCast(@alignCast(ret))).* = res;"
            L "        return .ok;"

        L "    } else {"
        L "        unreachable;"
        L "    }"

    L "}"

let emitFunction
    (out: StringBuilder)
    (rootNames: HashSet<string>)
    (fableAliases: HashSet<string>)
    (noTcFns: HashSet<string>)
    (noTailCalls: HashSet<string>)
    (adapters: Dictionary<string, Adapter>)
    (knowns: Dictionary<string, KnownDecl>)
    (knownIfaces: Dictionary<string, KnownIfaceDecl>)
    (ifaceVts: Dictionary<string, IfaceVt>)
    (fns: Dictionary<string, FnInfo>)
    (curried2: Dictionary<string, string>)
    (noTc: bool)
    (fn: FnInfo)
    =
    let renderBody (body: Expr) (kParamIds: Set<int>) (isTc: bool) =
        // Is there a self call, or `let r = self(..) in Case(.., r, ..)`, where the function ends?
        let sites = tailSites body

        let selfTail =
            sites
            |> List.exists (
                function
                | ECall(f, _, _, _)
                | EOnRaise(ECall(f, _, _, _), _) -> f = fn.Name
                | _ -> false
            )

        // (When the function can be left by an exception, what it has built so far must be
        // droppable: a field-less case if any, otherwise `fable_rt.nullOf(R)` behind `hasNull(R)`.)
        let plug =
            allCases fn.Ret
            |> List.tryFind (fun c -> isHeapTy fn.Ret && (caseFields fn.Ret c).IsEmpty)
            |> Option.map (fun c -> $"@as(%s{zigType fn.Ret}, .%s{fieldIdent c})")

        let hasTrmcSite =
            not isTc
            && fn.RetFrom.IsNone
            && (sites |> List.exists (fun s -> (trmcSite fn.Name s).IsSome))

        let trmc = hasTrmcSite && (fn.Raises = RNever || plug.IsSome)
        let splitHasNull = hasTrmcSite && fn.Raises <> RNever && plug.IsNone

        let reassignedFor (useTrmc: bool) =
            sites
            |> List.collect (fun s ->
                let args =
                    match
                        s,
                        (if useTrmc then
                             trmcSite fn.Name s
                         else
                             None)
                    with
                    | _, Some(a, _, _, _, _, _) -> a
                    | (ECall(f, _, a, _) | EOnRaise(ECall(f, _, a, _), _)), _ when f = fn.Name -> a
                    | _ -> []

                if args.IsEmpty then
                    []
                else
                    List.zip fn.Params args
                    |> List.choose (fun (p, a) ->
                        match a with
                        | EVar v when v.Id = p.Id -> None
                        | _ -> Some p.Id
                    )
            )
            |> Set.ofList

        let mutatedIds =
            // (a variable whose address is taken to be assigned through is a `var` too)
            let addressed = HashSet<int>()

            exists
                (fun x ->
                    match x with
                    | EAddr(EVar v, false) -> addressed.Add v.Id |> ignore
                    | _ -> ()

                    false
                )
                body
            |> ignore

            Set.unionMany [ assignedIn body; storedInto body; Set.ofSeq addressed ]

        let sigReassigned = reassignedFor (trmc || splitHasNull)
        let paramUsed = HashSet(rootNames)

        if isTc then
            paramUsed.Add "ctx" |> ignore
            paramUsed.Add "ret" |> ignore

        let paramLocalNames = Dictionary<int, string>()

        let allocName (baseStr: string) =
            let b =
                let c = cleanIdent baseStr

                if isReservedIdent c then
                    c + "_"
                else
                    c

            let mutable cand = b
            let mutable i = 1

            while paramUsed.Contains cand do
                cand <- $"%s{b}_%d{i}"
                i <- i + 1

            paramUsed.Add cand |> ignore
            cand

        let ps =
            fn.Params
            |> List.map (fun p ->
                let n = allocName p.Base
                paramLocalNames[p.Id] <- n

                let sigName =
                    if sigReassigned.Contains p.Id then
                        allocName (n + "_in")
                    else
                        n

                sigName, n, p
            )

        let emitVariant (useTrmc: bool) (plugOpt: string option) (baseInd: string) =
            let brReassigned = reassignedFor useTrmc

            let brLoop =
                if selfTail || useTrmc then
                    Some
                        {
                            Self = fn.Name
                            Params = fn.Params
                            Trmc = useTrmc
                            Plug = plugOpt
                        }
                else
                    None

            let namesDict = Dictionary<int, string>()

            for kv in paramLocalNames do
                namesDict[kv.Key] <- kv.Value

            let em =
                {
                    Out = StringBuilder()
                    Names = namesDict
                    Used = HashSet(paramUsed)
                    Mutated = mutatedIds
                    Loop = brLoop
                    Scc = None
                    Self = fn
                    Fns = fns
                    Curried2 = curried2
                    TryLabels = Stack()
                    Adapters = adapters
                    Knowns = knowns
                    KnownIfaces = knownIfaces
                    IfaceVts = ifaceVts
                    KParams = kParamIds
                    IsTc = isTc
                    FableAliases = fableAliases
                    NoTcFns = noTcFns
                    NoTailCalls = noTailCalls
                    CanTail =
                        not isTc
                        && kParamIds.IsEmpty
                        && not useTrmc
                        && fn.Raises = RNever
                        && not (
                            exists
                                (function
                                | EUnpack(u, _) -> u.Token.IsSome
                                | _ -> false)
                                body
                        )
                    Counter = 0
                }

            for (s, n, p) in ps do
                if s <> n then
                    if brReassigned.Contains p.Id then
                        line em baseInd $"var %s{n} = %s{s};"
                    elif splitHasNull then
                        line em baseInd $"const %s{n} = %s{s};"

            let retDest =
                if isTc then
                    DTcRet
                else
                    DReturn

            match brLoop with
            | Some l ->
                if l.Trmc then
                    line em baseInd $"var result: %s{zigType fn.Ret} = undefined;"
                    line em baseInd $"var hole: *%s{zigType fn.Ret} = &result;"

                line em baseInd "tail: while (true) {"
                stmt em (baseInd + "    ") body retDest
                line em baseInd "}"
            | None -> stmt em baseInd body retDest

            let raw = dropUnreadPaths (em.Out.ToString())

            let raw =
                if splitHasNull then
                    let extraUnused =
                        ps
                        |> List.choose (fun (s, n, p) ->
                            if s <> n && not (brReassigned.Contains p.Id) then
                                Some n
                            else
                                None
                        )

                    let unusedLocal = ensureUsed extraUnused raw
                    unusedLocal.Replace("    _ = ", baseInd + "_ = ") + raw
                else
                    raw

            if raw.Contains "fable_stack.alloc(" then
                $"%s{baseInd}var fable_stack: fable_rt.StackAlloc = .{{}};\n%s{baseInd}defer fable_stack.deinit();\n"
                + raw
            else
                raw

        let bodyText =
            if splitHasNull then
                let retZig = zigType fn.Ret
                let trmcBranch = emitVariant true (Some $"fable_rt.nullOf(%s{retZig})") "        "
                let plainBranch = emitVariant false None "        "
                $"    if (comptime fable_rt.hasNull(%s{retZig})) {{\n%s{trmcBranch}    }} else {{\n%s{plainBranch}    }}\n"
            else
                emitVariant trmc plug "    "

        // `[<StackArena(bytes)>]`: the function's cells come from a buffer on its stack
        let bodyText =
            match currentArenas.Value.Value.TryGetValue fn.Name with
            | true, bytes ->
                $"    var fable_arena_buffer: [%d{bytes}]u8 align(16) = undefined;\n"
                + "    var fable_arena_fba = std.heap.FixedBufferAllocator.init(&fable_arena_buffer);\n"
                + "    var fable_arena: fable_rt.Arena = undefined;\n"
                + "    fable_rt.arenaEnter(&fable_arena, &fable_arena_fba);\n"
                + "    defer fable_rt.arenaLeave(&fable_arena);\n"
                + bodyText
            | _ -> bodyText

        let factAsserts = formatFactAssertions [ fn ]
        let bodyText = factAsserts + branchQuota (factAsserts + bodyText) + bodyText

        let sigParams =
            ps
            |> List.map (fun (s, _, p) ->
                if kParamIds.Contains p.Id then
                    $"%s{s}: anytype"
                else
                    $"%s{s}: %s{zigType p.Ty}"
            )
            |> String.concat ", "

        let usedNames =
            let pNames = ps |> List.map (fun (s, _, _) -> s)

            if isTc then
                "ctx" :: "ret" :: pNames
            else
                pNames

        let unused = ensureUsed usedNames bodyText
        selfTail, (trmc || splitHasNull), sigParams, bodyText, unused

    let selfTail, trmc, sigParams, bodyText, unused = renderBody fn.Body Set.empty false

    let kVariant =
        fn.BodyK
        |> Option.map (fun bodyK ->
            let kParamIds =
                List.zip fn.Params fn.NoEscape
                |> List.choose (fun (p, isK) ->
                    if isK then
                        Some p.Id
                    else
                        None
                )
                |> Set.ofList

            let _, _, kSigParams, kBodyText, kUnused = renderBody bodyK kParamIds false
            kSigParams, kBodyText, kUnused
        )

    let tcVariant =
        if not noTc && fnHasTcBody fn then
            fn.BodyTc
            |> Option.map (fun bodyTc ->
                let _, _, tcParamDecls, tcBodyText, tcUnused = renderBody bodyTc Set.empty true
                tcParamDecls, tcBodyText, tcUnused
            )
        else
            None

    let paramTysStr =
        fn.Params |> List.map (fun p -> zigType p.Ty) |> String.concat ", "

    let retZig = zigType fn.Ret

    let modes =
        List.zip fn.Params fn.Modes
        |> List.choose (fun (p, m) ->
            match m with
            | MOwned -> Some(p.Base + ": owned")
            | MBorrowed -> Some(p.Base + ": borrowed")
            | MPlain -> None
        )

    let modes =
        match fn.RetFrom with
        | Some _ -> modes @ [ "result: borrowed" ]
        | None -> modes

    if not modes.IsEmpty then
        out.AppendLine($"""/// ownership: %s{String.concat ", " modes}""") |> ignore

    if trmc then
        out.AppendLine("/// tail recursion modulo cons: a loop that builds the result top-down")
        |> ignore
    elif selfTail then
        out.AppendLine("/// self tail call: a loop") |> ignore

    let visibility =
        if fn.IsLocal then
            ""
        else
            "pub "

    let emitFullTcFn (fnNameZig: string) (targetBody: string) (fnVis: string) =
        out.AppendLine($"%s{fnVis}fn %s{fnNameZig}(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {{")
        |> ignore

        if fn.Params.IsEmpty then
            out
                .AppendLine($"    const _next = %s{targetBody}(ctx, ret) catch {{")
                .AppendLine($"        fable_rt.plugRet(%s{retZig}, ret);")
                .AppendLine("        return .raised;")
                .AppendLine("    };")
                .AppendLine("    if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{ ctx, _next.ret });")
                .AppendLine("    return .ok;")
                .AppendLine("}")
            |> ignore
        else
            let loadArgs =
                fn.Params |> List.mapi (fun i _ -> $"_tca[%d{i}]") |> String.concat ", "

            out
                .AppendLine($"    if (comptime fable_rt.fitsTailArgs(&.{{ %s{paramTysStr} }})) {{")
                .AppendLine($"        const _tca = fable_rt.tailLoad(&.{{ %s{paramTysStr} }}, ctx);")
                .AppendLine($"        const _next = %s{targetBody}(ctx, ret, %s{loadArgs}) catch {{")
                .AppendLine($"            fable_rt.plugRet(%s{retZig}, ret);")
                .AppendLine("            return .raised;")
                .AppendLine("        };")
                .AppendLine(
                    "        if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{ ctx, _next.ret });"
                )
                .AppendLine("        return .ok;")
                .AppendLine("    } else {")
                .AppendLine("        unreachable;")
                .AppendLine("    }")
                .AppendLine("}")
            |> ignore

    match fn.TypeParams with
    | [] ->
        out
            .AppendLine($"%s{visibility}fn %s{topIdent fn.Name}(%s{sigParams}) %s{retType fn} {{")
            .Append(unused)
            .Append(bodyText)
            .AppendLine("}")
        |> ignore

        match kVariant with
        | Some(kSigParams, kBodyText, kUnused) ->
            out
                .AppendLine($"%s{visibility}fn @\"%s{topIdent fn.Name}$k\"(%s{kSigParams}) %s{retType fn} {{")
                .Append(kUnused)
                .Append(kBodyText)
                .AppendLine("}")
            |> ignore
        | None -> ()

        match tcVariant with
        | Some(tcParamDecls, tcBodyText, tcUnused) ->
            let tcSig =
                if tcParamDecls = "" then
                    "ctx: *fable_rt.TailCtx, ret: *anyopaque"
                else
                    $"ctx: *fable_rt.TailCtx, ret: *anyopaque, %s{tcParamDecls}"

            out
                .AppendLine($"fn @\"%s{topIdent fn.Name}$tcbody\"(%s{tcSig}) fable_rt.Raised!fable_rt.TailNext {{")
                .Append(tcUnused)
                .Append(tcBodyText)
                .AppendLine("}")
            |> ignore

            if fn.NeedsChain then
                emitFullTcFn $"@\"%s{topIdent fn.Name}$tc\"" $"@\"%s{topIdent fn.Name}$tcbody\"" visibility
            else
                emitFullTcFn $"@\"%s{topIdent fn.Name}$tcfull\"" $"@\"%s{topIdent fn.Name}$tcbody\"" ""
                emitThinTc out "" $"@\"%s{topIdent fn.Name}$tcthin\"" "" (topIdent fn.Name) fn

                out.AppendLine(
                    $"%s{visibility}const @\"%s{topIdent fn.Name}$tc\" = if (%s{chainName fn.Name}) @\"%s{topIdent fn.Name}$tcfull\" else @\"%s{topIdent fn.Name}$tcthin\";"
                )
                |> ignore
        | None when not fn.IsLocal && not noTc ->
            emitThinTc out "" $"@\"%s{topIdent fn.Name}$tc\"" visibility (topIdent fn.Name) fn
        | None -> ()
    | typeParams ->
        // A generic function: a Zig function from its type arguments to a namespace that holds
        // the function, so that `name(i32).call` is an ordinary function.
        let comptimeParams =
            typeParams
            |> List.map (fun g -> $"comptime %s{genName g}: type")
            |> String.concat ", "

        let indented (text: string) =
            text.Split('\n')
            |> Array.map (fun l ->
                if l = "" then
                    l
                else
                    "        " + l
            )
            |> String.concat "\n"

        // (a function lifted out of a generic one has its type parameters, and may not use
        // them all)
        let kCombined =
            match kVariant with
            | Some(ks, kb, _) -> $"%s{ks} %s{kb}"
            | None -> ""

        let tcCombined =
            match tcVariant with
            | Some(ts, tb, _) -> $"%s{ts} %s{tb}"
            | None -> ""

        let signature = $"%s{sigParams} %s{retType fn}"

        let discards =
            typeParams
            |> List.filter (fun g ->
                let name = genName g

                not (
                    bodyText.Contains name
                    || signature.Contains name
                    || kCombined.Contains name
                    || tcCombined.Contains name
                )
            )
            |> List.map (fun g -> $"    _ = %s{genName g};\n")
            |> String.concat ""

        let sigDecl =
            if hasManaged fn && not fn.IsLocal then
                $"        pub const sig = %s{sigName fn.Name};\n"
            else
                ""

        let noEscDecl =
            if kVariant.IsSome && not fn.IsLocal then
                $"        pub const noescape = %s{noEscapeName fn.Name};\n"
            else
                ""

        out
            .AppendLine($"%s{visibility}fn %s{topIdent fn.Name}(%s{comptimeParams}) type {{")
            .Append(discards)
            .AppendLine("    return struct {")
            .Append(sigDecl)
            .Append(noEscDecl)
            .AppendLine($"        pub fn call(%s{sigParams}) %s{retType fn} {{")
            .Append(indented unused)
            .Append(indented bodyText)
            .AppendLine("        }")
        |> ignore

        match kVariant with
        | Some(kSigParams, kBodyText, kUnused) ->
            out
                .AppendLine($"        pub fn callK(%s{kSigParams}) %s{retType fn} {{")
                .Append(indented kUnused)
                .Append(indented kBodyText)
                .AppendLine("        }")
            |> ignore
        | None -> ()

        match tcVariant with
        | Some(tcParamDecls, tcBodyText, tcUnused) ->
            let tcSig =
                if tcParamDecls = "" then
                    "ctx: *fable_rt.TailCtx, ret: *anyopaque"
                else
                    $"ctx: *fable_rt.TailCtx, ret: *anyopaque, %s{tcParamDecls}"

            out
                .AppendLine($"        pub fn tcbody(%s{tcSig}) fable_rt.Raised!fable_rt.TailNext {{")
                .Append(indented tcUnused)
                .Append(indented tcBodyText)
                .AppendLine("        }")
            |> ignore

            let tcSb = StringBuilder()

            let tcSigHeader =
                if fn.NeedsChain then
                    "        pub fn tc(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {"
                else
                    "        fn tcfull(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {"

            if fn.Params.IsEmpty then
                tcSb
                    .AppendLine(tcSigHeader)
                    .AppendLine("            const _next = tcbody(ctx, ret) catch {")
                    .AppendLine($"                fable_rt.plugRet(%s{retZig}, ret);")
                    .AppendLine("                return .raised;")
                    .AppendLine("            };")
                    .AppendLine(
                        "            if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{ ctx, _next.ret });"
                    )
                    .AppendLine("            return .ok;")
                    .AppendLine("        }")
                |> ignore
            else
                let loadArgs =
                    fn.Params |> List.mapi (fun i _ -> $"_tca[%d{i}]") |> String.concat ", "

                tcSb
                    .AppendLine(tcSigHeader)
                    .AppendLine($"            if (comptime fable_rt.fitsTailArgs(&.{{ %s{paramTysStr} }})) {{")
                    .AppendLine($"                const _tca = fable_rt.tailLoad(&.{{ %s{paramTysStr} }}, ctx);")
                    .AppendLine($"                const _next = tcbody(ctx, ret, %s{loadArgs}) catch {{")
                    .AppendLine($"                    fable_rt.plugRet(%s{retZig}, ret);")
                    .AppendLine("                    return .raised;")
                    .AppendLine("                };")
                    .AppendLine(
                        "                if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{ ctx, _next.ret });"
                    )
                    .AppendLine("                return .ok;")
                    .AppendLine("            } else {")
                    .AppendLine("                unreachable;")
                    .AppendLine("            }")
                    .AppendLine("        }")
                |> ignore

            out.Append(tcSb.ToString()) |> ignore

            if not fn.NeedsChain then
                emitThinTc out "        " "tcthin" "" "call" fn

                out.AppendLine($"        pub const tc = if (%s{chainName fn.Name}) tcfull else tcthin;")
                |> ignore
        | None when not fn.IsLocal && not noTc -> emitThinTc out "        " "tc" "pub " "call" fn
        | None -> ()

        out.AppendLine("    };").AppendLine("}") |> ignore

    // What the function borrows and stores, for the calls from other files.
    if hasManaged fn && not fn.IsLocal then
        out.AppendLine($"pub const %s{sigName fn.Name} = %s{formatSigValue fn};")
        |> ignore

    if not fn.IsLocal then
        out.AppendLine($"pub const %s{storesName fn.Name} = %s{formatStoresValue fn};")
        |> ignore

    if not noTc && (not fn.IsLocal || fnHasTcBody fn) then
        out.AppendLine($"%s{visibility}const %s{chainName fn.Name}: bool = %s{fnChainConstExpr fn};")
        |> ignore

    if kVariant.IsSome && not fn.IsLocal then
        let noEs =
            fn.NoEscape
            |> List.map (fun b ->
                if b then
                    "true"
                else
                    "false"
            )
            |> String.concat ", "
            |> sprintf ".{ %s }"

        out.AppendLine($"pub const %s{noEscapeName fn.Name} = %s{noEs};") |> ignore

    out.AppendLine() |> ignore


/// Detect and emit mutually tail-recursive SCC state machines and all functions in `state.Fns`.
let emitFnsAndSccs
    (out: StringBuilder)
    (rootNames: HashSet<string>)
    (fableAliases: HashSet<string>)
    (specialNoTc: HashSet<string>)
    (noTailCalls: HashSet<string>)
    (adapters: Dictionary<string, Adapter>)
    (knowns: Dictionary<string, KnownDecl>)
    (knownIfaces: Dictionary<string, KnownIfaceDecl>)
    (ifaceVts: Dictionary<string, IfaceVt>)
    (fns: Dictionary<string, FnInfo>)
    (state: FileState)
    =
    // Mutual tail recursion: intra-file SCCs of >= 2 functions with matching return type, type
    // parameters, and error behavior (not already covered by scalar sibling tail jumps) fuse into a
    // single state-machine loop (`switch (_st) { ... continue :tail; }`).
    let rec isScalarTy (t: Ty) =
        match t with
        | TPrim _ -> true
        | _ -> false

    let tailEdges = Dictionary<string, Set<string>>()

    for fn in state.Fns do
        let rec collectTail (e: Expr) =
            match e with
            | ELet(_, (ECall _ | EOnRaise(ECall _, _)), ECon _) ->
                match trmcSiteOf fns.ContainsKey e with
                | Some(g, tArgs, args, _, _, _, _, _) when
                    fn.RetFrom.IsNone
                    && tArgs = (fn.TypeParams |> List.map TGen)
                    && args.Length = fns[g].Params.Length
                    ->
                    Set.singleton g
                | _ -> Set.empty
            | ELet(_, rhs, _) when alwaysRaises rhs -> Set.empty
            | ELet(_, _, b)
            | EDrop(_, b)
            | EUnpack(_, b)
            | EPromote(_, b) -> collectTail b
            | ESeq(a, _) when alwaysRaises a -> Set.empty
            | ESeq(_, b) -> collectTail b
            | EIf(_, t, f, _) -> Set.union (collectTail t) (collectTail f)
            | ECall(g, tArgs, args, _)
            | EOnRaise(ECall(g, tArgs, args, _), []) when
                fns.ContainsKey g
                && tArgs = (fn.TypeParams |> List.map TGen)
                && args.Length = fns[g].Params.Length
                ->
                Set.singleton g
            | _ -> Set.empty

        tailEdges[fn.Name] <- collectTail fn.Body

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

            for w in tailEdges[v] do
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
                    comp.Add fns[w]

                    if w = v then
                        stop <- true

                if comp.Count >= 2 then
                    sccs.Add(List.rev (List.ofSeq comp))

        for fn in state.Fns do
            if not (indexOf.ContainsKey fn.Name) then
                strongconnect fn.Name

    let sccByMember = Dictionary<string, FnInfo list * string * Map<string, string>>()

    for scc in sccs do
        let rep = scc.Head
        let repRet = zigType rep.Ret
        let repRetText = retType rep

        let eligible =
            scc
            |> List.forall (fun fn ->
                not (state.Arenas.ContainsKey fn.Name)
                && fn.RetFrom.IsNone
                && fn.TypeParams = rep.TypeParams
                && zigType fn.Ret = repRet
                && retType fn = repRetText
            )

        let allScalarSameSig =
            rep.Raises = RNever
            && scc
               |> List.forall (fun fn ->
                   (fn.Ret :: (fn.Params |> List.map (fun p -> p.Ty))) |> List.forall isScalarTy
                   && (fn.Params |> List.map (fun p -> zigType p.Ty)) =
                       (rep.Params |> List.map (fun p -> zigType p.Ty))
               )

        if eligible && not allScalarSameSig then
            let mutable sccBase = $"%s{rep.Name}$scc"

            while rootNames.Contains(topIdent sccBase) do
                sccBase <- sccBase + "_"

            rootNames.Add(topIdent sccBase) |> ignore

            let tagMap = scc |> List.mapi (fun i fn -> fn.Name, $"s%d{i}") |> Map.ofList

            for fn in scc do
                sccByMember[fn.Name] <- scc, sccBase, tagMap

    let emittedSccs = HashSet<string>()

    let emitScc (scc: FnInfo list) (sccBase: string) (tagMap: Map<string, string>) =
        let rep = scc.Head
        let generic = not rep.TypeParams.IsEmpty
        let retZig = zigType rep.Ret

        let sccNeedsChain =
            scc
            |> List.exists (fun fn -> not (specialNoTc.Contains fn.Name) && fnHasTcBody fn)

        let stateTypeLocal =
            if generic then
                "State"
            else
                $"@\"%s{topIdent sccBase}$State\""

        let isSccTrmcSite (fn: FnInfo) (e: Expr) =
            match trmcSiteOf tagMap.ContainsKey e with
            | Some(g, tArgs, args, _, _, _, _, _) ->
                tArgs = (fn.TypeParams |> List.map TGen) && args.Length = fns[g].Params.Length
            | None -> false

        let anyTrmc =
            scc
            |> List.exists (fun fn -> fn.RetFrom.IsNone && (tailSites fn.Body |> List.exists (isSccTrmcSite fn)))

        let plug =
            allCases rep.Ret
            |> List.tryFind (fun c -> isHeapTy rep.Ret && (caseFields rep.Ret c).IsEmpty)
            |> Option.map (fun c -> $"@as(%s{retZig}, .%s{fieldIdent c})")

        let trmc = anyTrmc && (rep.Raises = RNever || plug.IsSome)
        let splitHasNull = anyTrmc && rep.Raises <> RNever && plug.IsNone

        let variantDecls =
            scc
            |> List.map (fun fn ->
                let tag = tagMap[fn.Name]

                if fn.Params.IsEmpty then
                    tag + ","
                else
                    let fs =
                        fn.Params
                        |> List.mapi (fun i p -> $"a%d{i}: %s{zigType p.Ty}")
                        |> String.concat ", "

                    $"%s{tag}: struct {{ %s{fs} }},"
            )

        let buildArms (isTc: bool) (useTrmc: bool) (plugOpt: string option) =
            let sccInfo =
                {
                    StateTypeName = stateTypeLocal
                    TagOf = tagMap
                    Trmc = useTrmc
                    Plug = plugOpt
                }

            scc
            |> List.map (fun fn ->
                let tag = tagMap[fn.Name]
                let emUsed = HashSet(rootNames)
                emUsed.Add "_st" |> ignore
                emUsed.Add "_args" |> ignore
                emUsed.Add "_next" |> ignore

                if isTc then
                    emUsed.Add "ctx" |> ignore
                    emUsed.Add "ret" |> ignore

                if useTrmc then
                    emUsed.Add "result" |> ignore
                    emUsed.Add "hole" |> ignore

                let armBodyExpr =
                    if isTc then
                        defaultArg fn.BodyTc fn.Body
                    else
                        fn.Body

                let em =
                    {
                        Out = StringBuilder()
                        Names = Dictionary()
                        Used = emUsed
                        Mutated = Set.union (assignedIn armBodyExpr) (storedInto armBodyExpr)
                        Loop = None
                        Scc = Some sccInfo
                        Self = fn
                        Fns = fns
                        Curried2 = state.Curried2
                        CanTail = false
                        TryLabels = Stack()
                        Adapters = adapters
                        Knowns = knowns
                        KnownIfaces = knownIfaces
                        IfaceVts = ifaceVts
                        KParams = Set.empty
                        IsTc = isTc
                        FableAliases = fableAliases
                        NoTcFns = specialNoTc
                        NoTailCalls = noTailCalls
                        Counter = 0
                    }

                let binds = List<string>()

                let paramNames =
                    fn.Params
                    |> List.mapi (fun i p ->
                        let name = vname em p

                        let kw =
                            if em.Mutated.Contains p.Id then
                                "var"
                            else
                                "const"

                        binds.Add($"%s{kw} %s{name} = _args.a%d{i};")
                        name
                    )

                stmt
                    em
                    ""
                    armBodyExpr
                    (if isTc then
                         DTcRet
                     else
                         DReturn)

                let rawBody = dropUnreadPaths (em.Out.ToString())
                let unusedText = ensureUsed paramNames rawBody

                let bodyText =
                    (binds |> Seq.map (fun b -> b + "\n") |> String.concat "")
                    + unusedText.Replace("    _ = ", "_ = ")
                    + rawBody

                tag, not fn.Params.IsEmpty, bodyText
            )

        let retTxt = retType rep
        let sccAsserts = formatFactAssertions scc

        let armsPair =
            if splitHasNull then
                Some(buildArms false true (Some $"fable_rt.nullOf(%s{retZig})"), buildArms false false None)
            else
                None

        let singleArms =
            if splitHasNull then
                []
            else
                buildArms
                    false
                    trmc
                    (if trmc && rep.Raises <> RNever then
                         plug
                     else
                         None)

        let allArmsText =
            match armsPair with
            | Some(trmcArms, plainArms) -> (trmcArms @ plainArms) |> List.map (fun (_, _, t) -> t) |> String.concat "\n"
            | None -> singleArms |> List.map (fun (_, _, t) -> t) |> String.concat "\n"

        let tcArmsPair =
            if sccNeedsChain && splitHasNull then
                Some(buildArms true true (Some $"fable_rt.nullOf(%s{retZig})"), buildArms true false None)
            else
                None

        let tcSingleArms =
            if sccNeedsChain && not splitHasNull then
                buildArms
                    true
                    trmc
                    (if trmc && rep.Raises <> RNever then
                         plug
                     else
                         None)
            else
                []

        let allTcArmsText =
            match tcArmsPair with
            | Some(trmcArms, plainArms) -> (trmcArms @ plainArms) |> List.map (fun (_, _, t) -> t) |> String.concat "\n"
            | None -> tcSingleArms |> List.map (fun (_, _, t) -> t) |> String.concat "\n"

        let quota = branchQuota (sccAsserts + "\n" + allArmsText)

        let tcQuota =
            if sccNeedsChain then
                branchQuota (sccAsserts + "\n" + allTcArmsText)
            else
                ""

        let appendLoop (baseInd: string) (isTc: bool) (useTrmc: bool) (arms: (string * bool * string) list) =
            if isTc then
                let armsCombined = arms |> List.map (fun (_, _, t) -> t) |> String.concat "\n"
                let tcUnused = ensureUsed [ "ctx"; "ret" ] armsCombined

                for l in tcUnused.Split('\n') do
                    if l <> "" then
                        out.AppendLine(baseInd + l.TrimStart()) |> ignore

            if useTrmc then
                out
                    .AppendLine($"%s{baseInd}var result: %s{retZig} = undefined;")
                    .AppendLine($"%s{baseInd}var hole: *%s{retZig} = &result;")
                |> ignore

            let hasLoop = arms |> List.exists (fun (_, _, t) -> t.Contains "continue :tail;")

            let switchInd =
                if hasLoop then
                    baseInd + "    "
                else
                    baseInd

            if hasLoop then
                out
                    .AppendLine($"%s{baseInd}var _st = init_st;")
                    .AppendLine($"%s{baseInd}tail: while (true) {{")
                    .AppendLine($"%s{switchInd}switch (_st) {{")
                |> ignore
            else
                out.AppendLine($"%s{switchInd}switch (init_st) {{") |> ignore

            for (tag, hasArgs, armBody) in arms do
                let pat =
                    if hasArgs then
                        $"%s{switchInd}    .%s{tag} => |_args| {{"
                    else
                        $"%s{switchInd}    .%s{tag} => {{"

                out.AppendLine(pat) |> ignore

                for lineTxt in armBody.Split('\n') do
                    if lineTxt <> "" then
                        out.AppendLine(switchInd + "        " + lineTxt) |> ignore

                out.AppendLine($"%s{switchInd}    }},") |> ignore

            out.AppendLine($"%s{switchInd}}}") |> ignore

            if hasLoop then
                out.AppendLine($"%s{baseInd}}}") |> ignore

        if generic then
            let comptimeParams =
                rep.TypeParams
                |> List.map (fun g -> $"comptime %s{genName g}: type")
                |> String.concat ", "

            let allText =
                (variantDecls |> String.concat "\n")
                + "\n"
                + retTxt
                + "\n"
                + sccAsserts
                + "\n"
                + allArmsText
                + "\n"
                + allTcArmsText

            let discards =
                rep.TypeParams
                |> List.filter (fun g -> not (allText.Contains(genName g)))
                |> List.map (fun g -> $"    _ = %s{genName g};\n")
                |> String.concat ""

            let indentedAsserts =
                if sccAsserts = "" then
                    ""
                else
                    sccAsserts.Split('\n')
                    |> Array.map (fun l ->
                        if l = "" then
                            ""
                        else
                            "        " + l
                    )
                    |> String.concat "\n"

            out
                .AppendLine($"fn %s{topIdent sccBase}(%s{comptimeParams}) type {{")
                .Append(discards)
                .AppendLine("    return struct {")
                .AppendLine("        pub const State = union(enum) {")
            |> ignore

            for v in variantDecls do
                out.AppendLine($"            %s{v}") |> ignore

            out
                .AppendLine("        };")
                .AppendLine($"        pub fn run(init_st: State) %s{retTxt} {{")
                .Append(indentedAsserts)
                .Append(quota)
            |> ignore

            match armsPair with
            | Some(trmcArms, plainArms) ->
                out.AppendLine($"            if (comptime fable_rt.hasNull(%s{retZig})) {{")
                |> ignore

                appendLoop "                " false true trmcArms
                out.AppendLine("            } else {") |> ignore
                appendLoop "                " false false plainArms
                out.AppendLine("            }") |> ignore
            | None -> appendLoop "            " false trmc singleArms

            out.AppendLine("        }") |> ignore

            if sccNeedsChain then
                out
                    .AppendLine(
                        "        pub fn tcbody(ctx: *fable_rt.TailCtx, ret: *anyopaque, init_st: State) fable_rt.Raised!fable_rt.TailNext {"
                    )
                    .Append(indentedAsserts)
                    .Append(tcQuota)
                |> ignore

                match tcArmsPair with
                | Some(trmcArms, plainArms) ->
                    out.AppendLine($"            if (comptime fable_rt.hasNull(%s{retZig})) {{")
                    |> ignore

                    appendLoop "                " true true trmcArms
                    out.AppendLine("            } else {") |> ignore
                    appendLoop "                " true false plainArms
                    out.AppendLine("            }") |> ignore
                | None -> appendLoop "            " true trmc tcSingleArms

                out.AppendLine("        }") |> ignore

            out.AppendLine("    };").AppendLine("}").AppendLine() |> ignore
        else
            out.AppendLine($"const %s{stateTypeLocal} = union(enum) {{") |> ignore

            for v in variantDecls do
                out.AppendLine($"    %s{v}") |> ignore

            out
                .AppendLine("};")
                .AppendLine($"fn %s{topIdent sccBase}(init_st: %s{stateTypeLocal}) %s{retTxt} {{")
                .Append(sccAsserts)
                .Append(quota)
            |> ignore

            match armsPair with
            | Some(trmcArms, plainArms) ->
                out.AppendLine($"    if (comptime fable_rt.hasNull(%s{retZig})) {{") |> ignore
                appendLoop "        " false true trmcArms
                out.AppendLine("    } else {") |> ignore
                appendLoop "        " false false plainArms
                out.AppendLine("    }") |> ignore
            | None -> appendLoop "    " false trmc singleArms

            out.AppendLine("}").AppendLine() |> ignore

            if sccNeedsChain then
                out
                    .AppendLine(
                        $"fn @\"%s{topIdent sccBase}$tcbody\"(ctx: *fable_rt.TailCtx, ret: *anyopaque, init_st: %s{stateTypeLocal}) fable_rt.Raised!fable_rt.TailNext {{"
                    )
                    .Append(sccAsserts)
                    .Append(tcQuota)
                |> ignore

                match tcArmsPair with
                | Some(trmcArms, plainArms) ->
                    out.AppendLine($"    if (comptime fable_rt.hasNull(%s{retZig})) {{") |> ignore
                    appendLoop "        " true true trmcArms
                    out.AppendLine("    } else {") |> ignore
                    appendLoop "        " true false plainArms
                    out.AppendLine("    }") |> ignore
                | None -> appendLoop "    " true trmc tcSingleArms

                out.AppendLine("}").AppendLine() |> ignore

    let emitSccMemberWrapper (noTc: bool) (fn: FnInfo) (sccBase: string) (tagMap: Map<string, string>) =
        let used = HashSet(rootNames)
        let names = Dictionary<int, string>()

        let paramDecls =
            fn.Params
            |> List.mapi (fun i p ->
                let n =
                    let b = cleanIdent p.Base

                    let b =
                        if isReservedIdent b then
                            b + "_"
                        else
                            b

                    let mutable cand = b
                    let mutable k = 1

                    while used.Contains cand do
                        cand <- $"%s{b}_%d{k}"
                        k <- k + 1

                    used.Add cand |> ignore
                    names[p.Id] <- cand
                    cand

                n, $"%s{n}: %s{zigType p.Ty}", i
            )

        let sigParams =
            paramDecls |> List.map (fun (_, decl, _) -> decl) |> String.concat ", "

        let tag = tagMap[fn.Name]

        let visibility =
            if fn.IsLocal then
                ""
            else
                "pub "

        let generic = not fn.TypeParams.IsEmpty

        let tArgs = fn.TypeParams |> List.map genName |> String.concat ", "

        let stateRef =
            if generic then
                $"%s{topIdent sccBase}(%s{tArgs}).State"
            else
                $"@\"%s{topIdent sccBase}$State\""

        let initVal =
            if fn.Params.IsEmpty then
                $"@as(%s{stateRef}, .%s{tag})"
            else
                let fs =
                    paramDecls
                    |> List.map (fun (n, _, i) -> $".a%d{i} = %s{n}")
                    |> String.concat ", "

                $"%s{stateRef}{{ .%s{tag} = .{{ %s{fs} }} }}"

        let dispatchCall =
            if generic then
                $"%s{topIdent sccBase}(%s{tArgs}).run(_init)"
            else
                $"%s{topIdent sccBase}(_init)"

        let tailStmt =
            match isVoid fn.Ret, fn.Raises with
            | true, RNever -> $"%s{dispatchCall};"
            | true, RAlways -> $"try %s{dispatchCall};"
            | true, RDepends _ ->
                $"if (comptime fable_rt.isRaised(@TypeOf(%s{dispatchCall}))) try %s{dispatchCall} else %s{dispatchCall};"
            | false, RNever -> $"return %s{dispatchCall};"
            | false, RAlways -> $"return try %s{dispatchCall};"
            | false, RDepends _ ->
                $"if (comptime fable_rt.isRaised(@TypeOf(%s{dispatchCall}))) return try %s{dispatchCall} else return %s{dispatchCall};"

        let paramTysStr =
            fn.Params |> List.map (fun p -> zigType p.Ty) |> String.concat ", "

        let retZig = zigType fn.Ret

        if generic then
            let comptimeParams =
                fn.TypeParams
                |> List.map (fun g -> $"comptime %s{genName g}: type")
                |> String.concat ", "

            let sigDecl =
                if hasManaged fn && not fn.IsLocal then
                    $"        pub const sig = %s{sigName fn.Name};\n"
                else
                    ""

            out
                .AppendLine($"%s{visibility}fn %s{topIdent fn.Name}(%s{comptimeParams}) type {{")
                .AppendLine("    return struct {")
                .Append(sigDecl)
                .AppendLine($"        pub fn call(%s{sigParams}) %s{retType fn} {{")
                .AppendLine($"            const _init: %s{stateRef} = %s{initVal};")
                .AppendLine($"            %s{tailStmt}")
                .AppendLine("        }")
            |> ignore

            if not noTc && fnHasTcBody fn then
                let tcSig =
                    if sigParams = "" then
                        "ctx: *fable_rt.TailCtx, ret: *anyopaque"
                    else
                        $"ctx: *fable_rt.TailCtx, ret: *anyopaque, %s{sigParams}"

                let tcDispatch = $"%s{topIdent sccBase}(%s{tArgs}).tcbody(ctx, ret, _init)"

                let tcEntryHeader =
                    if fn.NeedsChain then
                        "        pub fn tc(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {"
                    else
                        "        fn tcfull(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {"

                out
                    .AppendLine($"        pub fn tcbody(%s{tcSig}) fable_rt.Raised!fable_rt.TailNext {{")
                    .AppendLine($"            const _init: %s{stateRef} = %s{initVal};")
                    .AppendLine($"            return %s{tcDispatch};")
                    .AppendLine("        }")
                |> ignore

                if fn.Params.IsEmpty then
                    out
                        .AppendLine(tcEntryHeader)
                        .AppendLine("            const _next = tcbody(ctx, ret) catch {")
                        .AppendLine($"                fable_rt.plugRet(%s{retZig}, ret);")
                        .AppendLine("                return .raised;")
                        .AppendLine("            };")
                        .AppendLine(
                            "            if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{ ctx, _next.ret });"
                        )
                        .AppendLine("            return .ok;")
                        .AppendLine("        }")
                    |> ignore
                else
                    let loadArgs =
                        fn.Params |> List.mapi (fun i _ -> $"_tca[%d{i}]") |> String.concat ", "

                    out
                        .AppendLine(tcEntryHeader)
                        .AppendLine($"            if (comptime fable_rt.fitsTailArgs(&.{{ %s{paramTysStr} }})) {{")
                        .AppendLine($"                const _tca = fable_rt.tailLoad(&.{{ %s{paramTysStr} }}, ctx);")
                        .AppendLine($"                const _next = tcbody(ctx, ret, %s{loadArgs}) catch {{")
                        .AppendLine($"                    fable_rt.plugRet(%s{retZig}, ret);")
                        .AppendLine("                    return .raised;")
                        .AppendLine("                };")
                        .AppendLine(
                            "                if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{ ctx, _next.ret });"
                        )
                        .AppendLine("                return .ok;")
                        .AppendLine("            } else {")
                        .AppendLine("                unreachable;")
                        .AppendLine("            }")
                        .AppendLine("        }")
                    |> ignore

                if not fn.NeedsChain then
                    emitThinTc out "        " "tcthin" "" "call" fn

                    out.AppendLine($"        pub const tc = if (%s{chainName fn.Name}) tcfull else tcthin;")
                    |> ignore
            elif not fn.IsLocal && not noTc then
                emitThinTc out "        " "tc" "pub " "call" fn

            out.AppendLine("    };").AppendLine("}") |> ignore
        else
            out
                .AppendLine($"%s{visibility}fn %s{topIdent fn.Name}(%s{sigParams}) %s{retType fn} {{")
                .AppendLine($"    const _init: %s{stateRef} = %s{initVal};")
                .AppendLine($"    %s{tailStmt}")
                .AppendLine("}")
            |> ignore

            if not noTc && fnHasTcBody fn then
                let tcSig =
                    if sigParams = "" then
                        "ctx: *fable_rt.TailCtx, ret: *anyopaque"
                    else
                        $"ctx: *fable_rt.TailCtx, ret: *anyopaque, %s{sigParams}"

                let tcDispatch = $"@\"%s{topIdent sccBase}$tcbody\"(ctx, ret, _init)"

                out
                    .AppendLine($"fn @\"%s{topIdent fn.Name}$tcbody\"(%s{tcSig}) fable_rt.Raised!fable_rt.TailNext {{")
                    .AppendLine($"    const _init: %s{stateRef} = %s{initVal};")
                    .AppendLine($"    return %s{tcDispatch};")
                    .AppendLine("}")
                |> ignore

                let tcEntryHeader =
                    if fn.NeedsChain then
                        $"%s{visibility}fn @\"%s{topIdent fn.Name}$tc\"(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {{"
                    else
                        $"fn @\"%s{topIdent fn.Name}$tcfull\"(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {{"

                if fn.Params.IsEmpty then
                    out
                        .AppendLine(tcEntryHeader)
                        .AppendLine($"    const _next = @\"%s{topIdent fn.Name}$tcbody\"(ctx, ret) catch {{")
                        .AppendLine($"        fable_rt.plugRet(%s{retZig}, ret);")
                        .AppendLine("        return .raised;")
                        .AppendLine("    };")
                        .AppendLine(
                            "    if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{ ctx, _next.ret });"
                        )
                        .AppendLine("    return .ok;")
                        .AppendLine("}")
                    |> ignore
                else
                    let loadArgs =
                        fn.Params |> List.mapi (fun i _ -> $"_tca[%d{i}]") |> String.concat ", "

                    out
                        .AppendLine(tcEntryHeader)
                        .AppendLine($"    if (comptime fable_rt.fitsTailArgs(&.{{ %s{paramTysStr} }})) {{")
                        .AppendLine($"        const _tca = fable_rt.tailLoad(&.{{ %s{paramTysStr} }}, ctx);")
                        .AppendLine(
                            $"        const _next = @\"%s{topIdent fn.Name}$tcbody\"(ctx, ret, %s{loadArgs}) catch {{"
                        )
                        .AppendLine($"            fable_rt.plugRet(%s{retZig}, ret);")
                        .AppendLine("            return .raised;")
                        .AppendLine("        };")
                        .AppendLine(
                            "        if (_next.func) |tcfn| return @call(fable_rt.tail_call, tcfn, .{ ctx, _next.ret });"
                        )
                        .AppendLine("        return .ok;")
                        .AppendLine("    } else {")
                        .AppendLine("        unreachable;")
                        .AppendLine("    }")
                        .AppendLine("}")
                    |> ignore

                if not fn.NeedsChain then
                    emitThinTc out "" $"@\"%s{topIdent fn.Name}$tcthin\"" "" (topIdent fn.Name) fn

                    out.AppendLine(
                        $"%s{visibility}const @\"%s{topIdent fn.Name}$tc\" = if (%s{chainName fn.Name}) @\"%s{topIdent fn.Name}$tcfull\" else @\"%s{topIdent fn.Name}$tcthin\";"
                    )
                    |> ignore
            elif not fn.IsLocal && not noTc then
                emitThinTc out "" $"@\"%s{topIdent fn.Name}$tc\"" visibility (topIdent fn.Name) fn

        if hasManaged fn && not fn.IsLocal then
            out.AppendLine($"pub const %s{sigName fn.Name} = %s{formatSigValue fn};")
            |> ignore

        if not fn.IsLocal then
            out.AppendLine($"pub const %s{storesName fn.Name} = %s{formatStoresValue fn};")
            |> ignore

        if not noTc && (not fn.IsLocal || fnHasTcBody fn) then
            out.AppendLine($"%s{visibility}const %s{chainName fn.Name}: bool = %s{fnChainConstExpr fn};")
            |> ignore

        out.AppendLine() |> ignore

    for fn in state.Fns do
        try
            let noTc = specialNoTc.Contains fn.Name

            match sccByMember.TryGetValue fn.Name with
            | true, (scc, sccBase, tagMap) ->
                if emittedSccs.Add sccBase then
                    emitScc scc sccBase tagMap

                emitSccMemberWrapper noTc fn sccBase tagMap
            | _ ->
                emitFunction
                    out
                    rootNames
                    fableAliases
                    specialNoTc
                    noTailCalls
                    adapters
                    knowns
                    knownIfaces
                    ifaceVts
                    fns
                    state.Curried2
                    noTc
                    fn
        with ZigError(msg, None) ->
            raise (ZigError(msg, fn.Range))
