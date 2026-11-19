/// Tier 2 cross-file `HofUnit` cloning, hashing, export, and import rewriting.
module Fable.Transforms.Zig.PerceusTier2

open System.Collections.Generic
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.Facts
open Fable.Transforms.Zig.PerceusAnalysis
open Fable.Transforms.Zig.PerceusHof

/// Snapshot and prepared local state before awaiting cross-file facts.
type LocalPrepared =
    {
        State: FileState
        Hooks: HashSet<string>
        SnapshotFns: Map<string, FnInfo>
        SnapshotCurried2: Map<string, string>
    }

/// Context needed for Tier 2 cross-file `HofUnit` cloning.
type Tier2Context =
    {
        CallerZigPath: string
        ImportTargets: Facts.ImportTarget list
        ImportFacts: Map<string, Facts.FileFacts>
        ResolveLibPath: string -> string
        LookupCachedFacts: string option -> string -> Facts.FileFacts option
    }

let internal emitIdentRx =
    System.Text.RegularExpressions.Regex(
        @"(?<![\w.$@])(@""[^""]+""|[A-Za-z_][A-Za-z0-9_]*)",
        System.Text.RegularExpressions.RegexOptions.Compiled
    )

/// Deterministic cycle-safe SHA-256 digest over a `HofUnit`'s bodies, signatures, `NoEscape`, and imports.
let internal computeHofUnitHash
    (unitName: string)
    (noEscape: bool list)
    (unitFns: FnInfo list)
    (unitCurried2: (string * string) list)
    (unitImports: Facts.HofImport list)
    : string
    =
    let sb = System.Text.StringBuilder()
    let seenEnts = HashSet<string>()
    let extraDefs = System.Collections.Generic.List<Ent>()

    let rec writeTy (t: Ty) =
        match t with
        | TPrim s -> sb.Append("P(").Append(s).Append(')') |> ignore
        | TGen n -> sb.Append("G(").Append(n).Append(')') |> ignore
        | TOpt x ->
            sb.Append("O(") |> ignore
            writeTy x
            sb.Append(')') |> ignore
        | TTuple ts ->
            sb.Append("T(") |> ignore

            ts
            |> List.iteri (fun i x ->
                if i > 0 then
                    sb.Append(',') |> ignore

                writeTy x
            )

            sb.Append(')') |> ignore
        | TPtr(x, c) ->
            sb.Append("Ptr(").Append(c).Append(',') |> ignore
            writeTy x
            sb.Append(')') |> ignore
        | TSlice(x, c) ->
            sb.Append("Slc(").Append(c).Append(',') |> ignore
            writeTy x
            sb.Append(')') |> ignore
        | TArr(x, n) ->
            sb.Append("Arr(").Append(n).Append(',') |> ignore
            writeTy x
            sb.Append(')') |> ignore
        | TFn(ps, r) ->
            sb.Append("Fn(") |> ignore

            ps
            |> List.iteri (fun i p ->
                if i > 0 then
                    sb.Append(',') |> ignore

                writeTy p
            )

            sb.Append("->") |> ignore
            writeTy r
            sb.Append(')') |> ignore
        | TSlot(ps, r) ->
            sb.Append("Slot(") |> ignore

            ps
            |> List.iteri (fun i p ->
                if i > 0 then
                    sb.Append(',') |> ignore

                writeTy p
            )

            sb.Append("->") |> ignore
            writeTy r
            sb.Append(')') |> ignore
        | TTok(x, c) ->
            sb.Append("Tok(").Append(c).Append(',') |> ignore
            writeTy x
            sb.Append(')') |> ignore
        | TEnt(e, args) ->
            if seenEnts.Add(e.Ref.FullName + "|" + e.Name) && e.IsLocal then
                extraDefs.Add e

            sb
                .Append("Ent(")
                .Append(e.Ref.FullName)
                .Append('|')
                .Append(e.Name)
                .Append('|')
                .Append(string e.Kind)
                .Append('|')
                .Append(e.IsLocal)
                .Append('[')
            |> ignore

            args
            |> List.iteri (fun i a ->
                if i > 0 then
                    sb.Append(',') |> ignore

                writeTy a
            )

            sb.Append("])") |> ignore

    let writeVar (v: Var) =
        sb
            .Append("V(")
            .Append(v.Id)
            .Append(',')
            .Append(v.Base)
            .Append(',')
            .Append(string v.Kind)
            .Append(',')
            .Append(v.FMutable)
            .Append(',')
        |> ignore

        writeTy v.Ty
        sb.Append(')') |> ignore

    let rec writeExpr (e: Expr) =
        match e with
        | EVar v -> writeVar v
        | ELit(s, t) ->
            sb.Append("Lit(").Append(s).Append(',') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EUnit -> sb.Append("Unit") |> ignore
        | EPrim(op, xs, t) ->
            sb.Append("Prim(").Append(op).Append('[') |> ignore
            List.iter writeExpr xs
            sb.Append("],") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ECall(f, tys, xs, t) ->
            sb.Append("Call(").Append(f).Append('<') |> ignore
            List.iter writeTy tys
            sb.Append(">(") |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ECallClo(f, xs, t) ->
            sb.Append("CallClo(") |> ignore
            writeExpr f
            sb.Append('(') |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ECallVt(f, s, xs, t) ->
            sb.Append("CallVt(") |> ignore
            writeExpr f
            sb.Append(',') |> ignore
            writeExpr s
            sb.Append('(') |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EClosure(f, tys, xs, t) ->
            sb.Append("Clo(").Append(f).Append('<') |> ignore
            List.iter writeTy tys
            sb.Append(">(") |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EKnown(f, tys, xs, t) ->
            sb.Append("Known(").Append(f).Append('<') |> ignore
            List.iter writeTy tys
            sb.Append(">(") |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EUse(u, x) ->
            sb.Append("Use(").Append(string u).Append(',') |> ignore
            writeExpr x
            sb.Append(')') |> ignore
        | EAssumedRet(js, c) ->
            sb.Append("Assumed(") |> ignore

            for j in js do
                sb.Append(j).Append(';') |> ignore

            writeExpr c
            sb.Append(')') |> ignore
        | EIface _ -> sb.Append("Iface") |> ignore
        | EKnownIface _ -> sb.Append("KnownIface") |> ignore
        | ECallIface(r, slot, xs, t) ->
            sb.Append("CallIface(").Append(slot).Append(',') |> ignore
            writeExpr r
            sb.Append('(') |> ignore
            List.iter writeExpr xs
            sb.Append("):") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ECon(t, c, xs, tok) ->
            sb.Append("Con(").Append(c).Append(',') |> ignore
            writeTy t
            sb.Append('(') |> ignore
            List.iter writeExpr xs
            sb.Append(')') |> ignore

            match tok with
            | Some tk -> writeVar tk
            | None -> ()

            sb.Append(')') |> ignore
        | EGet(x, proj, t) ->
            sb.Append("Get(").Append(projKey proj).Append(',') |> ignore
            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ETest(x, c, t) ->
            sb.Append("Test(").Append(c).Append(',') |> ignore
            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EAddr(x, c) ->
            sb.Append("Addr(").Append(c).Append(',') |> ignore
            writeExpr x
            sb.Append(')') |> ignore
        | EDeref(x, t) ->
            sb.Append("Deref(") |> ignore
            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EIndex(a, b, t) ->
            sb.Append("Idx(") |> ignore
            writeExpr a
            sb.Append(',') |> ignore
            writeExpr b
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EEmit(m, xs, t) ->
            sb.Append("Emit(").Append(m).Append('[') |> ignore
            List.iter writeExpr xs
            sb.Append("]:") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ERt(m, xs, t) ->
            sb.Append("Rt(").Append(m).Append('[') |> ignore
            List.iter writeExpr xs
            sb.Append("]:") |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EExnNew(ent, xs) ->
            sb.Append("ExnNew(").Append(ent.Ref.FullName).Append('|').Append(ent.Name).Append('[')
            |> ignore

            List.iter writeExpr xs
            sb.Append("])") |> ignore
        | EExnTest(x, ent) ->
            sb.Append("ExnTest(").Append(ent.Ref.FullName).Append('|').Append(ent.Name).Append(',')
            |> ignore

            writeExpr x
            sb.Append(')') |> ignore
        | EExnGet(x, ent, f, t) ->
            sb.Append("ExnGet(").Append(ent.Ref.FullName).Append('|').Append(ent.Name).Append('.').Append(f).Append(',')
            |> ignore

            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | EOnRaise(x, ds) ->
            sb.Append("OnRaise(") |> ignore
            writeExpr x
            sb.Append('[') |> ignore
            List.iter writeVar ds
            sb.Append("])") |> ignore
        | EDup(x, t) ->
            sb.Append("Dup(") |> ignore
            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ELet(v, r, b) ->
            sb.Append("Let(") |> ignore
            writeVar v
            sb.Append('=') |> ignore
            writeExpr r
            sb.Append(" in ") |> ignore
            writeExpr b
            sb.Append(')') |> ignore
        | ESeq(a, b) ->
            sb.Append("Seq(") |> ignore
            writeExpr a
            sb.Append(';') |> ignore
            writeExpr b
            sb.Append(')') |> ignore
        | EIf(c, t, f, ty) ->
            sb.Append("If(") |> ignore
            writeExpr c
            sb.Append('?') |> ignore
            writeExpr t
            sb.Append(':') |> ignore
            writeExpr f
            sb.Append('#') |> ignore
            writeTy ty
            sb.Append(')') |> ignore
        | EWhile(c, b) ->
            sb.Append("While(") |> ignore
            writeExpr c
            sb.Append(',') |> ignore
            writeExpr b
            sb.Append(')') |> ignore
        | EFor(i, a, b, up, body) ->
            sb.Append("For(") |> ignore
            writeVar i
            sb.Append(',') |> ignore
            writeExpr a
            sb.Append(',') |> ignore
            writeExpr b
            sb.Append(',').Append(up).Append(',') |> ignore
            writeExpr body
            sb.Append(')') |> ignore
        | EAssign(v, r) ->
            sb.Append("Assign(") |> ignore
            writeVar v
            sb.Append(',') |> ignore
            writeExpr r
            sb.Append(')') |> ignore
        | EStore(lv, r) ->
            sb.Append("Store(") |> ignore
            writeExpr lv
            sb.Append(',') |> ignore
            writeExpr r
            sb.Append(')') |> ignore
        | EDrop(v, k) ->
            sb.Append("Drop(") |> ignore
            writeVar v
            sb.Append(',') |> ignore
            writeExpr k
            sb.Append(')') |> ignore
        | EUnpack(u, k) ->
            sb.Append("Unpack(").Append(u.Case).Append(',').Append(u.Heap).Append(',')
            |> ignore

            writeVar u.Scrut
            sb.Append(',') |> ignore
            writeExpr k
            sb.Append(')') |> ignore
        | EPromote(v, k) ->
            sb.Append("Promote(") |> ignore
            writeVar v
            sb.Append(',') |> ignore
            writeExpr k
            sb.Append(')') |> ignore
        | ERaise(x, t) ->
            sb.Append("Raise(") |> ignore
            writeExpr x
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore
        | ETry(b, v, h, t) ->
            sb.Append("Try(") |> ignore
            writeExpr b
            sb.Append(" catch ") |> ignore
            writeVar v
            sb.Append("=>") |> ignore
            writeExpr h
            sb.Append(':') |> ignore
            writeTy t
            sb.Append(')') |> ignore

    sb.Append("unit:").Append(unitName).Append(";ne:") |> ignore

    for b in noEscape do
        sb.Append(
            if b then
                '1'
            else
                '0'
        )
        |> ignore

    sb.Append(";fns:[") |> ignore

    for u in unitFns do
        sb.Append(u.Name).Append('<') |> ignore
        sb.Append(String.concat "," u.TypeParams).Append(">(") |> ignore

        for param in u.Params do
            writeVar param
            sb.Append(',') |> ignore

        sb.Append(")->") |> ignore
        writeTy u.Ret
        sb.Append('=') |> ignore
        writeExpr u.Body
        sb.Append(';') |> ignore

    sb.Append("];c2:[") |> ignore

    for (a, b) in List.sort unitCurried2 do
        sb.Append(a).Append("->").Append(b).Append(';') |> ignore

    sb.Append("];imp:[") |> ignore

    for imp in unitImports |> List.sortBy (fun i -> i.CalleeAlias, i.ZigPath) do
        sb.Append(imp.CalleeAlias).Append('=').Append(imp.ZigPath).Append(';') |> ignore

    sb.Append("];ents:[") |> ignore

    let mutable idx = 0

    while idx < extraDefs.Count do
        let e = extraDefs[idx]
        idx <- idx + 1

        sb
            .Append(e.Name)
            .Append('|')
            .Append(string e.Kind)
            .Append('|')
            .Append(e.Managed)
            .Append('|')
            .Append(e.Cyclic)
            .Append('|')
            .Append(String.concat "," e.MutableFields)
            .Append('{')
        |> ignore

        for (cName, fields) in e.Cases do
            sb.Append(cName).Append(':') |> ignore

            for (fName, fTy) in fields do
                sb.Append(fName).Append('=') |> ignore
                writeTy fTy
                sb.Append(';') |> ignore

        sb.Append("};") |> ignore

    sb.Append(']') |> ignore

    let bytes = System.Text.Encoding.UTF8.GetBytes(sb.ToString())
    use sha = System.Security.Cryptography.SHA256.Create()
    let digest = sha.ComputeHash(bytes)
    System.BitConverter.ToString(digest).Replace("-", "").ToLowerInvariant()

/// Build exportable Tier 2 `HofUnit` snapshots for eligible public HOFs (non-escaping fn params,
/// total pre-specialization size <= 250, no local-only entities/globals/emits/ifaces/arenas/hooks).
let internal exportHofUnits (prep: LocalPrepared) (p: P) (tier2Opt: Tier2Context option) : Map<string, Facts.HofUnit> =
    let state = prep.State
    let hooks = prep.Hooks

    let calleeZigPath =
        tier2Opt |> Option.map (fun t -> t.CallerZigPath) |> Option.defaultValue ""

    let targetByAlias =
        match tier2Opt with
        | Some t -> t.ImportTargets |> List.map (fun tgt -> tgt.Alias, tgt) |> Map.ofList
        | None -> Map.empty

    let rawKeyByAlias =
        state.Imports |> Seq.map (fun kv -> kv.Value, kv.Key) |> Map.ofSeq

    let userAliases = HashSet<string>(state.UserImports.Values)
    let pubLocalEntNames = state.LocalEnts |> Seq.map (fun e -> e.Name) |> HashSet
    let pubGlobals = HashSet<string>()

    for (n, _, _) in state.Consts do
        pubGlobals.Add n |> ignore

    for (n, _, _) in state.Values do
        pubGlobals.Add n |> ignore

    let localFileSymbols = HashSet<string>()

    let addSym (s: string) =
        if not (System.String.IsNullOrEmpty s) then
            localFileSymbols.Add s |> ignore
            localFileSymbols.Add(cleanIdent s) |> ignore
            localFileSymbols.Add(topIdent s) |> ignore

    for fn in state.Fns do
        addSym fn.Name

    for kv in prep.SnapshotFns do
        addSym kv.Key

    for (n, _, _) in state.Consts do
        addSym n

    for (n, _, _) in state.Values do
        addSym n

    for e in state.LocalEnts do
        addSym e.Name

    for o in state.Objs do
        addSym o.TypeName

        match o.Chain with
        | TEnt(e, _) -> addSym e.Name
        | _ -> ()

        for (thName, _, _, _, _) in o.Thunks do
            addSym thName

    for a in state.Imports.Values do
        addSym a

    for a in state.UserImports.Values do
        addSym a

    localFileSymbols.Remove "fable_rt" |> ignore
    localFileSymbols.Remove "std" |> ignore

    let result = Dictionary<string, Facts.HofUnit>()

    for fn in state.Fns do
        if
            not fn.IsLocal
            && not fn.IsEntryPoint
            && not (hooks.Contains fn.Name)
            && fn.NoEscape.Length = fn.Params.Length
            && List.exists2
                (fun (q: Var) noEsc ->
                    noEsc
                    && (
                        match q.Ty with
                        | TFn _ -> true
                        | _ -> false
                    )
                )
                fn.Params
                fn.NoEscape
        then
            match prep.SnapshotFns.TryFind fn.Name with
            | None -> ()
            | Some topSnap ->
                let reachable = System.Collections.Generic.List<FnInfo>()
                let seenFns = HashSet<string>()
                let work = Queue<FnInfo>()
                let mutable bfsOk = true

                seenFns.Add fn.Name |> ignore
                work.Enqueue topSnap

                while bfsOk && work.Count > 0 do
                    let cur = work.Dequeue()
                    reachable.Add cur

                    let tryEnqueue (target: string) =
                        if bfsOk && not (target.Contains ".") && not (seenFns.Contains target) then
                            match prep.SnapshotFns.TryFind target with
                            | Some g when g.IsLocal ->
                                seenFns.Add target |> ignore
                                work.Enqueue g
                            | Some _ -> ()
                            | None -> bfsOk <- false

                    exists
                        (fun x ->
                            match x with
                            | ECall(g, _, _, _) -> tryEnqueue g
                            | EClosure(g, _, _, ty)
                            | EKnown(g, _, _, ty) ->
                                tryEnqueue g

                                match ty with
                                | TFn([ _ ], TFn([ _ ], _)) ->
                                    match prep.SnapshotCurried2.TryFind g with
                                    | Some g2 -> tryEnqueue g2
                                    | None -> ()
                                | _ -> ()
                            | _ -> ()

                            false
                        )
                        cur.Body
                    |> ignore

                let unitFns = List.ofSeq reachable

                if bfsOk && (unitFns |> List.sumBy (fun u -> exprSize u.Body)) <= 250 then
                    let mutable ok = true
                    let usedImports = Dictionary<string, Facts.HofImport>()
                    let extraEnts = Dictionary<string, Ent>()
                    let checkedEnts = HashSet<string>()

                    let recordImportAlias (alias: string) =
                        if userAliases.Contains alias then
                            ok <- false
                        elif not (usedImports.ContainsKey alias) then
                            match targetByAlias.TryFind alias, rawKeyByAlias.TryFind alias with
                            | Some tgt, Some rawKey ->
                                usedImports[alias] <-
                                    {
                                        CalleeAlias = alias
                                        ZigPath = tgt.ZigPath
                                        FsPath = tgt.FsPath
                                        RawKey = rawKey
                                    }
                            | _ -> ok <- false

                    let rec checkEntAndTy (t: Ty) =
                        if ok then
                            match t with
                            | TPrim _
                            | TGen _ -> ()
                            | TOpt x
                            | TPtr(x, _)
                            | TSlice(x, _)
                            | TArr(x, _)
                            | TTok(x, _) -> checkEntAndTy x
                            | TTuple xs -> List.iter checkEntAndTy xs
                            | TFn(ps, r)
                            | TSlot(ps, r) ->
                                List.iter checkEntAndTy ps
                                checkEntAndTy r
                            | TEnt(ent, args) ->
                                checkEnt ent
                                List.iter checkEntAndTy args

                    and checkEnt (ent: Ent) =
                        if ok then
                            let ek = ent.Ref.FullName + "|" + ent.Name

                            if ent.IsLocal then
                                if not (pubLocalEntNames.Contains ent.Name) then
                                    ok <- false
                                elif checkedEnts.Add ek then
                                    for (_, fs) in ent.Cases do
                                        for (_, fTy) in fs do
                                            checkEntAndTy fTy
                            elif
                                ent.Ref.FullName.StartsWith("$anon:", System.StringComparison.Ordinal)
                                || ent.Ref.FullName.StartsWith("$iface:", System.StringComparison.Ordinal)
                            then
                                extraEnts[ent.Ref.FullName] <- ent

                                if checkedEnts.Add ek then
                                    for (_, fs) in ent.Cases do
                                        for (_, fTy) in fs do
                                            checkEntAndTy fTy
                            elif ent.Name.StartsWith("fable_rt.", System.StringComparison.Ordinal) then
                                if checkedEnts.Add ek then
                                    for (_, fs) in ent.Cases do
                                        for (_, fTy) in fs do
                                            checkEntAndTy fTy
                            else
                                match ent.Name.IndexOf '.' with
                                | dot when dot > 0 ->
                                    recordImportAlias (ent.Name.Substring(0, dot))

                                    if ok && checkedEnts.Add ek then
                                        for (_, fs) in ent.Cases do
                                            for (_, fTy) in fs do
                                                checkEntAndTy fTy
                                | _ -> ok <- false

                    let checkTargetFn (f: string) =
                        if ok then
                            match f.IndexOf '.' with
                            | -1 ->
                                if not (seenFns.Contains f) then
                                    match prep.SnapshotFns.TryFind f with
                                    | Some g when not g.IsLocal && not g.IsEntryPoint && not (hooks.Contains g.Name) ->
                                        ()
                                    | _ -> ok <- false
                            | dot -> recordImportAlias (f.Substring(0, dot))

                    let checkEmitMacro (macro: string) =
                        if macro.Contains "@This" then
                            ok <- false
                        else
                            for m in emitIdentRx.Matches macro do
                                let raw = m.Groups.[1].Value

                                let unquoted =
                                    if raw.StartsWith("@\"", System.StringComparison.Ordinal) && raw.Length >= 3 then
                                        raw.Substring(2, raw.Length - 3)
                                    else
                                        raw

                                if localFileSymbols.Contains raw || localFileSymbols.Contains unquoted then
                                    ok <- false

                    let checkGlobalVar (v: Var) =
                        checkEntAndTy v.Ty

                        if not (v.Base.Contains ".") then
                            if not (pubGlobals.Contains v.Base) then
                                ok <- false
                        else
                            let dot = v.Base.IndexOf '.'
                            let alias = v.Base.Substring(0, dot)

                            if alias <> "fable_rt" && alias <> "std" then
                                recordImportAlias alias

                    let rec walkExpr (e: Expr) =
                        if ok then
                            match e with
                            | EVar v ->
                                if v.Kind = VGlobal then
                                    checkGlobalVar v
                                else
                                    checkEntAndTy v.Ty
                            | ELit(_, t)
                            | ERaise(_, t) ->
                                checkEntAndTy t

                                match e with
                                | ERaise(x, _) -> walkExpr x
                                | _ -> ()
                            | EUnit -> ()
                            | EPrim(_, xs, t) ->
                                checkEntAndTy t
                                List.iter walkExpr xs
                            | ECall(f, tys, xs, t) ->
                                checkTargetFn f
                                List.iter checkEntAndTy tys
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | ECallClo(f, xs, t) ->
                                walkExpr f
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | ECallVt(f, s, xs, t) ->
                                walkExpr f
                                walkExpr s
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | EClosure(f, tys, xs, t)
                            | EKnown(f, tys, xs, t) ->
                                checkTargetFn f
                                List.iter checkEntAndTy tys
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | EUse(_, x)
                            | EAssumedRet(_, x) -> walkExpr x
                            | EIface _
                            | EKnownIface _ -> ok <- false
                            | ECallIface(r, _, xs, t) ->
                                walkExpr r
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | ECon(t, _, xs, tok) ->
                                checkEntAndTy t
                                List.iter walkExpr xs

                                match tok with
                                | Some tk -> checkEntAndTy tk.Ty
                                | None -> ()
                            | EGet(x, _, t)
                            | ETest(x, _, t)
                            | EDeref(x, t)
                            | EDup(x, t) ->
                                walkExpr x
                                checkEntAndTy t
                            | EAddr(x, _) -> walkExpr x
                            | EIndex(a, b, t) ->
                                walkExpr a
                                walkExpr b
                                checkEntAndTy t
                            | EEmit(m, xs, t) ->
                                checkEmitMacro m
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | ERt(_, xs, t) ->
                                List.iter walkExpr xs
                                checkEntAndTy t
                            | EExnNew(ent, xs) ->
                                checkEnt ent
                                List.iter walkExpr xs
                            | EExnTest(x, ent) ->
                                checkEnt ent
                                walkExpr x
                            | EExnGet(x, ent, _, t) ->
                                checkEnt ent
                                walkExpr x
                                checkEntAndTy t
                            | EOnRaise(x, ds) ->
                                walkExpr x

                                for d in ds do
                                    checkEntAndTy d.Ty
                            | ELet(v, r, b) ->
                                checkEntAndTy v.Ty
                                walkExpr r
                                walkExpr b
                            | ESeq(a, b)
                            | EWhile(a, b)
                            | EStore(a, b) ->
                                walkExpr a
                                walkExpr b
                            | EIf(c, t, f, ty) ->
                                walkExpr c
                                walkExpr t
                                walkExpr f
                                checkEntAndTy ty
                            | EFor(v, a, b, _, body) ->
                                checkEntAndTy v.Ty
                                walkExpr a
                                walkExpr b
                                walkExpr body
                            | EAssign(v, r) ->
                                if v.Kind = VGlobal then
                                    checkGlobalVar v
                                else
                                    checkEntAndTy v.Ty

                                walkExpr r
                            | EDrop(v, k)
                            | EPromote(v, k) ->
                                checkEntAndTy v.Ty
                                walkExpr k
                            | EUnpack(u, k) ->
                                checkEntAndTy u.Scrut.Ty

                                for (_, mv) in u.Moves do
                                    checkEntAndTy mv.Ty

                                for (_, dt) in u.Drops do
                                    checkEntAndTy dt

                                walkExpr k
                            | ETry(b, v, h, t) ->
                                checkEntAndTy v.Ty
                                checkEntAndTy t
                                walkExpr b
                                walkExpr h

                    for uFn in unitFns do
                        if
                            not ok
                            || uFn.IsEntryPoint
                            || hooks.Contains uFn.Name
                            || state.Arenas.ContainsKey uFn.Name
                        then
                            ok <- false
                        else
                            for param in uFn.Params do
                                checkEntAndTy param.Ty

                            checkEntAndTy uFn.Ret
                            walkExpr uFn.Body

                    if ok then
                        let unitCurried2 =
                            prep.SnapshotCurried2
                            |> Seq.choose (fun kv ->
                                if seenFns.Contains kv.Key && seenFns.Contains kv.Value then
                                    Some(kv.Key, kv.Value)
                                else
                                    None
                            )
                            |> Seq.sort
                            |> List.ofSeq

                        let unitImports =
                            usedImports.Values |> Seq.sortBy (fun i -> i.CalleeAlias) |> List.ofSeq

                        let unitExtraEnts =
                            extraEnts
                            |> Seq.map (fun kv -> kv.Key, kv.Value)
                            |> Seq.sortBy fst
                            |> List.ofSeq

                        let unitHash =
                            computeHofUnitHash fn.Name fn.NoEscape unitFns unitCurried2 unitImports

                        result[fn.Name] <-
                            {
                                Name = fn.Name
                                Hash = unitHash
                                CalleeZigPath = calleeZigPath
                                Fns = unitFns
                                Curried2 = unitCurried2
                                Imports = unitImports
                                ExtraEnts = unitExtraEnts
                            }

    result |> Seq.map (fun kv -> kv.Key, kv.Value) |> Map.ofSeq

/// Clone eligible imported `HofUnit`s into the caller when a call site passes at least one
/// known caller closure to a non-escaping parameter, then run `specializeHofs` to fold them.
let internal importTier2Hofs
    (state: FileState)
    (hooks: HashSet<string>)
    (tier2: Tier2Context)
    : string list * Map<string, Facts.FileFacts>
    =
    let zigPathToAlias = Dictionary<string, string>()

    for tgt in tier2.ImportTargets do
        zigPathToAlias[tgt.ZigPath] <- tgt.Alias

    let usedAliases =
        HashSet<string>(Seq.append state.Imports.Values state.UserImports.Values)

    let usedTopNames = HashSet<string>()

    for fn in state.Fns do
        usedTopNames.Add fn.Name |> ignore

    for (n, _, _) in state.Values do
        usedTopNames.Add n |> ignore

    for (n, _, _) in state.Consts do
        usedTopNames.Add n |> ignore

    for e in state.LocalEnts do
        usedTopNames.Add e.Name |> ignore

    let callerFnNames = HashSet<string>(state.Fns |> Seq.map (fun fn -> fn.Name))
    let extraFacts = Dictionary<string, Facts.FileFacts>()
    let addedFsImports = List<string>()

    let freshAlias (hint: string) =
        let baseName = "m_" + cleanIdent hint
        let mutable cand = baseName
        let mutable i = 1

        while usedAliases.Contains cand do
            cand <- $"%s{baseName}_%d{i}"
            i <- i + 1

        usedAliases.Add cand |> ignore
        cand

    let freshUnitFnName (prefix: string) =
        let mutable i = 0
        let mutable cand = $"%s{prefix}_%d{i}"

        while usedTopNames.Contains cand do
            i <- i + 1
            cand <- $"%s{prefix}_%d{i}"

        usedTopNames.Add cand |> ignore
        cand

    let ensureImport (imp: Facts.HofImport) : string =
        match zigPathToAlias.TryGetValue imp.ZigPath with
        | true, existing -> existing
        | _ ->
            let rawKey =
                match imp.FsPath with
                | Some fsPath ->
                    addedFsImports.Add fsPath
                    fsPath
                | None ->
                    let modName = System.IO.Path.GetFileNameWithoutExtension imp.ZigPath
                    tier2.ResolveLibPath modName

            let alias =
                match state.Imports.TryGetValue rawKey with
                | true, existing -> existing
                | _ ->
                    let a = freshAlias (System.IO.Path.GetFileNameWithoutExtension imp.ZigPath)
                    state.Imports[rawKey] <- a
                    a

            zigPathToAlias[imp.ZigPath] <- alias

            match tier2.LookupCachedFacts imp.FsPath imp.ZigPath with
            | Some ff -> extraFacts[alias] <- ff
            | None -> ()

            alias

    let clonedUnits = Dictionary<string, string>()

    let cloneUnit (calleeAlias: string) (unit: Facts.HofUnit) : string =
        let memoKey = calleeAlias + ":" + unit.Name

        match clonedUnits.TryGetValue memoKey with
        | true, topName -> topName
        | _ ->
            let impAliasMap =
                unit.Imports
                |> List.map (fun imp -> imp.CalleeAlias, ensureImport imp)
                |> Map.ofList

            let remappedEnts = Dictionary<string, Ent>()
            let entKey (e: Ent) = e.Ref.FullName + "|" + e.Name

            let rec remapEnt (ent: Ent) : Ent =
                let k = entKey ent

                match remappedEnts.TryGetValue k with
                | true, existing -> existing
                | _ ->
                    match state.Ents.TryGetValue ent.Ref.FullName with
                    | true, existing ->
                        remappedEnts[k] <- existing
                        existing
                    | _ ->
                        let newName, newHooks =
                            if ent.IsLocal then
                                let h =
                                    ent.Hooks
                                    |> Option.map (fun (d, dup) ->
                                        let q (s: string) =
                                            if s.Contains "." then
                                                s
                                            else
                                                calleeAlias + "." + s

                                        q d, Option.map q dup
                                    )

                                calleeAlias + "." + ent.Name, h
                            elif ent.Name.StartsWith("fable_rt.", System.StringComparison.Ordinal) then
                                state.UsesRuntime <- true
                                ent.Name, ent.Hooks
                            elif
                                ent.Ref.FullName.StartsWith("$anon:", System.StringComparison.Ordinal)
                                || ent.Ref.FullName.StartsWith("$iface:", System.StringComparison.Ordinal)
                            then
                                state.UsesRuntime <- true
                                ent.Name, ent.Hooks
                            else
                                match ent.Name.IndexOf '.' with
                                | -1 -> calleeAlias + "." + ent.Name, ent.Hooks
                                | dot ->
                                    let oldAlias = ent.Name.Substring(0, dot)
                                    let rest = ent.Name.Substring(dot + 1)

                                    let newAlias = impAliasMap.TryFind oldAlias |> Option.defaultValue oldAlias

                                    newAlias + "." + rest, ent.Hooks

                        let e' =
                            { ent with
                                Name = newName
                                IsLocal = false
                                Cases = []
                                Hooks = newHooks
                                Overrides = []
                            }

                        remappedEnts[k] <- e'

                        e'.Cases <-
                            ent.Cases
                            |> List.map (fun (cName, fields) ->
                                cName, fields |> List.map (fun (fName, fTy) -> fName, remapTy fTy)
                            )

                        e'

            and remapTy (t: Ty) : Ty =
                match t with
                | TPrim _
                | TGen _ -> t
                | TOpt x -> TOpt(remapTy x)
                | TTuple xs -> TTuple(List.map remapTy xs)
                | TPtr(x, c) -> TPtr(remapTy x, c)
                | TSlice(x, c) -> TSlice(remapTy x, c)
                | TArr(x, n) -> TArr(remapTy x, n)
                | TFn(ps, r) -> TFn(List.map remapTy ps, remapTy r)
                | TSlot(ps, r) -> TSlot(List.map remapTy ps, remapTy r)
                | TTok(x, c) -> TTok(remapTy x, c)
                | TEnt(ent, args) -> TEnt(remapEnt ent, List.map remapTy args)

            for (extraKey, extraEnt) in unit.ExtraEnts do
                if not (state.Ents.ContainsKey extraKey) then
                    state.Ents[extraKey] <- remapEnt extraEnt

                state.UsesRuntime <- true

            let fnRename = Dictionary<string, string>()

            for uFn in unit.Fns do
                let cleanCallee = cleanIdent calleeAlias
                let cleanFn = cleanIdent uFn.Name
                fnRename[uFn.Name] <- freshUnitFnName $"%s{cleanCallee}_%s{cleanFn}$t2"

            let remapFnTarget (f: string) : string =
                match fnRename.TryGetValue f with
                | true, r -> r
                | _ ->
                    match f.IndexOf '.' with
                    | -1 -> calleeAlias + "." + f
                    | dot ->
                        let oldAlias = f.Substring(0, dot)
                        let rest = f.Substring(dot + 1)
                        let newAlias = impAliasMap.TryFind oldAlias |> Option.defaultValue oldAlias
                        newAlias + "." + rest

            for (c1, c2) in unit.Curried2 do
                match fnRename.TryGetValue c1, fnRename.TryGetValue c2 with
                | (true, r1), (true, r2) -> state.Curried2[r1] <- r2
                | _ -> ()

            for uFn in unit.Fns do
                let varMap = Dictionary<int, Var>()

                let freshVar (v: Var) =
                    let v' = state.NewVar(v.Base, remapTy v.Ty, v.Kind, v.FMutable)
                    varMap[v.Id] <- v'
                    v'

                let mapVar (v: Var) =
                    if v.Kind = VGlobal then
                        { v with
                            Base = remapFnTarget v.Base
                            Ty = remapTy v.Ty
                        }
                    else
                        match varMap.TryGetValue v.Id with
                        | true, v' -> v'
                        | _ -> v

                let newParams = uFn.Params |> List.map freshVar

                let rec remapExpr (e: Expr) : Expr =
                    match e with
                    | EVar v -> EVar(mapVar v)
                    | ELit(s, t) -> ELit(s, remapTy t)
                    | EUnit -> EUnit
                    | EPrim(op, xs, t) -> EPrim(op, List.map remapExpr xs, remapTy t)
                    | ECall(f, tys, xs, t) ->
                        ECall(remapFnTarget f, List.map remapTy tys, List.map remapExpr xs, remapTy t)
                    | ECallClo(f, xs, t) -> ECallClo(remapExpr f, List.map remapExpr xs, remapTy t)
                    | ECallVt(f, s, xs, t) -> ECallVt(remapExpr f, remapExpr s, List.map remapExpr xs, remapTy t)
                    | EClosure(f, tys, xs, t) ->
                        EClosure(remapFnTarget f, List.map remapTy tys, List.map remapExpr xs, remapTy t)
                    | EKnown(f, tys, xs, t) ->
                        EKnown(remapFnTarget f, List.map remapTy tys, List.map remapExpr xs, remapTy t)
                    | EUse(u, x) -> EUse(u, remapExpr x)
                    | EAssumedRet(js, x) -> EAssumedRet(js, remapExpr x)
                    | EIface(t, src, slots) -> EIface(remapTy t, src, slots)
                    | EKnownIface(t, src, slots, isOpt) -> EKnownIface(remapTy t, src, slots, isOpt)
                    | ECallIface(r, slot, xs, t) -> ECallIface(remapExpr r, slot, List.map remapExpr xs, remapTy t)
                    | ECon(t, c, xs, tok) -> ECon(remapTy t, c, List.map remapExpr xs, Option.map mapVar tok)
                    | EGet(x, p, t) -> EGet(remapExpr x, p, remapTy t)
                    | ETest(x, c, t) -> ETest(remapExpr x, c, remapTy t)
                    | EAddr(x, c) -> EAddr(remapExpr x, c)
                    | EDeref(x, t) -> EDeref(remapExpr x, remapTy t)
                    | EIndex(a, b, t) -> EIndex(remapExpr a, remapExpr b, remapTy t)
                    | EEmit(m, xs, t) ->
                        if m.Contains "fable_rt." then
                            state.UsesRuntime <- true

                        EEmit(m, List.map remapExpr xs, remapTy t)
                    | ERt(m, xs, t) ->
                        state.UsesRuntime <- true
                        ERt(m, List.map remapExpr xs, remapTy t)
                    | EExnNew(ent, xs) -> EExnNew(remapEnt ent, List.map remapExpr xs)
                    | EExnTest(x, ent) -> EExnTest(remapExpr x, remapEnt ent)
                    | EExnGet(x, ent, f, t) -> EExnGet(remapExpr x, remapEnt ent, f, remapTy t)
                    | EOnRaise(x, ds) -> EOnRaise(remapExpr x, List.map mapVar ds)
                    | EDup(x, t) -> EDup(remapExpr x, remapTy t)
                    | ELet(v, r, b) ->
                        let r' = remapExpr r
                        let v' = freshVar v
                        ELet(v', r', remapExpr b)
                    | ESeq(a, b) -> ESeq(remapExpr a, remapExpr b)
                    | EIf(c, t, f, ty) -> EIf(remapExpr c, remapExpr t, remapExpr f, remapTy ty)
                    | EWhile(c, b) -> EWhile(remapExpr c, remapExpr b)
                    | EFor(v, a, b, up, body) ->
                        let a' = remapExpr a
                        let b' = remapExpr b
                        let v' = freshVar v
                        EFor(v', a', b', up, remapExpr body)
                    | EAssign(v, r) -> EAssign(mapVar v, remapExpr r)
                    | EStore(lv, r) -> EStore(remapExpr lv, remapExpr r)
                    | EDrop(v, k) -> EDrop(mapVar v, remapExpr k)
                    | EUnpack(u, k) ->
                        let u' =
                            { u with
                                Scrut = mapVar u.Scrut
                                Moves = u.Moves |> List.map (fun (s, v) -> s, freshVar v)
                                Token = u.Token |> Option.map freshVar
                            }

                        EUnpack(u', remapExpr k)
                    | EPromote(v, k) -> EPromote(mapVar v, remapExpr k)
                    | ERaise(x, t) -> ERaise(remapExpr x, remapTy t)
                    | ETry(b, v, h, t) ->
                        let b' = remapExpr b
                        let v' = freshVar v
                        ETry(b', v', remapExpr h, remapTy t)

                let clonedBody = remapExpr uFn.Body

                state.Fns.Add
                    {
                        Name = fnRename[uFn.Name]
                        TypeParams = uFn.TypeParams
                        Params = newParams
                        Modes = newParams |> List.map (fun _ -> MPlain)
                        Ret = remapTy uFn.Ret
                        Body = clonedBody
                        RetFrom = None
                        Raises = RNever
                        Stores = false
                        IsLocal = true
                        IsEntryPoint = false
                        Range = uFn.Range
                        NoEscape = []
                        BodyK = None
                        StoreFacts = [], false, false
                        AssertedNoRaise = []
                        AssertedStores = []
                        NeedsChain = false
                        PendingChainDeps = []
                        BodyTc = None
                    }

            let topCloned = fnRename[unit.Name]
            clonedUnits[memoKey] <- topCloned
            topCloned

    let mutable anyCloned = false

    let rec rewriteCaller (env: Map<int, string * Ty list * Expr list * Ty>) (e: Expr) : Expr =
        let go = rewriteCaller env

        match e with
        | ELet(v, r, b) ->
            let r' = go r

            let env' =
                match r' with
                | EClosure(target, cTypeArgs, caps, cloTy) when not v.FMutable && capsAreImmutableVars caps ->
                    env.Add(v.Id, (target, cTypeArgs, caps, cloTy))
                | _ -> env

            ELet(v, r', rewriteCaller env' b)
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
                match calleeName.IndexOf '.' with
                | dot when dot > 0 ->
                    let calleeAlias = calleeName.Substring(0, dot)
                    let memberName = calleeName.Substring(dot + 1)

                    match tier2.ImportFacts.TryFind calleeAlias with
                    | Some fileFacts ->
                        match fileFacts.Fns.TryFind memberName with
                        | Some ff when ff.Hof.IsSome ->
                            let unit = ff.Hof.Value

                            match unit.Fns |> List.tryHead with
                            | Some topUnitFn when
                                callArgs.Length = topUnitFn.Params.Length
                                && callTypeArgs.Length = topUnitFn.TypeParams.Length
                                && ff.FnParamsNoEscape.Length = callArgs.Length
                                ->
                                let hasKnownCallerLambda =
                                    List.zip ff.FnParamsNoEscape callArgs
                                    |> List.exists (fun (noEsc, a) ->
                                        if not noEsc then
                                            false
                                        else
                                            match resolveKnownClosure env a with
                                            | Some(cloTarget, _, _, _) -> callerFnNames.Contains cloTarget
                                            | None -> false
                                    )

                                if hasKnownCallerLambda then
                                    anyCloned <- true
                                    let clonedTop = cloneUnit calleeAlias unit
                                    ECall(clonedTop, callTypeArgs, callArgs, callRetTy)
                                else
                                    e'
                            | _ -> e'
                        | _ -> e'
                    | None -> e'
                | _ -> e'
            | _ -> e'

    for fn in List.ofSeq state.Fns do
        fn.Body <- rewriteCaller Map.empty fn.Body

    if anyCloned then
        specializeHofs state hooks

    List.ofSeq addedFsImports |> List.distinct, extraFacts |> Seq.map (fun kv -> kv.Key, kv.Value) |> Map.ofSeq
