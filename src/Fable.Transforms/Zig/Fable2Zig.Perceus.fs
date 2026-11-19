/// The ownership passes on the IR: borrow inference for parameters and results, then Perceus
/// (dup/drop insertion, drop-unpack and reuse of dead cells).
module Fable.Transforms.Zig.Perceus

open System.Collections.Generic
open Fable.Transforms.Zig.IR
open Fable.Transforms.Zig.Facts
open Fable.Transforms.Zig.PerceusAnalysis
open Fable.Transforms.Zig.PerceusInsert
open Fable.Transforms.Zig.PerceusHof
open Fable.Transforms.Zig.PerceusTier2

type LocalPrepared = Fable.Transforms.Zig.PerceusTier2.LocalPrepared
type Tier2Context = Fable.Transforms.Zig.PerceusTier2.Tier2Context

/// Run the local normalization passes (cleanup, resource hooks scan, intra-file HOF specialization)
/// that need no cross-file facts.
let prepareLocal (state: FileState) : LocalPrepared =
    // The hooks of a resource only borrow the value they are given: the runtime calls them when
    // it gives the value up or copies it, and a hook that took it would give it up again.
    let hooks =
        state.Ents.Values
        |> Seq.choose (fun e -> e.Hooks)
        |> Seq.collect (fun (destroy, dup) -> destroy :: Option.toList dup)
        |> HashSet

    for fn in state.Fns do
        fn.Body <- cleanup fn.Body

    let snapshotFns =
        state.Fns
        |> Seq.map (fun fn -> fn.Name, { fn with Body = fn.Body })
        |> Map.ofSeq

    let snapshotCurried2 =
        state.Curried2 |> Seq.map (fun kv -> kv.Key, kv.Value) |> Map.ofSeq

    specializeHofs state hooks

    {
        State = state
        Hooks = hooks
        SnapshotFns = snapshotFns
        SnapshotCurried2 = snapshotCurried2
    }

/// Run cross-file-aware inference, publish public `FnFacts`, specialize `callK`, and run Perceus.
let inferAndFinish
    (prep: LocalPrepared)
    (extLookup: string -> Facts.FnFacts option)
    (tier2Opt: Tier2Context option)
    (publishFacts: string list -> Map<string, Facts.FnFacts> -> unit)
    : unit
    =
    let state = prep.State
    let hooks = prep.Hooks

    let addedFsImports, extraImportFacts =
        match tier2Opt with
        | Some tier2 -> importTier2Hofs state hooks tier2
        | None -> [], Map.empty

    let effectiveExtLookup (fname: string) =
        match extLookup fname with
        | Some _ as hit -> hit
        | None ->
            match fname.IndexOf '.' with
            | -1 -> None
            | dot ->
                let alias = fname.Substring(0, dot)
                let memberName = fname.Substring(dot + 1)

                match extraImportFacts.TryFind alias with
                | Some ff -> ff.Fns.TryFind memberName
                | None -> None

    let pureStdlibModules =
        HashSet
            [
                "List"
                "Array"
                "Seq"
                "Map"
                "Set"
                "Option"
                "Result"
                "Guid"
                "TimeSpan"
                "DateTime"
                "DateOnly"
                "DateTimeOffset"
                "Uri"
                "Path"
                "ResizeArray"
                "HashSet"
                "Queue"
                "Stack"
                "ListCollector"
            ]

    let hasFableLibPrefix =
        state.Imports.Keys
        |> Seq.exists (fun path -> path.Replace('\\', '/').Contains "fable-library-zig")

    let pureStdlibAliases =
        state.Imports
        |> Seq.choose (fun kv ->
            let norm = kv.Key.Replace('\\', '/')
            let baseName = System.IO.Path.GetFileNameWithoutExtension norm

            let isLibPath =
                if hasFableLibPrefix then
                    norm.Contains "fable-library-zig/"
                else
                    norm.StartsWith("./", System.StringComparison.Ordinal)
                    && norm.IndexOf('/', 2) = -1

            if isLibPath && pureStdlibModules.Contains baseName then
                Some kv.Value
            else
                None
        )
        |> HashSet

    let p =
        {
            State = state
            Fns = Dictionary()
            Ext = effectiveExtLookup
            StoredFields = Dictionary()
            CallsCallback = HashSet()
            CallsExtStore = HashSet()
            ExtStoreDeps = Dictionary()
            PureStdlibAliases = pureStdlibAliases
        }

    for fn in state.Fns do
        p.Fns[fn.Name] <- fn

    let located (fn: FnInfo) (f: unit -> unit) =
        try
            f ()
        with ZigError(msg, None) ->
            raise (ZigError(msg, fn.Range))

    inferRaises p

    let collectNoRaiseAsserts (fn: FnInfo) =
        let tpSet = Set.ofList fn.TypeParams
        let seen = HashSet<string>()
        let acc = List<string * Ty list>()

        let rec scan (e: Expr) =
            match e with
            | ECall(f, tyArgs, xs, _) ->
                if not (p.Fns.ContainsKey f) then
                    match p.Ext f with
                    | Some ff when ff.Raises = Facts.PRNever ->
                        if freeGens tyArgs |> List.forall tpSet.Contains then
                            let key = f + "<" + (tyArgs |> List.map tyKey |> String.concat ",") + ">"

                            if seen.Add key then
                                acc.Add(f, tyArgs)
                    | _ -> ()

                List.iter scan xs
            | ELet(_, r, b)
            | ESeq(r, b)
            | EWhile(r, b)
            | EStore(r, b) ->
                scan r
                scan b
            | EIf(c, t, f, _) ->
                scan c
                scan t
                scan f
            | EFor(_, a, b, _, bd) ->
                scan a
                scan b
                scan bd
            | EAssign(_, r) -> scan r
            | ETry(b, _, h, _) ->
                scan b
                scan h
            | EDrop(_, k)
            | EUnpack(_, k)
            | EPromote(_, k) -> scan k
            | _ -> List.iter scan (flatKids e)

        scan fn.Body
        fn.AssertedNoRaise <- List.ofSeq acc

    for fn in state.Fns do
        collectNoRaiseAsserts fn

    for fn in state.Fns do
        fn.Body <- fn.Body |> elideDeadTry p |> cleanup

    inferStores p

    for fn in state.Fns do
        located
            fn
            (fun () ->
                fn.Body <-
                    fn.Body
                    |> hoistRaising p
                    |> hoistMutableReads p
                    |> nameProjections state
                    |> splitPathsIn state Map.empty
                    |> cleanup
            )

    inferBorrows p

    for fn in state.Fns do
        if hooks.Contains fn.Name then
            fn.Modes <- fn.Modes |> List.map (fun _ -> MBorrowed)

            // A hook runs here and never on .NET: what it does must not change what the program
            // computes. It may read the value and call `[<Emit>]` code (the hardware), nothing
            // that assigns.
            let assigns =
                exists
                    (fun x ->
                        match x with
                        | EStore _ -> true
                        | EAssign(v, _) -> v.Kind = VGlobal
                        | EEmit(m, _, _) -> m.StartsWith("fable_rt.store(", System.StringComparison.Ordinal)
                        | _ -> false
                    )
                    fn.Body

            if assigns then
                raise (
                    ZigError(
                        $"%s{fn.Name}: a resource's Destroy and Dup run on the Zig target only (never on .NET), so they may not change what the program computes: they may read the value and call [<Emit>] code, but not assign",
                        fn.Range
                    )
                )

    inferNoEscape p hooks
    inferNeedsChain p hooks

    let exportedHofUnits = exportHofUnits prep p tier2Opt

    let exportedFns =
        state.Fns
        |> Seq.choose (fun fn ->
            if fn.IsLocal then
                None
            else
                let portableRaises =
                    match fn.Raises with
                    | RNever -> Facts.PRNever
                    | RAlways -> Facts.PRAlways
                    | RDepends _ -> Facts.PRDepends []

                let storedFields =
                    match p.StoredFields.TryGetValue fn.Name with
                    | true, s -> Set.toList s
                    | _ -> []

                let callsCb = p.CallsCallback.Contains fn.Name
                let callsExt = p.CallsExtStore.Contains fn.Name
                fn.StoreFacts <- (storedFields, callsCb, callsExt)

                Some(
                    fn.Name,
                    ({
                        Modes = fn.Modes
                        RetFrom = fn.RetFrom
                        Raises = portableRaises
                        StoredFields = storedFields
                        CallsCallback = callsCb
                        CallsExtStore = callsExt
                        FnParamsNoEscape = fn.NoEscape
                        NeedsChain = fn.NeedsChain
                        Hof = exportedHofUnits.TryFind fn.Name
                    }
                    : FnFacts)
                )
        )
        |> Map.ofSeq

    publishFacts addedFsImports exportedFns
    specializeCallKHofs p

    for fn in state.Fns do
        let owned =
            List.zip fn.Params fn.Modes
            |> List.choose (fun (q, m) ->
                if m = MOwned then
                    Some q.Id
                else
                    None
            )
            |> Set.ofList

        let kParams =
            if fn.NoEscape.Length = fn.Params.Length && List.exists id fn.NoEscape then
                List.zip fn.Params fn.NoEscape
                |> List.choose (fun (q, isK) ->
                    if isK then
                        Some q.Id
                    else
                        None
                )
                |> Set.ofList
            else
                Set.empty

        located
            fn
            (fun () ->
                let prePcBody = fn.Body
                let unescaped = localUnescapedRefVars prePcBody
                let storeAsserts = List<string * Set<string> * bool>()

                fn.Body <-
                    pc
                        p
                        { emptyEnv with
                            Owned = owned
                            TailBorrowed = fn.RetFrom.IsSome
                            UnescapedRefs = unescaped
                            StoreAsserts = storeAsserts
                        }
                        prePcBody
                        Set.empty

                if not kParams.IsEmpty then
                    fn.BodyK <-
                        Some(
                            pc
                                p
                                { emptyEnv with
                                    Owned = owned
                                    TailBorrowed = fn.RetFrom.IsSome
                                    UnescapedRefs = unescaped
                                    KParams = kParams
                                    StoreAsserts = storeAsserts
                                }
                                prePcBody
                                Set.empty
                        )

                if fn.NeedsChain || not fn.PendingChainDeps.IsEmpty then
                    if fn.RetFrom.IsNone && fn.Modes |> List.forall ((<>) MBorrowed) then
                        fn.BodyTc <- Some fn.Body
                    else
                        let ownedTc =
                            fn.Params
                            |> List.choose (fun q ->
                                if isManaged q.Ty then
                                    Some q.Id
                                else
                                    None
                            )
                            |> Set.ofList

                        let tcAsserts = List<string * Set<string> * bool>()

                        fn.BodyTc <-
                            Some(
                                pc
                                    p
                                    { emptyEnv with
                                        Owned = ownedTc
                                        TailBorrowed = false
                                        UnescapedRefs = unescaped
                                        StoreAsserts = tcAsserts
                                    }
                                    prePcBody
                                    Set.empty
                            )

                if storeAsserts.Count > 0 then
                    fn.AssertedStores <-
                        storeAsserts
                        |> Seq.groupBy (fun (extFn, _, _) -> extFn)
                        |> Seq.map (fun (extFn, items) ->
                            let fields =
                                items
                                |> Seq.collect (fun (_, fs, _) -> fs)
                                |> Set.ofSeq
                                |> Set.toList
                                |> List.sort

                            let checkExt = items |> Seq.exists (fun (_, _, c) -> c)
                            extFn, fields, checkExt
                        )
                        |> Seq.sortBy (fun (extFn, _, _) -> extFn)
                        |> Seq.toList
            )

/// Standalone single-file entry point running all ownership passes without external facts.
let run (state: FileState) : unit =
    let prep = prepareLocal state
    inferAndFinish prep (fun _ -> None) None (fun _ _ -> ())
