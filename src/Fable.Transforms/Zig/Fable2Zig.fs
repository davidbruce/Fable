/// The Zig target: Fable AST -> ownership IR -> Zig source.
module Fable.Transforms.Zig.Compiler

open Fable
open Fable.AST
open Fable.Transforms.Zig.IR

type ZigFile =
    {
        /// (alias, path of the imported file as Fable knows it)
        Imports: (string * string) list
        /// the hand-written runtime, if the file uses it (its path as Fable knows it)
        Runtime: string option
        Body: string
    }

type LoweredZigFile =
    {
        Com: Compiler
        State: FileState
        Prepared: Perceus.LocalPrepared
        Timing: bool
    }

let private runOnBigStack (work: unit -> 'T) : 'T =
    let mutable result = Unchecked.defaultof<'T>
    let mutable error: exn = null

    let worker =
        System.Threading.Thread(
            (fun () ->
                try
                    result <- work ()
                with e ->
                    error <- e
            ),
            256 * 1024 * 1024
        )

    worker.Start()
    worker.Join()

    if not (isNull error) then
        System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(error).Throw()

    result

let private logZigError (com: Compiler) (e: exn) =
    match e with
    | ZigError(msg, r) -> com.AddLog(msg, Severity.Error, ?range = r, fileName = com.CurrentFile)
    | e ->
        let where (exn: exn) =
            (if isNull exn.StackTrace then
                 ""
             else
                 exn.StackTrace)
                .Split('\n')
            |> Array.map (fun l -> l.Trim())
            |> Array.tryFind (fun l -> l.Contains "Fable2Zig" || l.Contains "Zig.")
            |> Option.defaultValue "no frame"

        com.AddLog(
            $"internal error of the Zig target: %s{e.GetType().Name}: %s{e.Message} (%s{where e})",
            Severity.Error,
            fileName = com.CurrentFile
        )

let private buildZigFile (com: Compiler) (state: FileState) (body: string) : ZigFile =
    {
        Imports =
            Seq.append state.Imports state.UserImports
            |> Seq.map (fun kv -> kv.Value, kv.Key)
            |> Seq.sortBy fst
            |> List.ofSeq
        Runtime =
            if state.UsesRuntime || body.Contains "fable_rt." then
                Some(Fable.Transforms.AST.getLibPath com "fable_rt")
            else
                None
        Body = body
    }

/// First hop (local only, on a 256 MB stack thread): lowering, NonNull, local cleanup and
/// intra-file HOF specialization, before waiting for imported files' facts.
let lowerOnBigStack (com: Compiler) (file: Fable.File) : LoweredZigFile =
    runOnBigStack (fun () ->
        Fable.Transforms.Zig.LowerContext.domainCalls <-
            function
            | "async" -> DotnetAsync.call
            | "collections" -> DotnetCollections.call
            | "text" -> DotnetText.call
            | "numbers" -> DotnetNumbers.call
            | _ -> DotnetMisc.call

        let timing = System.Environment.GetEnvironmentVariable "FABLE_ZIG_TIME" = "1"
        let sw = System.Diagnostics.Stopwatch.StartNew()
        let state = Lower.lowerFile com file

        if timing then
            eprintfn "ZIGTIME lower %s %dms" com.CurrentFile sw.ElapsedMilliseconds

        NonNull.run state
        let prepared = Perceus.prepareLocal state

        {
            Com = com
            State = state
            Prepared = prepared
            Timing = timing
        }
    )

/// Second hop (after imported facts arrive, on a 256 MB stack thread): Tier 2 cloning,
/// inference, publishing facts (or publishing `None` in `finally` on error), Perceus dup/drop,
/// and Zig emission.
let inferAndEmitOnBigStack
    (lowered: LoweredZigFile)
    (projFile: string)
    (outPath: string)
    (importTargets: Facts.ImportTarget list)
    (directFsImports: string list)
    (importFacts: Map<string, Facts.FileFacts>)
    (publish: Facts.FileFacts option -> unit)
    : ZigFile * Facts.FileFacts option
    =
    runOnBigStack (fun () ->
        let com = lowered.Com
        let state = lowered.State
        let sw = System.Diagnostics.Stopwatch.StartNew()
        let mutable hasPublished = false
        let mutable publishedFacts: Facts.FileFacts option = None

        let doPublish (factsOpt: Facts.FileFacts option) =
            if not hasPublished then
                hasPublished <- true
                publishedFacts <- factsOpt
                publish factsOpt

        let extLookup (fname: string) =
            match fname.IndexOf '.' with
            | -1 -> None
            | dot ->
                let alias = fname.Substring(0, dot)
                let memberName = fname.Substring(dot + 1)

                match importFacts.TryFind alias with
                | Some ff -> ff.Fns.TryFind memberName
                | None -> None

        let tier2Opt: Perceus.Tier2Context option =
            if System.String.IsNullOrEmpty outPath then
                None
            else
                Some
                    {
                        CallerZigPath = Fable.Path.normalizeFullPath outPath
                        ImportTargets = importTargets
                        ImportFacts = importFacts
                        ResolveLibPath = Fable.Transforms.AST.getLibPath com
                        LookupCachedFacts = Facts.tryGetCachedFacts projFile
                    }

        let body =
            try
                try
                    Perceus.inferAndFinish
                        lowered.Prepared
                        extLookup
                        tier2Opt
                        (fun addedFsImports fns ->
                            let hash = Facts.computeFileHash fns

                            let allFsImports =
                                (directFsImports @ addedFsImports)
                                |> List.map Facts.normalizeFsPath
                                |> List.distinct

                            let ff: Facts.FileFacts =
                                {
                                    Version = Facts.FactsVersion
                                    File = Facts.normalizeFsPath com.CurrentFile
                                    Hash = hash
                                    Imports = allFsImports
                                    Fns = fns
                                }

                            doPublish (Some ff)
                        )

                    if lowered.Timing then
                        eprintfn "ZIGTIME perceus %dms" sw.ElapsedMilliseconds

                    sw.Restart()
                    let text = Emit.emitFile state

                    if lowered.Timing then
                        eprintfn "ZIGTIME emit %dms" sw.ElapsedMilliseconds

                    text
                with
                | ZigError _ as e ->
                    logZigError com e
                    ""
                | e when not (e :? System.OutOfMemoryException) ->
                    logZigError com e
                    ""
            finally
                if not hasPublished then
                    doPublish None

        buildZigFile com state body, publishedFacts
    )

/// Standalone single-file entry point (no cross-file facts wait).
let transformFile (com: Compiler) (file: Fable.File) : ZigFile =
    let lowered = lowerOnBigStack com file
    let zig, _ = inferAndEmitOnBigStack lowered "" "" [] [] Map.empty ignore
    zig
