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

let private transformFileHere (com: Compiler) (file: Fable.File) : ZigFile =
    // (the .NET members by domain, which come after the lowering, given to it)
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

    let body =
        try
            sw.Restart()
            Perceus.run state

            if timing then
                eprintfn "ZIGTIME perceus %dms" sw.ElapsedMilliseconds

            sw.Restart()
            let text = Emit.emitFile state

            if timing then
                eprintfn "ZIGTIME emit %dms" sw.ElapsedMilliseconds

            text
        with
        | ZigError(msg, r) ->
            com.AddLog(msg, Severity.Error, ?range = r, fileName = com.CurrentFile)
            ""
        | e when not (e :? System.OutOfMemoryException) ->
            // (the innermost frame of the target's own code, for a report of the bug)
            let where (e: exn) =
                (if isNull e.StackTrace then
                     ""
                 else
                     e.StackTrace)
                    .Split('\n')
                |> Array.map (fun l -> l.Trim())
                |> Array.tryFind (fun l -> l.Contains "Fable2Zig" || l.Contains "Zig.")
                |> Option.defaultValue "no frame"

            com.AddLog(
                $"internal error of the Zig target: %s{e.GetType().Name}: %s{e.Message} (%s{where e})",
                Severity.Error,
                fileName = com.CurrentFile
            )

            ""

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

/// The file's Zig, made on a thread of a large stack: lowering, Perceus and emission recurse once
/// per nested expression, and a long function of statements nests deeply.
let transformFile (com: Compiler) (file: Fable.File) : ZigFile =
    let mutable result = Unchecked.defaultof<ZigFile>
    let mutable error: exn = null

    let worker =
        System.Threading.Thread(
            (fun () ->
                try
                    result <- transformFileHere com file
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
