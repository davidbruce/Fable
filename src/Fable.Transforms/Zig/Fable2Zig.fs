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

let transformFile (com: Compiler) (file: Fable.File) : ZigFile =
    let state = Lower.lowerFile com file

    let body =
        try
            Perceus.run state
            Emit.emitFile state
        with ZigError(msg, r) ->
            com.AddLog(msg, Severity.Error, ?range = r, fileName = com.CurrentFile)
            ""

    {
        Imports =
            state.Imports
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
