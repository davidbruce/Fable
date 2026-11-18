/// Cross-file ownership, exception, store, and tail-call facts for the Zig target:
/// project-scoped batch coordination (two-hop async wait) plus *.facts.json sidecars.
module Fable.Transforms.Zig.Facts

open System
open System.Collections.Concurrent
open System.Collections.Generic
open System.IO
open System.Security.Cryptography
open System.Text
open System.Threading.Tasks
open Fable.Transforms.Zig.IR

/// Bump whenever FnFacts, FileFacts, or $sig/$stores ABI changes; mismatched sidecars are ignored.
[<Literal>]
let FactsVersion = 1

/// Portable representation of `Ty` qualified for cross-file storage in `FnFacts.Raises`.
type PortableTy =
    | PTPrim of string
    | PTEnt of filePath: string option * zigName: string * generics: PortableTy list
    | PTGen of string
    | PTOpt of PortableTy
    | PTTuple of PortableTy list
    | PTPtr of PortableTy * bool
    | PTSlice of PortableTy * bool
    | PTArr of PortableTy * int
    | PTFn of PortableTy list * PortableTy
    | PTSlot of PortableTy list * PortableTy
    | PTTok of PortableTy * string

/// Portable exception summary published across files (`RDepends` callees qualified by source path).
type PortableRaises =
    | PRNever
    | PRAlways
    | PRDepends of (string option * string * PortableTy list) list

/// Resolved import entry carried inside a `HofUnit` for Tier 2 cross-file cloning.
type HofImport =
    {
        CalleeAlias: string
        ZigPath: string
        FsPath: string option
        RawKey: string
    }

/// Snapshot of an eligible higher-order function and its reachable local helpers for Tier 2 cloning.
/// Shared in memory only (omitted from .facts.json sidecars, while its Hash feeds FileFacts.Hash).
type HofUnit =
    {
        Name: string
        Hash: string
        CalleeZigPath: string
        Fns: FnInfo list
        Curried2: (string * string) list
        Imports: HofImport list
        ExtraEnts: (string * Ent) list
    }

/// Published summary of one public function (`IsLocal = false`).
type FnFacts =
    {
        Modes: Mode list
        RetFrom: int list option
        Raises: PortableRaises
        StoredFields: string list
        CallsCallback: bool
        CallsExtStore: bool
        FnParamsNoEscape: bool list
        NeedsChain: bool
        Hof: HofUnit option
    }

/// Published summary for a compiled F# source file.
type FileFacts =
    {
        Version: int
        File: string
        Hash: string
        Imports: string list
        Fns: Map<string, FnFacts>
    }

/// Resolved import entry supplied by `Pipeline.Zig` when awaiting imported files.
type ImportTarget =
    {
        Alias: string
        /// Normalized `.fs`/`.fsx` source path when the import refers to a file in the current compilation.
        FsPath: string option
        /// Normalized `.zig` path where the target file (or its `.facts.json` sidecar) resides.
        ZigPath: string
    }

let factsPathOf (zigPath: string) : string =
    Fable.Path.ChangeExtension(zigPath, ".facts.json")

let normalizeFsPath (path: string) : string =
    Fable.Path.normalizeFullPath path |> Fable.Path.ensureFsExtension

// =============================================================================================
// Canonical serialization, SHA-256 hashing, and self-contained JSON sidecar I/O
// =============================================================================================

type private JsonVal =
    | JNull
    | JBool of bool
    | JInt of int64
    | JStr of string
    | JArr of JsonVal list
    | JObj of (string * JsonVal) list

let private writeJsonStr (sb: StringBuilder) (s: string) =
    sb.Append('"') |> ignore

    for i = 0 to s.Length - 1 do
        let c = s[i]

        match c with
        | '"' -> sb.Append("\\\"") |> ignore
        | '\\' -> sb.Append("\\\\") |> ignore
        | '\b' -> sb.Append("\\b") |> ignore
        | '\f' -> sb.Append("\\f") |> ignore
        | '\n' -> sb.Append("\\n") |> ignore
        | '\r' -> sb.Append("\\r") |> ignore
        | '\t' -> sb.Append("\\t") |> ignore
        | _ when int c < 0x20 -> sb.Append($"\\u%04x{int c}") |> ignore
        | _ -> sb.Append(c) |> ignore

    sb.Append('"') |> ignore

let rec private writeJsonVal (sb: StringBuilder) (v: JsonVal) =
    match v with
    | JNull -> sb.Append("null") |> ignore
    | JBool true -> sb.Append("true") |> ignore
    | JBool false -> sb.Append("false") |> ignore
    | JInt n ->
        sb.Append(n.ToString(System.Globalization.CultureInfo.InvariantCulture))
        |> ignore
    | JStr s -> writeJsonStr sb s
    | JArr xs ->
        sb.Append('[') |> ignore

        xs
        |> List.iteri (fun i x ->
            if i > 0 then
                sb.Append(',') |> ignore

            writeJsonVal sb x
        )

        sb.Append(']') |> ignore
    | JObj kvs ->
        sb.Append('{') |> ignore

        kvs
        |> List.iteri (fun i (k, x) ->
            if i > 0 then
                sb.Append(',') |> ignore

            writeJsonStr sb k
            sb.Append(':') |> ignore
            writeJsonVal sb x
        )

        sb.Append('}') |> ignore

let private parseJson (text: string) : JsonVal option =
    let len = text.Length
    let mutable pos = 0

    let skipWs () =
        while pos < len && Char.IsWhiteSpace text[pos] do
            pos <- pos + 1

    let parseStr () : string option =
        if pos >= len || text[pos] <> '"' then
            None
        else
            pos <- pos + 1
            let sb = StringBuilder()
            let mutable ok = true
            let mutable done_ = false

            while ok && not done_ && pos < len do
                let c = text[pos]
                pos <- pos + 1

                if c = '"' then
                    done_ <- true
                elif c = '\\' then
                    if pos >= len then
                        ok <- false
                    else
                        let esc = text[pos]
                        pos <- pos + 1

                        match esc with
                        | '"' -> sb.Append('"') |> ignore
                        | '\\' -> sb.Append('\\') |> ignore
                        | '/' -> sb.Append('/') |> ignore
                        | 'b' -> sb.Append('\b') |> ignore
                        | 'f' -> sb.Append('\f') |> ignore
                        | 'n' -> sb.Append('\n') |> ignore
                        | 'r' -> sb.Append('\r') |> ignore
                        | 't' -> sb.Append('\t') |> ignore
                        | 'u' when pos + 4 <= len ->
                            let hex = text.Substring(pos, 4)
                            pos <- pos + 4

                            match
                                Int32.TryParse(
                                    hex,
                                    System.Globalization.NumberStyles.HexNumber,
                                    System.Globalization.CultureInfo.InvariantCulture
                                )
                            with
                            | true, code -> sb.Append(char code) |> ignore
                            | _ -> ok <- false
                        | _ -> ok <- false
                else
                    sb.Append(c) |> ignore

            if ok && done_ then
                Some(sb.ToString())
            else
                None

    let rec parseVal () : JsonVal option =
        skipWs ()

        if pos >= len then
            None
        else
            match text[pos] with
            | '"' -> parseStr () |> Option.map JStr
            | '{' -> parseObj ()
            | '[' -> parseArr ()
            | 't' when pos + 4 <= len && text.Substring(pos, 4) = "true" ->
                pos <- pos + 4
                Some(JBool true)
            | 'f' when pos + 5 <= len && text.Substring(pos, 5) = "false" ->
                pos <- pos + 5
                Some(JBool false)
            | 'n' when pos + 4 <= len && text.Substring(pos, 4) = "null" ->
                pos <- pos + 4
                Some JNull
            | c when c = '-' || Char.IsDigit c ->
                let start = pos

                if c = '-' then
                    pos <- pos + 1

                let digitStart = pos

                while pos < len && Char.IsDigit text[pos] do
                    pos <- pos + 1

                if pos = digitStart then
                    None
                else
                    match
                        Int64.TryParse(
                            text.Substring(start, pos - start),
                            System.Globalization.NumberStyles.Integer,
                            System.Globalization.CultureInfo.InvariantCulture
                        )
                    with
                    | true, n -> Some(JInt n)
                    | _ -> None
            | _ -> None

    and parseArr () : JsonVal option =
        pos <- pos + 1
        skipWs ()

        if pos < len && text[pos] = ']' then
            pos <- pos + 1
            Some(JArr [])
        else
            let items = List<JsonVal>()
            let mutable ok = true
            let mutable stop = false

            while ok && not stop do
                match parseVal () with
                | Some v ->
                    items.Add v
                    skipWs ()

                    if pos < len && text[pos] = ',' then
                        pos <- pos + 1
                    elif pos < len && text[pos] = ']' then
                        pos <- pos + 1
                        stop <- true
                    else
                        ok <- false
                | None -> ok <- false

            if ok then
                Some(JArr(List.ofSeq items))
            else
                None

    and parseObj () : JsonVal option =
        pos <- pos + 1
        skipWs ()

        if pos < len && text[pos] = '}' then
            pos <- pos + 1
            Some(JObj [])
        else
            let pairs = List<string * JsonVal>()
            let mutable ok = true
            let mutable stop = false

            while ok && not stop do
                skipWs ()

                match parseStr () with
                | Some k ->
                    skipWs ()

                    if pos < len && text[pos] = ':' then
                        pos <- pos + 1

                        match parseVal () with
                        | Some v ->
                            pairs.Add(k, v)
                            skipWs ()

                            if pos < len && text[pos] = ',' then
                                pos <- pos + 1
                            elif pos < len && text[pos] = '}' then
                                pos <- pos + 1
                                stop <- true
                            else
                                ok <- false
                        | None -> ok <- false
                    else
                        ok <- false
                | None -> ok <- false

            if ok then
                Some(JObj(List.ofSeq pairs))
            else
                None

    let res = parseVal ()
    skipWs ()

    if pos = len then
        res
    else
        None

let private modeToStr =
    function
    | MPlain -> "p"
    | MOwned -> "o"
    | MBorrowed -> "b"

let private modeFromStr =
    function
    | "p" -> Some MPlain
    | "o" -> Some MOwned
    | "b" -> Some MBorrowed
    | _ -> None

let rec private portableTyToJson (t: PortableTy) : JsonVal =
    match t with
    | PTPrim s -> JArr [ JStr "prim"; JStr s ]
    | PTEnt(fileOpt, name, gs) ->
        JArr
            [
                JStr "ent"
                (match fileOpt with
                 | Some f -> JStr f
                 | None -> JNull)
                JStr name
                JArr(List.map portableTyToJson gs)
            ]
    | PTGen n -> JArr [ JStr "gen"; JStr n ]
    | PTOpt x -> JArr [ JStr "opt"; portableTyToJson x ]
    | PTTuple xs -> JArr [ JStr "tup"; JArr(List.map portableTyToJson xs) ]
    | PTPtr(x, c) -> JArr [ JStr "ptr"; portableTyToJson x; JBool c ]
    | PTSlice(x, c) -> JArr [ JStr "slc"; portableTyToJson x; JBool c ]
    | PTArr(x, n) -> JArr [ JStr "arr"; portableTyToJson x; JInt(int64 n) ]
    | PTFn(ps, r) -> JArr [ JStr "fn"; JArr(List.map portableTyToJson ps); portableTyToJson r ]
    | PTSlot(ps, r) -> JArr [ JStr "slot"; JArr(List.map portableTyToJson ps); portableTyToJson r ]
    | PTTok(x, c) -> JArr [ JStr "tok"; portableTyToJson x; JStr c ]

let rec private portableTyFromJson (v: JsonVal) : PortableTy option =
    match v with
    | JArr [ JStr "prim"; JStr s ] -> Some(PTPrim s)
    | JArr [ JStr "ent"; fJson; JStr name; JArr gs ] ->
        let fileOpt =
            match fJson with
            | JNull -> Some None
            | JStr s -> Some(Some s)
            | _ -> None

        let gsOpt = List.choose portableTyFromJson gs

        match fileOpt with
        | Some fo when gsOpt.Length = gs.Length -> Some(PTEnt(fo, name, gsOpt))
        | _ -> None
    | JArr [ JStr "gen"; JStr n ] -> Some(PTGen n)
    | JArr [ JStr "opt"; x ] -> portableTyFromJson x |> Option.map PTOpt
    | JArr [ JStr "tup"; JArr xs ] ->
        let ps = List.choose portableTyFromJson xs

        if ps.Length = xs.Length then
            Some(PTTuple ps)
        else
            None
    | JArr [ JStr "ptr"; x; JBool c ] -> portableTyFromJson x |> Option.map (fun t -> PTPtr(t, c))
    | JArr [ JStr "slc"; x; JBool c ] -> portableTyFromJson x |> Option.map (fun t -> PTSlice(t, c))
    | JArr [ JStr "arr"; x; JInt n ] -> portableTyFromJson x |> Option.map (fun t -> PTArr(t, int n))
    | JArr [ JStr "fn"; JArr ps; r ] ->
        let ps' = List.choose portableTyFromJson ps

        match portableTyFromJson r with
        | Some r' when ps'.Length = ps.Length -> Some(PTFn(ps', r'))
        | _ -> None
    | JArr [ JStr "slot"; JArr ps; r ] ->
        let ps' = List.choose portableTyFromJson ps

        match portableTyFromJson r with
        | Some r' when ps'.Length = ps.Length -> Some(PTSlot(ps', r'))
        | _ -> None
    | JArr [ JStr "tok"; x; JStr c ] -> portableTyFromJson x |> Option.map (fun t -> PTTok(t, c))
    | _ -> None

let private raisesToJson (r: PortableRaises) : JsonVal =
    match r with
    | PRNever -> JStr "never"
    | PRAlways -> JStr "always"
    | PRDepends ds ->
        ds
        |> List.map (fun (fileOpt, fnName, tys) ->
            JArr
                [
                    (match fileOpt with
                     | Some f -> JStr f
                     | None -> JNull)
                    JStr fnName
                    JArr(List.map portableTyToJson tys)
                ]
        )
        |> JArr

let private raisesFromJson (v: JsonVal) : PortableRaises option =
    match v with
    | JStr "never" -> Some PRNever
    | JStr "always" -> Some PRAlways
    | JArr items ->
        let parsed =
            items
            |> List.choose (
                function
                | JArr [ fJson; JStr fnName; JArr tys ] ->
                    let fo =
                        match fJson with
                        | JNull -> Some None
                        | JStr f -> Some(Some f)
                        | _ -> None

                    let ptys = List.choose portableTyFromJson tys

                    match fo with
                    | Some fileOpt when ptys.Length = tys.Length -> Some(fileOpt, fnName, ptys)
                    | _ -> None
                | _ -> None
            )

        if parsed.Length = items.Length then
            Some(PRDepends parsed)
        else
            None
    | _ -> None

let private fnFactsToJson (includeHofHash: bool) (ff: FnFacts) : JsonVal =
    let fields =
        [
            "modes", JArr(ff.Modes |> List.map (modeToStr >> JStr))
            "retFrom",
            (match ff.RetFrom with
             | None -> JNull
             | Some js -> JArr(js |> List.map (int64 >> JInt)))
            "raises", raisesToJson ff.Raises
            "stored", JArr(ff.StoredFields |> List.map JStr)
            "cb", JBool ff.CallsCallback
            "ext", JBool ff.CallsExtStore
            "noEsc", JArr(ff.FnParamsNoEscape |> List.map JBool)
            "chain", JBool ff.NeedsChain
        ]

    let fields =
        if includeHofHash then
            match ff.Hof with
            | Some h -> fields @ [ "hofHash", JStr h.Hash ]
            | None -> fields
        else
            fields

    JObj fields

let private tryField (name: string) (kvs: (string * JsonVal) list) : JsonVal option =
    kvs
    |> List.tryPick (fun (k, v) ->
        if k = name then
            Some v
        else
            None
    )

let private fnFactsFromJson (v: JsonVal) : FnFacts option =
    match v with
    | JObj kvs ->
        match
            tryField "modes" kvs,
            tryField "retFrom" kvs,
            tryField "raises" kvs,
            tryField "stored" kvs,
            tryField "cb" kvs,
            tryField "ext" kvs,
            tryField "noEsc" kvs,
            tryField "chain" kvs
        with
        | Some(JArr ms),
          Some rfJson,
          Some rJson,
          Some(JArr st),
          Some(JBool cb),
          Some(JBool ext),
          Some(JArr ne),
          Some(JBool ch) ->
            let modes =
                ms
                |> List.choose (
                    function
                    | JStr s -> modeFromStr s
                    | _ -> None
                )

            let retFrom =
                match rfJson with
                | JNull -> Some None
                | JArr js ->
                    let nums =
                        js
                        |> List.choose (
                            function
                            | JInt i -> Some(int i)
                            | _ -> None
                        )

                    if nums.Length = js.Length then
                        Some(Some nums)
                    else
                        None
                | _ -> None

            let stored =
                st
                |> List.choose (
                    function
                    | JStr s -> Some s
                    | _ -> None
                )

            let noEsc =
                ne
                |> List.choose (
                    function
                    | JBool b -> Some b
                    | _ -> None
                )

            match raisesFromJson rJson, retFrom with
            | Some r, Some rf when
                modes.Length = ms.Length
                && stored.Length = st.Length
                && noEsc.Length = ne.Length
                ->
                Some
                    {
                        Modes = modes
                        RetFrom = rf
                        Raises = r
                        StoredFields = stored
                        CallsCallback = cb
                        CallsExtStore = ext
                        FnParamsNoEscape = noEsc
                        NeedsChain = ch
                        Hof = None
                    }
            | _ -> None
        | _ -> None
    | _ -> None

/// Deterministic SHA-256 hex digest over all published `FnFacts` and any exported Tier 2 `HofUnit` hashes.
let computeFileHash (fns: Map<string, FnFacts>) : string =
    let fnsJson =
        fns
        |> Map.toList
        |> List.sortBy fst
        |> List.map (fun (k, ff) -> k, fnFactsToJson true ff)
        |> JObj

    let sb = StringBuilder()
    sb.Append($"v%d{FactsVersion}:") |> ignore
    writeJsonVal sb fnsJson
    let bytes = Encoding.UTF8.GetBytes(sb.ToString())
    use sha = SHA256.Create()
    let digest = sha.ComputeHash(bytes)
    BitConverter.ToString(digest).Replace("-", "").ToLowerInvariant()

let serializeSidecar (facts: FileFacts) : string =
    let fnsJson =
        facts.Fns
        |> Map.toList
        |> List.sortBy fst
        |> List.map (fun (k, ff) -> k, fnFactsToJson false ff)
        |> JObj

    let root =
        JObj
            [
                "version", JInt(int64 facts.Version)
                "file", JStr facts.File
                "hash", JStr facts.Hash
                "imports", JArr(facts.Imports |> List.map JStr)
                "fns", fnsJson
            ]

    let sb = StringBuilder()
    writeJsonVal sb root
    sb.Append('\n') |> ignore
    sb.ToString()

let tryDeserializeSidecar (jsonText: string) : FileFacts option =
    try
        match parseJson jsonText with
        | Some(JObj kvs) ->
            match
                tryField "version" kvs,
                tryField "file" kvs,
                tryField "hash" kvs,
                tryField "imports" kvs,
                tryField "fns" kvs
            with
            | Some(JInt v), Some(JStr file), Some(JStr hash), Some(JArr impArr), Some(JObj fnPairs) when
                int v = FactsVersion
                ->
                let imports =
                    impArr
                    |> List.choose (
                        function
                        | JStr s -> Some s
                        | _ -> None
                    )

                let parsed =
                    fnPairs
                    |> List.choose (fun (fnName, ffVal) -> fnFactsFromJson ffVal |> Option.map (fun ff -> fnName, ff))

                if imports.Length = impArr.Length && parsed.Length = fnPairs.Length then
                    Some
                        {
                            Version = int v
                            File = file
                            Hash = hash
                            Imports = imports
                            Fns = Map.ofList parsed
                        }
                else
                    None
            | _ -> None
        | _ -> None
    with _ ->
        None

let private utf8NoBom = UTF8Encoding(false)

let tryWriteSidecarFile (zigPath: string) (facts: FileFacts) : unit =
    try
        let sidecarPath = factsPathOf zigPath
        let content = serializeSidecar facts
        let dir = Path.GetDirectoryName sidecarPath

        if not (String.IsNullOrEmpty dir) && not (Directory.Exists dir) then
            Directory.CreateDirectory dir |> ignore

        let write =
            if File.Exists sidecarPath then
                File.ReadAllText(sidecarPath, utf8NoBom) <> content
            else
                true

        if write then
            File.WriteAllText(sidecarPath, content, utf8NoBom)
    with _ ->
        ()

// =============================================================================================
// Project-scoped facts coordinator (Sources 1: current batch, 2: in-process, 3: sidecars)
// =============================================================================================

let private isImplFile (file: string) =
    file.EndsWith(".fs", StringComparison.OrdinalIgnoreCase)
    || file.EndsWith(".fsx", StringComparison.OrdinalIgnoreCase)

type private ProjectTable() =
    let gate = obj ()
    let batch = Dictionary<string, TaskCompletionSource<FileFacts option>>()
    let undispatched = HashSet<string>()
    let lastPropagatedHash = Dictionary<string, string>()
    let published = Dictionary<string, FileFacts>()
    let importersOf = Dictionary<string, HashSet<string>>()
    let compiledAgainst = Dictionary<string, Map<string, string>>()
    let waitsFor = Dictionary<string, HashSet<string>>()
    let sidecarCache = Dictionary<string, DateTime * FileFacts option>()

    let addImporterEdges (importerFs: string) (directImports: string list) =
        for imp in directImports do
            let nimp = normalizeFsPath imp

            let set =
                match importersOf.TryGetValue nimp with
                | true, s -> s
                | _ ->
                    let s = HashSet<string>()
                    importersOf[nimp] <- s
                    s

            set.Add importerFs |> ignore

    let readSidecarCached (zigPath: string) : FileFacts option =
        let sidecarPath = factsPathOf zigPath

        try
            if not (File.Exists sidecarPath) then
                None
            else
                let mtime = File.GetLastWriteTimeUtc sidecarPath

                match sidecarCache.TryGetValue sidecarPath with
                | true, (cachedMtime, cachedVal) when cachedMtime = mtime -> cachedVal
                | _ ->
                    let text = File.ReadAllText(sidecarPath, utf8NoBom)
                    let parsed = tryDeserializeSidecar text
                    sidecarCache[sidecarPath] <- (mtime, parsed)
                    parsed
        with _ ->
            None

    let wouldCycle (src: string) (dst: string) : bool =
        if src = dst then
            true
        else
            let visited = HashSet<string>()
            let stack = Stack<string>()
            stack.Push dst
            let mutable found = false

            while not found && stack.Count > 0 do
                let cur = stack.Pop()

                if cur = src then
                    found <- true
                elif visited.Add cur then
                    match waitsFor.TryGetValue cur with
                    | true, nexts ->
                        for n in nexts do
                            stack.Push n
                    | _ -> ()

            found

    member _.BeginBatch(files: seq<string>, seedPairs: (string * string) seq) =
        lock
            gate
            (fun () ->
                for (fsPath, zigPath) in seedPairs do
                    let nfs = normalizeFsPath fsPath

                    if isImplFile nfs && not (published.ContainsKey nfs) then
                        match readSidecarCached zigPath with
                        | Some ff ->
                            published[nfs] <- ff
                            lastPropagatedHash[nfs] <- ff.Hash
                            addImporterEdges nfs ff.Imports
                        | None -> ()

                undispatched.Clear()

                for f in files do
                    if isImplFile f then
                        let nf = normalizeFsPath f

                        batch[nf] <-
                            TaskCompletionSource<FileFacts option>(TaskCreationOptions.RunContinuationsAsynchronously)

                        undispatched.Add nf |> ignore
            )

    member _.MarkDispatched(file: string) =
        let nf = normalizeFsPath file
        lock gate (fun () -> undispatched.Remove nf |> ignore)

    member _.CompleteUndispatched() =
        let toFail =
            lock
                gate
                (fun () ->
                    let list =
                        undispatched
                        |> Seq.choose (fun nf ->
                            match batch.TryGetValue nf with
                            | true, tcs -> Some(nf, tcs)
                            | _ -> None
                        )
                        |> List.ofSeq

                    undispatched.Clear()

                    for (nf, _) in list do
                        published.Remove nf |> ignore

                    list
                )

        for (_, tcs) in toFail do
            tcs.TrySetResult None |> ignore

    member _.Publish(file: string, factsOpt: FileFacts option, directFsImports: string list) =
        let nf = normalizeFsPath file
        let directs = directFsImports |> List.map normalizeFsPath |> List.distinct

        let tcsOpt =
            lock
                gate
                (fun () ->
                    undispatched.Remove nf |> ignore
                    waitsFor.Remove nf |> ignore

                    for kv in importersOf do
                        kv.Value.Remove nf |> ignore

                    match factsOpt with
                    | Some ff ->
                        published[nf] <- ff
                        addImporterEdges nf directs
                    | None -> published.Remove nf |> ignore

                    match batch.TryGetValue nf with
                    | true, tcs -> Some tcs
                    | _ -> None
                )

        match tcsOpt with
        | Some tcs -> tcs.TrySetResult factsOpt |> ignore
        | None -> ()

    member _.AwaitImports(callerFile: string, targets: ImportTarget list) : Task<Map<string, FileFacts>> =
        let normCaller = normalizeFsPath callerFile

        let pending, immediate, waitEdges =
            lock
                gate
                (fun () ->
                    let waitSet =
                        match waitsFor.TryGetValue normCaller with
                        | true, s -> s
                        | _ ->
                            let s = HashSet<string>()
                            waitsFor[normCaller] <- s
                            s

                    waitSet.Clear()

                    let pend = List<string * string * Task<FileFacts option>>()
                    let imm = List<string * string option * FileFacts option>()

                    for t in targets do
                        match t.FsPath with
                        | Some fs ->
                            let nfs = normalizeFsPath fs

                            match batch.TryGetValue nfs with
                            | true, tcs ->
                                if tcs.Task.IsCompleted then
                                    imm.Add(t.Alias, Some nfs, tcs.Task.Result)
                                elif wouldCycle normCaller nfs then
                                    imm.Add(t.Alias, Some nfs, None)
                                else
                                    waitSet.Add nfs |> ignore
                                    pend.Add(t.Alias, nfs, tcs.Task)
                            | _ ->
                                match published.TryGetValue nfs with
                                | true, ff -> imm.Add(t.Alias, Some nfs, Some ff)
                                | _ -> imm.Add(t.Alias, Some nfs, readSidecarCached t.ZigPath)
                        | None -> imm.Add(t.Alias, None, readSidecarCached t.ZigPath)

                    List.ofSeq pend, List.ofSeq imm, waitSet.Count > 0
                )

        async {
            let! awaited =
                if pending.IsEmpty then
                    async.Return [||]
                else
                    pending
                    |> List.map (fun (alias, nfs, t) ->
                        async {
                            let! res = Async.AwaitTask t
                            return alias, nfs, res
                        }
                    )
                    |> Async.Parallel

            let results = Dictionary<string, FileFacts>()
            let depHashes = Dictionary<string, string>()

            for (alias, fsOpt, resOpt) in immediate do
                match resOpt with
                | Some ff -> results[alias] <- ff
                | None -> ()

                match fsOpt with
                | Some nfs ->
                    depHashes[nfs] <-
                        match resOpt with
                        | Some ff -> ff.Hash
                        | None -> "none"
                | None -> ()

            for (alias, nfs, resOpt) in awaited do
                match resOpt with
                | Some ff -> results[alias] <- ff
                | None -> ()

                depHashes[nfs] <-
                    match resOpt with
                    | Some ff -> ff.Hash
                    | None -> "none"

            lock
                gate
                (fun () ->
                    if waitEdges then
                        waitsFor.Remove normCaller |> ignore

                    compiledAgainst[normCaller] <- depHashes |> Seq.map (fun kv -> kv.Key, kv.Value) |> Map.ofSeq
                )

            return results |> Seq.map (fun kv -> kv.Key, kv.Value) |> Map.ofSeq
        }
        |> Async.StartAsTask

    member _.NextStaleImporters
        (batchFiles: Set<string>, sourceOrder: string[], validImplFiles: Set<string>)
        : string[]
        =
        lock
            gate
            (fun () ->
                let normBatch = batchFiles |> Set.map normalizeFsPath
                let changedFiles = List<string>()

                for kv in published do
                    let nf = kv.Key
                    let ff = kv.Value

                    let changed =
                        match lastPropagatedHash.TryGetValue nf with
                        | true, prev -> prev <> ff.Hash
                        | false, _ -> true

                    if changed then
                        changedFiles.Add nf
                        lastPropagatedHash[nf] <- ff.Hash

                if changedFiles.Count = 0 then
                    [||]
                else
                    let candidates = HashSet<string>()

                    for changedFile in changedFiles do
                        let changedInThisBatch = normBatch.Contains changedFile

                        match importersOf.TryGetValue changedFile with
                        | true, imps ->
                            for imp in imps do
                                if not (changedInThisBatch && normBatch.Contains imp) then
                                    let stillStale =
                                        match compiledAgainst.TryGetValue imp, published.TryGetValue changedFile with
                                        | (true, depMap), (true, ff) ->
                                            match depMap.TryFind changedFile with
                                            | Some usedHash -> usedHash <> ff.Hash
                                            | None -> true
                                        | _ -> true

                                    if stillStale then
                                        candidates.Add imp |> ignore
                        | _ -> ()

                    if candidates.Count = 0 then
                        [||]
                    else
                        sourceOrder
                        |> Array.filter (fun p ->
                            let np = normalizeFsPath p
                            candidates.Contains np && validImplFiles.Contains p
                        )
            )

    member _.TryGetCached(fsPathOpt: string option, zigPath: string) : FileFacts option =
        lock
            gate
            (fun () ->
                match fsPathOpt |> Option.map normalizeFsPath with
                | Some nfs ->
                    match published.TryGetValue nfs with
                    | true, ff -> Some ff
                    | _ -> readSidecarCached zigPath
                | None -> readSidecarCached zigPath
            )

let private tables = ConcurrentDictionary<string, ProjectTable>()

let private tableFor (projectFile: string) : ProjectTable =
    let key =
        if String.IsNullOrWhiteSpace projectFile then
            ""
        else
            Fable.Path.normalizeFullPath projectFile

    tables.GetOrAdd(key, fun _ -> ProjectTable())

let beginBatch (projectFile: string) (files: seq<string>) (seedPairs: (string * string) seq) : unit =
    (tableFor projectFile).BeginBatch(files, seedPairs)

let markDispatched (projectFile: string) (file: string) : unit =
    (tableFor projectFile).MarkDispatched(file)

let completeUndispatched (projectFile: string) : unit =
    (tableFor projectFile).CompleteUndispatched()

let publish (projectFile: string) (file: string) (factsOpt: FileFacts option) (directFsImports: string list) : unit =
    (tableFor projectFile).Publish(file, factsOpt, directFsImports)

let awaitImports
    (projectFile: string)
    (callerFile: string)
    (targets: ImportTarget list)
    : Task<Map<string, FileFacts>>
    =
    (tableFor projectFile).AwaitImports(callerFile, targets)

let nextStaleImporters
    (projectFile: string)
    (batchFiles: Set<string>)
    (sourceOrder: string[])
    (validImplFiles: Set<string>)
    : string[]
    =
    (tableFor projectFile).NextStaleImporters(batchFiles, sourceOrder, validImplFiles)

let tryGetCachedFacts (projectFile: string) (fsPathOpt: string option) (zigPath: string) : FileFacts option =
    (tableFor projectFile).TryGetCached(fsPathOpt, zigPath)
