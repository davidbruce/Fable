module Loops

// `for x in ...` over lists, sets, maps, strings and .NET's collections, and .NET's mutable
// collections: ResizeArray, Dictionary, HashSet. Every expected text is what .NET gives.
// `run` returns the number of failed checks.

open System.Collections.Generic
open Fable.Core.Zig

let liveCells () : int = Counters.liveCells ()
let counting () : bool = Counters.isCounting ()

let check (ok: bool) : int =
    if ok then
        0
    else
        1

let same (expected: string) (actual: string) : int =
    if actual = expected then
        0
    else
        1

let raised (f: unit -> string) : string =
    try
        f ()
    with
    | :? KeyNotFoundException as e -> "KeyNotFound: " + e.Message
    | :? System.ArgumentOutOfRangeException as e -> "ArgumentOutOfRange: " + e.Message
    | :? System.ArgumentException as e -> "Argument: " + e.Message
    | e -> "other: " + e.Message

let loops () : int =
    let mutable total = 0
    let mutable text = ""

    for x in [ 1; 2; 3 ] do
        total <- total + x

    for s in [ "a" + "b"; "c" ] do
        text <- text + s + ","

    for c in "héllo" do
        text <- text + string (int c) + " "

    for x in set [ 3; 1; 2 ] do
        text <- text + string x

    for kv in Map.ofList [ (2, "b"); (1, "a") ] do
        text <- text + string kv.Key + kv.Value

    let words = [ "one"; "two" ]

    for w in words do
        for c in w do
            total <- total + 1

    check (total = 12) + same "ab,c,104 233 108 108 111 1231a2b" text

let collections () : int =
    let r = ResizeArray [ 3; 1; 2 ]
    r.Add 5
    let first = sprintf "%A|%d" r r.Count
    r.Insert(0, 9)
    r.RemoveAt 1
    r.Sort()
    let names = ResizeArray<string>()
    names.Add("x" + "y")
    names.Add "z"
    names.[0] <- names.[0] + "!"
    let d = Dictionary<int, string>()
    d.Add(2, "b")
    d.Add(1, "a")
    d.[3] <- "c"
    d.[2] <- "B"
    let before = sprintf "%A" d
    d.Remove 2 |> ignore
    d.[7] <- "g"
    let mutable walked = ""

    for kv in d do
        walked <- walked + string kv.Key + kv.Value

    let found =
        match d.TryGetValue 7 with
        | true, v -> v
        | _ -> "-"

    let missing =
        match d.TryGetValue 8 with
        | true, v -> v
        | _ -> "-"

    let h = HashSet<int>([ 3; 1; 3 ])
    let added = h.Add 4
    let again = h.Add 1
    let mutable sum = 0

    for x in r do
        sum <- sum + x

    let counts = Dictionary<string, int>()

    for w in [ "to"; "be"; "or"; "not"; "to"; "be" ] do
        if counts.ContainsKey w then
            counts.[w] <- counts.[w] + 1
        else
            counts.[w] <- 1

    same "seq [3; 1; 2; 5]|4" first
    + same "seq [1; 2; 5; 9]" (sprintf "%A" r)
    + check (
        not (r.Contains 3)
        && r.IndexOf 5 = 2
        && not (r.Remove 3)
        && r.Remove 2
        && sum = 17
    )
    + same "[|1; 5; 9|]|seq [\"xy!\"; \"z\"]" (sprintf "%A|%A" (r.ToArray()) names)
    + same "seq [[2, B]; [1, a]; [3, c]]|seq [[7, g]; [1, a]; [3, c]]" (before + "|" + sprintf "%A" d)
    + same "7g1a3c|g|-" (walked + "|" + found + "|" + missing)
    + check (d.Count = 3 && d.ContainsKey 7 && not (d.ContainsKey 2) && d.ContainsValue "a")
    + same "seq [3; 1; 4]" (sprintf "%A" h)
    + check (
        added
        && not again
        && h.Count = 3
        && h.Contains 4
        && h.Remove 3
        && not (h.Contains 3)
    )
    + same "seq [[to, 2]; [be, 2]; [or, 1]; [not, 1]]" (sprintf "%A" counts)
    + check (r = r && r <> ResizeArray [ 1; 5; 9 ])
    + same
        "ArgumentOutOfRange: Index was out of range. Must be non-negative and less than the size of the collection. (Parameter 'index')"
        (raised (fun () -> string r.[9]))
    + same
        "ArgumentOutOfRange: Index must be within the bounds of the List. (Parameter 'index')"
        (raised (fun () ->
            r.Insert(9, 1)
            ""
        ))
    + same
        "Argument: An item with the same key has already been added. Key: 1"
        (raised (fun () ->
            d.Add(1, "x")
            ""
        ))
    + same "KeyNotFound: The given key '9' was not present in the dictionary." (raised (fun () -> d.[9]))

type Node =
    {
        Name: string
        Links: ResizeArray<Node>
    }

let cycles () : int =
    let before = liveCells ()

    let build () =
        let a =
            {
                Name = "a"
                Links = ResizeArray()
            }

        let b =
            {
                Name = "b"
                Links = ResizeArray [ a ]
            }

        a.Links.Add b
        let index = Dictionary<string, Node>()
        index.["a"] <- a
        index.["b"] <- b
        a.Links.Count + b.Links.Count + index.Count

    let n = build ()
    Collector.collect () |> ignore

    check (n = 4)
    + (if counting () then
           check (liveCells () = before)
       else
           0)

let run () : int =
    let before = liveCells ()
    let failed = loops () + collections () + cycles ()
    printfn "loops: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
