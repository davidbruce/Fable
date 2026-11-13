module Maps

// Map and Set: balanced trees written in F# in the runtime library. Two maps are equal when
// they hold the same entries, whatever the shape of their trees. Every expected text is what
// .NET gives. `run` returns the number of failed checks.

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
    | :? System.Collections.Generic.KeyNotFoundException as e -> "KeyNotFound: " + e.Message
    | :? System.ArgumentException as e -> "Argument: " + e.Message
    | e -> "other: " + e.Message

let wordCounts (words: string list) : Map<string, int> =
    List.fold
        (fun (acc: Map<string, int>) w ->
            match Map.tryFind w acc with
            | Some n -> Map.add w (n + 1) acc
            | None -> Map.add w 1 acc
        )
        Map.empty
        words

let maps () : int =
    let m = Map.ofList [ (2, "b"); (1, "a"); (3, "c") ]
    let counts = wordCounts [ "to"; "be"; "or"; "not"; "to"; "be" ]

    let big =
        List.fold (fun acc i -> Map.add i (i * i) acc) Map.empty (List.init 1000 id)

    let seen = ref ""
    Map.iter (fun k v -> seen.Value <- seen.Value + string k + v) m

    same "map [(1, \"a\"); (2, \"b\"); (3, \"c\")]" (sprintf "%A" m)
    + same "map [(\"be\", 2); (\"not\", 1); (\"or\", 1); (\"to\", 2)]" (sprintf "%A" counts)
    + check (
        m.[2] = "b"
        && Map.find 3 m = "c"
        && m.Count = 3
        && Map.count m = 3
        && not m.IsEmpty
        && Map.isEmpty (Map.empty: Map<int, int>)
    )
    + check (
        Map.tryFind 9 m = None
        && m.TryFind 1 = Some "a"
        && m.ContainsKey 2
        && not (Map.containsKey 7 m)
    )
    + same
        "map [(1, \"a\"); (3, \"c\")]|map [(1, \"a\"); (2, \"B\"); (3, \"c\")]"
        (sprintf "%A|%A" (Map.remove 2 m) (m.Add(2, "B")))
    + same "1a2b3c" seen.Value
    + check (
        Map.fold (fun acc k (v: string) -> acc + k * v.Length) 0 m = 6
        && Map.foldBack (fun k v acc -> v + acc) m "" = "abc"
    )
    + same
        "[(1, \"a\"); (2, \"b\"); (3, \"c\")]|[1; 2; 3]|[\"a\"; \"b\"; \"c\"]"
        (sprintf "%A|%A|%A" (Map.toList m) (Map.keys m |> List.ofSeq) (Map.values m |> List.ofSeq))
    + same
        "map [(1, \"a!\"); (2, \"b!\"); (3, \"c!\")]|map [(2, \"b\")]"
        (sprintf "%A|%A" (Map.map (fun _ v -> v + "!") m) (Map.filter (fun k _ -> k = 2) m))
    + check (
        Map.exists (fun k _ -> k > 2) m
        && Map.forall (fun k _ -> k > 0) m
        && Map.findKey (fun _ v -> v = "b") m = 2
    )
    + check (
        Map.tryPick
            (fun k v ->
                if k = 2 then
                    Some(v + v)
                else
                    None
            )
            m
            =
            Some "bb"
        && Map.minKeyValue m = (1, "a")
        && Map.maxKeyValue m = (3, "c")
    )
    + check (
        m = Map.ofList [ (3, "c"); (1, "a"); (2, "b") ]
        && m <> Map.remove 1 m
        && compare m (Map.ofList [ (1, "a") ]) = 1
    )
    + check (hash m = hash (Map.ofList [ (3, "c"); (1, "a"); (2, "b") ]))
    + check (
        Map.count big = 1000
        && big.[999] = 998001
        && Map.count (List.fold (fun acc i -> Map.remove i acc) big (List.init 500 id)) = 500
    )
    + same
        "map\n  [(1, 1); (2, 2); (3, 3); (4, 4); (5, 5); (6, 6); (7, 7); (8, 8); (9, 9); ...]"
        (sprintf "%A" (Map.ofList (List.init 10 (fun i -> (i + 1, i + 1)))))
    + same "KeyNotFound: The given key was not present in the dictionary." (raised (fun () -> m.[9]))
    + same "KeyNotFound: The given key was not present in the dictionary." (raised (fun () -> Map.find 9 m))
    + same
        "map [(1, \"a\"); (2, \"x\"); (3, \"c\")]|map [(1, \"a\"); (3, \"c\")]"
        (sprintf "%A|%A" (Map.change 2 (fun _ -> Some "x") m) (m.Change(2, fun _ -> None)))

let sets () : int =
    let s = set [ 3; 1; 2; 3 ]
    let t = Set.ofList [ 2; 3; 4 ]

    same "set [1; 2; 3]|set []" (sprintf "%A|%A" s (Set.empty: Set<int>))
    + check (
        s.Count = 3
        && Set.count s = 3
        && s.Contains 2
        && Set.contains 1 s
        && not (Set.contains 9 s)
        && not s.IsEmpty
    )
    + same
        "set [1; 2; 3; 4]|set [2; 3]|set [1]|set [1; 2; 3; 4]|set [1]"
        (sprintf "%A|%A|%A|%A|%A" (Set.union s t) (Set.intersect s t) (Set.difference s t) (s + t) (s - t))
    + check (
        Set.isSubset (set [ 1; 2 ]) s
        && Set.isSuperset s (set [ 1 ])
        && not (Set.isSubset t s)
        && Set.isProperSubset (set [ 1 ]) s
    )
    + check (
        Set.minElement s = 1
        && Set.maxElement s = 3
        && s.MinimumElement = 1
        && Set.toList (Set.map (fun x -> x % 2) s) = [ 0; 1 ]
    )
    + check (
        Set.filter (fun x -> x > 1) s = set [ 2; 3 ]
        && Set.fold (+) 0 s = 6
        && Set.exists (fun x -> x = 3) s
        && Set.forall (fun x -> x < 4) s
    )
    + check (
        s = set [ 2; 1; 3 ]
        && compare (set [ 1; 2 ]) (set [ 1; 3 ]) = -1
        && Set.add 2 s = s
        && Set.remove 2 s = set [ 1; 3 ]
    )
    + same
        "set [\"a\"; \"b\"]|Some (set [1; 2])|[set [1]; set [2]]"
        (sprintf "%A|%A|%A" (set [ "b"; "a"; "b" ]) (Some(set [ 1; 2 ])) [ set [ 1 ]; set [ 2 ] ])
    + same
        "Argument: Set contains no elements. (Parameter 's')"
        (raised (fun () -> string (Set.minElement (Set.empty: Set<int>))))
    + check (Set.count (Set.ofList (List.init 2000 (fun i -> i % 700))) = 700)

let run () : int =
    let before = liveCells ()
    let failed = maps () + sets ()
    printfn "maps: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
