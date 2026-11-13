module Lists

// The `List` module. The functions are written in F# in the runtime library and compiled by
// the Zig target; a call of `List.map` goes to that. Every expected text is what .NET gives.
// `run` returns the number of failed checks.

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
    | :? System.ArgumentOutOfRangeException as e -> "ArgumentOutOfRange: " + e.Message
    | :? System.ArgumentException as e -> "Argument: " + e.Message
    | :? System.InvalidOperationException as e -> "InvalidOperation: " + e.Message
    | :? System.Collections.Generic.KeyNotFoundException as e -> "KeyNotFound: " + e.Message
    | e -> "other: " + e.Message

type Item =
    {
        Name: string
        Qty: int
    }

let basics () : int =
    let xs = [ 1; 2; 3; 4 ]
    let names = [ "x"; "yy"; "zzz" ]
    let seen = ref ""
    List.iter (fun (s: string) -> seen.Value <- seen.Value + s + ".") names
    let places = ref 0
    List.iteri (fun i (s: string) -> places.Value <- places.Value * 10 + i + s.Length) names

    check (
        List.length xs = 4
        && xs.Length = 4
        && List.head xs = 1
        && List.last xs = 4
        && List.item 2 xs = 3
        && xs.[1] = 2
    )
    + same
        "[2; 3; 4]|[4; 3; 2; 1]|[1; 2; 3; 4; 9]|[1; 2; 3; 4; 5; 6]"
        (sprintf "%A|%A|%A|%A" (List.tail xs) (List.rev xs) (xs @ [ 9 ]) (List.concat [ xs; []; [ 5; 6 ] ]))
    + same
        "Some 1|None|Some 4|Some 3|None"
        (sprintf
            "%A|%A|%A|%A|%A"
            (List.tryHead xs)
            (List.tryHead ([]: int list))
            (List.tryLast xs)
            (List.tryItem 2 xs)
            (List.tryItem 9 xs))
    + same
        "[\"x!\"; \"yy!\"; \"zzz!\"]|[1; 2; 3]|[\"0x\"; \"1yy\"; \"2zzz\"]"
        (sprintf
            "%A|%A|%A"
            (List.map (fun s -> s + "!") names)
            (List.map String.length names)
            (List.mapi (fun i s -> string i + s) names))
    + same
        "[\"x1\"; \"yy2\"; \"zzz3\"]"
        (sprintf "%A" (List.map2 (fun (s: string) (n: int) -> s + string n) names [ 1; 2; 3 ]))
    + same "x.yy.zzz." seen.Value
    + check (
        places.Value = 135
        && List.fold (fun acc x -> acc + x) 0 xs = 10
        && List.fold (fun acc s -> acc + s) ">" names = ">xyyzzz"
    )
    + check (
        List.foldBack (fun s acc -> acc + s) names ">" = ">zzzyyx"
        && List.reduce (fun a b -> a * b) xs = 24
    )
    + same
        "[2; 4]|[\"yy\"; \"zzz\"]|[10; 30]|[1; 1; 2; 2]"
        (sprintf
            "%A|%A|%A|%A"
            (List.filter (fun x -> x % 2 = 0) xs)
            (List.filter (fun (s: string) -> s.Length > 1) names)
            (List.choose
                (fun x ->
                    if x % 2 = 1 then
                        Some(x * 10)
                    else
                        None
                )
                xs)
            (List.collect (fun x -> [ x; x ]) [ 1; 2 ]))
    + check (
        List.exists (fun x -> x > 3) xs
        && not (List.exists (fun x -> x > 4) xs)
        && List.forall (fun x -> x > 0) xs
    )
    + check (List.contains 3 xs && not (List.contains 9 xs) && List.contains "yy" names)
    + same
        "Some 3|None|3|Some 2|2|Some \"yy!\"|\"zzz?\""
        (sprintf
            "%A|%A|%A|%A|%A|%A|%A"
            (List.tryFind (fun x -> x > 2) xs)
            (List.tryFind (fun x -> x > 9) xs)
            (List.find (fun x -> x > 2) xs)
            (List.tryFindIndex (fun x -> x > 2) xs)
            (List.findIndex (fun x -> x > 2) xs)
            (List.tryPick
                (fun (s: string) ->
                    if s.Length = 2 then
                        Some(s + "!")
                    else
                        None
                )
                names)
            (List.pick
                (fun (s: string) ->
                    if s.Length = 3 then
                        Some(s + "?")
                    else
                        None
                )
                names))
    + same
        "[0; 2; 4]|[\"ab\"; \"ab\"]|[7]"
        (sprintf "%A|%A|%A" (List.init 3 (fun i -> i * 2)) (List.replicate 2 ("a" + "b")) (List.singleton 7))
    + same
        "[(1, \"x\"); (2, \"yy\"); (3, \"zzz\")]|([1; 2], [\"a\"; \"b\"])"
        (sprintf "%A|%A" (List.zip [ 1; 2; 3 ] names) (List.unzip [ (1, "a"); (2, "b") ]))
    + same
        "[1; 2]|[1; 2; 3; 4]|[3; 4]|[1; 2]|[3; 4]"
        (sprintf
            "%A|%A|%A|%A|%A"
            (List.take 2 xs)
            (List.truncate 9 xs)
            (List.skip 2 xs)
            (List.takeWhile (fun x -> x < 3) xs)
            (List.skipWhile (fun x -> x < 3) xs))
    + same
        "([2; 4], [1; 3])|[(0, \"x\"); (1, \"yy\"); (2, \"zzz\")]|[(1, 2); (2, 3); (3, 4)]"
        (sprintf "%A|%A|%A" (List.partition (fun x -> x % 2 = 0) xs) (List.indexed names) (List.pairwise xs))
    + same
        "[1; 2; 3]|[\"a\"; \"b\"]|7"
        (sprintf "%A|%A|%A" (List.distinct [ 1; 2; 1; 3; 2 ]) (List.distinct [ "a"; "b"; "a" ]) (List.exactlyOne [ 7 ]))
    + same "[|1; 2; 3; 4|]|[\"p\"; \"q\"]" (sprintf "%A|%A" (List.toArray xs) (List.ofArray [| "p"; "q" |]))

let records () : int =
    let items =
        [
            {
                Name = "nut"
                Qty = 3
            }
            {
                Name = "bolt"
                Qty = 0
            }
            {
                Name = "gear"
                Qty = 7
            }
        ]

    let stocked =
        items |> List.filter (fun i -> i.Qty > 0) |> List.map (fun i -> i.Name)

    let total = items |> List.fold (fun acc i -> acc + i.Qty) 0
    let big = List.init 20000 id

    same "[\"nut\"; \"gear\"]" (sprintf "%A" stocked)
    + check (
        total = 10
        && List.contains
            {
                Name = "bolt"
                Qty = 0
            }
            items
    )
    // (long lists: the functions run in loops, not on the stack)
    + check (
        List.length (List.map (fun x -> x + 1) big) = 20000
        && List.fold (+) 0 (List.filter (fun x -> x % 2 = 0) big) = 99990000
    )
    + check (List.length (big @ big) = 40000 && List.last (List.rev big) = 0)

let errors () : int =
    let empty: int list = []

    same "Argument: The input list was empty. (Parameter 'list')" (raised (fun () -> string (List.head empty)))
    + same "Argument: The input list was empty. (Parameter 'list')" (raised (fun () -> string (List.last empty)))
    + same "Argument: The input list was empty. (Parameter 'list')" (raised (fun () -> string (List.reduce (+) empty)))
    + same "Argument: The input list was empty. (Parameter 'list')" (raised (fun () -> sprintf "%A" (List.tail empty)))
    + same
        "Argument: The index was outside the range of elements in the list. (Parameter 'index')"
        (raised (fun () -> string (List.item 5 [ 1 ])))
    + same
        "Argument: The index was outside the range of elements in the list. (Parameter 'n')"
        (raised (fun () -> string ([ 1 ].[5])))
    + same
        "KeyNotFound: An index satisfying the predicate was not found in the collection."
        (raised (fun () -> string (List.find (fun x -> x > 5) [ 1 ])))
    + same
        "KeyNotFound: An index satisfying the predicate was not found in the collection."
        (raised (fun () ->
            string (
                List.pick
                    (fun x ->
                        if x > 5 then
                            Some x
                        else
                            None
                    )
                    [ 1 ]
            )
        ))
    + same
        "Argument: The lists had different lengths.\nlist1 is 1 element shorter than list2 (Parameter 'list1')"
        (raised (fun () -> sprintf "%A" (List.zip [ 1 ] [ 1; 2 ])))
    + same
        "Argument: The lists had different lengths.\nlist2 is 2 elements shorter than list1 (Parameter 'list2')"
        (raised (fun () -> sprintf "%A" (List.map2 (+) [ 1; 2; 3 ] [ 1 ])))
    + same
        "InvalidOperation: The input sequence has an insufficient number of elements.\nThe list was 2 elements shorter than the index"
        (raised (fun () -> sprintf "%A" (List.take 3 [ 1 ])))
    + same
        "ArgumentOutOfRange: The index is outside the legal range.\ncount = 3, distance past the list = 2 (Parameter 'count')"
        (raised (fun () -> sprintf "%A" (List.skip 3 [ 1 ])))
    + same
        "Argument: The input must be non-negative.\ncount = -1 (Parameter 'count')"
        (raised (fun () -> sprintf "%A" (List.init -1 id)))
    + same
        "Argument: The input must be non-negative. (Parameter 'count')"
        (raised (fun () -> sprintf "%A" (List.replicate -1 1)))
    + same
        "Argument: The input sequence contains more than one element. (Parameter 'source')"
        (raised (fun () -> string (List.exactlyOne [ 1; 2 ])))
    + same
        "other: stop"
        (raised (fun () ->
            sprintf
                "%A"
                (List.map
                    (fun x ->
                        if x = 2 then
                            failwith "stop"
                        else
                            string x
                    )
                    [ 1; 2; 3 ])
        ))

let run () : int =
    let before = liveCells ()
    let big = List.init 1000000 id
    let other = List.init 1000000 id

    let long =
        check (
            big = other
            && compare
                big
                (List.init
                    1000000
                    (fun i ->
                        if i = 999999 then
                            0
                        else
                            i
                    ))
                =
                1
            && hash big = hash other
        )

    let failed = basics () + records () + errors () + long
    printfn "lists: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
