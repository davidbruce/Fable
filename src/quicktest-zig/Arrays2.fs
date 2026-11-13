module Arrays2

// The rest of the Array module (written in F# in the runtime library). Every expected text is
// what .NET gives. `run` returns the number of failed checks.

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
    | :? System.InvalidOperationException as e -> "InvalidOperation: " + e.Message
    | :? System.ArgumentException as e -> "Argument: " + e.Message
    | e -> "other: " + e.Message

type Person =
    {
        Name: string
        Age: int
    }

let run () : int =
    let before = liveCells ()
    let a = [| 5; 3; 9; 1; 3 |]

    let people =
        [|
            {
                Name = "Cy"
                Age = 30
            }
            {
                Name = "Al"
                Age = 25
            }
            {
                Name = "Bo"
                Age = 30
            }
        |]

    let inPlace = Array.copy a
    Array.sortInPlace inPlace
    let target = Array.create 5 0
    Array.blit a 1 target 2 3

    let failed =
        check (
            Array.head a = 5
            && Array.last a = 3
            && Array.item 2 a = 9
            && Array.tryItem 9 a = None
            && Array.tryHead [||] = (None: int option)
        )
        + same
            "[|1; 3; 3; 5; 9|]|[|9; 5; 3; 3; 1|]|[|1; 3; 3; 5; 9|]"
            (sprintf "%A|%A|%A" (Array.sort a) (Array.sortDescending a) inPlace)
        + same
            "[|\"Al\"; \"Cy\"; \"Bo\"|]"
            (sprintf "%A" (people |> Array.sortBy (fun p -> p.Age) |> Array.map (fun p -> p.Name)))
        + check (
            Array.max a = 9
            && Array.min a = 1
            && (Array.maxBy (fun p -> p.Age) people).Name = "Cy"
            && Array.reduce (+) a = 21
        )
        + same
            "[|5; 3; 9; 1|]|[|(30, 2); (25, 1)|]"
            (sprintf "%A|%A" (Array.distinct a) (Array.countBy (fun p -> p.Age) people))
        + same
            "Some 9|2|Some 1|[|10; 18|]"
            (sprintf
                "%A|%d|%A|%A"
                (Array.tryFind (fun x -> x > 5) a)
                (Array.findIndex (fun x -> x > 5) a)
                (Array.tryFindBack (fun x -> x < 3) a)
                (Array.choose
                    (fun x ->
                        if x > 4 then
                            Some(x * 2)
                        else
                            None
                    )
                    a))
        + same
            "[|1; 1; 2; 2|]|[|0; 5; 8; 17|]|[|(0, 'x'); (1, 'y')|]"
            (sprintf
                "%A|%A|%A"
                (Array.collect (fun x -> [| x; x |]) [| 1; 2 |])
                (Array.scan (+) 0 [| 5; 3; 9 |])
                (Array.indexed [| 'x'; 'y' |]))
        + same
            "[|(1, 'a'); (2, 'b')|]|([|1; 2|], [|'a'; 'b'|])|[|11; 22|]"
            (sprintf
                "%A|%A|%A"
                (Array.zip [| 1; 2 |] [| 'a'; 'b' |])
                (Array.unzip [| (1, 'a'); (2, 'b') |])
                (Array.map2 (+) [| 1; 2 |] [| 10; 20 |]))
        + same
            "([|5; 9|], [|3; 1; 3|])|[|5; 3|]|[|9; 1; 3|]|[|5|]|[|3; 9; 1; 3|]"
            (sprintf
                "%A|%A|%A|%A|%A"
                (Array.partition (fun x -> x > 4) a)
                (Array.take 2 a)
                (Array.skip 2 a)
                (Array.takeWhile (fun x -> x > 4) a)
                (Array.skipWhile (fun x -> x > 4) a))
        + same
            "[|[|5; 3|]; [|9; 1|]; [|3|]|]|[|[|5; 3|]; [|3; 9|]; [|9; 1|]; [|1; 3|]|]|[|(5, 3); (3, 9); (9, 1); (1, 3)|]"
            (sprintf "%A|%A|%A" (Array.chunkBySize 2 a) (Array.windowed 2 a) (Array.pairwise a))
        + same "[|0; 0; 3; 9; 1|]|[|7; 7; 7|]" (sprintf "%A|%A" target (Array.replicate 3 7))
        + same
            "Argument: The input array was empty. (Parameter 'array')"
            (raised (fun () -> string (Array.head ([||]: int[]))))
        + same
            "KeyNotFound: An index satisfying the predicate was not found in the collection."
            (raised (fun () -> string (Array.find (fun x -> x > 100) a)))
        + same
            "InvalidOperation: The input sequence has an insufficient number of elements."
            (raised (fun () -> sprintf "%A" (Array.take 9 a)))
        + same
            "Argument: The arrays have different lengths.\narray1.Length = 5, array2.Length = 1 (Parameter 'array1')"
            (raised (fun () -> sprintf "%A" (Array.map2 (+) a [| 1 |])))

    printfn "arrays2: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
