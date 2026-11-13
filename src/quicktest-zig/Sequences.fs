module Sequences

// Sequences: `seq { }`, the Seq module, list and array comprehensions, ranges, and `for` over
// a sequence. Nothing is computed before it is asked for. Every expected text is what .NET
// gives. `run` returns the number of failed checks.

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

let rec fib (a: int) (b: int) : seq<int> =
    seq {
        yield a
        yield! fib b (a + b)
    }

let squaresOfOdds (xs: int list) : int list =
    [
        for x in xs do
            if x % 2 = 1 then
                yield x * x
    ]

let run () : int =
    let before = liveCells ()
    let mutable evaluated = 0

    let lazyNumbers =
        seq {
            for i in 1..5 do
                evaluated <- evaluated + 1
                yield i * 10
        }

    let firstTwo = lazyNumbers |> Seq.take 2 |> Seq.toList
    let afterTake = evaluated

    let words =
        seq {
            "a"
            "b" + "c"
            "d"
        }

    let mutable walked = ""

    for w in words do
        walked <- walked + w + "."

    for i in 10..-3..1 do
        walked <- walked + string i

    let mutable closedEarly = 0

    let guarded =
        seq {
            try
                yield 10
                yield 20
                yield 30
            finally
                closedEarly <- closedEarly + 1
        }

    let takenOne = guarded |> Seq.take 1 |> Seq.toList
    let headItem = guarded |> Seq.head
    let truncZero = guarded |> Seq.truncate 0 |> Seq.toList
    let picked = guarded |> Seq.tryFind (fun x -> x = 20)

    let failed =
        same
            "[2; 4; 6]|[1; 2; 3; 4; 5]|[|0; 2; 4; 6; 8; 10|]"
            (sprintf "%A|%A|%A" [ for i in 1..3 -> i * 2 ] [ 1..5 ] [| for i in 0..2..10 -> i |])
        + same
            "[1; 9; 25]|[]|['a'; 'b'; 'c']"
            (sprintf "%A|%A|%A" (squaresOfOdds [ 1; 2; 3; 4; 5 ]) [ 5..1 ] [ 'a' .. 'c' ])
        + same "[10; 20]|2" (sprintf "%A|%d" firstTwo afterTake)
        + same "[0; 1; 1; 2; 3; 5; 8; 13; 21; 34]" (sprintf "%A" (fib 0 1 |> Seq.take 10 |> Seq.toList))
        + same "a.bc.d.10741" walked
        + same
            "seq [1; 2; 3; 4; ...]|seq [1; 2]|seq []"
            (sprintf
                "%A|%A|%A"
                (seq { 1..10 })
                (seq {
                    1
                    2
                })
                (Seq.empty: seq<int>))
        + check (
            Seq.length words = 3
            && Seq.head words = "a"
            && Seq.last words = "d"
            && Seq.item 1 words = "bc"
            && Seq.isEmpty Seq.empty<int>
        )
        + same
            "[3; 5]|[\"A\"; \"BC\"; \"D\"]|[(0, 'x'); (1, 'y')]"
            (sprintf
                "%A|%A|%A"
                (Seq.filter (fun x -> x > 2) [ 1; 3; 5 ] |> List.ofSeq)
                (words |> Seq.map (fun s -> s.ToUpper()) |> Seq.toList)
                (Seq.indexed [ 'x'; 'y' ] |> Seq.toList))
        + check (
            Seq.sum [ 1; 2; 3 ] = 6
            && Seq.fold (+) 0 (seq { 1..100 }) = 5050
            && Seq.exists (fun x -> x = 3) [ 1; 3 ]
            && Seq.forall (fun x -> x > 0) [ 1; 3 ]
        )
        + same
            "[1; 2; 3; 4]|[2; 3]|[1; 2]|[3; 4; 5]"
            (sprintf
                "%A|%A|%A|%A"
                (Seq.append [ 1; 2 ] [ 3; 4 ] |> Seq.toList)
                (Seq.collect (fun x -> [ x + 1 ]) [ 1; 2 ] |> Seq.toList)
                (Seq.takeWhile (fun x -> x < 3) [ 1; 2; 3; 1 ] |> Seq.toList)
                (Seq.skip 2 [ 1; 2; 3; 4; 5 ] |> Seq.toList))
        + same
            "[1; 2; 4; 8; 16]|[0; 1; 4]|[(1, 'a'); (2, 'b')]"
            (sprintf
                "%A|%A|%A"
                (Seq.unfold
                    (fun x ->
                        if x > 16 then
                            None
                        else
                            Some(x, x * 2)
                    )
                    1
                 |> Seq.toList)
                (Seq.init 3 (fun i -> i * i) |> Seq.toList)
                (Seq.zip [ 1; 2; 3 ] [ 'a'; 'b' ] |> Seq.toList))
        + same
            "[1; 2; 3]|[3; 2; 1]|Some 2|[(1, 2); (2, 3)]"
            (sprintf
                "%A|%A|%A|%A"
                (Seq.sort [ 3; 1; 2 ] |> Seq.toList)
                (Seq.rev [ 1; 2; 3 ] |> Seq.toList)
                (Seq.tryFind (fun x -> x > 1) [ 1; 2; 3 ])
                (Seq.pairwise [ 1; 2; 3 ] |> Seq.toList))
        + check (
            Seq.max [ 3; 9; 2 ] = 9
            && Seq.toArray (seq { 1..3 }) = [| 1; 2; 3 |]
            && Set.ofSeq (seq { 1..3 }) = set [ 1; 2; 3 ]
            && List.ofSeq (ResizeArray [ 1; 2 ]) = [ 1; 2 ]
        )
        + check (Seq.length (Seq.initInfinite id |> Seq.take 1000) = 1000)
        + check (
            takenOne = [ 10 ]
            && headItem = 10
            && truncZero = []
            && picked = Some 20
            && closedEarly = 3
        )

    printfn "sequences: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
