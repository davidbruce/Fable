module Arrays

// Arrays: counted cells whose items can be assigned, with an identity as on .NET. An index
// outside the array raises. An array can be part of a cycle. Every expected text is what
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
    | :? System.IndexOutOfRangeException as e -> "IndexOutOfRange: " + e.Message
    | :? System.ArgumentOutOfRangeException as e -> "ArgumentOutOfRange: " + e.Message
    | :? System.ArgumentException as e -> "Argument: " + e.Message
    | e -> "other: " + e.Message

// ---- the basics ----
let sum (a: int[]) : int =
    let mutable total = 0

    for x in a do
        total <- total + x

    total

let squares (n: int) : int[] =
    let a = Array.zeroCreate n

    for i in 0 .. n - 1 do
        a.[i] <- i * i

    a

let swap (a: string[]) (i: int) (j: int) : unit =
    let t = a.[i]
    a.[i] <- a.[j]
    a.[j] <- t

let bubble (a: int[]) : unit =
    let mutable changed = true

    while changed do
        changed <- false

        for i in 0 .. a.Length - 2 do
            if a.[i] > a.[i + 1] then
                let t = a.[i]
                a.[i] <- a.[i + 1]
                a.[i + 1] <- t
                changed <- true

let basics () : int =
    let a = [| 1; 2; 3 |]
    let alias = a
    alias.[0] <- 10
    let words = [| "a" + "b"; "c"; "d" + "e" |]
    swap words 0 2
    let mixed = [| 5; 3; 9; 1; 7 |]
    bubble mixed
    let empty: int[] = [||]

    check (a.Length = 3 && a.[0] = 10 && sum a = 15 && sum empty = 0 && empty.Length = 0)
    + same "[|0; 1; 4; 9; 16|]" (sprintf "%A" (squares 5))
    + same "[|\"de\"; \"c\"; \"ab\"|]" (sprintf "%A" words)
    + same "[|1; 3; 5; 7; 9|]" (sprintf "%A" mixed)
    + check (a = [| 10; 2; 3 |] && a <> [| 10; 2 |] && words = [| "de"; "c"; "ab" |])
    + same
        "[|2; 3|]|[||]|[|10; 2|]|[||]|[|10; 2|]"
        (sprintf "%A|%A|%A|%A|%A" a.[1..5] a.[5..] a.[..1] a.[2..1] a.[-1 .. 1])
    + same "IndexOutOfRange: Index was outside the bounds of the array." (raised (fun () -> string a.[5]))
    + same "IndexOutOfRange: Index was outside the bounds of the array." (raised (fun () -> string a.[-1]))
    + same
        "IndexOutOfRange: Index was outside the bounds of the array."
        (raised (fun () ->
            a.[3] <- 1
            ""
        ))

// ---- the Array module ----
let arrayModule () : int =
    let a = [| 1; 2; 3; 4 |]
    let names = [| "x"; "yy"; "zzz" |]
    let seen = ref ""
    Array.iter (fun (s: string) -> seen.Value <- seen.Value + s + ".") names
    let places = ref 0
    Array.iteri (fun i (s: string) -> places.Value <- places.Value * 10 + i + s.Length) names
    let filled = Array.create 4 "-"
    Array.fill filled 1 2 "+"
    let zeros: string[] = Array.zeroCreate 2

    check (
        Array.length a = 4
        && not (Array.isEmpty a)
        && Array.isEmpty (Array.empty: int[])
        && Array.get a 1 = 2
    )
    + same
        "[|0; 2; 4|]|[|7; 7|]|[|1; 2; 3; 4|]"
        (sprintf "%A|%A|%A" (Array.init 3 (fun i -> i * 2)) (Array.create 2 7) (Array.copy a))
    + same
        "[|1; 2; 3; 4; 1; 2|]|[|4; 3; 2; 1|]|[|2; 3|]"
        (sprintf "%A|%A|%A" (Array.append a [| 1; 2 |]) (Array.rev a) (Array.sub a 1 2))
    + same
        "[|\"x!\"; \"yy!\"; \"zzz!\"|]|[|1; 2; 3|]"
        (sprintf "%A|%A" (Array.map (fun s -> s + "!") names) (Array.map String.length names))
    + same "[|\"0x\"; \"1yy\"; \"2zzz\"|]" (sprintf "%A" (Array.mapi (fun i s -> string i + s) names))
    + same
        "x.yy.zzz.|[|\"-\"; \"+\"; \"+\"; \"-\"|]|[|null; null|]"
        (seen.Value + "|" + sprintf "%A" filled + "|" + sprintf "%A" zeros)
    + check (
        places.Value = 135
        && Array.fold (fun acc x -> acc + x) 0 a = 10
        && Array.fold (fun acc s -> acc + s) ">" names = ">xyyzzz"
    )
    + same
        "[|2; 4|]|[|\"yy\"; \"zzz\"|]"
        (sprintf "%A|%A" (Array.filter (fun x -> x % 2 = 0) a) (Array.filter (fun (s: string) -> s.Length > 1) names))
    + check (
        Array.exists (fun x -> x > 3) a
        && not (Array.exists (fun x -> x > 4) a)
        && Array.forall (fun x -> x > 0) a
    )
    + check (Array.contains 3 a && not (Array.contains 9 a) && Array.contains "yy" names)
    + same "[1; 2; 3; 4]|[|\"p\"; \"q\"|]" (sprintf "%A|%A" (Array.toList a) (Array.ofList [ "p"; "q" ]))
    + same
        "Argument: The input must be non-negative.\ncount = -1 (Parameter 'count')"
        (raised (fun () -> string (Array.zeroCreate<int> -1).Length))
    + same
        "Argument: The input must be non-negative.\ncount = -1 (Parameter 'count')"
        (raised (fun () -> string (Array.create -1 1).Length))
    + same
        "ArgumentOutOfRange: The index is outside the legal range.\ncount = 5, array.Length = 4 (Parameter 'count')"
        (raised (fun () -> sprintf "%A" (Array.sub a 1 5)))
    + same
        "other: stop"
        (raised (fun () ->
            sprintf
                "%A"
                (Array.map
                    (fun (s: string) ->
                        if s = "yy" then
                            failwith "stop"
                        else
                            s + s
                    )
                    names)
        ))

// ---- arrays inside other values, and the other way round ----
type Point =
    {
        X: int
        Y: int
    }

type Shelf =
    {
        Label: string
        Slots: string option[]
    }

type Node =
    {
        Id: int
        Kids: Node[]
    }

type Tree =
    | Tip of int
    | Branch of Tree[]

let rec total (t: Tree) : int =
    match t with
    | Tip n -> n
    | Branch kids ->
        let mutable s = 0

        for k in kids do
            s <- s + total k

        s

let inData () : int =
    let points =
        [|
            {
                X = 1
                Y = 2
            }
            {
                X = 3
                Y = 4
            }
        |]

    points.[0] <- { points.[1] with Y = 9 }

    let shelf =
        {
            Label = "top"
            Slots = Array.create 3 None
        }

    shelf.Slots.[1] <- Some("book" + string 1)
    let grid = Array.init 3 (fun i -> Array.create 2 i)
    grid.[1].[0] <- 7
    let tree = Branch [| Tip 1; Branch [| Tip 2; Tip 3 |]; Branch [||] |]
    let pairs = [| (1, "one"); (2, "two") |]
    let fns = [| (fun x -> x + 1); (fun x -> x * 2) |]

    // (a ring through an array: the collector frees it)
    let leaf =
        {
            Id = 2
            Kids = Array.zeroCreate 0
        }

    let parent =
        {
            Id = 1
            Kids = [| leaf; leaf |]
        }

    let holder: Node option[] = Array.create 1 None
    let ring = [| holder |]
    ignore ring

    same "[|{ X = 3\n    Y = 9 }; { X = 3\n               Y = 4 }|]" (sprintf "%A" points)
    + same "{ Label = \"top\"\n  Slots = [|None; Some \"book1\"; None|] }" (sprintf "%A" shelf)
    + same "[|[|0; 0|]; [|7; 1|]; [|2; 2|]|]" (sprintf "%A" grid)
    + check (total tree = 6 && parent.Kids.[1].Id = 2 && parent.Kids.Length = 2)
    + same "Branch [|Tip 1; Branch [|Tip 2; Tip 3|]; Branch [||]|]" (sprintf "%A" tree)
    + check (snd pairs.[1] = "two" && fns.[0]5 + fns.[1]5 = 16)

type Cell =
    {
        Name: string
        Links: Cell[]
    }

let cycles () : int =
    let before = liveCells ()

    let build () : int =
        let a =
            {
                Name = "a" + string 1
                Links = Array.zeroCreate 0
            }

        let links: Cell option[] = Array.create 2 None
        ignore links

        let b =
            {
                Name = "b"
                Links = [| a |]
            }

        let c =
            {
                Name = "c"
                Links = [| b; a |]
            }

        // (close a ring: c -> b -> ... and b's array is given c)
        b.Links.[0] <- c
        c.Links.Length + b.Links.[0].Links.Length

    let n = build ()
    Collector.collect () |> ignore

    check (n = 4)
    + (if counting () then
           check (liveCells () = before)
       else
           0)

let run () : int =
    let before = liveCells ()
    let failed = basics () + arrayModule () + inData () + cycles ()
    printfn "arrays: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
