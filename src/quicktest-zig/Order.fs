module Order

// Comparison and hashing of any F# value, and what is built on them: sorting, min and max,
// grouping. The Option and Result modules. Every expected text is what .NET gives.
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

type Person =
    {
        Name: string
        Age: int
    }

type Suit =
    | Clubs
    | Hearts
    | Rank of int

let people =
    [
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
        {
            Name = "Al"
            Age = 20
        }
    ]

let comparing () : int =
    check (
        compare
            {
                Name = "Al"
                Age = 2
            }
            {
                Name = "Al"
                Age = 3
            }
            =
            -1
        && compare
            {
                Name = "B"
                Age = 0
            }
            {
                Name = "Al"
                Age = 9
            }
            =
            1
    )
    + check (
        {
            Name = "Al"
            Age = 2
        }
            <
            {
                Name = "Al"
                Age = 3
            }
        && (1, "b") > (1, "a")
        && Some 1 > None
        && [ 1; 2 ] < [ 1; 3 ]
        && [ 1 ] < [ 1; 0 ]
    )
    + check (
        Clubs < Hearts
        && Hearts < Rank 2
        && Rank 2 < Rank 3
        && compare (Rank 5) (Rank 5) = 0
    )
    + check (
        max 3 7 = 7
        && min "b" "a" = "a"
        && max (Some 2) None = Some 2
        && min (1, "z") (1, "a") = (1, "a")
    )
    + check (
        hash
            {
                Name = "Al"
                Age = 2
            }
            =
            hash
                {
                    Name = "Al"
                    Age = 2
                }
        && hash 42 = 42
        && hash "abc" = hash ("ab" + "c")
    )
    + check ([| 1; 2 |] < [| 1; 3 |] && [| 9 |] < [| 1; 1 |])

let sorting () : int =
    let byAge =
        List.sortBy (fun p -> p.Age) people |> List.map (fun p -> p.Name + string p.Age)

    let groups =
        List.groupBy (fun p -> p.Age) people
        |> List.map (fun (age, ps) -> (age, List.map (fun p -> p.Name) ps))

    same
        "[1; 1; 2; 3; 5; 9]|[9; 5; 3; 2; 1; 1]"
        (sprintf "%A|%A" (List.sort [ 3; 1; 9; 1; 5; 2 ]) (List.sortDescending [ 3; 1; 9; 1; 5; 2 ]))
    + same "[\"Al20\"; \"Al25\"; \"Cy30\"; \"Bo30\"]" (sprintf "%A" byAge)
    + same
        "[\"a\"; \"b\"; \"c\"]|[Clubs; Hearts; Rank 1; Rank 4]"
        (sprintf "%A|%A" (List.sort [ "c"; "a"; "b" ]) (List.sort [ Rank 4; Hearts; Rank 1; Clubs ]))
    + same "[(30, [\"Cy\"; \"Bo\"]); (25, [\"Al\"]); (20, [\"Al\"])]" (sprintf "%A" groups)
    + same "[(\"Cy\", 1); (\"Al\", 2); (\"Bo\", 1)]" (sprintf "%A" (List.countBy (fun p -> p.Name) people))
    + check (
        List.max [ 3; 9; 2 ] = 9
        && List.min [ "b"; "a" ] = "a"
        && (List.maxBy (fun p -> p.Age) people).Name = "Cy"
        && (List.minBy (fun p -> p.Age) people).Age = 20
    )
    + same
        "[\"Cy\"; \"Al\"; \"Bo\"]"
        (sprintf "%A" (List.distinctBy (fun p -> p.Name) people |> List.map (fun p -> p.Name)))
    + same
        "[0; 1; 3; 6]|([1; 2], [3])|[[1; 2]; [3; 4]; [5]]|[[1; 2]; [2; 3]]"
        (sprintf
            "%A|%A|%A|%A"
            (List.scan (+) 0 [ 1; 2; 3 ])
            (List.splitAt 2 [ 1; 2; 3 ])
            (List.chunkBySize 2 [ 1; 2; 3; 4; 5 ])
            (List.windowed 2 [ 1; 2; 3 ]))
    + same
        "[2; 4]|[(1, 'a'); (1, 'b'); (2, 'a'); (2, 'b')]"
        (sprintf "%A|%A" (List.except [ 1; 3 ] [ 1; 2; 3; 4 ]) (List.allPairs [ 1; 2 ] [ 'a'; 'b' ]))
    + check (
        List.fold2 (fun acc a b -> acc + a * b) 0 [ 1; 2 ] [ 3; 4 ] = 11
        && List.forall2 (=) [ 1 ] [ 1 ]
        && List.exists2 (<) [ 1; 5 ] [ 0; 6 ]
    )
    // (a long list sorts without running out of stack)
    + check (List.sort (List.init 20000 (fun i -> 20000 - i)) |> List.head = 1)

let options () : int =
    let parse (s: string) : int option =
        if s = "" then
            None
        else
            Some s.Length

    let half (n: int) : Result<int, string> =
        if n % 2 = 0 then
            Ok(n / 2)
        else
            Error("odd " + string n)

    same
        "Some 4|None|Some 3|None"
        (sprintf
            "%A|%A|%A|%A"
            (Option.map (fun x -> x * 2) (Some 2))
            (Option.map (fun x -> x * 2) None)
            (Option.bind parse (Some "abc"))
            (Option.bind parse (Some "")))
    + check (
        Option.defaultValue 0 None = 0
        && Option.defaultWith (fun () -> 5) None = 5
        && Option.defaultValue 0 (Some 3) = 3
    )
    + check (
        Option.isSome (Some 1)
        && Option.isNone None
        && (Some 1).IsSome
        && (None: int option).IsNone
        && Option.get (Some "x") = "x"
    )
    + check (
        Option.filter (fun x -> x > 2) (Some 3) = Some 3
        && Option.filter (fun x -> x > 2) (Some 1) = None
        && Option.exists (fun x -> x = 1) (Some 1)
    )
    + check (
        Option.toList (Some 1) = [ 1 ]
        && Option.count None = 0
        && Option.orElse (Some 2) None = Some 2
        && Option.flatten (Some(Some 1)) = Some 1
    )
    + check (
        Option.fold (+) 1 (Some 2) = 3
        && Option.contains "a" (Some "a")
        && Option.map2 (+) (Some 1) (Some 2) = Some 3
    )
    + same
        "Ok 2|Error \"odd 3\"|Ok 1|Error \"odd 3\"|Error 9"
        (sprintf
            "%A|%A|%A|%A|%A"
            (half 4)
            (half 3)
            (Result.bind half (half 4))
            (Result.bind half (Ok 3))
            (Result.mapError String.length (half 33333)))
    + same "Ok \"4\"" (sprintf "%A" (Result.map string (half 8)))

let run () : int =
    let before = liveCells ()
    let failed = comparing () + sorting () + options ()
    printfn "order: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
