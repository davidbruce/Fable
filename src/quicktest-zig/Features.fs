module Features

// Language features: active patterns (also with several cases, which give `Choice`),
// enums, anonymous records, struct records and unions, units of measure, `lazy`.
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

// ---- active patterns ----
let (|Even|Odd|) (n: int) =
    if n % 2 = 0 then
        Even
    else
        Odd

let (|Small|Medium|Large|) (n: int) =
    if n < 10 then
        Small
    elif n < 100 then
        Medium n
    else
        Large(n / 100, "big")

let (|Positive|_|) (n: int) =
    if n > 0 then
        Some n
    else
        None

let (|Prefix|_|) (prefix: string) (s: string) =
    if s.StartsWith prefix then
        Some(s.Substring prefix.Length)
    else
        None

let describe (n: int) : string =
    match n with
    | Positive p & Even -> "pos even " + string p
    | Even -> "even"
    | Odd -> "odd"

let size (n: int) : string =
    match n with
    | Small -> "small"
    | Medium m -> "medium " + string m
    | Large(h, tag) -> tag + " " + string h

let command (s: string) : string =
    match s with
    | Prefix "go " rest -> "going " + rest
    | Prefix "stop" _ -> "stopping"
    | _ -> "?"

// ---- enums ----
type Color =
    | Red = 1
    | Green = 2
    | Blue = 4

let weight (c: Color) : int =
    match c with
    | Color.Red -> 10
    | Color.Green -> 20
    | _ -> int c

// ---- struct records and unions, units of measure ----
[<Struct>]
type P =
    {
        X: int
        Y: int
    }

[<Struct>]
type S =
    | A of a: int
    | B of b: string

[<Measure>]
type m

[<Measure>]
type s

let speed (d: float<m>) (t: float<s>) : float<m / s> = d / t

let run () : int =
    let before = liveCells ()

    let person =
        {|
            Name = "Ann"
            Age = 3
        |}

    let older = {| person with Age = 4 |}

    let point =
        {|
            X = 1
            Y = 2
        |}

    let mutable calls = 0

    let l =
        lazy
            (calls <- calls + 1
             "computed " + string calls)

    let notYet = sprintf "%A" l
    let first = l.Force()
    let second = l.Value
    let failing = lazy (failwith "boom": int)

    let attempts =
        [ 1; 2 ]
        |> List.map (fun _ ->
            try
                string (failing.Force())
            with e ->
                e.Message
        )

    let failed =
        same "pos even 4|even|odd|odd" (describe 4 + "|" + describe -2 + "|" + describe 3 + "|" + describe -3)
        + same "small|medium 42|big 5" (size 3 + "|" + size 42 + "|" + size 512)
        + same "going home|stopping|?" (command "go home" + "|" + command "stop now" + "|" + command "x")
        + check (
            weight Color.Red = 10
            && weight Color.Blue = 4
            && int Color.Green = 2
            && Color.Red <> Color.Blue
            && enum<Color> 2 = Color.Green
        )
        + check (
            person.Age = 3
            && person.Name = "Ann"
            && older.Age = 4
            && older.Name = "Ann"
            && person <> older
            && point =
                {|
                    X = 1
                    Y = 2
                |}
        )
        + same "{ Age = 3\n  Name = \"Ann\" }|[{ X = 1\n   Y = 2 }]" (sprintf "%A|%A" person [ point ])
        + check (
            {
                X = 1
                Y = 2
            }
                =
                {
                    X = 1
                    Y = 2
                }
            && (match B "xy" with
                | B b -> b.Length
                | A a -> a)
                =
                2
        )
        + check (speed 10.0<m> 2.0<s> = 5.0<m / s>)
        + same
            "Value is not created.|computed 1|computed 1|1|True|computed 1"
            (notYet
             + "|"
             + first
             + "|"
             + second
             + "|"
             + string calls
             + "|"
             + string l.IsValueCreated
             + "|"
             + sprintf "%A" l)
        + same "[\"boom\"; \"boom\"]" (sprintf "%A" attempts)

    printfn "features: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
