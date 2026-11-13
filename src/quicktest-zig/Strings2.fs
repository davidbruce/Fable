module Strings2

// More of System.String and System.Text: Split, Join, ToCharArray, StringBuilder,
// String.Format, .NET's ToString of options, tuples and lists, the classes of characters,
// and comparison that ignores case. Every expected text is what .NET gives.
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

let classes (c: char) : string =
    [
        System.Char.IsDigit c
        System.Char.IsLetter c
        System.Char.IsLetterOrDigit c
        System.Char.IsUpper c
        System.Char.IsLower c
        System.Char.IsPunctuation c
        System.Char.IsControl c
        System.Char.IsSeparator c
        System.Char.IsSymbol c
        System.Char.IsNumber c
    ]
    |> List.map (fun b ->
        if b then
            "1"
        else
            "0"
    )
    |> String.concat ""

let run () : int =
    let before = liveCells ()
    let sb = System.Text.StringBuilder()
    sb.Append("a").Append(1).Append('c').Append(2.5).Append(true) |> ignore
    sb.AppendLine("x").AppendLine() |> ignore
    let built = sb.ToString() + "|" + string sb.Length
    sb.Clear().Append("z") |> ignore

    // appending: a string grows in place only when nothing else refers to it
    let mutable grown = ""

    for _ in 1..100000 do
        grown <- grown + "x"

    let mutable step = "a"
    let mutable kept = []

    for _ in 1..3 do
        kept <- step :: kept
        step <- step + "b"

    let twice = step + step

    let failed =
        same
            "100000|[\"abb\"; \"ab\"; \"a\"]|abbb|abbbabbb"
            (string grown.Length + "|" + sprintf "%A" kept + "|" + step + "|" + twice)
        + same
            "[|\"a\"; \"b\"; \"\"; \"c\"|]|[|\"a\"; \" b\"; \"c\"|]|[|\"a\"; \"b\"; \"c\"|]|[|\"a\"; \"b\"|]"
            (sprintf
                "%A|%A|%A|%A"
                ("a,b,,c".Split(','))
                ("a, b;c".Split([| ','; ';' |]))
                ("a--b--c".Split("--"))
                ("a,,b".Split([| ',' |], System.StringSplitOptions.RemoveEmptyEntries)))
        + same
            "[|\"\"; \"a\"; \"\"; \"b\"; \"\"|]|[|\"a\"; \"b\"; \"c\"|]"
            (sprintf "%A|%A" (" a  b ".Split(' ')) ("a b\tc".Split()))
        + same
            "a, b|1-2-3|x+y||p.q"
            (System.String.Join(", ", [| "a"; "b" |])
             + "|"
             + System.String.Join("-", [ 1; 2; 3 ])
             + "|"
             + String.concat
                 "+"
                 (seq {
                     "x"
                     "y"
                 })
             + "|"
             + System.String.Join(",", ([||]: string[]))
             + "|"
             + String.concat "." [ "p"; "q" ])
        + same
            "[|'h'; 'é'; 'l'; 'l'; 'o'|]|ab"
            (sprintf "%A|%s" ("héllo".ToCharArray()) (System.String([| 'a'; 'b' |])))
        + same "a1c2.5Truex\n\n|13" built
        + same "z" (sb.ToString())
        + same
            "1 + two = 3.14|    1|two |{x}|100%"
            (System.String.Format("{0} + {1} = {2:N2}|{0,5}|{1,-4}|{{x}}|{3}%", 1, "two", 3.14159, 100))
        + same
            "Some(1)||[1; 2]|(1, a)|[1; 2; 3; ... ]|Some(x)|[a]"
            (string (Some 1)
             + "|"
             + string (None: int option)
             + "|"
             + string [ 1; 2 ]
             + "|"
             + string (1, "a")
             + "|"
             + string [ 1..10 ]
             + "|"
             + string (Some "x")
             + "|"
             + string [ "a" ])
        + same
            "Some(Some(2))|[Some(1)]|((1, 2), 3)|[]|map [(1, a)]|set [1; 2]"
            (string (Some(Some 2))
             + "|"
             + string [ Some 1 ]
             + "|"
             + string ((1, 2), 3)
             + "|"
             + string ([]: int list)
             + "|"
             + string (Map.ofList [ (1, "a") ])
             + "|"
             + string (set [ 1; 2 ]))
        + same "v=Some(3) t=(1, 2)" $"v={Some 3} t={(1, 2)}"
        + same
            "0110100000|0111000000|1010000001|0000000100|0000001000|0000010000|0000000010|0000010000|0110100000|1010000001|0000000100|0000000010|0000010000"
            (String.concat "|" (List.map classes [ 'a'; 'Z'; '5'; ' '; '\t'; '!'; '+'; '_'; 'é'; '٣'; ' '; '€'; '(' ]))
        + check (
            System.String.Compare("a", "B", System.StringComparison.Ordinal) = 31
            && System.String.Compare("a", "A", System.StringComparison.OrdinalIgnoreCase) = 0
        )
        + check (
            "abc".Equals("ABC", System.StringComparison.OrdinalIgnoreCase)
            && "Abc".StartsWith("ab", System.StringComparison.OrdinalIgnoreCase)
            && "abc".IndexOf("C", System.StringComparison.OrdinalIgnoreCase) = 2
        )
        + check (System.Char.GetNumericValue '7' = 7.0 && System.Char.GetNumericValue 'x' = -1.0)

    printfn "strings2: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
