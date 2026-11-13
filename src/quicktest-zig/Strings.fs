module Strings

// Strings: immutable UTF-16 text as on .NET, counted unless they are literals. Formatting
// (sprintf, interpolation, `string`), printing, and exceptions that carry a message.
// Every expected text is what .NET gives. `run` returns the number of failed checks.

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

// ---- the basics ----
let greet (name: string) : string = "hello, " + name + "!"

let rec repeat (s: string) (n: int) : string =
    if n = 0 then
        ""
    else
        s + repeat s (n - 1)

let countOf (c: char) (s: string) : int =
    let mutable n = 0

    for i in 0 .. s.Length - 1 do
        if s.[i] = c then
            n <- n + 1

    n

let digits (n: int) : string =
    let mutable s = ""

    for i in 1..n do
        s <- s + string i

    s

let kind (s: string) : int =
    match s with
    | "" -> 0
    | "one" -> 1
    | "two" -> 2
    | _ -> s.Length

let basics () : int =
    let name = greet "wörld"
    let twice = name + name

    check (name.Length = 13 && twice.Length = 26)
    + same "hello, wörld!" name
    + check (name.[7] = 'w' && name.[8] = 'ö' && int name.[8] = 246)
    + check ("😀".Length = 2 && String.length "añb" = 3)
    + same "ababab" (repeat "ab" 3)
    + same "" (repeat "ab" 0)
    + check (countOf 'l' "hello, world" = 3)
    + same "12345678910" (digits 10)
    + check (kind "" = 0 && kind "one" = 1 && kind "two" = 2 && kind "three" = 5)
    + check (name = greet "wörld" && name <> greet "world" && "" + name = name)

// ---- order: by code unit, with the numbers that .NET's ordinal comparison gives ----
let ordering () : int =
    let smaller (a: string) (b: string) : string =
        if a < b then
            a
        else
            b

    check (compare "abc" "abd" = -1 && compare "b" "abc" = 1 && compare "a" "A" = 32)
    + check (compare "" "a" = -97 && compare "ab" "abcd" = -2 && compare "ab" "ab" = 0)
    + check (
        "a" < "b"
        && "B" < "a"
        && not ("a" < "B")
        && "ab" <= "ab"
        && "b" > "abc"
        && "b" >= "b"
    )
    + same "apple" (smaller "pear" "apple")
    + check (
        compare 1 2 = -1
        && compare 2.0 1.0 = 1
        && compare 'a' 'c' = -1
        && compare true false = 1
    )
    + check (compare nan 1.0 = -1 && compare 1.0 nan = 1 && compare 5L 5L = 0)

// ---- strings inside other values ----
type Person =
    {
        Name: string
        Age: int
    }

type Token =
    | Word of string
    | Number of int
    | Pair of Token * Token

type Label = { mutable Text: string }

type Link =
    {
        Title: string
        mutable Next: Link option
    }

let rec show (t: Token) : string =
    match t with
    | Word w -> w
    | Number n -> string n
    | Pair(a, b) -> "(" + show a + ", " + show b + ")"

let rec joinWith (sep: string) (xs: string list) : string =
    match xs with
    | [] -> ""
    | [ x ] -> x
    | x :: rest -> x + sep + joinWith sep rest

let rec mapList (f: 'a -> 'b) (xs: 'a list) : 'b list =
    match xs with
    | [] -> []
    | x :: rest -> f x :: mapList f rest

let longest (xs: string list) : string option =
    let rec go (best: string option) (xs: string list) : string option =
        match xs, best with
        | [], _ -> best
        | x :: rest, Some b when b.Length >= x.Length -> go best rest
        | x :: rest, _ -> go (Some x) rest

    go None xs

let inData () : int =
    let ann =
        {
            Name = "Ann" + string 1
            Age = 30
        }

    let older = { ann with Age = 31 }
    let words = [ "a"; "bb" + "b"; "cc" ]
    let label = { Text = "first" }
    let before = label.Text
    label.Text <- before + "+" + string label.Text.Length
    let cell = ref "x"
    cell.Value <- cell.Value + cell.Value
    let prefix = "<" + string 7
    let wrap = fun (s: string) -> prefix + s + ">"
    let pair = ("left", 2)

    // (a ring of records that hold strings: the collector must leave the strings to their counts)
    let first =
        {
            Title = "one" + string 1
            Next = None
        }

    let second =
        {
            Title = "two" + string 2
            Next = Some first
        }

    first.Next <- Some second

    let ring =
        match first.Next with
        | Some n ->
            match n.Next with
            | Some back -> n.Title + back.Title
            | None -> ""
        | None -> ""

    same "Ann1" older.Name
    + check (ann <> older && ann = { older with Age = 30 })
    + same "(x, (12, y))" (show (Pair(Word "x", Pair(Number 12, Word "y"))))
    + check (Word "a" = Word "a" && Word "a" <> Word "b" && Word "1" <> Number 1)
    + same "a, bbb, cc" (joinWith ", " words)
    + same "<7a>|<7bbb>|<7cc>" (joinWith "|" (mapList wrap words))
    + check (mapList (fun (s: string) -> s.Length) words = [ 1; 3; 2 ])
    + check (longest words = Some "bbb" && longest [] = None)
    + same "first" before
    + same "first+5" label.Text
    + same "xx" cell.Value
    + check (fst pair = "left" && pair = ("le" + "ft", 2))
    + check (Helpers.boxOf 1 "boxed" = Helpers.boxOf 1 ("box" + "ed"))
    + same "two2one1" ring

// ---- formatting ----
let formatting () : int =
    let n = 42
    let s = "str"
    let x = 3.14159

    same "n=42 s=str" (sprintf "n=%d s=%s" n s)
    + same
        "   42|42   |00042|+42| 42|  +42|+42  |-0042"
        (sprintf "%5d|%-5d|%05d|%+d|% d|%+5d|%-+5d|%05d" n n n n n n n -n)
    + same "4294967295|ffffffff|FF|10|-7|7" (sprintf "%u|%x|%X|%o|%d|%i" -1 -1 255 8 -7 7)
    + same
        "-9223372036854775808|255|-1|65535|ffff|ff"
        (sprintf "%d|%d|%d|%d|%x|%x" System.Int64.MinValue 255uy -1y 65535us -1s 255uy)
    + same "true|x|str|   ab|ab   | true|    x" (sprintf "%b|%c|%s|%5s|%-5s|%5b|%5c" true 'x' s "ab" "ab" true 'x')
    + same "50%|x%y|é|😀" (sprintf "%d%%|%s|%c|%s" 50 "x%y" 'é' "😀")
    + same
        "3.141590|2.67|0.12|1.00|0|2|2.000000"
        (sprintf "%f|%.2f|%.2f|%.2f|%.0f|%.0f|%F" x 2.675 0.125 1.005 0.5 1.5 2.0)
    + same "0003.142|+2.50|2.50    |-000003.14" (sprintf "%08.3f|%+.2f|%-8.2f|%010.2f" x 2.5 2.5 -x)
    + same
        "1.500000e+020|1.500000E-020|1.23e+004|1.234e+003"
        (sprintf "%e|%E|%.2e|%10.3e" 1.5e20 1.5e-20 12345.678 1234.5)
    + same
        "3|1e+20|0.0001|1e-05|3.14159|123456|1.23457e+06"
        (sprintf "%g|%g|%g|%g|%g|%g|%g" 3.0 1e20 0.0001 0.00001 x 123456.0 1234567.0)
    + same "1E-20|3.14|2.5|0|-1.5" (sprintf "%G|%.3g|%.0g|%g|%g" 1e-20 x 2.5 0.0 -1.5)
    + same "0.100000|0.1000000015|0.1|1.000000e-001" (sprintf "%f|%.10f|%g|%e" 0.1f 0.1f 0.1f 0.1f)
    + same "NaN|Infinity|-Infinity" (sprintf "%f|%g|%e" nan infinity -infinity)
    + same "True|1|s|c|1.5|1E+20" (sprintf "%O|%O|%O|%O|%O|%O" true 1.0 "s" 'c' 1.5f 1e20)

let conversions () : int =
    let n = 5
    let s = "st"
    let f = 2.5
    let b = true
    let c = 'q'

    same "5|st|2.5|True|q|5|  2.5" $"{n}|{s}|{f}|{b}|{c}|%d{n}|%5.1f{f}"
    + same "sum: 7, twice st: stst" $"sum: {n + 2}, twice {s}: {s + s}"
    + same "1|1E+20|1E-07|-0|NaN" $"{1.0}|{1e20}|{1e-7}|{-0.0}|{nan}"
    + same
        "True|c|5|-5|x"
        (string true
         + "|"
         + string 'c'
         + "|"
         + string 5uy
         + "|"
         + string -5L
         + "|"
         + string "x")
    + same
        "1|10000000000000000|1E+17|0.0001|1E-05"
        (string 1.0
         + "|"
         + string 1e16
         + "|"
         + string 1e17
         + "|"
         + string 0.0001
         + "|"
         + string 0.00001)
    + same
        "1.5|16777216|1E+09|0.1|3E-05"
        (string 1.5f
         + "|"
         + string 16777216f
         + "|"
         + string 1e9f
         + "|"
         + string 0.1f
         + "|"
         + string 3.0e-5f)
    + same "1.7976931348623157E+308|5E-324" (string System.Double.MaxValue + "|" + string System.Double.Epsilon)

// ---- exceptions that carry a message ----
exception Refused of code: int * reason: string

let positive (n: int) : int =
    if n < 0 then
        failwith ("negative: " + string n)
    else
        n

let guarded (n: int) : int =
    if n > 100 then
        invalidArg "n" "too big"
    elif n = 100 then
        invalidOp "exactly 100"
    elif n = 99 then
        failwithf "almost: %d of %d" n 100
    elif n = 98 then
        raise (System.NotSupportedException("no " + string n))
    elif n = 97 then
        raise (Refused(n, "prime " + string n))
    else
        n

let describe (n: int) : string =
    try
        string (guarded (positive n))
    with
    | Failure msg -> "failure: " + msg
    | :? System.ArgumentException as e -> "argument: " + e.Message
    | :? System.InvalidOperationException as e -> "invalid: " + e.Message
    | Refused(code, reason) -> $"refused {code}: {reason}"
    | e -> "other: " + e.Message

let messages () : int =
    let caught =
        try
            raise (System.Exception "plain")
        with e ->
            e.Message

    let rethrown =
        try
            try
                positive -5
            with Failure msg when msg.Length > 100 ->
                0
        with e ->
            e.Message.Length

    same "7" (describe 7)
    + same "failure: negative: -1" (describe -1)
    + same "argument: too big (Parameter 'n')" (describe 101)
    + same "invalid: exactly 100" (describe 100)
    + same "failure: almost: 99 of 100" (describe 99)
    + same "other: no 98" (describe 98)
    + same "refused 97: prime 97" (describe 97)
    + same "plain" caught
    + check (rethrown = 12)

type ShowBox<'T> = { Item: 'T }

type ShowBranch =
    | Tip of uint16 voption
    | Branch of ShowBranch * struct (int * string) * ShowBranch

let showShapes () : int =
    let f = fun (x: int) -> x + 1
    let vo1: int voption = ValueSome 42
    let vo2: int voption = ValueNone
    let st = struct (1, "a")
    let nested = Branch(Tip(ValueSome 16us), struct (7, "ok"), Tip ValueNone)
    let boxV: ShowBox<int voption> = { Item = ValueSome 9 }

    let anon =
        {|
            S = struct (16us, 'a')
            V = ValueSome 'z'
        |}

    let m = Map.ofList [ (ValueSome 1, struct (2, "b")) ]

    same "ValueSome 42" (sprintf "%A" vo1)
    + same "ValueNone" (sprintf "%A" vo2)
    + same "ValueSome (1, 2)" (sprintf "%A" (ValueSome(1, 2)))
    + same "ValueSome struct (1, 2)" (sprintf "%A" (ValueSome(struct (1, 2))))
    + same "Some (ValueSome 5)" (sprintf "%A" (Some(ValueSome 5)))
    + same "ValueSome ValueNone" (sprintf "%A" (ValueSome(ValueNone: int voption)))
    + same "Some struct (1, 2)" (sprintf "%A" (Some(struct (1, 2))))
    + same "struct (1, \"a\")" (sprintf "%A" st)
    + same "[struct (1, 2); struct (3, 4)]" (sprintf "%A" [ struct (1, 2); struct (3, 4) ])
    + same "(1, struct (2, 3))" (sprintf "%A" (1, struct (2, 3)))
    + same "struct (1, (2, 3))" (sprintf "%A" (struct (1, (2, 3))))
    + same "16us" (sprintf "%A" 16us)
    + same "(16us, 'a')" (sprintf "%A" (16us, 'a'))
    + same "{ Item = ValueSome 9 }" (sprintf "%A" boxV)
    + same "Branch (Tip (ValueSome 16us), struct (7, \"ok\"), Tip ValueNone)" (sprintf "%A" nested)
    + same "{ S = struct (16us, 'a')\n  V = ValueSome 'z' }" (sprintf "%A" anon)
    + same "map [(ValueSome 1, struct (2, \"b\"))]" (sprintf "%A" m)
    + same "42" (string vo1)
    + same "ValueNone" (string vo2)
    + same "(1, a)" (string st)
    + same "[(1, 2)]" (string [ struct (1, 2) ])
    + same "(42, Some(7))" (string (struct (vo1, Some 7)))
    + same "7|(1, 2)" $"{ValueSome 7}|{struct (1, 2)}"
    + check ((sprintf "%A" f).StartsWith("<fun"))

let run () : int =
    let before = liveCells ()

    let failed =
        basics ()
        + ordering ()
        + inData ()
        + formatting ()
        + conversions ()
        + showShapes ()
        + messages ()

    printfn "strings: %d failed, %s, %5.2f|%-4d|" failed ("héllo " + "😀") 3.14159 42
    eprintfn "strings: this line goes to standard error (%s)" "ok"

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
