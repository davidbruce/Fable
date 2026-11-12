module Text

// What .NET does with text, done the same here: the methods of `System.String` and the
// `String` module, null strings, `%A`, .NET formats in interpolated strings, a printf that is
// used as a function, the messages and classes of exceptions, and what a division by zero or
// a match without a case raises. Every expected text is what .NET gives.
// `run` returns the number of failed checks.

#nowarn "25" // (the incomplete matches below are the point)

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

/// what `f` raises: the class it is told by, and its message
let raised (f: unit -> string) : string =
    try
        f ()
    with
    | :? System.ArgumentNullException as e -> "ArgumentNull: " + e.Message
    | :? System.ArgumentOutOfRangeException as e -> "ArgumentOutOfRange: " + e.Message
    | :? System.ArgumentException as e -> "Argument: " + e.Message
    | :? System.NullReferenceException as e -> "NullReference: " + e.Message
    | :? System.IndexOutOfRangeException as e -> "IndexOutOfRange: " + e.Message
    | :? System.DivideByZeroException as e -> "DivideByZero: " + e.Message
    | :? System.OverflowException as e -> "Overflow: " + e.Message
    | :? MatchFailureException as e -> "MatchFailure: " + e.Message
    | e -> "other: " + e.Message

// ---- System.String ----
let methods () : int =
    let s = "Hello, World"
    let padded = "  " + s + "\t\n"

    same "World" (s.Substring 7)
    + same "Hello" (s.Substring(0, 5))
    + same "" (s.Substring 12)
    + check (
        s.IndexOf 'o' = 4
        && s.IndexOf('o', 5) = 8
        && s.IndexOf "World" = 7
        && s.IndexOf "world" = -1
    )
    + check (
        s.IndexOf("o", 5) = 8
        && s.IndexOf "" = 0
        && s.LastIndexOf 'o' = 8
        && s.LastIndexOf "l" = 10
    )
    + check (
        s.Contains "lo, W"
        && s.Contains 'W'
        && not (s.Contains "xyz")
        && s.StartsWith "Hell"
        && s.EndsWith "ld"
    )
    + check (
        s.StartsWith 'H'
        && s.EndsWith 'd'
        && not (s.StartsWith "World")
        && s.StartsWith ""
        && s.EndsWith ""
    )
    + same "HELLO, WORLD|hello, world" (s.ToUpper() + "|" + s.ToLower())
    + same
        "Ǆ STRAßE ΐ İI|ǆ strasse İi σ"
        ("ǅ straße ΐ İi".ToUpperInvariant() + "|" + "ǅ STRASSE İI Σ".ToLowerInvariant())
    + same
        "[Hello, World][Hello, World\t\n][  Hello, World]"
        ("[" + padded.Trim() + "][" + padded.TrimStart() + "][" + padded.TrimEnd() + "]")
    + same "a|axx|xxa" ("xxaxx".Trim 'x' + "|" + "xxaxx".TrimStart 'x' + "|" + "xxaxx".TrimEnd 'x')
    + same
        "Hell0, W0rld|Help, World|Heo, Word"
        (s.Replace('o', '0') + "|" + s.Replace("lo", "p") + "|" + s.Replace("l", ""))
    + same "Hello, big World|Hello|Hello World" (s.Insert(7, "big ") + "|" + s.Remove 5 + "|" + s.Remove(5, 1))
    + same
        "  abc|abc..|abc|xxx"
        ("abc".PadLeft 5
         + "|"
         + "abc".PadRight(5, '.')
         + "|"
         + "abc".PadLeft 2
         + "|"
         + System.String('x', 3))
    + check (
        s.Equals "Hello, World"
        && not (s.Equals "hello, world")
        && System.String.Equals(s, s + "")
    )
    + check (
        System.String.CompareOrdinal("b", "A") = 33
        && System.String.Concat("a", "b", "c") = "abc"
    )
    + check (
        System.String.IsNullOrEmpty ""
        && not (System.String.IsNullOrEmpty s)
        && System.String.IsNullOrWhiteSpace " \t"
    )

let methodErrors () : int =
    let s = "abc"

    same
        "ArgumentOutOfRange: startIndex cannot be larger than length of string. (Parameter 'startIndex')"
        (raised (fun () -> s.Substring 5))
    + same
        "ArgumentOutOfRange: Index and length must refer to a location within the string. (Parameter 'length')"
        (raised (fun () -> s.Substring(1, 5)))
    + same
        "ArgumentOutOfRange: startIndex ('-1') must be a non-negative value. (Parameter 'startIndex')\nActual value was -1."
        (raised (fun () -> s.Substring -1))
    + same
        "ArgumentOutOfRange: length ('-1') must be a non-negative value. (Parameter 'length')\nActual value was -1."
        (raised (fun () -> s.Substring(2, -1)))
    + same "IndexOutOfRange: Index was outside the bounds of the array." (raised (fun () -> string s.[5]))
    + same "IndexOutOfRange: Index was outside the bounds of the array." (raised (fun () -> string s.[-1]))
    + same
        "Argument: The value cannot be an empty string. (Parameter 'oldValue')"
        (raised (fun () -> s.Replace("", "x")))
    + same
        "ArgumentOutOfRange: startIndex ('5') must be less than or equal to '3'. (Parameter 'startIndex')\nActual value was 5."
        (raised (fun () -> s.Insert(5, "x")))
    + same
        "ArgumentOutOfRange: startIndex cannot be larger than length of string. (Parameter 'startIndex')"
        (raised (fun () -> s.Remove 5))
    + same
        "ArgumentOutOfRange: count ('5') must be less than or equal to '2'. (Parameter 'count')\nActual value was 5."
        (raised (fun () -> s.Remove(1, 5)))
    + same
        "ArgumentOutOfRange: totalWidth ('-1') must be a non-negative value. (Parameter 'totalWidth')\nActual value was -1."
        (raised (fun () -> s.PadLeft -1))
    + same
        "ArgumentOutOfRange: Index was out of range. Must be non-negative and less than or equal to the size of the collection. (Parameter 'startIndex')"
        (raised (fun () -> string (s.IndexOf("c", 4))))
    + same
        "Argument: The input must be non-negative.\ncount = -1 (Parameter 'count')"
        (raised (fun () -> String.replicate -1 s))

// ---- the String module ----
let stringModule () : int =
    let s = "abcb"
    let seen = ref ""
    String.iter (fun c -> seen.Value <- seen.Value + string c + ".") s
    let places = ref 0

    String.iteri
        (fun i c ->
            if c = 'b' then
                places.Value <- places.Value * 10 + i
        )
        s

    check (String.length s = 4)
    + same "a, b, c" (String.concat ", " [ "a"; "b"; "c" ])
    + same "ababab|" (String.replicate 3 "ab" + "|" + String.replicate 0 "ab")
    + same "0-1-2-" (String.init 3 (fun i -> string i + "-"))
    + same
        "ABCB|aXcb|ac|aabbccbb"
        (String.map System.Char.ToUpperInvariant s
         + "|"
         + String.mapi
             (fun i c ->
                 if i = 1 then
                     'X'
                 else
                     c
             )
             s
         + "|"
         + String.filter (fun c -> c <> 'b') s
         + "|"
         + String.collect (fun c -> string c + string c) s)
    + check (String.forall (fun c -> c < 'd') s && not (String.forall (fun c -> c < 'c') s))
    + check (String.exists (fun c -> c = 'c') s && not (String.exists (fun c -> c = 'z') s))
    + same "a.b.c.b." seen.Value
    + check (places.Value = 13)
    // (a function that raises in the middle gives up what was built)
    + same
        "other: stop at c"
        (raised (fun () ->
            String.map
                (fun c ->
                    if c = 'c' then
                        failwith "stop at c"
                    else
                        c
                )
                s
        ))
    + same
        "other: stop at c"
        (raised (fun () ->
            String.collect
                (fun c ->
                    if c = 'c' then
                        failwith "stop at c"
                    else
                        string c + "!"
                )
                s
        ))

// ---- null ----
let orEmpty (s: string) : string =
    match s with
    | null -> "(null)"
    | "" -> "(empty)"
    | _ -> s

let nulls () : int =
    let nothing: string = null
    let text = "a"

    check (
        isNull nothing
        && not (isNull text)
        && nothing = null
        && nothing <> ""
        && text <> null
    )
    + same "(null)|(empty)|a" (orEmpty nothing + "|" + orEmpty "" + "|" + orEmpty text)
    + same "[]|a|a" ("[" + nothing + "]" + "|" + (nothing + text) + "|" + (text + nothing))
    + check (nothing + nothing = "" && not (isNull (nothing + nothing)))
    + check (
        String.length nothing = 0
        && compare nothing "" = -1
        && compare "" nothing = 1
        && compare nothing nothing = 0
    )
    + check (
        nothing < text
        && System.String.IsNullOrEmpty nothing
        && System.String.IsNullOrWhiteSpace nothing
    )
    + same
        "|     |<null>||"
        (sprintf "%s|%5s|%O" nothing nothing nothing
         + "|"
         + string nothing
         + "|"
         + $"{nothing}")
    + same "<null>" (sprintf "%A" nothing)
    + same
        "NullReference: Object reference not set to an instance of an object."
        (raised (fun () -> string nothing.Length))
    + same
        "NullReference: Object reference not set to an instance of an object."
        (raised (fun () -> string nothing.[0]))
    + same
        "NullReference: Object reference not set to an instance of an object."
        (raised (fun () -> nothing.Substring 1))
    + same "NullReference: Object reference not set to an instance of an object." (raised (fun () -> nothing.ToUpper()))
    + same "ArgumentNull: Value cannot be null. (Parameter 'value')" (raised (fun () -> string (text.IndexOf nothing)))
    + same "ArgumentNull: Value cannot be null. (Parameter 'value')" (raised (fun () -> string (text.Contains nothing)))
    + same "ArgumentNull: Value cannot be null. (Parameter 'oldValue')" (raised (fun () -> text.Replace(nothing, "x")))
    + same "" (text.Replace("a", nothing))
    + check (
        String.forall (fun c -> c = 'a') nothing
        && String.map id nothing = ""
        && String.concat nothing [ "a"; "b" ] = "ab"
    )

// ---- %A ----
type Person =
    {
        Name: string
        Age: int
    }

type Team =
    {
        Lead: Person
        Tags: string list
        Size: int option
    }

type Shape =
    | Dot
    | Circle of float
    | Label of string * int
    | Of of Person
    | Wrap of Shape
    | At of (int * int)

type Tree =
    | Leaf
    | Node of Tree * int * Tree

type Ring =
    {
        Count: int
        mutable Next: Ring option
    }

exception Broken of int * string
exception Plain
exception One of string
exception Holding of Person

let rec numbersFrom (lo: int) (hi: int) : int list =
    if lo > hi then
        []
    else
        lo :: numbersFrom (lo + 1) hi

let structured () : int =
    let ann =
        {
            Name = "Ann"
            Age = 3
        }

    let team =
        {
            Lead = ann
            Tags = [ "a"; "b" ]
            Size = Some 1
        }

    let tree = Node(Node(Leaf, 1, Leaf), 2, Node(Leaf, 3, Leaf))

    let bigTree =
        Node(
            Node(Node(Node(Leaf, 1111111111, Leaf), 222222222, Leaf), 333333333, Node(Leaf, 444444444, Leaf)),
            555555555,
            Node(Leaf, 666666666, Node(Leaf, 777777777, Leaf))
        )

    let ring =
        {
            Count = 1
            Next = None
        }

    ring.Next <-
        Some
            {
                Count = 2
                Next = Some ring
            }

    let ringText = sprintf "%A" ring
    ring.Next <- None

    same "1|-1|1uy|1y|1s|1us|1u|1L|1UL" (sprintf "%A|%A|%A|%A|%A|%A|%A|%A|%A" 1 -1 1uy 1y 1s 1us 1u 1L 1UL)
    + same
        "1.0|1.5|-0.0|1e+20|1e-05|123456789.1|1.0f|1.5f|1e+10f"
        (sprintf "%A|%A|%A|%A|%A|%A|%A|%A|%A" 1.0 1.5 -0.0 1e20 1e-5 123456789.123456789 1.0f 1.5f 1e10f)
    + same "nan|infinity|-infinity|1.23456789e+12" (sprintf "%A|%A|%A|%A" nan infinity -infinity 1234567890123.0)
    + same "'a'|'\\010'|'\\''|'\"'|'\\\\'|'é'" (sprintf "%A|%A|%A|%A|%A|%A" 'a' '\n' '\'' '"' '\\' 'é')
    + same "\"plain\"|\"q\"uote\"|\"\"" (sprintf "%A|%A|%A" "plain" "q\"uote" "")
    + same "true|false|()|(1, \"a\")" (sprintf "%A|%A|%A|%A" true false () (1, "a"))
    + same
        "Some 1|None|Some (Some 1)|Some None|Some \"x\""
        (sprintf "%A|%A|%A|%A|%A" (Some 1) (None: int option) (Some(Some 1)) (Some(None: int option)) (Some "x"))
    + same
        "Some (1, 2)|Some -1|Some [1]|Some Dot"
        (sprintf "%A|%A|%A|%A" (Some(1, 2)) (Some -1) (Some [ 1 ]) (Some Dot))
    + same
        "Dot|Circle 1.5|Label (\"x\", 2)|Wrap (Circle 1.0)|Wrap Dot|At (1, 2)"
        (sprintf "%A|%A|%A|%A|%A|%A" Dot (Circle 1.5) (Label("x", 2)) (Wrap(Circle 1.0)) (Wrap Dot) (At(1, 2)))
    + same "Wrap (Wrap (Label (\"s\", 1)))" (sprintf "%A" (Wrap(Wrap(Label("s", 1)))))
    + same "{ Name = \"Ann\"\n  Age = 3 }" (sprintf "%A" ann)
    + same "Of { Name = \"Ann\"\n     Age = 3 }" (sprintf "%A" (Of ann))
    + same
        "{ Lead = { Name = \"Ann\"\n           Age = 3 }\n  Tags = [\"a\"; \"b\"]\n  Size = Some 1 }"
        (sprintf "%A" team)
    + same
        "[1; 2; 3]|[]|[\"a\"]|[[1]; [2; 3]]"
        (sprintf "%A|%A|%A|%A" [ 1; 2; 3 ] ([]: int list) [ "a" ] [ [ 1 ]; [ 2; 3 ] ])
    + same
        "[1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22;\n 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40]"
        (sprintf "%A" (numbersFrom 1 40))
    + check (
        (sprintf "%A" (numbersFrom 1 120)).EndsWith
            " 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99; 100; ...]"
    )
    + same
        "[{ Name = \"Ann\"\n   Age = 3 }; { Name = \"Bob\"\n                Age = 4 }]"
        (sprintf
            "%A"
            [
                ann
                {
                    Name = "Bob"
                    Age = 4
                }
            ])
    + same "Node (Node (Leaf, 1, Leaf), 2, Node (Leaf, 3, Leaf))" (sprintf "%A" tree)
    + same
        "Node\n  (Node\n     (Node (Node (Leaf, 1111111111, Leaf), 222222222, Leaf), 333333333,\n      Node (Leaf, 444444444, Leaf)), 555555555,\n   Node (Leaf, 666666666, Node (Leaf, 777777777, Leaf)))"
        (sprintf "%A" bigTree)
    + same "(1, \"two\", 3.0, [4], Some 5, (6, 7))" (sprintf "%A" (1, "two", 3.0, [ 4 ], Some 5, (6, 7)))
    + same ("Label\n  (\"" + String.replicate 80 "z" + "\",\n   1)") (sprintf "%A" (Label(String.replicate 80 "z", 1)))
    + same ("Some\n  \"" + String.replicate 80 "z" + "\"") (sprintf "%A" (Some(String.replicate 80 "z")))
    + same "{ contents = 5 }" (sprintf "%A" (ref 5))
    + same "{ Count = 1\n  Next = Some { Count = 2\n                Next = Some ... } }" ringText
    + same "x=[1; 2] y={ Name = \"Ann\"\n  Age = 3 }!" (sprintf "x=%A y=%A!" [ 1; 2 ] ann)
    + same
        "[(1, \"one\"); (2, \"two\")]|[Some (1, \"a\"); None]"
        (sprintf "%A|%A" [ (1, "one"); (2, "two") ] [ Some(1, "a"); None ])
    // (`string` and `{x}` of a record or a union are its `%A`)
    + same "{ Name = \"Ann\"\n  Age = 3 }|Circle 1.5|Dot" (string ann + "|" + string (Circle 1.5) + "|" + $"{Dot}")

// ---- the messages of exceptions, and their classes ----
let messages () : int =
    let messageOf (e: exn) : string = e.Message

    let caughtAs (e: exn) : string =
        try
            raise e
        with
        | :? System.ArgumentNullException -> "ArgumentNull"
        | :? System.ArgumentException -> "Argument"
        | :? System.ArithmeticException -> "Arithmetic"
        | :? System.SystemException -> "System"
        | Failure _ -> "Failure"
        | _ -> "other"

    same
        "Broken (1, \"a\")|Plain|One \"x\""
        (messageOf (Broken(1, "a")) + "|" + messageOf Plain + "|" + messageOf (One "x"))
    + same
        "Holding { Name = \"n\"\n          Age = 1 }"
        (messageOf (
            Holding
                {
                    Name = "n"
                    Age = 1
                }
        ))
    + same "Broken (1, \"a\")|One \"x\"" (sprintf "%A|%A" (Broken(1, "a")) (One "x"))
    + same
        "System.Exception: boom|System.ArgumentException: bad"
        (sprintf "%A|%A" (exn "boom") (System.ArgumentException "bad"))
    + same
        "ArgumentNull|Argument|Argument|Arithmetic|Arithmetic|System|Failure|other"
        (caughtAs (System.ArgumentNullException "p")
         + "|"
         + caughtAs (System.ArgumentOutOfRangeException "p")
         + "|"
         + caughtAs (System.ArgumentException "m")
         + "|"
         + caughtAs (System.DivideByZeroException "m")
         + "|"
         + caughtAs (System.OverflowException "m")
         + "|"
         + caughtAs (System.InvalidOperationException "m")
         + "|"
         + caughtAs (exn "m")
         + "|"
         + caughtAs Plain)
    + same
        "Value cannot be null. (Parameter 'p')|Specified argument was out of the range of valid values. (Parameter 'p')"
        (messageOf (System.ArgumentNullException "p")
         + "|"
         + messageOf (System.ArgumentOutOfRangeException "p"))

// ---- what arithmetic and matching raise ----
let colour (n: int) : string =
    match n with
    | 0 -> "red"
    | 1 -> "green"

let faults () : int =
    let zero = 0
    let minusOne = -1
    let mutable loops = 0
    let mutable i = 10

    // (a condition that can raise, and one with `&&` in it)
    while 100 / i > 5 && i < 50 do
        i <- i + 5
        loops <- loops + 1

    check (
        7 / 2 = 3
        && -7 / 2 = -3
        && 7 % -2 = 1
        && -7 % 2 = -1
        && 7 / minusOne = -7
        && 7 % minusOne = 0
    )
    + check (loops = 2 && -128y / sbyte minusOne = -128y && 5.0 / float zero = infinity)
    + same "DivideByZero: Attempted to divide by zero." (raised (fun () -> string (5 / zero)))
    + same "DivideByZero: Attempted to divide by zero." (raised (fun () -> string (5 % zero)))
    + same "DivideByZero: Attempted to divide by zero." (raised (fun () -> string (5u / uint32 zero)))
    + same
        "Overflow: Arithmetic operation resulted in an overflow."
        (raised (fun () -> string (System.Int32.MinValue / minusOne)))
    + same
        "Overflow: Arithmetic operation resulted in an overflow."
        (raised (fun () -> string (System.Int32.MinValue % minusOne)))
    + same
        "Overflow: Arithmetic operation resulted in an overflow."
        (raised (fun () -> string (System.Int64.MinValue / int64 minusOne)))
    + same "red|green" (colour 0 + "|" + colour 1)
    + same "MatchFailure: The match cases were incomplete" (raised (fun () -> colour 2))
    + same
        "MatchFailure: The match cases were incomplete"
        (raised (fun () ->
            let (Some v) =
                (if zero = 0 then
                     None
                 else
                     Some 1)

            string v
        ))

// ---- .NET formats in interpolated strings, and printf as a function ----
let formats () : int =
    let x = 1234.5678
    let n = 42
    let neg = -1234567
    let s = "str"
    let twice (f: int -> string) : string = f 1 + f 2
    let show = sprintf "<%d>"
    let pair = sprintf "%s=%d" "k"
    let padded = sprintf "%5.1f|%s"
    let total = ref 0
    let add = fun (k: int) -> total.Value <- total.Value + k

    let rec each (f: int -> unit) (xs: int list) : unit =
        match xs with
        | [] -> ()
        | h :: t ->
            f h
            each f t

    each add [ 1; 2; 3 ]

    // (only formats that every culture writes the same way: here the culture is the invariant
    // one, on .NET it is the machine's)
    same
        "1,234.57|1,235|1234.6|1.23E+003|1.234568e+003|1234.5678|1.23E+03"
        $"{x:N2}|{x:N0}|{x:F1}|{x:E2}|{x:e}|{x:G}|{x:G3}"
    + same "42|00042|2A|002a|42.00|4.20E+001|101010" $"{n:D}|{n:D5}|{n:X}|{n:x4}|{n:N2}|{n:E2}|{n:B}"
    + same
        "-1234567|-0001234567|FFED2979|-1,234,567|-1.235E+006|-1.235E+06"
        $"{neg:D}|{neg:D10}|{neg:X}|{neg:N0}|{neg:E3}|{neg:G4}"
    + same "0.12|2.67|2|0|100,000,000,000,000,000,000|NaN" $"{0.125:F2}|{2.675:F2}|{2.5:F0}|{0.5:N0}|{1e20:N0}|{nan:N2}"
    + same "   42|42   |   str|str   |     1,234.6|1235        " $"{n, 5}|{n, -5}|{s, 6}|{s, -6}|{x, 12:N1}|{x, -12:F0}"
    + same "<1><2>|k=7|  2.5|z" (twice show + "|" + pair 7 + "|" + padded 2.5 "z")
    + same "<1><2>" (twice (sprintf "<%d>"))
    + check (total.Value = 6)

/// (a printf that is passed on as a function)
let each3 (f: int -> unit) (n: int) : unit = f n

let run () : int =
    let before = liveCells ()

    let failed =
        methods ()
        + methodErrors ()
        + stringModule ()
        + nulls ()
        + structured ()
        + messages ()
        + faults ()
        + formats ()

    each3 (printfn "text: %d") failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
