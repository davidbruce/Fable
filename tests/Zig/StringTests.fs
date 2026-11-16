module Fable.Tests.Zig.StringTests

open System
open System.Globalization

open Fable.Tests.Util
open Fable.Tests.Util
open Fable.Tests.Util.Testing

#nowarn "44" // This construct is deprecated. Uri.EscapeUriString can corrupt the Uri string in some cases. (code 44)

module M =
    let f x = nameof x

[<Literal>]
let formatCoordinateBody = "(%f,%f)"

[<Literal>]
let formatPrefix = "Person at coordinates"

[<Literal>]
let fullFormat = formatPrefix + formatCoordinateBody

let containsInOrder (substrings: string list) (str: string) =
    let mutable lastIndex = -1
    substrings |> List.forall (fun s ->
      let i = str.IndexOf(s)
      let success = i >= 0 && i > lastIndex
      lastIndex <- i
      success)


type MyUnion = Bar of int * int | Foo1 of float | Foo3 | Foo4 of MyUnion

[<Fact>]
let ``test F# nameof works`` () =
    M.f 12 |> equal "x"
    nameof M |> equal "M"
    nameof M.f |> equal "f"

[<Fact>]
let ``test sprintf works`` () =
    // Immediately applied
    sprintf "%.2f %g" 0.5468989 5.
    |> equal "0.55 5"
    // Curried
    let printer = sprintf "Hi %s, good %s!"
    let printer = printer "Alfonso"
    printer "morning" |> equal "Hi Alfonso, good morning!"
    printer "evening" |> equal "Hi Alfonso, good evening!"

[<Fact>]
let ``test sprintf works II`` () =
      let printer2 = sprintf "Hi %s, good %s%s" "Maxime"
      let printer2 = printer2 "afternoon"
      printer2 "?" |> equal "Hi Maxime, good afternoon?"

[<Fact>]
let ``test sprintf with different decimal digits works`` () =
      sprintf "Percent: %.0f%%" 5.0 |> equal "Percent: 5%"
      sprintf "Percent: %.2f%%" 5. |> equal "Percent: 5.00%"
      sprintf "Percent: %.1f%%" 5.24 |> equal "Percent: 5.2%"
      sprintf "Percent: %.2f%%" 5.268 |> equal "Percent: 5.27%"
      sprintf "Percent: %f%%" 5.67 |> equal "Percent: 5.670000%"

[<Fact>]
let ``test sprintf displays sign correctly`` () =
      sprintf "%i" 1 |> equal "1"
      sprintf "%d" 1 |> equal "1"
      sprintf "%d" 1L |> equal "1"
      sprintf "%.2f" 1. |> equal "1.00"
      sprintf "%i" -1 |> equal "-1"
      sprintf "%d" -1 |> equal "-1"
      sprintf "%d" -1L |> equal "-1"
      sprintf "%.2f" -1. |> equal "-1.00"

[<Fact>]
let ``test format string can use and compose string literals`` () =
    let renderedCoordinates = sprintf formatCoordinateBody 0.25 0.75
    let renderedText = sprintf fullFormat 0.25 0.75

    equal "(0.250000,0.750000)" renderedCoordinates
    equal "Person at coordinates(0.250000,0.750000)" renderedText

[<Fact>]
let ``test Print.sprintf works`` () =
    let res = Printf.sprintf "%s" "abc"
    equal "res: abc" ("res: " + res)

[<Fact>]
let ``test sprintf without arguments works`` () =
    sprintf "hello" |> equal "hello"

[<Fact>]
let ``test input of print format can be retrieved`` () =
    let pathScan (pf:PrintfFormat<_,_,_,_,'t>) =
        let formatStr = pf.Value
        formatStr

    equal "/hello/%s" (pathScan "/hello/%s")

[<Fact>]
let ``test interpolate works`` () =
    let name = "Phillip"
    let age = 29
    $"Name: %s{name}, Age: %i{age}"
    |> equal "Name: Phillip, Age: 29"

#if FABLE_COMPILER
[<Fact>]
let ``test string interpolation works with inline expressions`` () =
    $"I think {3.0 + 0.14} is close to %.8f{3.14159265}!"
    |> equal "I think 3.14 is close to 3.14159265!"
#endif

[<Fact>]
let ``test string interpolation works with .NET format specifiers`` () = // See Fable.Python #36
    let i = 123
    $"{i:X4}" |> equal "007B"
    $"{i:x4}" |> equal "007b"
    $"{i:D5}" |> equal "00123"
    $"{5:B}" |> equal "101"
    $"\\u{i:X4}" |> equal "\\u007B"
    $"{3.14159:F2}" |> equal "3.14"

[<Fact>]
let ``test string interpolation works with alignment`` () =
    let i = 123
    $"[{i,6}]" |> equal "[   123]"
    $"[{i,-6}]" |> equal "[123   ]"
    $"[{i,6:X4}]" |> equal "[  007B]"
    $"[{i,-6:X4}]" |> equal "[007B  ]"

[<Fact>]
let ``test string interpolation works with anonymous records`` () =
    let person =
        {|
            Name = "John"
            Surname = "Doe"
            Age = 32
            Country = "The United Kingdom"
        |}
    $"Hi! My name is %s{person.Name} %s{person.Surname.ToUpper()}. I'm %i{person.Age} years old and I'm from %s{person.Country}!"
    |> equal "Hi! My name is John DOE. I'm 32 years old and I'm from The United Kingdom!"

[<Fact>]
let ``test Extended string interpolation syntax`` () =
    let classAttr = "item-panel"
    let cssNew = $$""".{{classAttr}}:hover {background-color: #eee;}"""
    cssNew |> equal ".item-panel:hover {background-color: #eee;}"

[<Fact>]
let ``test sprintf \"%A\" formats booleans as lowercase`` () =
    // Test that %A formats booleans as lowercase true/false (F# semantics)
    let result = sprintf "%A" true
    equal "true" result

    let result2 = sprintf "%A" false
    equal "false" result2

    // Also test in composed context
    let optResult = sprintf "Some(%A)" true
    equal "Some(true)" optResult

// See https://github.com/fable-compiler/Fable/issues/4732
[<Fact>]
let ``test sprintf \"%A\" quotes strings`` () =
    sprintf "%A" "test" |> equal "\"test\""
    sprintf "%A" "" |> equal "\"\""
    // %O and %s don't quote a bare string
    sprintf "%O" "test" |> equal "test"
    sprintf "%s" "test" |> equal "test"

// See https://github.com/fable-compiler/Fable/issues/4732
[<Fact>]
let ``test sprintf \"%A\" wraps strings without escaping`` () =
    // F#'s %A only wraps a string in quotes; it does NOT escape embedded
    // double-quotes, backslashes, or control characters (verified on .NET).
    sprintf "%A" "a\"b" |> equal "\"a\"b\""
    sprintf "%A" "a\\b" |> equal "\"a\\b\""
    sprintf "%A" "a\nb" |> equal "\"a\nb\""
    sprintf "%A" "a\tb" |> equal "\"a\tb\""
    // Same behavior when the string is nested inside a container
    sprintf "%A" [ "a\"b" ] |> equal "[\"a\"b\"]"

[<Fact>]
let ``test sprintf \"%A\" with lists works`` () =
    let xs = ["Hi"; "Hello"; "Hola"]
    sprintf "%A" xs |> equal "[\"Hi\"; \"Hello\"; \"Hola\"]"

[<Fact>]
let ``test sprintf \"%A\" with nested lists works`` () =
    let xs = [["Hi"]; ["Hello"]; ["Hola"]]
    sprintf "%A" xs |> equal "[[\"Hi\"]; [\"Hello\"]; [\"Hola\"]]"

[<Fact>]
let ``test sprintf \"%A\" with sequences works`` () =
    let xs = seq { "Hi"; "Hello"; "Hola" }
    sprintf "%A" xs |> containsInOrder ["Hi"; "Hello"; "Hola"] |> equal true

[<Fact>]
let ``test Storing result of Seq.tail and printing the result several times works. Related to #1996`` () =
    let tweets = seq { "Hi"; "Hello"; "Hola" }
    let tweetsTailR: seq<string> = tweets |> Seq.tail

    let a = sprintf "%A" (tweetsTailR)
    let b = sprintf "%A" (tweetsTailR)

    containsInOrder ["Hello"; "Hola"] a |> equal true
    containsInOrder ["Hello"; "Hola"] b |> equal true

[<Fact>]
let ``test sprintf \"%X\" works`` () =
    //These should all be the Native JS Versions (except int64 / uint64)
    //See #1530 for more information.

    sprintf "255: %X" 255 |> equal "255: FF"
    sprintf "255: %x" 255 |> equal "255: ff"
    sprintf "-255: %X" -255 |> equal "-255: FFFFFF01"
    sprintf "4095L: %X" 4095L |> equal "4095L: FFF"
    sprintf "-4095L: %X" -4095L |> equal "-4095L: FFFFFFFFFFFFF001"
    sprintf "1 <<< 31: %x" (1 <<< 31) |> equal "1 <<< 31: 80000000"
    sprintf "1u <<< 31: %x" (1u <<< 31) |> equal "1u <<< 31: 80000000"
    sprintf "2147483649L: %x" 2147483649L |> equal "2147483649L: 80000001"
    sprintf "2147483650uL: %x" 2147483650uL |> equal "2147483650uL: 80000002"
    sprintf "1L <<< 63: %x" (1L <<< 63) |> equal "1L <<< 63: 8000000000000000"
    sprintf "1uL <<< 63: %x" (1uL <<< 63) |> equal "1uL <<< 63: 8000000000000000"

[<Fact>]
let ``test sprintf integers with sign and padding works`` () =
    sprintf "%+04i" 1 |> equal "+001"
    sprintf "%+04i" -1 |> equal "-001"
    sprintf "%5d" -5 |> equal "   -5"
    sprintf "%5d" -5L |> equal "   -5"
    sprintf "%- 4i" 5 |> equal " 5  "

// [<Fact>]
// let ``test parameterized padding works`` () =
//     sprintf "[%*s][%*s]" 6 "Hello" 5 "Foo"
//     |> equal "[ Hello][  Foo]"

[<Fact>]
let ``test String.Format combining padding and zeroes pattern works`` () =
    String.Format(CultureInfo.InvariantCulture, "{0:++0.00++}", -5000.5657) |> equal "-++5000.57++"
    String.Format(CultureInfo.InvariantCulture, "{0:000.00}foo", 5) |> equal "005.00foo"
    String.Format(CultureInfo.InvariantCulture, "{0,-8:000.00}foo", 12.456) |> equal "012.46  foo"

[<Fact>]
let ``test String.Format works`` () =
    let arg1, arg2, arg3 = "F#", "Fable", "Babel"
    String.Format(CultureInfo.InvariantCulture, "{2} is to {1} what {1} is to {0}", arg1, arg2, arg3)
    |> equal "Babel is to Fable what Fable is to F#"

[<Fact>]
let ``test String.Format with array works`` () =
    let args = [| "F#" :> obj; "Fable"; "Babel" |]
    String.Format("{2} is to {1} what {1} is to {0}", args=args)
    |> equal "Babel is to Fable what Fable is to F#"

[<Fact>]
let ``test StringBuilder works`` () =
    let sb = System.Text.StringBuilder()
    sb.Append "Hello" |> ignore
    sb.AppendLine () |> ignore
    sb.AppendLine "World!" |> ignore
    let expected = System.Text.StringBuilder()
                      .AppendFormat("Hello{0}World!{0}", Environment.NewLine)
                      .ToString()
    sb.ToString() |> equal expected

[<Fact>]
let ``test StringBuilder.Length works`` () =
    let sb = System.Text.StringBuilder()
    sb.Append("Hello") |> ignore
    // We don't test the AppendLine for Length because depending on the OS
    // the result is different. Unix \n VS Windows \r\n
    // sb.AppendLine() |> ignore
    sb.Length |> equal 5

[<Fact>]
let ``test StringBuilder.ToString works with index and length`` () =
    let sb = System.Text.StringBuilder()
    sb.Append("Hello") |> ignore
    sb.AppendLine() |> ignore
    sb.ToString(2, 2) |> equal "ll"

[<Fact>]
let ``test StringBuilder.Clear works`` () =
    let sb = new System.Text.StringBuilder()
    sb.Append("1111") |> ignore
    sb.Clear() |> ignore
    sb.ToString() |> equal ""

[<Fact>]
let ``test StringBuilder.Append works with various overloads`` () =
    let sb = System.Text.StringBuilder()
                        .Append(System.Text.StringBuilder "aaa")
                        .Append("bcd".ToCharArray())
                        .Append('/')
                        .Append(true)
                        .AppendFormat(CultureInfo.InvariantCulture, "{0}", 5.2)
                        .Append(34)
                        .Append('x', 4)
    let actual = sb.ToString().ToLower()
    actual |> equal "aaabcd/true5.234xxxx"

[<Fact>]
let ``test StringBuilder.Append works with numeric type overloads`` () =
    let sb = System.Text.StringBuilder()
    sb.Append(1y) |> ignore   // int8
    sb.Append(2uy) |> ignore  // byte
    sb.Append(3s) |> ignore   // int16
    sb.Append(4us) |> ignore  // uint16
    sb.Append(5u) |> ignore   // uint32
    sb.Append(6L) |> ignore   // int64
    sb.Append(7UL) |> ignore  // uint64
    sb.Append(8.0f) |> ignore // float32
    sb.ToString() |> equal "12345678"

[<Fact>]
let ``test StringBuilder.AppendFormat works`` () =
    let sb = System.Text.StringBuilder()
    sb.AppendFormat("Hello{0}World{1}", " ", "!") |> ignore
    sb.ToString() |> equal "Hello World!"

[<Fact>]
let ``test StringBuilder.AppendFormat with provider works`` () =
    let sb = System.Text.StringBuilder()
    sb.AppendFormat(CultureInfo.InvariantCulture, "Hello{0}World{1}", " ", "!") |> ignore
    sb.ToString() |> equal "Hello World!"

[<Fact>]
let ``test StringBuilder.Chars works`` () =
    let sb = System.Text.StringBuilder()
                        .Append("abc")
                        .Append("def")
    sb.Chars(0) |> equal 'a'
    sb.Chars(1) |> equal 'b'
    sb.Chars(2) |> equal 'c'
    sb.Chars(3) |> equal 'd'
    sb.Chars(4) |> equal 'e'
    sb.Chars(5) |> equal 'f'

[<Fact>]
let ``test StringBuilder.Chars throws when index is out of bounds`` () =
    let sb = System.Text.StringBuilder()
                        .Append("abc")
    throwsAnyError <| fun () ->
        sb.Chars(-1) |> ignore
    throwsAnyError <| fun () ->
        sb.Chars(3) |> ignore

[<Fact>]
let ``test StringBuilder.Replace works`` () =
    let sb = System.Text.StringBuilder()
                        .Append("abc")
                        .Append("abc")
                        .Replace('a', 'x')
                        .Replace("cx", "yz")
    equal "xbyzbc" (sb.ToString())

[<Fact>]
let ``test StringBuilder index getter works`` () =
    let sb = System.Text.StringBuilder()
                        .Append("abc")
    equal 'b' (sb[1])

[<Fact>]
let ``test StringBuilder index setter works`` () =
    let sb = System.Text.StringBuilder()
                        .Append("abc")
    sb[1] <- 'x'
    equal "axc" (sb.ToString())
    throwsAnyError <| fun () ->
        sb[-1] <- 'y'
    throwsAnyError <| fun () ->
        sb[3] <- 'z'

[<Fact>]
let ``test Conversion char to int works`` () =
    equal 97 (int 'a')
    equal 'a' (char 97)

[<Fact>]
let ``test Conversion string to char works`` () =
    equal 'a' (char "a")
    equal "a" (string 'a')

[<Fact>]
let ``test Conversion string to negative int8 works`` () =
    equal -5y (int8 "-5")
    equal "-5" (string -5y)

[<Fact>]
let ``test Conversion string to negative int16 works`` () =
    equal -5s (int16 "-5")
    equal "-5" (string -5s)

[<Fact>]
let ``test Conversion string to negative int32 works`` () =
    equal -5 (int32 "-5")
    equal "-5" (string -5)

[<Fact>]
let ``test Conversion string to negative int64 works`` () =
    equal -5L (int64 "-5")
    equal "-5" (string -5L)

[<Fact>]
let ``test Conversion string to int8 works`` () =
    equal 5y (int8 "5")
    equal "5" (string 5y)

[<Fact>]
let ``test Conversion string to int16 works`` () =
    equal 5s (int16 "5")
    equal "5" (string 5s)

[<Fact>]
let ``test Conversion string to int32 works`` () =
    equal 5 (int32 "5")
    equal "5" (string 5)

[<Fact>]
let ``test Conversion string to int64 works`` () =
    equal 5L (int64 "5")
    equal "5" (string 5L)

[<Fact>]
let ``test Conversion string to uint8 works`` () =
    equal 5uy (uint8 "5")
    equal "5" (string 5uy)

[<Fact>]
let ``test Conversion string to uint16 works`` () =
    equal 5us (uint16 "5")
    equal "5" (string 5us)

[<Fact>]
let ``test Conversion string to uint32 works`` () =
    equal 5u (uint32 "5")
    equal "5" (string 5u)

[<Fact>]
let ``test Conversion string to uint64 works`` () =
    equal 5uL (uint64 "5")
    equal "5" (string 5uL)

[<Fact>]
let ``test Conversion string to single works`` () =
    equal 5.f (float32 "5.0")
    equal -5.f (float32 "-5.0")
    (string 5.f).StartsWith("5") |> equal true
    equal 5.25f (float32 "5.25")
    (string 5.25f).StartsWith("5.25") |> equal true

[<Fact>]
let ``test Conversion string to double works`` () =
    equal 5. (float "5.0")
    equal -5. (float "-5.0")
    (string 5.).StartsWith("5") |> equal true
    equal 5.25 (float "5.25")
    (string 5.25).StartsWith("5.25") |> equal true


[<Fact>]
let ``test Conversion string to decimal works`` () =
    equal 5.m (decimal "5.0")
    equal -5.m (decimal "-5.0")
    (string 5.m).StartsWith("5") |> equal true
    equal 5.25m (decimal "5.25")
    (string 5.25m).StartsWith("5.25") |> equal true

// System.String - constructors

[<Fact>]
let ``test String.ctor(char[]) works`` () =
    System.String([|'f'; 'a'; 'b'; 'l'; 'e'|])
    |> equal "fable"

[<Fact>]
let ``test String.ctor(char, int) works`` () =
    System.String('f', 5)
    |> equal "fffff"

[<Fact>]
let ``test String.ctor(char[], int, int) works`` () =
    System.String([|'f'; 'a'; 'b'; 'l'; 'e'|], 1, 3)
    |> equal "abl"

// System.String - static methods

[<Fact>]
let ``test System.String.Equals works`` () =
    System.String.Equals("abc", "abc") |> equal true
    System.String.Equals("ABC", "abc") |> equal false
    System.String.Equals("abc", "abd") |> equal false
    "abc".Equals("abc") |> equal true
    "ABC".Equals("abc") |> equal false
    "abc".Equals("abd") |> equal false
    System.String.Equals("ABC", "abc", StringComparison.Ordinal) |> equal false
    System.String.Equals("ABC", "abc", StringComparison.OrdinalIgnoreCase) |> equal true
    "ABC".Equals("abc", StringComparison.Ordinal) |> equal false
    "ABC".Equals("abc", StringComparison.OrdinalIgnoreCase) |> equal true

[<Fact>]
let ``test String.Compare works`` () =
    "ABC".CompareTo("abc") > 0 |> equal true
    System.String.Compare("abc", "abc") |> equal 0
    System.String.Compare("ABC", "abc") |> equal 1
    System.String.Compare("abc", "abd") |> equal -1
    System.String.Compare("bbc", "abd") |> equal 1
    System.String.Compare("ABC", "abc", false) |> equal 1
    System.String.Compare("ABC", "abc", true) |> equal 0
    System.String.Compare("ABC", "abd", true) |> equal -1
    System.String.Compare("BBC", "abd", true) |> equal 1
    System.String.Compare("ABC", "abc", StringComparison.CurrentCulture) > 0 |> equal true
    System.String.Compare("ABC", "abc", StringComparison.Ordinal) < 0 |> equal true
    System.String.Compare("ABC", "abc", StringComparison.OrdinalIgnoreCase) |> equal 0
    System.String.Compare("abc", 0, "bcd", 0, 3) |> equal -1
    System.String.Compare("abc", 1, "bcd", 0, 2) |> equal 0
    System.String.Compare("ABC", 1, "bcd", 0, 2, StringComparison.CurrentCulture) > 0 |> equal true
    System.String.Compare("ABC", 1, "bcd", 0, 2, StringComparison.Ordinal) < 0 |> equal true
    System.String.Compare("ABC", 1, "bcd", 0, 2, StringComparison.OrdinalIgnoreCase) |> equal 0


[<Fact>]
let ``test String.IsNullOrEmpty works`` () =
    let args = [("", true); (null, true); ("test", false); (" \t", false)]
    for arg in args do
          System.String.IsNullOrEmpty(fst arg)
          |> equal (snd arg)

[<Fact>]
let ``test String.IsNullOrWhiteSpace works`` () =
    let args = [("", true); (null, true); ("test", false); (" \t", true)]
    for arg in args do
          System.String.IsNullOrWhiteSpace(fst arg)
          |> equal (snd arg)

[<Fact>]
let ``test String.Contains works`` () =
    "ABC".Contains("B") |> equal true
    "ABC".Contains("Z") |> equal false

[<Fact>]
let ``test String.Contains with empty pattern works`` () =
    // .NET: every string contains ""
    "ABC".Contains("") |> equal true
    "".Contains("") |> equal true

[<Fact>]
let ``test String.Contains with StringComparison works`` () =
    "ABC".Contains("b", StringComparison.Ordinal) |> equal false
    "ABC".Contains("b", StringComparison.OrdinalIgnoreCase) |> equal true
    "ABC".Contains("b", StringComparison.InvariantCultureIgnoreCase) |> equal true

[<Fact>]
let ``test String.Split works`` () =
    "a b c  d".Split(' ')
    |> (=) [|"a";"b";"c";"";"d"|] |> equal true
    "a b c  d ".Split()
    |> (=) [|"a";"b";"c";"";"d";""|] |> equal true
    let array = "a;b,c".Split(',', ';')
    "abc" = array.[0] + array.[1] + array.[2]
    |> equal true
    "a--b-c".Split([|"--"|], StringSplitOptions.None)
    |> (=) [|"a";"b-c"|] |> equal true

[<Fact>]
let ``test String.Split with remove empties works`` () =
    "a b c  d ".Split([|" "|], StringSplitOptions.RemoveEmptyEntries)
    |> (=) [|"a";"b";"c";"d"|] |> equal true
    let array = ";,a;b,c".Split([|','; ';'|], StringSplitOptions.RemoveEmptyEntries)
    "abc" = array.[0] + array.[1] + array.[2]
    |> equal true

[<Fact>]
let ``test String.Split with count works`` () =
    let array = "a b  c d".Split ([|' '|], 2)
    equal "a" array.[0]
    equal "b  c d" array.[1]
    "a;,b,c;d".Split([|','; ';'|], 3, StringSplitOptions.RemoveEmptyEntries)
    |> (=) [|"a";"b";"c;d"|] |> equal true

[<Fact>]
let ``test String.Replace works`` () =
    "abc abc abc".Replace("abc", "d") |> equal "d d d"
    // String.Replace does not get stuck in endless loop
    "...".Replace(".", "..") |> equal "......"

[<Fact>]
let ``test Access char by index works`` () =
    let c = "abcd".[2]
    equal 'c' c
    equal 'd' (char ((int c) + 1))

[<Fact>]
let ``test String.IndexOf char works`` () =
    "abcd".IndexOf('b') * 100 + "abcd".IndexOf('e')
    |> equal 99

[<Fact>]
let ``test String.IndexOf char works with offset`` () =
    "abcdbc".IndexOf('b', 3)
    |> equal 4

[<Fact>]
let ``test String.LastIndexOf char works`` () =
    "abcdbc".LastIndexOf('b') * 100 + "abcd".LastIndexOf('e')
    |> equal 399

[<Fact>]
let ``test String.LastIndexOf char works with offset`` () =
    "abcdbcebc".LastIndexOf('b', 3)
    |> equal 1

[<Fact>]
let ``test String.IndexOf works`` () =
    "abcd".IndexOf("bc") * 100 + "abcd".IndexOf("bd")
    |> equal 99

[<Fact>]
let ``test String.IndexOf works with offset`` () =
    "abcdbc".IndexOf("bc", 3)
    |> equal 4

[<Fact>]
let ``test String.IndexOf with empty pattern works`` () =
    "abcdbc".IndexOf("") |> equal 0
    "abcdbc".IndexOf("", 3) |> equal 3
    "abcdbc".IndexOf("", 6) |> equal 6

[<Fact>]
let ``test String.LastIndexOf works`` () =
    "abcdbc".LastIndexOf("bc") * 100 + "abcd".LastIndexOf("bd")
    |> equal 399

[<Fact>]
let ``test String.LastIndexOf works with offset`` () =
    "abcdbcebc".LastIndexOf("bc", 3)
    |> equal 1

[<Fact>]
let ``test String.LastIndexOf with empty pattern works`` () =
    "abcdbc".LastIndexOf("") |> equal 6
    "abcdbc".LastIndexOf("", 3) |> equal 4
    "abcdbc".LastIndexOf("", 0) |> equal 1

[<Fact>]
let ``test String.IndexOf with StringComparison works`` () =
    "abcdbc".IndexOf("b", StringComparison.Ordinal)
    |> equal 1

[<Fact>]
let ``test String.IndexOf char with StringComparison works`` () =
    "abcdbc".IndexOf('b', StringComparison.Ordinal)
    |> equal 1

[<Fact>]
let ``test String.IndexOf with index and StringComparison works`` () =
    "abcdbc".IndexOf("b", 3, StringComparison.Ordinal)
    |> equal 4

[<Fact>]
let ``test String.LastIndexOf with StringComparison works`` () =
    "abcdbc".LastIndexOf("b", StringComparison.Ordinal)
    |> equal 4

[<Fact>]
let ``test String.LastIndexOf with index and StringComparison works`` () =
    "abcdbc".LastIndexOf("b", 3, StringComparison.Ordinal)
    |> equal 1


[<Fact>]
let ``test String.IndexOfAny works`` () =
    "abcdbcebc".IndexOfAny([|'b'|]) |> equal 1
    "abcdbcebc".IndexOfAny([|'b'|], 2) |> equal 4
    "abcdbcebc".IndexOfAny([|'b'|], 2, 2) |> equal -1
    "abcdbcebc".IndexOfAny([|'f';'e'|]) |> equal 6
    "abcdbcebc".IndexOfAny([|'f';'e'|], 2) |> equal 6
    "abcdbcebc".IndexOfAny([|'f';'e'|], 2, 4) |> equal -1
    "abcdbcebc".IndexOfAny([|'c';'b'|]) |> equal 1

[<Fact>]
let ``test String.StartsWith char works`` () =
    "abcd".StartsWith('a') |> equal true
    "abcd".StartsWith('d') |> equal false

[<Fact>]
let ``test String.EndsWith char works`` () =
    "abcd".EndsWith('a') |> equal false
    "abcd".EndsWith('d') |> equal true

[<Fact>]
let ``test String.StartsWith works`` () =
    let args = [("ab", true); ("bc", false); ("cd", false); ("abcdx", false); ("abcd", true); ("", true)]
    for arg in args do
        "abcd".StartsWith(fst arg)
        |> equal (snd arg)

[<Fact>]
let ``test String.StartsWith with OrdinalIgnoreCase works`` () =
    let args = [("ab", true); ("AB", true); ("BC", false); ("cd", false); ("abcdx", false); ("abcd", true); ("", true)]
    for arg in args do
        "ABCD".StartsWith(fst arg, StringComparison.OrdinalIgnoreCase)
        |> equal (snd arg)

[<Fact>]
let ``test String.StartsWith with ignoreCase boolean works`` () =
    let args = [("ab", true); ("AB", true); ("BC", false); ("cd", false); ("abcdx", false); ("abcd", true); ("", true)]
    for arg in args do
        "ABCD".StartsWith(fst arg, true, CultureInfo.InvariantCulture)
        |> equal (snd arg)

[<Fact>]
let ``test String.EndsWith works`` () =
    let args = [("ab", false); ("cd", true);  ("bc", false); ("abcdx", false); ("abcd", true); ("", true)]
    for arg in args do
        "abcd".EndsWith(fst arg)
        |> equal (snd arg)

[<Fact>]
let ``test String.EndsWith with OrdinalIgnoreCase works`` () =
    let args = [("ab", false); ("CD", true); ("cd", true); ("bc", false); ("xabcd", false); ("abcd", true); ("", true)]
    for arg in args do
        "ABCD".EndsWith(fst arg, StringComparison.OrdinalIgnoreCase)
        |> equal (snd arg)

[<Fact>]
let ``test String.EndsWith with ignoreCase boolean works`` () =
    let args = [("ab", false); ("CD", true); ("cd", true); ("bc", false); ("xabcd", false); ("abcd", true); ("", true)]
    for arg in args do
        "ABCD".EndsWith(fst arg, true, CultureInfo.InvariantCulture)
        |> equal (snd arg)

[<Fact>]
let ``test String.Trim works`` () =
    "   abc   ".Trim()
    |> equal "abc"

[<Fact>]
let ``test String.Trim with chars works`` () =
    @"\\\abc///".Trim('\\','/')
    |> equal "abc"

[<Fact>]
let ``test String.Trim with special chars works`` () =
    @"()[]{}abc/.?*+-^$|\".Trim(@"()[]{}/.?*+-^$|\".ToCharArray())
    |> equal "abc"

[<Fact>]
let ``test String.TrimStart works`` () =
    "!!--abc   ".TrimStart('!','-')
    |> equal "abc   "

[<Fact>]
let ``test String.TrimStart with chars works`` () =
    "   abc   ".TrimStart()
    |> equal "abc   "

[<Fact>]
let ``test String.TrimEnd works`` () =
    "   abc   ".TrimEnd()
    |> equal "   abc"

[<Fact>]
let ``test String.TrimEnd with chars works`` () =
    "   abc??**".TrimEnd('*','?')
    |> equal "   abc"
    @"\foo\bar\".Replace("\\", "/").TrimEnd('/')
    |> equal "/foo/bar"

[<Fact>]
let ``test String.Empty works`` () =
    let s = String.Empty
    s |> equal ""

[<Fact>]
let ``test String.Chars works`` () =
    let input = "hello"
    input.Chars(2)
    |> equal 'l'

[<Fact>]
let ``test String.Substring works`` () =
    "abcdefg".Substring(2)
    |> equal "cdefg"

[<Fact>]
let ``test String.Substring works with length`` () =
    "abcdefg".Substring(2, 2)
    |> equal "cd"

[<Fact>]
let ``test String.Substring throws error if startIndex or length are out of bounds`` () =
    let throws f =
        try f () |> ignore; false
        with _ -> true
    throws (fun _ -> "abcdefg".Substring(20)) |> equal true
    throws (fun _ -> "abcdefg".Substring(2, 10)) |> equal true

[<Fact>]
let ``test String.ToUpper works`` () =
    "AbC".ToUpper() |> equal "ABC"

[<Fact>]
let ``test String.ToLower works`` () =
    "aBc".ToLower() |> equal "abc"


[<Fact>]
let ``test String.ToUpperInvariant works`` () =
    "AbC".ToUpperInvariant() |> equal "ABC"

[<Fact>]
let ``test String.ToLowerInvariant works`` () =
    "aBc".ToLowerInvariant() |> equal "abc"

[<Fact>]
let ``test String.Length works`` () =
    "AbC".Length |> equal 3

[<Fact>]
let ``test String item works`` () =
    "AbC".[1] |> equal 'b'

[<Fact>]
let ``test String.ToCharArray works`` () =
    let arr = "abcd".ToCharArray()
    arr |> equal [|'a';'b';'c';'d'|]

[<Fact>]
let ``test String.ToCharArray with range works`` () =
    let arr = "abcd".ToCharArray(1, 2)
    arr |> equal [|'b';'c'|]

// [<Fact>]
// let ``test String enumeration handles surrogates pairs`` () =
//     let unicodeString = ".\U0001f404."
//     unicodeString |> List.ofSeq |> Seq.length |> equal 4
//     String.length unicodeString |> equal 4
//     let mutable len = 0
//     for i in unicodeString do
//         len <- len + 1
//     equal 4 len

[<Fact>]
let ``test String.Join works`` () =
    String.Join("--", "a", "b", "c")
    |> equal "a--b--c"
    String.Join("--", seq { yield "a"; yield "b"; yield "c" })
    |> equal "a--b--c"

[<Fact>]
let ``test String.Join with indices works`` () =
    String.Join("**", [|"a"; "b"; "c"; "d"|], 1, 2)
    |> equal "b**c"
    String.Join("*", [|"a"; "b"; "c"; "d"|], 1, 3)
    |> equal "b*c*d"

[<Fact>]
let ``test String.Join works with chars`` () =
    String.Join("--", 'a', 'b', 'c')
    |> equal "a--b--c"
    String.Join("--", seq { yield 'a'; yield 'b'; yield 'c' })
    |> equal "a--b--c"
    [0..10]
    |> List.map (fun _ -> '*')
    |> fun chars -> String.Join("", chars)
    |> equal "***********"

[<Fact>]
let ``test String.Join with big integers works`` () =
    String.Join("--", [|3I; 5I|])
    |> equal "3--5"
    String.Join("--", 3I, 5I)
    |> equal "3--5"

[<Fact>]
let ``test String.Join with single argument works`` () =
    String.Join(",", "abc") |> equal "abc"
    String.Join(",", [|"abc"|]) |> equal "abc"
    String.Join(",", ["abc"]) |> equal "abc"

[<Fact>]
let ``test System.String.Concat works`` () =
    String.Concat("a", "b", "c")
    |> equal "abc"
    String.Concat(seq { yield "a"; yield "b"; yield "c" })
    |> equal "abc"

[<Fact>]
let ``test System.String.Join with long array works`` () =
    let n = 100_000
    let a = Array.init n (fun _i -> "a")
    let s = String.Join("", a)
    s.Length |> equal n

[<Fact>]
let ``test System.String.Join with long seq works`` () =
    let n = 100_000
    let a = seq { for i in 1..n -> "a" }
    let s = String.Join("", a)
    s.Length |> equal n

[<Fact>]
let ``test System.String.Concat with long array works`` () =
    let n = 100_000
    let a = Array.init n (fun _i -> "a")
    let s = String.Concat(a)
    s.Length |> equal n

[<Fact>]
let ``test System.String.Concat with long seq works`` () =
    let n = 100_000
    let a = seq { for i in 1..n -> "a" }
    let s = String.Concat(a)
    s.Length |> equal n

[<Fact>]
let ``test String.concat with long array works`` () =
    let n = 1_000_000
    let a = Array.init n (fun _i -> "a")
    let s = String.concat "" a
    s.Length |> equal n

[<Fact>]
let ``test String.concat with long seq works`` () =
    let n = 1_000_000
    let a = seq { for i in 1..n -> "a" }
    let s = String.concat "" a
    s.Length |> equal n

[<Fact>]
let ``test String.Remove works`` () =
    "abcd".Remove(2)
    |> equal "ab"
    "abcd".Remove(1,2)
    |> equal "ad"
    "abcd".Remove(0,2)
    |> equal "cd"
    "abcd".Remove(0,4)
    |> equal ""
    "abcd".Remove(0,0)
    |> equal "abcd"

[<Fact>]
let ``test String.Insert work`` () =
    "foobar".Insert(3, " is ")
    |> equal "foo is bar"

[<Fact>]
let ``test Enumerating string works`` () =
    let mutable res = ""
    for c in "HELLO" |> Seq.rev do
          res <- res + (string c)
    equal "OLLEH" res

// String - F# module functions

[<Fact>]
let ``test String.concat works`` () =
    String.concat "--" ["a"; "b"; "c"] |> equal "a--b--c"
    seq { yield "a"; yield "b"; yield "c" }
    |> String.concat "-" |> equal "a-b-c"

[<Fact>]
let ``test String.forall and exists work`` () =
    "!!!" |> String.forall (fun c -> c = '!') |> equal true
    "a!a" |> String.forall (fun c -> c = '!') |> equal false
    "aaa" |> String.forall (fun c -> c = '!') |> equal false

[<Fact>]
let ``test String.init works`` () =
    String.init 3 (fun i -> "a")
    |> equal "aaa"

[<Fact>]
let ``test String.collect works`` () =
    "abc" |> String.collect (fun c -> "bcd")
    |> equal "bcdbcdbcd"

[<Fact>]
let ``test String.iter works`` () =
    let res = ref ""
    "Hello world!"
    |> String.iter (fun c -> res.Value <- res.Value + c.ToString())
    equal "Hello world!" res.Value

[<Fact>]
let ``test String.iteri works`` () =
    let mutable res = ""
    "Hello world!"
    |> String.iteri (fun c i -> res <- res + i.ToString() + c.ToString())
    equal "H0e1l2l3o4 5w6o7r8l9d10!11" res

[<Fact>]
let ``test String.length function works`` () =
    "AbC" |> String.length
    |> equal 3

[<Fact>]
let ``test String.map works`` () =
    "Hello world!" |> String.map (fun c -> if c = 'H' then '_' else c)
    |> equal "_ello world!"

[<Fact>]
let ``test String.mapi works`` () =
    "Hello world!" |> String.mapi (fun i c -> if i = 1 || c = 'H' then '_' else c)
    |> equal "__llo world!"

[<Fact>]
let ``test String.replicate works`` () =
    String.replicate 3 "hi there"
    |> equal "hi therehi therehi there"

[<Fact>]
let ``test String.IsNullOrWhiteSpace works on string with blanks`` () =
    String.IsNullOrWhiteSpace "Fri Jun 30 2017 12:30:00 GMT+0200 (Mitteleuropäische Sommerzeit)"
    |> equal false


[<Fact>]
let ``test String.IsNullOrWhiteSpace works on blank only string`` () =
    String.IsNullOrWhiteSpace "      "
    |> equal true

[<Fact>]
let ``test String.filter works`` () =
    String.filter (fun x -> x <> '.') "a.b.c"
    |> equal "abc"

[<Fact>]
let ``test String.filter works when predicate matches everything`` () =
    String.filter (fun x -> x <> '.') "abc"
    |> equal "abc"

[<Fact>]
let ``test String.filter works when predicate doesn't match`` () =
    String.filter (fun x -> x <> '.') "..."
    |> equal ""

[<Fact>]
let ``test String.filter works with empty string`` () =
    String.filter (fun x -> x <> '.') ""
    |> equal ""

#if FABLE_COMPILER
[<Fact>]
let ``test System.Environment.NewLine works`` () =
  System.Environment.NewLine
  |> equal "\n"
#endif

[<Fact>]
let ``test System.Uri.UnescapeDataString works`` () =
    System.Uri.UnescapeDataString("Kevin%20van%20Zonneveld%21") |> equal "Kevin van Zonneveld!"
    System.Uri.UnescapeDataString("http%3A%2F%2Fkvz.io%2F") |> equal "http://kvz.io/"
    System.Uri.UnescapeDataString("http%3A%2F%2Fwww.google.nl%2Fsearch%3Fq%3DLocutus%26ie%3Dutf-8%26oe%3Dutf-8%26aq%3Dt%26rls%3Dcom.ubuntu%3Aen-US%3Aunofficial%26client%3Dfirefox-a")
    |> equal "http://www.google.nl/search?q=Locutus&ie=utf-8&oe=utf-8&aq=t&rls=com.ubuntu:en-US:unofficial&client=firefox-a"

[<Fact>]
let ``test System.Uri.EscapeDataString works`` () =
    System.Uri.EscapeDataString("Kevin van Zonneveld!") |> equal "Kevin%20van%20Zonneveld%21"
    System.Uri.EscapeDataString("http://kvz.io/") |> equal "http%3A%2F%2Fkvz.io%2F"
    System.Uri.EscapeDataString("http://www.google.nl/search?q=Locutus&ie=utf-8&oe=utf-8&aq=t&rls=com.ubuntu:en-US:unofficial&client=firefox-a")
    |> equal "http%3A%2F%2Fwww.google.nl%2Fsearch%3Fq%3DLocutus%26ie%3Dutf-8%26oe%3Dutf-8%26aq%3Dt%26rls%3Dcom.ubuntu%3Aen-US%3Aunofficial%26client%3Dfirefox-a"

[<Fact>]
let ``test System.Uri.EscapeUriString works`` () =
    System.Uri.EscapeUriString("Kevin van Zonneveld!") |> equal "Kevin%20van%20Zonneveld!"
    System.Uri.EscapeUriString("http://kvz.io/") |> equal "http://kvz.io/"
    System.Uri.EscapeUriString("http://www.google.nl/search?q=Locutus&ie=utf-8&oe=utf-8&aq=t&rls=com.ubuntu:en-US:unofficial&client=firefox-a")
    |> equal "http://www.google.nl/search?q=Locutus&ie=utf-8&oe=utf-8&aq=t&rls=com.ubuntu:en-US:unofficial&client=firefox-a"

// See #1628, though I'm not sure if the compiled tests are passing just the function reference without wrapping it
[<Fact>]
let ``test Passing Char.IsDigit as a function reference does not make String.filter hang`` () =
    "Hello! 123" |> String.filter System.Char.IsDigit |> equal "123"

[<Fact>]
let ``test sprintf with double percent should be unescaped`` () =
    sprintf "%d%%" 100 |> equal "100%"

[<Fact>]
let ``test interpolated string with double percent should be unescaped`` () =
    $"{100}%%" |> equal "100%"

[<Fact>]
let ``test Can create FormattableString`` () =
    let orderAmount = 100
    let convert (s: FormattableString) = s
    let s = convert $"You owe: {orderAmount:N5} {3} {5 = 5}"
    s.Format |> equal "You owe: {0:N5} {1} {2}"
    s.ArgumentCount |> equal 3
    s.GetArgument(2) |> equal (box true)
    s.GetArguments() |> equal [|100; 3; true|]

#if FABLE_COMPILER
//[<Fact>]
//let ``test Can use FormattableString.GetStrings() extension`` () =
//    let orderAmount = 100
//    let convert (s: FormattableString) = s
//    let s = convert $"You owe: {orderAmount:N5} {3} {5 = 5}"
//    s.GetStrings() |> equal [|"You owe: "; " "; " "; ""|]
//    let s2: FormattableString = $"""{5 + 2}This is "{"really"}" awesome!"""
//    s2.GetStrings() |> equal [|""; "This is \""; "\" awesome!"|]
//    let s3: FormattableString = $"""I have no holes"""
//    s3.GetStrings() |> equal [|"I have no holes"|]
#endif

[<Fact>]
let ``test printing strings with unicode characters`` () =
    printfn "🚀 printing unicode ..."

[<Fact>]
let ``test calling ToString(CultureInfo.InvariantCulture) works`` () =
    (1).ToString(CultureInfo.InvariantCulture) |> equal "1"
    (7923209L).ToString(CultureInfo.InvariantCulture) |> equal "7923209"
    (7923209UL).ToString(CultureInfo.InvariantCulture) |> equal "7923209"


[<Fact>]
let ``test printf.cont applies continuation after all args collected`` () =
    let mutable called = false
    let mutable receivedMsg = ""
    let cont msg =
        called <- true
        receivedMsg <- msg

    Printf.kprintf cont "%s: %d" "Value" 42

    called |> equal true
    receivedMsg |> equal "Value: 42"

[<Fact>]
let ``test printf.cont works with single argument`` () =
    let mutable result = ""
    let cont msg = result <- msg

    Printf.kprintf cont "Hello %s" "World"

    result |> equal "Hello World"

[<Fact>]
let ``test printf.cont raises exception via continuation`` () =
    let fail msg = failwith msg

    let mutable exceptionRaised = false
    try
        Printf.kprintf fail "Error: %s" "test error" |> ignore
    with
    | ex ->
        exceptionRaised <- true
        ex.Message |> equal "Error: test error"

    exceptionRaised |> equal true

[<Fact>]
let ``test failwithf works`` () =
    let mutable exceptionRaised = false
    try
        failwithf "Error: %s %d" "test" 42
    with
    | ex ->
        exceptionRaised <- true
        ex.Message |> equal "Error: test 42"

    exceptionRaised |> equal true

#if FABLE_COMPILER
open Fable.Core

#if !FABLE_COMPILER_ZIG // (imports are not supported by the Zig target)
[<Import("category", "unicodedata")>]
let unicodeCategory: char -> string = nativeOnly
#endif

#if !FABLE_COMPILER_ZIG // (not supported by the Zig target yet: comparison by a culture, params of obj, FormattableString, PrintfFormat.Value, a function whose result type F# leaves open, imports)
[<Fact>]
let ``test unicode categories`` () =
    let chars = [
      "\x00", "Cc"
      " ", "Zs"
      "!", "Po"
      "$", "Sc"
      "(", "Ps"
      ")", "Pe"
      "+", "Sm"
      "-", "Pd"
      "0", "Nd"
      "A", "Lu"
      "^", "Sk"
      "_", "Pc"
      "a", "Ll"
      "¦", "So"
      "ª", "Lo"
      "«", "Pi"
      "\xad", "Cf"
      "²", "No"
      "»", "Pf"
      "ǅ", "Lt"
      "ʰ", "Lm"
      "", "Mn"
      "\u0378", "Cn"
      "\u0488", "Me"
      "\u0903", "Mc"
      "\u16ee", "Nl"
      "\u2028", "Zl"
      "\u2029", "Zp"
     //TODO: this fails with error EXCEPTION: Unable to translate Unicode character \\uD800 at index 116 to specified code page.
      //"\ud800" , "Cs"
      "\ue000", "Co"
    ]
    for (s, cat) in chars do
      s
      |> String.iter (fun c ->
        // this ensures that the character is from the expected category
        cat |> equal (unicodeCategory c)
        Char.IsLetterOrDigit c |> ignore
      )
#endif
#endif

[<Fact>]
let ``test String slices clamp the bounds like .NET`` () =
    let s = "abc"
    s.[-1..1] |> equal "ab"
    s.[-5..] |> equal "abc"
    s.[1..5] |> equal "bc"
    s.[.. -2] |> equal ""
    s.[-3.. -2] |> equal ""
    s.[2..1] |> equal ""
    let lower, upper = -1, 1
    s.[lower..upper] |> equal "ab"

type private ShowBox<'T> = { BoxItem: 'T }

type private ShowTree =
    | Leaf of uint16 voption
    | Fork of ShowTree * struct (int * string) * ShowTree

[<Fact>]
let ``test %A and ToString for voption, struct tuple, uint16, and functions`` () =
    sprintf "%A" (ValueSome 42) |> equal "ValueSome 42"
    sprintf "%A" (ValueNone: int voption) |> equal "ValueNone"
    sprintf "%A" (ValueSome(1, 2)) |> equal "ValueSome (1, 2)"
    sprintf "%A" (ValueSome(struct (1, 2))) |> equal "ValueSome struct (1, 2)"
    sprintf "%A" (Some(ValueSome 5)) |> equal "Some (ValueSome 5)"
    sprintf "%A" (ValueSome(ValueNone: int voption)) |> equal "ValueSome ValueNone"
    sprintf "%A" (struct (1, "a")) |> equal "struct (1, \"a\")"
    sprintf "%A" [ struct (1, 2); struct (3, 4) ] |> equal "[struct (1, 2); struct (3, 4)]"
    sprintf "%A" (1, struct (2, 3)) |> equal "(1, struct (2, 3))"
    sprintf "%A" (struct (1, (2, 3))) |> equal "struct (1, (2, 3))"
    sprintf "%A" 16us |> equal "16us"
    sprintf "%A" (16us, 'a') |> equal "(16us, 'a')"
    sprintf "%A" { BoxItem = ValueSome 9 } |> equal "{ BoxItem = ValueSome 9 }"
    sprintf "%A" (Fork(Leaf(ValueSome 16us), struct (7, "ok"), Leaf ValueNone))
    |> equal "Fork (Leaf (ValueSome 16us), struct (7, \"ok\"), Leaf ValueNone)"
    sprintf "%A" {| A = ValueSome 3; B = struct (1, 2) |}
    |> equal "{ A = ValueSome 3\n  B = struct (1, 2) }"
    sprintf "%A" (Map.ofList [ (ValueSome 1, struct (2, "b")) ])
    |> equal "map [(ValueSome 1, struct (2, \"b\"))]"
    (sprintf "%A" (fun (x: int) -> x + 1)).StartsWith("<fun") |> equal true
#if FABLE_COMPILER_ZIG
    sprintf "%A" (fun (x: int) -> x + 1) |> equal "<fun>"
#endif
    string (ValueSome 42) |> equal "42"
    string (ValueNone: int voption) |> equal "ValueNone"
    string (struct (1, "a")) |> equal "(1, a)"
    string (struct (ValueSome 42, Some 7)) |> equal "(42, Some(7))"
    $"{ValueSome 7}|{struct (1, 2)}" |> equal "7|(1, 2)"
    sprintf "%O" (ValueSome 42) |> equal "42"

// ---- ported from tests/Js/Main (2026-11-16) ----

#if !FABLE_COMPILER_ZIG // (a format known only when the program runs, given its values: printf whose type F# takes from each use)
let spr fmt =
    let fmt = Printf.StringFormat<_>(fmt)
    sprintf fmt
#endif





type B() =
      let mutable a = 5
      override x.ToString() =
            a <- a + 1
            $"a=%O{a}"

type Test(i: int) =
      override _.ToString() = string(i + i)

let [<Literal>] aLiteral = "foo"
let notALiteral = "foo"


open System.Globalization

[<Fact>]
let ``test String chunkBySize works`` () =
    // See #1296
    "fffff" |> Seq.chunkBySize 3 |> Seq.map String |> Seq.toList
    |> equal ["fff"; "ff"]

[<Fact>]
let ``test StringBuilder.Append treats null as empty`` () =
    // See #5162
    let n: string = null
    let o: obj = null
    let sb = System.Text.StringBuilder()
    sb.Append("a").Append(n).Append(o).Append("b").ToString() |> equal "ab"

[<Fact>]
let ``test kprintf works`` () =
    let f (s:string) = s + "XX"
    Printf.kprintf f "hello" |> equal "helloXX"
    Printf.kprintf f "%X" 255 |> equal "FFXX"
    Printf.kprintf f "%.2f %g" 0.5468989 5. |> equal "0.55 5XX"

[<Fact>]
let ``test kprintf works indirectly`` () =
    // See #1204
    let lines = ResizeArray<string>()
    let linef fmt = Printf.ksprintf lines.Add fmt // broken
    linef "open %s" "Foo"
    lines |> Seq.toList |> equal ["open Foo"]

[<Fact>]
let ``test sprintf "%s" prints null as empty`` () =
    // See #5162
    let n: string = null
    sprintf "%s" n |> equal ""
    sprintf "a%sb" n |> equal "ab"
    sprintf "[%5s]" n |> equal "[     ]"
    sprintf "[%-5s]" n |> equal "[     ]"
    (try failwithf "x%sy" n with e -> e.Message) |> equal "xy"

[<Fact>]
let ``test ksprintf and kprintf work with interpolated strings`` () =
    // See #3969
    let x = 3
    Printf.ksprintf (fun s -> s + "!") $"ks %d{x} {x + 1}" |> equal "ks 3 4!"
    Printf.kprintf (fun s -> s + "?") $"kp {x}" |> equal "kp 3?"

[<Fact>]
let ``test sprintf with escaped percent symbols works`` () =
    // See #195
    let r, r1, r2 = "Ratio", 0.213849, 0.799898
    sprintf "%s1: %.2f%% %s2: %.2f%%" r (r1*100.) r (r2*100.)
    |> equal "Ratio1: 21.38% Ratio2: 79.99%"

[<Fact>]
let ``test sprintf with percent symbols in arguments works`` () =
    // See #329
    let same s = sprintf "%s" s |> equal s
    same "%"
    same "%%"
    same "%%%"
    same "%%%%"
    same "% %"
    same "%% %%"
    same "%% % % %%"

[<Fact>]
let ``test Fix #2398: Exception when two successive string format placeholders and value of first one ends in percent`` () =
    sprintf "%c%s" '%' "text" |> equal "%text"

[<Fact>]
let ``test string interpolation works`` () =
    let name = "Phillip"
    let age = 29
    sprintf $"Name: %s{name}, Age: %i{age}"
    |> equal "Name: Phillip, Age: 29"

[<Fact>]
let ``test Printf %A works with anonymous records`` () =
    // See #4029
    let person  = {| FirstName = "John"; LastName = "Doe" |}
    let s = sprintf "%A" person
    System.Text.RegularExpressions.Regex.Replace(s, @"\s+", " ")
    |> equal """{ FirstName = "John" LastName = "Doe" }"""

[<Fact>]
let ``test Backslash is escaped in interpolated strings`` () =
    // See #2649
    $"\\" |> equal @"\"
    $"\\".Length |> equal 1
    $@"\" |> equal @"\"
    $@"\".Length |> equal 1
    @$"\" |> equal @"\"
    @$"\".Length |> equal 1
    $"\\{4}" |> equal @"\4"
    $"\\{4}".Length |> equal 2
    $@"\{4}" |> equal @"\4"
    $@"\{4}".Length |> equal 2
    @$"\{4}" |> equal @"\4"
    @$"\{4}".Length |> equal 2

[<Fact>]
let ``test sprintf "%o" works`` () =
    sprintf "%o" 8 |> equal "10"
    sprintf "%o" 0 |> equal "0"
    sprintf "%o" -1 |> equal "37777777777"
    sprintf "%o" -8 |> equal "37777777770"
    sprintf "%o" (1 <<< 31) |> equal "20000000000"
    sprintf "%o" 255uy |> equal "377"
    sprintf "%o" 65535us |> equal "177777"
    sprintf "%o" 4095L |> equal "7777"
    sprintf "%o" -1L |> equal "1777777777777777777777"
    sprintf "%o" 18446744073709551615UL |> equal "1777777777777777777777"

[<Fact>]
let ``test interpolated "%o" works`` () =
    $"%o{-1}|%o{8}|%5o{8}" |> equal "37777777777|10|   10"

[<Fact>]
let ``test String.Format {0:x} works`` () =
    //See above comment on expected values
    String.Format(CultureInfo.InvariantCulture, "255: {0:X}", 255) |> equal "255: FF"
    String.Format(CultureInfo.InvariantCulture, "255: {0:x}", 255) |> equal "255: ff"
    String.Format(CultureInfo.InvariantCulture, "-255: {0:X}", -255) |> equal "-255: FFFFFF01"
    String.Format(CultureInfo.InvariantCulture, "4095L: {0:X}", 4095L) |> equal "4095L: FFF"
    String.Format(CultureInfo.InvariantCulture, "-4095L: {0:X}", -4095L) |> equal "-4095L: FFFFFFFFFFFFF001"
    String.Format(CultureInfo.InvariantCulture, "1 <<< 31: {0:x}", (1 <<< 31)) |> equal "1 <<< 31: 80000000"
    String.Format(CultureInfo.InvariantCulture, "1u <<< 31: {0:x}", (1u <<< 31)) |> equal "1u <<< 31: 80000000"
    String.Format(CultureInfo.InvariantCulture, "2147483649L: {0:x}", 2147483649L) |> equal "2147483649L: 80000001"
    String.Format(CultureInfo.InvariantCulture, "2147483650uL: {0:x}", 2147483650uL) |> equal "2147483650uL: 80000002"
    String.Format(CultureInfo.InvariantCulture, "1L <<< 63: {0:x}", (1L <<< 63)) |> equal "1L <<< 63: 8000000000000000"
    String.Format(CultureInfo.InvariantCulture, "1uL <<< 63: {0:x}", (1uL <<< 63)) |> equal "1uL <<< 63: 8000000000000000"

[<Fact>]
let ``test String.Format {0:x} with precision works`` () =
    String.Format(CultureInfo.InvariantCulture, "#{0:X3}", 0xC149D) |> equal "#C149D"
    String.Format(CultureInfo.InvariantCulture, "#{0:X6}", 0xC149D) |> equal "#0C149D"

[<Fact>]
let ``test String.Format works with thousands separator`` () =
    String.Format(CultureInfo.InvariantCulture, "{0}", 12343235354.6547757) |> equal "12343235354.654776"
    String.Format(CultureInfo.InvariantCulture, "{0:#,##.000}", 12343235354.6547757) |> equal "12,343,235,354.655"
    String.Format(CultureInfo.InvariantCulture, "{0:#,##.000}", 12343235354.6547757M) |> equal "12,343,235,354.655"
    String.Format(CultureInfo.InvariantCulture, "{0:#,##.00}", 123.456) |> equal "123.46"
    String.Format(CultureInfo.InvariantCulture, "{0:#,##.00}", 123.456M) |> equal "123.46"
    String.Format(CultureInfo.InvariantCulture, "{0:#,##.00}", 123438192123.456M) |> equal "123,438,192,123.46"
    String.Format(CultureInfo.InvariantCulture, "{0:#,##}", 1.456M) |> equal "1"
    String.Format(CultureInfo.InvariantCulture, "{0:0,0}", 1.456M) |> equal "01"

[<Fact>]
let ``test String.Format can omit decimal digits`` () =
    String.Format(CultureInfo.InvariantCulture, "{0:#,##}", 12343235354.6547757) |> equal "12,343,235,355"
    String.Format(CultureInfo.InvariantCulture, "{0:0,00}", 12343235354.6547757) |> equal "12,343,235,355"
    String.Format(CultureInfo.InvariantCulture, "{0:0,00}", 12343235354.) |> equal "12,343,235,354"
    String.Format(CultureInfo.InvariantCulture, "{0:#}", 12343235354.) |> equal "12343235354"
    String.Format(CultureInfo.InvariantCulture, "{0:0}", 12343235354.) |> equal "12343235354"

    String.Format(CultureInfo.InvariantCulture, "{0:#,#}", 12343235354.6547757M) |> equal "12,343,235,355"
    String.Format(CultureInfo.InvariantCulture, "{0:0,0}", 12343235354.6547757M) |> equal "12,343,235,355"

    String.Format(CultureInfo.InvariantCulture, "{0:0,0}", 1234323535) |> equal "1,234,323,535"
    String.Format(CultureInfo.InvariantCulture, "{0:#}", 1234323535) |> equal "1234323535"
    String.Format(CultureInfo.InvariantCulture, "{0:0}", 1234323535) |> equal "1234323535"

    String.Format(CultureInfo.InvariantCulture, "{0:0,0}", 12343235354M) |> equal "12,343,235,354"
    String.Format(CultureInfo.InvariantCulture, "{0:0,0}", 343235354M) |> equal "343,235,354"
    String.Format(CultureInfo.InvariantCulture, "{0:#}", 12343235354M) |> equal "12343235354"
    String.Format(CultureInfo.InvariantCulture, "{0:0}", 12343235354M) |> equal "12343235354"

[<Fact>]
let ``test String.Format works with N format specifier`` () =
    // See #2582
    String.Format(CultureInfo.InvariantCulture, "{0:N0}", 1000) |> equal "1,000"
    String.Format(CultureInfo.InvariantCulture, "{0:N0}", 12345678) |> equal "12,345,678"
    String.Format(CultureInfo.InvariantCulture, "{0:N0}", -1000) |> equal "-1,000"
    String.Format(CultureInfo.InvariantCulture, "{0:N2}", 1000) |> equal "1,000.00"
    String.Format(CultureInfo.InvariantCulture, "{0:N}", 1000) |> equal "1,000.00"
    (1000).ToString("N0") |> equal "1,000"
    (1000).ToString("N2") |> equal "1,000.00"

[<Fact>]
let ``test String.Format trims trailing zeroes when using # placeholder`` () =
    // Fix #2950
    String.Format(CultureInfo.InvariantCulture, "{0:######,###.000####}", -6789.5688) |> equal "-6,789.5688"
    String.Format(CultureInfo.InvariantCulture, "{0:######,###.000####}", 6789.5688) |> equal "6,789.5688"
    String.Format(CultureInfo.InvariantCulture, "{0:0######,###.000####0}", -6789.5688) |> equal "-0,000,006,789.56880000"
    String.Format(CultureInfo.InvariantCulture, "{0:0######,###.000####0}", 6789.5688) |> equal "0,000,006,789.56880000"

[<Fact>]
let ``test C and P format specifiers work with zero precision`` () =
    // See #2582
    String.Format(CultureInfo.InvariantCulture, "{0:C0}", 1000) |> equal "¤1,000"
    String.Format(CultureInfo.InvariantCulture, "{0:C0}", -1000) |> equal "(¤1,000)"
    String.Format(CultureInfo.InvariantCulture, "{0:P0}", 0.5) |> equal "50 %"
    String.Format(CultureInfo.InvariantCulture, "{0:P2}", 0.1234) |> equal "12.34 %"
    String.Format(CultureInfo.InvariantCulture, "{0:C2}", 1000) |> equal "¤1,000.00"

[<Fact>]
let ``test sprintf rounds exact midpoints of floats to even`` () =
    // See #5202
    sprintf "%.2f" 0.125 |> equal "0.12"
    sprintf "%.0f" 2.5 |> equal "2"
    sprintf "%.0f" 0.5 |> equal "0"
    sprintf "%.0f" 1.5 |> equal "2"
    sprintf "%.0f" -2.5 |> equal "-2"
    sprintf "%.0f" -0.5 |> equal "-0"
    sprintf "%.0f" 2.5f |> equal "2"
    sprintf "%.2g" 0.125 |> equal "0.12"
    sprintf "%.2f" 1.005 |> equal "1.00"
    sprintf "%.2f" 0.375 |> equal "0.38"
    sprintf "%.1f" 0.05 |> equal "0.1"
    sprintf "%.0f" 2.5m |> equal "3"
    sprintf "%.2f" 0.125m |> equal "0.13"

[<Fact>]
let ``test Standard numeric formats round exact midpoints of floats to even`` () =
    // See #5202
    (0.125).ToString("F2", CultureInfo.InvariantCulture) |> equal "0.12"
    (2.5).ToString("F0", CultureInfo.InvariantCulture) |> equal "2"
    (-2.5).ToString("F0", CultureInfo.InvariantCulture) |> equal "-2"
    (0.125f).ToString("F2", CultureInfo.InvariantCulture) |> equal "0.12"
    (0.125).ToString("E1", CultureInfo.InvariantCulture) |> equal "1.2E-001"
    (9.5).ToString("E0", CultureInfo.InvariantCulture) |> equal "1E+001"
    (2.5e20).ToString("E0", CultureInfo.InvariantCulture) |> equal "2E+020"
    (3.5e20).ToString("E0", CultureInfo.InvariantCulture) |> equal "4E+020"
    (0.125).ToString("P0", CultureInfo.InvariantCulture) |> equal "12 %"
    (-0.125).ToString("P0", CultureInfo.InvariantCulture) |> equal "-12 %"
    (0.00125).ToString("P1", CultureInfo.InvariantCulture) |> equal "0.1 %"
    (0.005).ToString("P0", CultureInfo.InvariantCulture) |> equal "1 %"
    (2.5).ToString("N0", CultureInfo.InvariantCulture) |> equal "2"
    (2.5).ToString("C0", CultureInfo.InvariantCulture) |> equal "¤2"
    (0.125).ToString("G2", CultureInfo.InvariantCulture) |> equal "0.12"
    String.Format(CultureInfo.InvariantCulture, "{0:F2}", 0.125) |> equal "0.12"
    (1.005).ToString("F2", CultureInfo.InvariantCulture) |> equal "1.00"
    (0.375).ToString("F2", CultureInfo.InvariantCulture) |> equal "0.38"
    (0.125).ToString("0.00", CultureInfo.InvariantCulture) |> equal "0.13"
    (2.5m).ToString("F0", CultureInfo.InvariantCulture) |> equal "3"
    (0.125m).ToString("F2", CultureInfo.InvariantCulture) |> equal "0.13"

[<Fact>]
let ``test G format specifier trims trailing zeros without corrupting exponential notation`` () =
    (123.45).ToString("G17", CultureInfo.InvariantCulture) |> equal "123.45"
    (10000.0).ToString("G17", CultureInfo.InvariantCulture) |> equal "10000"
    (0.000222).ToString("G17", CultureInfo.InvariantCulture) |> equal "0.000222"
    (1e-10).ToString("G17", CultureInfo.InvariantCulture) |> equal "1E-10"
    (1e-10).ToString("g17", CultureInfo.InvariantCulture) |> equal "1e-10"
    (1.5e10).ToString("G17", CultureInfo.InvariantCulture) |> equal "15000000000"

[<Fact>]
let ``test G format specifier pads exponent to at least 2 digits`` () =
    (1e-7).ToString("G2", CultureInfo.InvariantCulture) |> equal "1E-07"
    (1e7).ToString("G2", CultureInfo.InvariantCulture) |> equal "1E+07"
    (1.5e-7).ToString("G2", CultureInfo.InvariantCulture) |> equal "1.5E-07"
    (-1e-7).ToString("G2", CultureInfo.InvariantCulture) |> equal "-1E-07"
    (1e-7).ToString("g2", CultureInfo.InvariantCulture) |> equal "1e-07"

[<Fact>]
let ``test x and X format specifiers work with no defined precision`` () =
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 0) |> equal "0"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 0u) |> equal "0"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 0l) |> equal "0"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 0UL) |> equal "0"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 0L) |> equal "0"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 1) |> equal "1"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 1u) |> equal "1"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 1l) |> equal "1"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 1UL) |> equal "1"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 1L) |> equal "1"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 8) |> equal "8"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 8u) |> equal "8"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 8l) |> equal "8"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 8UL) |> equal "8"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 8L) |> equal "8"
    String.Format(CultureInfo.InvariantCulture, "{0:x}", 15) |> equal "f"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 15) |> equal "F"
    String.Format(CultureInfo.InvariantCulture, "{0:x}", 15u) |> equal "f"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 15u) |> equal "F"
    String.Format(CultureInfo.InvariantCulture, "{0:x}", 15l) |> equal "f"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 15l) |> equal "F"
    String.Format(CultureInfo.InvariantCulture, "{0:x}", 15UL) |> equal "f"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 15UL) |> equal "F"
    String.Format(CultureInfo.InvariantCulture, "{0:x}", 15L) |> equal "f"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 15L) |> equal "F"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 16) |> equal "10"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 16u) |> equal "10"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 16l) |> equal "10"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 16UL) |> equal "10"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 16L) |> equal "10"
    String.Format(CultureInfo.InvariantCulture, "{0:x}", 26) |> equal "1a"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 26) |> equal "1A"
    String.Format(CultureInfo.InvariantCulture, "{0:x}", 26u) |> equal "1a"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 26u) |> equal "1A"
    String.Format(CultureInfo.InvariantCulture, "{0:x}", 26l) |> equal "1a"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 26l) |> equal "1A"
    String.Format(CultureInfo.InvariantCulture, "{0:x}", 26UL) |> equal "1a"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 26UL) |> equal "1A"
    String.Format(CultureInfo.InvariantCulture, "{0:x}", 26L) |> equal "1a"
    String.Format(CultureInfo.InvariantCulture, "{0:X}", 26L) |> equal "1A"

    (0).ToString("X") |> equal "0"
    (0u).ToString("X") |> equal "0"
    (0l).ToString("X") |> equal "0"
    (0UL).ToString("X") |> equal "0"
    (0L).ToString("X") |> equal "0"
    (1).ToString("X") |> equal "1"
    (1u).ToString("X") |> equal "1"
    (1l).ToString("X") |> equal "1"
    (1UL).ToString("X") |> equal "1"
    (1L).ToString("X") |> equal "1"
    (8).ToString("X") |> equal "8"
    (8u).ToString("X") |> equal "8"
    (8l).ToString("X") |> equal "8"
    (8UL).ToString("X") |> equal "8"
    (8L).ToString("X") |> equal "8"
    (15).ToString("x") |> equal "f"
    (15).ToString("X") |> equal "F"
    (15u).ToString("x") |> equal "f"
    (15u).ToString("X") |> equal "F"
    (15l).ToString("x") |> equal "f"
    (15l).ToString("X") |> equal "F"
    (15UL).ToString("x") |> equal "f"
    (15UL).ToString("X") |> equal "F"
    (15L).ToString("x") |> equal "f"
    (15L).ToString("X") |> equal "F"
    (16).ToString("X") |> equal "10"
    (16u).ToString("X") |> equal "10"
    (16l).ToString("X") |> equal "10"
    (16UL).ToString("X") |> equal "10"
    (16L).ToString("X") |> equal "10"
    (26).ToString("x") |> equal "1a"
    (26).ToString("X") |> equal "1A"
    (26u).ToString("x") |> equal "1a"
    (26u).ToString("X") |> equal "1A"
    (26l).ToString("x") |> equal "1a"
    (26l).ToString("X") |> equal "1A"
    (26UL).ToString("x") |> equal "1a"
    (26UL).ToString("X") |> equal "1A"
    (26L).ToString("x") |> equal "1a"
    (26L).ToString("X") |> equal "1A"

[<Fact>]
let ``test ToString formatted works with decimals`` () =
    // See #2276
    let decimal = 78.6M
    decimal.ToString("0.000").Replace(",", ".") |> equal "78.600"

[<Fact>]
let ``test Printf in sequence is not erased`` () =
    let x = sprintf "Foo"
    let y = sprintf "B%sr" "a"
    x + y |> equal "FooBar"

[<Fact>]
let ``test String slicing works`` () =
    let s = "cat and dog"
    sprintf "%s" s.[2..8] |> equal "t and d"
    sprintf "%s" s.[2..] |> equal "t and dog"
    sprintf "%s" s.[..8] |> equal "cat and d"

[<Fact>]
let ``test String.Format unescapes doubled braces`` () =
    // See #5163
    String.Format(CultureInfo.InvariantCulture, "{{{0}}}", 5) |> equal "{5}"
    String.Format(CultureInfo.InvariantCulture, "{{x}} {0}", 1) |> equal "{x} 1"
    String.Format(CultureInfo.InvariantCulture, "}}{{", 1) |> equal "}{"
    String.Format(CultureInfo.InvariantCulture, "{{{0:N1}}}", 2.26) |> equal "{2.3}"
    String.Format(CultureInfo.InvariantCulture, "{{{0,4}}}", 5) |> equal "{   5}"

[<Fact>]
let ``test Padding works`` () =
    "3.14".PadLeft(10)      |> equal "      3.14"
    "3.14".PadRight(10)     |> equal "3.14      "
    "22".PadLeft(10, '0')   |> equal "0000000022"
    "-22".PadRight(10, 'X') |> equal "-22XXXXXXX"
    "333".PadLeft(1) |> equal "333"

[<Fact>]
let ``test Padding with sprintf works`` () =
    sprintf "%10.1f" 3.14  |> equal "       3.1"
    sprintf "%-10.1f" 3.14 |> equal "3.1       "
    sprintf "%+010i" 22    |> equal "+000000022"
    sprintf "%+0-10i" -22  |> equal "-22       "

[<Fact>]
let ``test Padding with String.Format works`` () =
    String.Format(CultureInfo.InvariantCulture, "{0,10:F1}", 3.14)  |> equal "       3.1"
    String.Format(CultureInfo.InvariantCulture, "{0,-10:F1}", 3.14) |> equal "3.1       "
    String.Format(CultureInfo.InvariantCulture, "{0,10}", 22)       |> equal "        22"
    String.Format(CultureInfo.InvariantCulture, "{0,-10}", -22)     |> equal "-22       "

[<Fact>]
let ``test String.Split with empty works`` () =
    let array = "a b cd".Split()
    array |> equal [| "a"; "b"; "cd" |]

[<Fact>]
let ``test String.Split with trim entries works`` () =
    " a-- b- c ".Split('-', 2, StringSplitOptions.TrimEntries)
    |> (=) [|"a"; "- b- c"|] |> equal true
    " a-- b- c ".Split('-', 3, StringSplitOptions.TrimEntries)
    |> (=) [|"a"; ""; "b- c"|] |> equal true

[<Fact>]
let ``test String.Split with consecutive separators works`` () =
    "       ".Split(" ", 4,  StringSplitOptions.None)
    |> equal [|"";"";"";"    "|]
    "       ".Split(" ", 4,  StringSplitOptions.RemoveEmptyEntries)
    |> equal [||]
    "       ".Split(" ", 4,  StringSplitOptions.TrimEntries)
    |> equal [|"";"";"";""|]
    "       ".Split(" ", 4,  StringSplitOptions.RemoveEmptyEntries ||| StringSplitOptions.TrimEntries)
    |> equal [||]

[<Fact>]
let ``test String.IndexOf with StringComparison`` () =
    "abcdbc".IndexOf("b", StringComparison.Ordinal)
    |> equal 1

[<Fact>]
let ``test String.IndexOf with index and StringComparison`` () =
    "abcdbc".IndexOf("b", 3, StringComparison.Ordinal)
    |> equal 4

[<Fact>]
let ``test String.IndexOf with OrdinalIgnoreCase StringComparison`` () =
    "ABCDBC".IndexOf("b", StringComparison.OrdinalIgnoreCase) |> equal 1
    "ABCDBC".IndexOf("b", StringComparison.Ordinal) |> equal -1
    "ABCDBC".IndexOf("b", StringComparison.InvariantCultureIgnoreCase) |> equal 1

[<Fact>]
let ``test String.LastIndexOf with StringComparison`` () =
    "abcdbc".LastIndexOf("b", StringComparison.Ordinal)
    |> equal 4

[<Fact>]
let ``test String.LastIndexOf with index and StringComparison`` () =
    "abcdbc".LastIndexOf("b", 3, StringComparison.Ordinal)
    |> equal 1

[<Fact>]
let ``test String.EndsWith with empty pattern and StringComparison works`` () =
    // .NET: every string ends with "" for all StringComparison values
    "hello".EndsWith("", StringComparison.CurrentCulture) |> equal true
    "hello".EndsWith("", StringComparison.InvariantCulture) |> equal true
    "hello".EndsWith("", StringComparison.Ordinal) |> equal true
    "hello".EndsWith("", StringComparison.OrdinalIgnoreCase) |> equal true
    "hello".EndsWith("", StringComparison.InvariantCultureIgnoreCase) |> equal true
    "".EndsWith("", StringComparison.CurrentCulture) |> equal true
    "hello".StartsWith("", StringComparison.CurrentCulture) |> equal true
    "hello".StartsWith("", StringComparison.Ordinal) |> equal true
    "hello".StartsWith("", StringComparison.OrdinalIgnoreCase) |> equal true

[<Fact>]
let ``test String.EndsWith with non-empty pattern and StringComparison works`` () =
    "hello".EndsWith("LO", StringComparison.OrdinalIgnoreCase) |> equal true
    "hello".EndsWith("LO", StringComparison.InvariantCultureIgnoreCase) |> equal true
    "hello".EndsWith("lo", StringComparison.Ordinal) |> equal true
    "hello".EndsWith("LO", StringComparison.Ordinal) |> equal false
    "hello".EndsWith("he", StringComparison.Ordinal) |> equal false
    "hello".EndsWith("hello", StringComparison.CurrentCulture) |> equal true
    "hello".EndsWith("xhello", StringComparison.Ordinal) |> equal false

[<Fact>]
let ``test String.Chars throws when index is out of bounds`` () =
    let input = "abc"
    throwsAnyError <| fun () ->
        input.Chars(-1) |> ignore
    throwsAnyError <| fun () ->
        input.Chars(3) |> ignore

[<Fact>]
let ``test String indexer evaluates the string and the index once`` () =
    let mutable calls = 0
    let next () =
        calls <- calls + 1
        calls
    let pick () =
        calls <- calls + 1
        "abc"
    "abc".[next ()] |> equal 'b'
    calls |> equal 1
    (pick ()).[2] |> equal 'c'
    calls |> equal 2
    throwsAnyError (fun () -> "abc".[next () + 2])
    calls |> equal 3

[<Fact>]
let ``test String indexer works`` () =
    let input = "hello"
    input.[1] |> equal 'e'
    input.[4] |> equal 'o'

[<Fact>]
let ``test String indexer throws when index is out of bounds`` () =
    let input = "abc"
    throwsAnyError <| fun () ->
        input.[-1] |> ignore
    throwsAnyError <| fun () ->
        input.[3] |> ignore

[<Fact>]
let ``test String.Join treats a null separator as empty`` () =
    // See #5167
    String.Join((null: string), [| "a"; "b" |]) |> equal "ab"
    String.Join((null: string), seq { yield "a"; yield "b" }) |> equal "ab"
    String.Join((null: string), "a", "b") |> equal "ab"
    String.Join((null: string), [| "a"; "b"; "c" |], 1, 2) |> equal "bc"

[<Fact>]
let ``test String.Join treats null elements as empty`` () =
    String.Join(",", [| "a"; null; "b" |]) |> equal "a,,b"
    String.Join(",", [| box "a"; null; box 1 |]) |> equal "a,,1"

[<Fact>]
let ``test string treats null as empty`` () =
    // See #5162
    let n: string = null
    let o: obj = null
    string n |> equal ""
    string (box n) |> equal ""
    string o |> equal ""
    string (None: int option) |> equal ""
    string "a" |> equal "a"

[<Fact>]
let ``test System.String.Concat with long string arg works`` () =
    // Fixed-arity overload (string, string) must not spread the last argument
    // as characters, otherwise large strings overflow the call stack.
    let n = 1_000_000
    let big = String.replicate n "a"
    let s = String.Concat("p", big)
    s.Length |> equal (n + 1)

[<Fact>]
let ``test Interpolated string with %s and long string value works`` () =
    // Lowered by the F# compiler to String.Concat(prefix, value), which must
    // not spread the value as characters into the runtime call.
    let n = 1_000_000
    let data = String.replicate n "a"
    let s = $"prefix:%s{data}"
    s.Length |> equal (n + 7)

[<Fact>]
let ``test String.length (function) works`` () =
    "AbC" |> String.length
    |> equal 3

[<Fact>]
let ``test Passing Char.IsDigit as a function reference doesn't make String.filter hang`` () =
    "Hello! 123" |> String.filter System.Char.IsDigit |> equal "123"

[<Fact>]
let ``test sprintf with double % should be unescaped`` () =
    sprintf "%d%%" 100 |> equal "100%"

[<Fact>]
let ``test interpolated string with double % should be unescaped`` () =
    $"{100}%%" |> equal "100%"

[<Fact>]
let ``test interpolated string with format and double % should be unescaped`` () =
    $"%.2f{100.4566666}%%" |> equal "100.46%"

[<Fact>]
let ``test interpolated string with double % should not interfere with holes afterwards `` () =
    $"%%{99. - 1.5}".Replace(",", ".") |> equal "%97.5"

[<Fact>]
let ``test interpolated string with double braces should be unescaped`` () =
    $"{{ {100} }}" |> equal "{ 100 }"

[<Fact>]
let ``test interpolated string with format and double braces should be unescaped`` () =
    $"{{ %.2f{100.4566666} }}" |> equal "{ 100.46 }"

[<Fact>]
let ``test interpolated string with consecutive holes work`` () =
    $"""{"foo"}{5}""" |> equal "foo5"
    $"""%s{"foo"}%i{5}""" |> equal "foo5"
    $"""{"foo"}/{5}.fsi""" |> equal "foo/5.fsi"
[<Fact>]
let ``test sprintf "%o" padding and flags work`` () =
    sprintf "%5o|%-5o|%05o" 8 8 8 |> equal "   10|10   |00010"
    sprintf "%+o|% o|%+05o" 8 8 8 |> equal "+10| 10|+0010"
    sprintf "%+o" -1 |> equal "+37777777777"

[<Fact>]
let ``test sprintf "%x" sign flags work`` () =
    sprintf "%+x|% x|%+X" 8 8 255 |> equal "+8| 8|+FF"
    sprintf "%+x" -1 |> equal "+ffffffff"

[<Fact>]
let ``test String.Format with extra formatting works`` () =
    let i = 0.5466788
    let dt = DateTime(2014, 9, 26).AddMinutes(19.)
    String.Format(CultureInfo.InvariantCulture, "{0:F2} {0:P2} {1:yyyy-MM-dd HH:mm}", i, dt)
            .Replace(",", ".").Replace(" %", "%")
    |> equal "0.55 54.67% 2014-09-26 00:19"

[<Fact>]
let ``test String.Format uses .NET formatting for DateOnly, TimeOnly and TimeSpan`` () =
    let d = DateOnly(2024, 1, 2)
    let t = TimeOnly(1, 2, 3)
    let ts = TimeSpan.FromHours(1.)
    String.Format(CultureInfo.InvariantCulture, "{0}", d) |> equal "01/02/2024"
    String.Format(CultureInfo.InvariantCulture, "{0:O}", d) |> equal "2024-01-02"
    String.Format(CultureInfo.InvariantCulture, "{0}", t) |> equal "01:02"
    String.Format(CultureInfo.InvariantCulture, "{0:T}", t) |> equal "01:02:03"
    String.Format(CultureInfo.InvariantCulture, "{0}", ts) |> equal "01:00:00"
    String.Format(CultureInfo.InvariantCulture, "{0:g}", ts) |> equal "1:00:00"
    String.Format(CultureInfo.InvariantCulture, "{0} {1} {2}", d, t, ts)
    |> equal "01/02/2024 01:02 01:00:00"

[<Fact>]
let ``test String.Split with trim and remove entries works`` () =
    " a-- b- c ".Split([| "-" |], 2, StringSplitOptions.RemoveEmptyEntries ||| StringSplitOptions.TrimEntries)
    |> equal [|"a"; "b- c"|]
    " a-- b- c ".Split([| '-' |], 3, StringSplitOptions.RemoveEmptyEntries ||| StringSplitOptions.TrimEntries)
    |> equal  [|"a"; "b"; "c"|]

[<Fact>]
let ``test String.IndexOf with index and OrdinalIgnoreCase StringComparison`` () =
    "ABCDBC".IndexOf("b", 2, StringComparison.OrdinalIgnoreCase) |> equal 4
    "ABCDBC".IndexOf("b", 2, StringComparison.Ordinal) |> equal -1

[<Fact>]
let ``test String.LastIndexOf with OrdinalIgnoreCase StringComparison`` () =
    "ABCDBC".LastIndexOf("b", StringComparison.OrdinalIgnoreCase) |> equal 4
    "ABCDBC".LastIndexOf("b", StringComparison.Ordinal) |> equal -1
    "ABCDBC".LastIndexOf("b", StringComparison.InvariantCultureIgnoreCase) |> equal 4

[<Fact>]
let ``test String.LastIndexOf with index and OrdinalIgnoreCase StringComparison`` () =
    "ABCDBC".LastIndexOf("b", 3, StringComparison.OrdinalIgnoreCase) |> equal 1
    "ABCDBC".LastIndexOf("b", 3, StringComparison.Ordinal) |> equal -1


// ---- ported from tests/Js/Main (2026-11-16) ----

[<Fact>]
let ``test sprintf "%O" with overloaded string works`` () =
    let o = Test(5)
    sprintf "%O" o |> equal "10"

[<Fact>]
let ``test sprintf "%A" with overloaded string works`` () =
    let o = Test(5)
    (sprintf "%A" o).Replace("\"", "") |> equal "10"

[<Fact>]
let ``test %O in interpolated strings works recursively`` () =
    // See #3078
    let b = B()
    $"b=(%O{b})" |> equal "b=(a=6)"
    $"%O{b}%O{b}" |> equal "a=7a=8"

[<Fact>]
let ``test String.Format should fail if there are less arguments than placeholders`` () =
    // See #2768
    throwsAnyError <| fun () -> String.Format ("Hello {0}", args = Array.empty)

[<Fact>]
let ``test String.Format treats null arguments as empty`` () =
    // See #5162
    let n: string = null
    let o: obj = null
    String.Format("a{0}b", n) |> equal "ab"
    String.Format("a{0}b", o) |> equal "ab"
    String.Format("[{0,3}]", n) |> equal "[   ]"

[<Fact>]
let ``test System.String.Concat treats null arguments as empty`` () =
    // See #5167
    String.Concat("a", (null: string), "b") |> equal "ab"
    String.Concat((null: string), "b") |> equal "b"
    String.Concat([| "a"; null; "b" |]) |> equal "ab"
    String.Concat(box "a", null, box 1) |> equal "a1"

[<Fact>]
let ``test kbprintf works`` () =
    let sb = System.Text.StringBuilder()
    let mutable i = 0
    let f () = i <- i + 1
    Printf.kbprintf f sb "Hello"
    Printf.kbprintf f sb " %s!" "world"
    i |> equal 2
    sb.ToString() |> equal "Hello world!"

[<Fact>]
let ``test bprintf works`` () =
    let sb = System.Text.StringBuilder(10)
    Printf.bprintf sb "Hello"
    Printf.bprintf sb " %s!" "world"
    sb.ToString() |> equal "Hello world!"
[<Fact>]
let ``test ksprintf curries correctly`` () =
    let append (a: string) b = a + b
    let step1 = Printf.ksprintf append "%d"
    let step2 = step1 42
    let result = step2 "The answer is: "
    result |> equal "42The answer is: "

[<Fact>]
let ``test input of interpolated print format can be retrieved`` () =
    // See #3969
    let f (fmt: Printf.StringFormat<string>) = fmt.Value, sprintf fmt
    let x, s = 42, "z"
    f $"wow %d{x}" |> equal ("wow %d%P()", "wow 42")
    f $"a %d{x} b %s{s} c {x + 1}" |> equal ("a %d%P() b %s%P() c %P()", "a 42 b z c 43")

[<Fact>]
let ``test System.String.Normalize works`` () =
    let name1 = "\u0041\u006d\u00e9\u006c\u0069\u0065";
    let name2 = "\u0041\u006d\u0065\u0301\u006c\u0069\u0065";
    notEqual name1 name2

    let normalized1 = name1.Normalize System.Text.NormalizationForm.FormC
    let normalized2 = name2.Normalize System.Text.NormalizationForm.FormC
    equal normalized1 normalized2


[<Fact>]
let ``test String.Normalize gives each of Unicode's forms`` () =
    let hex (s: string) = s |> Seq.map (fun c -> (int c).ToString("X4")) |> String.concat " "
    let forms (s: string) =
        [ System.Text.NormalizationForm.FormC; System.Text.NormalizationForm.FormD
          System.Text.NormalizationForm.FormKC; System.Text.NormalizationForm.FormKD ]
        |> List.map (fun f -> hex (s.Normalize f))
    forms "é" |> equal [ "00E9"; "0065 0301"; "00E9"; "0065 0301" ]
    forms "ﬁ" |> equal [ "FB01"; "FB01"; "0066 0069"; "0066 0069" ]
    forms "한" |> equal [ "D55C"; "1112 1161 11AB"; "D55C"; "1112 1161 11AB" ]
    forms "ḍ̇" |> equal [ "1E0D 0307"; "0064 0323 0307"; "1E0D 0307"; "0064 0323 0307" ]
    forms "Å" |> equal [ "00C5"; "0041 030A"; "00C5"; "0041 030A" ]
    "é".IsNormalized() |> equal false
    "é".IsNormalized(System.Text.NormalizationForm.FormD) |> equal true
    hex ("\uDC00".Normalize()) |> equal "FFFD"
    throwsAnyError (fun () -> "a￾".Normalize() |> ignore)


// ---- ported from tests/Js/Main (2026-11-16, remaining) ----

[<Fact>]
let ``test Fix #2398: Exception when two successive string format placeholders and value of first one ends in %`` () =
    sprintf "%c%s" '%' "text" |> equal "%text"

[<Fact>]
let ``test Interpolated strings keep empty lines`` () =
    let s1 = $"""1


    {1+1}


3"""
    let s2 = """1


    2


3"""
    equal s1 s2
    equal s1.Length s2.Length

[<Fact>]
let ``test Can use backslash is interpolated strings`` () =
    $"\n{1+1}\n" |> equal """
2
"""

#if !FABLE_COMPILER_ZIG // (a format known only when the program runs, given its values: printf whose type F# takes from each use)
[<Fact>]
let ``test Printf works with generic argument`` () =
    spr "bar %s" "a" |> equal "bar a"
    spr "foo %i %i" 3 5 |> equal "foo 3 5"
    let f1 = spr "foo %i %i"
    let f2 = f1 2
    f2 2 |> equal "foo 2 2"
    let f1 = spr "foo %i %i %i"
    let f2 = f1 2
    let f3 = f2 2
    f3 2 |> equal "foo 2 2 2"
#endif
[<Fact>]
let ``test String literal addition is optimized`` () =
    "bar" + aLiteral |> equal "barfoo"
    "bar" + notALiteral |> equal "barfoo"

[<Fact>]
let ``test Unions with sprintf %A`` () =
    Bar(1,5) |> sprintf "%A" |> equal "Bar (1, 5)"
    Foo1 4.5 |> sprintf "%A" |> equal "Foo1 4.5"
    Foo4 Foo3 |> sprintf "%A" |> equal "Foo4 Foo3"
    Foo4(Foo1 4.5) |> sprintf "%A" |> equal "Foo4 (Foo1 4.5)"
    Foo3 |> sprintf "%A" |> equal "Foo3"

[<Fact>]
let ``test Unions with string operator`` () =
    Bar(1,5) |> string |> equal "Bar (1, 5)"
    Foo1 4.5 |> string |> equal "Foo1 4.5"
    Foo4 Foo3 |> string |> equal "Foo4 Foo3"
    Foo4(Foo1 4.5) |>string |> equal "Foo4 (Foo1 4.5)"
    Foo3 |> string |> equal "Foo3"

