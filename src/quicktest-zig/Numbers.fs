module Numbers

// Math, rounding, parsing and sums, with .NET's results and exceptions.
// `run` returns the number of failed checks.

open Fable.Core.Zig

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
    | :? System.OverflowException as e -> "Overflow: " + e.Message
    | :? System.FormatException as e -> "Format: " + e.Message
    | :? System.ArithmeticException as e -> "Arithmetic: " + e.Message
    | :? System.ArgumentException as e -> "Argument: " + e.Message
    | e -> "other: " + e.Message

let parseOr (s: string) : int =
    match System.Int32.TryParse s with
    | true, v -> v
    | _ -> -1

let run () : int =
    let minInt = System.Int32.MinValue
    let x = 2.5

    let failed =
        same
            "5|-1|0|2.5"
            (string (abs -5)
             + "|"
             + string (sign -3.0)
             + "|"
             + string (sign 0)
             + "|"
             + string (abs -2.5))
        + same
            "Overflow: Negating the minimum value of a twos complement number is invalid."
            (raised (fun () -> string (abs minInt)))
        + same
            "Arithmetic: Function does not accept floating point Not-a-Number values."
            (raised (fun () -> string (sign nan)))
        + same
            "1024|0.25|1|1.4142135623730951"
            (string (pown 2 10)
             + "|"
             + string (pown 2.0 -2)
             + "|"
             + string (pown 3 0)
             + "|"
             + string (2.0 ** 0.5))
        + same
            "2|4|-2|2.57|-2|3"
            (string (round x)
             + "|"
             + string (round 3.5)
             + "|"
             + string (round -x)
             + "|"
             + string (System.Math.Round(2.567, 2))
             + "|"
             + string (truncate -2.7)
             + "|"
             + string (ceil 2.1))
        + same
            "4|3|3.141592653589793|0.7853981633974483|3|3"
            (string (System.Math.Max(3, 4))
             + "|"
             + string (System.Math.Clamp(5, 1, 3))
             + "|"
             + string System.Math.PI
             + "|"
             + string (System.Math.Atan2(1.0, 1.0))
             + "|"
             + string (log10 1000.0)
             + "|"
             + string (System.Math.Log(8.0, 2.0)))
        + check (
            sqrt 16.0 = 4.0
            && floor -1.5 = -2.0
            && exp 0.0 = 1.0
            && log 1.0 = 0.0
            && sin 0.0 = 0.0
            && cos 0.0 = 1.0
        )
        + same
            "42|-7|5|123|31|5|15|10"
            (string (int "42")
             + "|"
             + string (int " -7 ")
             + "|"
             + string (int "+5")
             + "|"
             + string (System.Int32.Parse "123")
             + "|"
             + string (int "0x1F")
             + "|"
             + string (int "0b101")
             + "|"
             + string (int "0o17")
             + "|"
             + string (int "1_0"))
        + same "Format: The input string '4x' was not in a correct format." (raised (fun () -> string (int "4x")))
        + same "Format: Input string was not in a correct format." (raised (fun () -> string (int "")))
        + same
            "Overflow: Value was either too large or too small for an Int32."
            (raised (fun () -> string (int "99999999999")))
        + same "Overflow: Arithmetic operation resulted in an overflow." (raised (fun () -> string (byte "256")))
        + same
            "Format: The input string '0x1F' was not in a correct format."
            (raised (fun () -> string (System.Int32.Parse "0x1F")))
        + same
            "Overflow: Value was either too large or too small for an unsigned byte."
            (raised (fun () -> string (System.Byte.Parse "300")))
        + same
            "3.5|1000|-0.25|NaN|Infinity|0.5"
            (string (float "3.5")
             + "|"
             + string (float " 1e3 ")
             + "|"
             + string (float "-0.25")
             + "|"
             + string (float "NaN")
             + "|"
             + string (float "Infinity")
             + "|"
             + string (float ".5"))
        + same "Format: The input string 'abc' was not in a correct format." (raised (fun () -> string (float "abc")))
        + check (parseOr "12" = 12 && parseOr "x" = -1 && parseOr " 7 " = 7)
        + check (
            int64 "9223372036854775807" = 9223372036854775807L
            && uint32 "4294967295" = 4294967295u
            && System.Boolean.Parse "True"
        )
        + same
            "6|0|2.3333333333333335|6|1.5"
            (string (List.sum [ 1; 2; 3 ])
             + "|"
             + string (List.sum ([]: int list))
             + "|"
             + string (List.average [ 1.0; 2.0; 4.0 ])
             + "|"
             + string (List.sumBy (fun x -> x * 2) [ 1; 2 ])
             + "|"
             + string (List.averageBy float [ 1; 2 ]))
        + same
            "Argument: The input sequence was empty. (Parameter 'source')"
            (raised (fun () -> string (List.average ([]: float list))))
        + check (Array.sum [| 1; 2; 3 |] = 6 && Array.average [| 1.0; 3.0 |] = 2.0)
        // bigint
        + same
            "15241578753238836750495351562536198787501905199875019052100|17636684144620811271604938270|0|-17636684144620811271604938270|1267650600228229401496703205376"
            (let a = 123456789012345678901234567890I in

             string (a * a)
             + "|"
             + string (a / 7I)
             + "|"
             + string (a % 7I)
             + "|"
             + string (-a / 7I)
             + "|"
             + string (bigint.Pow(2I, 100)))
        + same
            "1TrueTrue4242|1.2345678901234568E+29"
            (let a = 123456789012345678901234567890I in

             string (compare a 1I)
             + string (a = a + 0I)
             + string (abs -a = a)
             + string (bigint 42)
             + string (int 42I)
             + "|"
             + string (float a))
        + same "Arithmetic: Attempted to divide by zero." (raised (fun () -> string (5I / 0I)))
        + same
            "Overflow: Value was either too large or too small for an Int32."
            (raised (fun () -> string (int 123456789012345678901I)))
        + same "Format: The value could not be parsed." (raised (fun () -> string (bigint.Parse "12x")))
        + same
            "-123|265252859812191058636308480000000|[1; 2]|6"
            (string (bigint.Parse " -123 ")
             + "|"
             + string (Seq.fold (fun acc (n: int) -> acc * bigint n) 1I [ 1..30 ])
             + "|"
             + sprintf "%A" [ 1I; 2I ]
             + "|"
             + string (List.sum [ 1I; 2I; 3I ]))
        + check (hash 5I = hash 5I && max 3I 4I = 4I && 2I < 3I && sign -4I = -1)
        // decimal
        + same
            "3.0476818181818181818181818182|2.345|2|5|1.5|1.5|1|false|true"
            (let x, y = 2.345m, 1.10m in

             sprintf
                 "%s|%s|%d|%M|%M|%M|%d|%b|%b"
                 (string (x * y + 1.5m - x / y % y))
                 (string x)
                 (int x)
                 (decimal 5)
                 (decimal 1.5)
                 (decimal "1.5")
                 (compare x 1m)
                 (x = 2m)
                 (x < 3m))
        + same
            "2.345|-2.345|2.345000|12|2|2|2.34|1|2.35|2.345 2.35|1,234.50"
            (let x = 2.345m in

             sprintf
                 "%M|%M|%f|%M|%M|%M|%M|%d|%s|%s|%s"
                 (abs -x)
                 (-x)
                 (float x)
                 (System.Decimal.Parse "12")
                 (round x)
                 (floor x)
                 (System.Math.Round(x, 2))
                 (sign x)
                 (x.ToString("F2"))
                 (sprintf "%M %.2f" x x)
                 ((1234.5m).ToString("N2")))
        + same
            "2.345|3.5|1.5|79228162514264337593543950335|0.3333333333333333333333333333|[1.5M; 2M]"
            (sprintf
                "%M|%M|%M|%M|%s|%A"
                (max 2.345m 1m)
                (List.sum [ 1m; 2.5m ])
                (List.average [ 1m; 2m ])
                System.Decimal.MaxValue
                (string (1m / 3m))
                [ 1.5m; 2m ])
        + same
            "Overflow: Value was either too large or too small for a Decimal."
            (raised (fun () -> string (System.Decimal.MaxValue + 1m)))
        + same "Arithmetic: Attempted to divide by zero." (raised (fun () -> string (1m / 0m)))
        + same "Overflow: Value was either too large or too small for an Int32." (raised (fun () -> string (int 1e20m)))
        + same
            "Format: The input string '1.5x' was not in a correct format."
            (raised (fun () -> string (System.Decimal.Parse "1.5x")))
        + check (
            1.0m = 1.00m
            && hash 1.0m = hash 1.00m
            && Some 1.0m = Some 1.00m
            && (1.0m, "a") = (1.00m, "a")
            && Array.sum [| 1.5m; 2m |] = 3.5m
        )
        + same
            "3.14|42|0x2A|1.500"
            ((3.14159).ToString("F2")
             + "|"
             + (42).ToString("D")
             + "|0x"
             + (42).ToString("X")
             + "|"
             + (1.5).ToString("F3"))
        // .NET's custom numeric formats
        + same
            "1234.57|1,234.6|50%|0042|-3.142|1,234,567||12.00|1.5|(1.5)|zero|1.01|0.13|-0.00|1,235|1.23E+3|(555) 123-4567|$1,234.57|#0"
            ((1234.5678).ToString("0.00")
             + "|"
             + (1234.5678).ToString("#,##0.0")
             + "|"
             + (0.5).ToString("0%")
             + "|"
             + (42).ToString("0000")
             + "|"
             + (-3.14159).ToString("0.###")
             + "|"
             + (1234567).ToString("#,#")
             + "|"
             + (0.0).ToString("#.##")
             + "|"
             + (12.0).ToString("00.00")
             + "|"
             + (1.5).ToString("0.0;(0.0);zero")
             + "|"
             + (-1.5).ToString("0.0;(0.0);zero")
             + "|"
             + (0.0).ToString("0.0;(0.0);zero")
             + "|"
             + (1.005).ToString("0.00")
             + "|"
             + (0.125).ToString("0.00")
             + "|"
             + (-0.001).ToString("0.00")
             + "|"
             + (1234567.0).ToString("#,##0,")
             + "|"
             + (1234.5678).ToString("0.00E+0")
             + "|"
             + (5551234567.0).ToString("(###) ###-####")
             + "|"
             + (1234.5678).ToString("'$'#,##0.00")
             + "|"
             + (0.4).ToString("\\#0"))
        + same
            "3.14|1,234,567|     2.3|007|1.01|(2.3)"
            (System.String.Format("{0:0.00}|{1:#,##0}|{2,8:0.0}|{3:000}", 3.14159, 1234567, 2.25, 7)
             + "|"
             + System.String.Format("{0:0.00}|{1:0.0;(0.0)}", 1.005m, -2.345m))
        // `open Checked`
        + same
            "Overflow: Arithmetic operation resulted in an overflow."
            (raised (fun () -> string (Checked.(+) System.Int32.MaxValue 1)))
        + same
            "Overflow: Arithmetic operation resulted in an overflow."
            (raised (fun () -> string (Checked.(*) System.Int32.MaxValue 2)))
        + same
            "Overflow: Arithmetic operation resulted in an overflow."
            (raised (fun () -> string (Checked.(~-) System.Int32.MinValue)))
        + same
            "Overflow: Arithmetic operation resulted in an overflow."
            (raised (fun () -> string (Checked.int 3000000000L)))
        + same "Overflow: Arithmetic operation resulted in an overflow." (raised (fun () -> string (Checked.byte 300)))
        + same "Overflow: Arithmetic operation resulted in an overflow." (raised (fun () -> string (Checked.int 1e10)))
        + check (
            Checked.(+) 2 3 = 5
            && Checked.(-) 2 3 = -1
            && Checked.int 7L = 7
            && Checked.(+) 1.5 1.0 = 2.5
        )

    printfn "numbers: %d" failed
    failed
