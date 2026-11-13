module QuickTest

// What the Zig target compiles so far: numbers and booleans, let, if, loops, operators,
// functions (also recursive and across files), pattern matching, records, unions, tuples
// and options. Heap.fs and Stress.fs cover recursive unions (reference-counted cells),
// Functions.fs covers lambdas, local functions and function values, Generics.fs covers
// generic types and functions and F#'s list, Exceptions.fs covers raise and try,
// Records.fs covers records that can be assigned and ref cells, Cycles.fs covers
// structures that reach themselves, Strings.fs covers strings, formatting, printing and
// exceptions with messages, Text.fs covers the string functions, null strings, `%A`, .NET
// formats and what .NET raises on its own (division by zero, a match without a case).
// The entry point returns the number of failed checks as the process exit code.

let limit = 10

let add (a: int) (b: int) : int = a + b

let rec fib (n: int) : int =
    if n < 2 then
        n
    else
        fib (n - 1) + fib (n - 2)

let rec gcd (a: int) (b: int) : int =
    if b = 0 then
        a
    else
        gcd b (a % b)

let sumTo (n: int) : int =
    let mutable acc = 0

    for i in 1..n do
        acc <- acc + i

    acc

let countDown (n: int) : int =
    let mutable steps = 0
    let mutable x = n

    while x > 0 do
        x <- x - 3
        steps <- steps + 1

    steps

let describe (x: int) : int =
    match x with
    | 0 -> 100
    | 1
    | 2 -> 200
    | n when n < 0 -> -1
    | _ -> 300

let bits (x: int) : int =
    ((x <<< 3) ||| 5) ^^^ (x >>> 1) &&& 0xFF

let mean (a: float) (b: float) : float = (a + b) / 2.0

let wrapsAround () : bool =
    let big = 2147483647
    big + 1 < 0

let check (ok: bool) : int =
    if ok then
        0
    else
        1

// ---- records ----
type Vec =
    {
        Dx: int
        Dy: int
    }

type Segment =
    {
        From: Helpers.Point
        Delta: Vec
        Weight: float
    }

let translate (p: Helpers.Point) (v: Vec) : Helpers.Point =
    {
        X = p.X + v.Dx
        Y = p.Y + v.Dy
    }

let endOf (s: Segment) : Helpers.Point = translate s.From s.Delta

let heavier (s: Segment) : Segment = { s with Weight = s.Weight * 2.0 }

// ---- unions ----
type Command =
    | Move of Vec
    | Scale of factor: int
    | Reset
    | Pair of Command2 * int

and Command2 =
    | Up
    | Down

let apply (p: Helpers.Point) (c: Command) : Helpers.Point =
    match c with
    | Move v -> translate p v
    | Scale k ->
        {
            X = p.X * k
            Y = p.Y * k
        }
    | Reset -> Helpers.origin ()
    | Pair(Up, n) -> { p with Y = p.Y + n }
    | Pair(Down, n) -> { p with Y = p.Y - n }

let tagOf (c: Command) : int =
    match c with
    | Move _ -> 0
    | Scale _ -> 1
    | Reset -> 2
    | Pair _ -> 3

// ---- tuples ----
let divMod (a: int) (b: int) : int * int = (a / b, a % b)

let swap (pair: int * bool) : bool * int =
    let (n, flag) = pair
    (flag, n)

let minMax (a: int) (b: int) (c: int) : int * int =
    let lo =
        if a < b then
            (if a < c then
                 a
             else
                 c)
        else
            (if b < c then
                 b
             else
                 c)

    let hi =
        if a > b then
            (if a > c then
                 a
             else
                 c)
        else
            (if b > c then
                 b
             else
                 c)

    lo, hi

// ---- options ----
let safeDiv (a: int) (b: int) : int option =
    if b = 0 then
        None
    else
        Some(a / b)

let orZero (o: int option) : int =
    match o with
    | Some v -> v
    | None -> 0

let firstPositive (a: int) (b: int) : Vec option =
    if a > 0 then
        Some
            {
                Dx = a
                Dy = 0
            }
    elif b > 0 then
        Some
            {
                Dx = 0
                Dy = b
            }
    else
        None

let nested (o: int option option) : int =
    match o with
    | None -> -1
    | Some None -> 0
    | Some(Some v) -> v

let lengthOf (v: Vec voption) : int =
    match v with
    | ValueSome d -> d.Dx + d.Dy
    | ValueNone -> -1

let typesWork () : int =
    let p =
        {
            Helpers.X = 1
            Helpers.Y = 2
        }

    let seg =
        {
            From = p
            Delta =
                {
                    Dx = 10
                    Dy = 20
                }
            Weight = 1.5
        }

    let q, r = divMod 17 5
    let lo, hi = minMax 4 9 2

    check (
        endOf seg =
            {
                Helpers.X = 11
                Helpers.Y = 22
            }
    )
    + check ((heavier seg).Weight = 3.0 && (heavier seg).From = p)
    + check (seg <> heavier seg)
    + check (
        apply
            p
            (Move
                {
                    Dx = 1
                    Dy = 1
                }) =
            {
                Helpers.X = 2
                Helpers.Y = 3
            }
    )
    + check (
        apply p (Scale 3) =
            {
                Helpers.X = 3
                Helpers.Y = 6
            }
    )
    + check (apply p Reset = Helpers.origin ())
    + check ((apply p (Pair(Down, 5))).Y = -3)
    + check (tagOf (Pair(Up, 1)) = 3 && tagOf Reset = 2)
    + check (
        Move
            {
                Dx = 1
                Dy = 2
            }
            =
            Move
                {
                    Dx = 1
                    Dy = 2
                }
        && Move
            {
                Dx = 1
                Dy = 2
            }
           <> Scale 1
    )
    + check (Helpers.area (Helpers.Rect(2.0, 4.0)) = 8.0 && Helpers.area Helpers.Dot = 0.0)
    + check (Helpers.area (Helpers.Circle 2.0) = 12.0)
    + check (q = 3 && r = 2)
    + check (swap (7, true) = (true, 7))
    + check (lo = 2 && hi = 9)
    + check (safeDiv 7 2 = Some 3 && safeDiv 7 0 = None)
    + check (orZero (safeDiv 9 3) = 3 && orZero None = 0)
    + check (
        firstPositive 0 5 =
            Some
                {
                    Dx = 0
                    Dy = 5
                }
        && firstPositive 0 0 = None
    )
    + check (nested None = -1 && nested (Some None) = 0 && nested (Some(Some 42)) = 42)
    + check (
        lengthOf (
            ValueSome
                {
                    Dx = 3
                    Dy = 4
                }
        )
            =
            7
        && lengthOf ValueNone = -1
    )

// ---- calls into FSharp.Core (kept under their .NET names, resolved by the target) ----
let conversions () : int =
    let big = 300
    let neg = -5
    let x = 3.99

    check (byte big = 44uy && sbyte 200 = -56y)
    + check (int64 neg = -5L && uint64 neg = 18446744073709551611UL)
    + check (int x = 3 && int -x = -3 && int 1e30 = 2147483647)
    + check (float big = 300.0 && float32 big = 300.0f)
    + check (uint32 neg = 4294967291u && int (uint32 neg) = -5)
    + check (int 'A' = 65 && char 66 = 'B')

let coreFunctions () : int =
    let pair = (7, true)
    ignore (add 1 2)

    check (fst pair = 7 && snd pair)
    + check (not (snd pair) = false)
    + check (id 5 = 5)

[<EntryPoint>]
let main _ =
    check (add 3 4 = 7)
    + check (fib 20 = 6765)
    + check (gcd 1071 462 = 21)
    + check (sumTo limit = 55)
    + check (countDown 10 = 4)
    + check (describe 0 = 100 && describe 2 = 200 && describe -5 = -1 && describe 9 = 300)
    + check (bits 77 = (((77 <<< 3) ||| 5) ^^^ (77 >>> 1) &&& 0xFF))
    + check (mean 1.0 4.0 = 2.5)
    + check (wrapsAround ())
    + check (Helpers.clamp 0 10 42 = 10 && Helpers.isEven 4 && not (Helpers.isEven 7))
    + typesWork ()
    + conversions ()
    + coreFunctions ()
    + Heap.run ()
    + Stress.run ()
    + Functions.run ()
    + Generics.run ()
    + Exceptions.run ()
    + Records.run ()
    + Cycles.run ()
    + Strings.run ()
    + Text.run ()
    + Arrays.run ()
    + Members.run ()
    + Values.run ()
    + Lists.run ()
    + Order.run ()
    + Numbers.run ()
    + Maps.run ()
    + Loops.run ()
    + Features.run ()
    + Classes.run ()
    + Sequences.run ()
    + Computations.run ()
