module QuickTest

// What the Zig target compiles so far: numbers and booleans, let, if, loops, operators,
// functions (also recursive and across files) and pattern matching on values.
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
