module Fable.Tests.Zig.ArithmeticTests

open System
open Fable.Tests.Util
open Fable.Tests.Util
open Fable.Tests.Util.Testing

#if FABLE_COMPILER
open Fable.Core
#endif

#nowarn "3370" // Silence deprecation warnings for incr/decr

let [<Literal>] posLiteral = 5
let [<Literal>] negLiteral = -345
let notALiteral = 5

let checkTo3dp (expected: float) actual =
    floor (actual * 1000.) |> equal expected

let moduleSinglePositiveInfinity = Single.PositiveInfinity
let moduleSingleNegativeInfinity = Single.NegativeInfinity
let moduleSingleNaN = Single.NaN

[<Fact>]
let ``test Adding floats works`` () =
    3.141 + 2.85 |> equal 5.991

[<Fact>]
let ``test Infix add can be generated`` () =
    4 + 2 |> equal 6

[<Fact>]
let ``test Int32 literal addition is optimized`` () =
    posLiteral + 7 |> equal 12
    notALiteral + 7 |> equal 12

[<Fact>]
let ``test Unary negation with negative literal values works`` () =
    -negLiteral |> equal 345

[<Fact>]
let ``test Unary negation with integer MinValue works`` () =
    -(-128y) |> equal SByte.MinValue
    -(-32768s) |> equal Int16.MinValue
    -(-2147483648) |> equal Int32.MinValue
    -(-9223372036854775808L) |> equal Int64.MinValue

[<Fact>]
let ``test Infix subtract can be generated`` () =
    4 - 2 |> equal 2

[<Fact>]
let ``test Infix multiply can be generated`` () =
    4 * 2 |> equal 8

[<Fact>]
let ``test Infix divide can be generated`` () =
    4 / 2 |> equal 2

[<Fact>]
let ``test Integer division doesn't produce floats`` () =
    5. / 2. |> equal 2.5
    5 / 2 |> equal 2
    5 / 3 |> equal 1
    float 5 / 2. |> equal 2.5

[<Fact>]
let ``test Infix modulo can be generated`` () =
    4 % 3 |> equal 1
    5 % 3 |> equal 2

[<Fact>]
let ``test Infix modulo with negative numbers`` () =
    -5 % 3 |> equal -2
    5 % -3 |> equal 2
    -5 % -3 |> equal -2

[<Fact>]
let ``test Math.DivRem works with bytes`` () =
    Math.DivRem(5y, 2y) |> equal struct (2y, 1y)
    Math.DivRem(4y, 2y) |> equal struct (2y, 0y)

[<Fact>]
let ``test Math.DivRem works with ints`` () =
    Math.DivRem(5, 2) |> equal struct (2, 1)
    Math.DivRem(4, 2) |> equal struct (2, 0)

[<Fact>]
let ``test Math.DivRem works with longs`` () =
    Math.DivRem(5L, 2L) |> equal struct (2L, 1L)
    Math.DivRem(4L, 2L) |> equal struct (2L, 0L)

[<Fact>]
let ``test Math.DivRem works with ints and outref`` () =
    let mutable rem = -1
    Math.DivRem(5, 2, &rem) |> equal 2
    rem |> equal 1
    Math.DivRem(4, 2, &rem) |> equal 2
    rem |> equal 0

[<Fact>]
let ``test Math.DivRem works with longs and outref`` () =
    let mutable rem = -1L
    Math.DivRem(5L, 2L, &rem) |> equal 2L
    rem |> equal 1L
    Math.DivRem(4L, 2L, &rem) |> equal 2L
    rem |> equal 0L

[<Fact>]
let ``test Evaluation order is preserved by generated code`` () =
    (4 - 2) * 2 + 1 |> equal 5

// Int32 is a plain Python `int` on the Python target, which is arbitrary precision,
// so the compiler normalizes results back into 32 bits. These use function
// parameters rather than literals so the values are not constant-folded away and
// the runtime normalization path is exercised. All expectations verified on .NET.
let private addI (a: int) (b: int) = a + b
let private mulI (a: int) (b: int) = a * b
let private divI (a: int) (b: int) = a / b
let private remI (a: int) (b: int) = a % b
let private shlI (a: int) (n: int) = a <<< n
let private shrI (a: int) (n: int) = a >>> n

[<Fact>]
let ``test Int32 arithmetic wraps at 32 bits`` () =
    let a = addI 2000000000 0
    let b = addI 1500000000 0
    addI a a |> equal -294967296
    mulI a a |> equal -1651507200
    addI (addI a a) a |> equal 1705032704
    addI (mulI a b) a |> equal 1835111424
    addI 2147483647 1 |> equal -2147483648
    -(addI -2147483648 0) |> equal -2147483648

[<Fact>]
let ``test Int32 operands are normalized before non-wrapping operations`` () =
    // Normalization commutes with + - * <<< so it can happen once per expression
    // tree, but these consumers must see the already-wrapped value.
    let a = addI 2000000000 0
    divI (addI a a) 2 |> equal -147483648
    remI (addI a a) 7 |> equal -1
    (addI a a) &&& 0xFF |> equal 0
    (addI a a) > 0 |> equal false
    string (addI a a) |> equal "-294967296"
    shrI (addI a a) 4 |> equal -18435456

[<Fact>]
let ``test Int32 division truncates toward zero`` () =
    // Python's // floors: -7 // 2 is -4 there and -3 in .NET
    divI -7 2 |> equal -3
    divI 7 -2 |> equal -3
    divI -7 -2 |> equal 3
    divI 7 2 |> equal 3

[<Fact>]
let ``test Int32 remainder takes the sign of the dividend`` () =
    // Python's % takes the sign of the divisor: -5 % 3 is 1 there and -2 in .NET
    remI -5 3 |> equal -2
    remI 5 -3 |> equal 2
    remI -5 -3 |> equal -2
    remI 5 3 |> equal 2
    remI 6 3 |> equal 0
    remI -6 3 |> equal 0

[<Fact>]
let ``test Int32 shift counts are masked at runtime`` () =
    shlI 1 32 |> equal 1
    shlI 1 33 |> equal 2
    shlI 3 31 |> equal -2147483648
    shrI -1 32 |> equal -1
    shrI -2 1 |> equal -1

// Float64 is a plain Python `float` on the Python target -- an IEEE double, so
// arithmetic needs no adjustment. Only `/` by zero and `%` diverge: Python raises
// where .NET yields +/-inf or nan, and Python's float `%` takes the sign of the
// divisor where .NET takes the dividend's. Non-literal operands keep the runtime
// path in play. All expectations verified on .NET.
let private divF (a: float) (b: float) = a / b
let private remF (a: float) (b: float) = a % b

[<Fact>]
let ``test Float division by zero yields infinity at runtime`` () =
    divF 1.0 0.0 |> Double.IsPositiveInfinity |> equal true
    divF -1.0 0.0 |> Double.IsNegativeInfinity |> equal true
    divF 1.0 -0.0 |> Double.IsNegativeInfinity |> equal true
    divF -1.0 -0.0 |> Double.IsPositiveInfinity |> equal true
    divF 0.0 0.0 |> Double.IsNaN |> equal true
    divF infinity 0.0 |> Double.IsPositiveInfinity |> equal true
    divF 1.0 2.0 |> equal 0.5

[<Fact>]
let ``test Float remainder takes the sign of the dividend`` () =
    remF -5.0 3.0 |> equal -2.0
    remF 5.0 -3.0 |> equal 2.0
    remF -5.0 -3.0 |> equal -2.0
    remF 5.0 3.0 |> equal 2.0

[<Fact>]
let ``test Float remainder edge cases yield NaN`` () =
    remF 5.0 0.0 |> Double.IsNaN |> equal true
    remF infinity 2.0 |> Double.IsNaN |> equal true
    remF nan 2.0 |> Double.IsNaN |> equal true
    remF 5.0 infinity |> equal 5.0
    remF -5.0 infinity |> equal -5.0

// Rendering a plain Python `float` has to shorten a whole double ("5", not "5.0") and
// spell the non-finite values out, and the two interact: the shortening runs `int()`,
// which raises OverflowError on the infinities and ValueError on NaN. Non-literal
// operands keep the runtime path in play. All expectations verified on .NET.
let private strF (x: float) = string x

[<Fact>]
let ``test Float to string spells the non-finite values out`` () =
    strF infinity |> equal "Infinity"
    strF -infinity |> equal "-Infinity"
    strF nan |> equal "NaN"
    strF 5.0 |> equal "5"
    strF 2.5 |> equal "2.5"
    strF -0.5 |> equal "-0.5"

[<Fact>]
let ``test Float printf formatting handles the non-finite values`` () =
    sprintf "%f" (divF 1.0 0.0) |> equal "Infinity"
    sprintf "%f" (divF -1.0 0.0) |> equal "-Infinity"
    sprintf "%f" (divF 0.0 0.0) |> equal "NaN"
    sprintf "%f" 2.5 |> equal "2.500000"
    sprintf "%g" (divF 1.0 0.0) |> equal "Infinity"

[<Fact>]
let ``test Bitwise and can be generated`` () =
    6 &&& 2 |> equal 2

[<Fact>]
let ``test Bitwise or can be generated`` () =
    4 ||| 2 |> equal 6

[<Fact>]
let ``test Bitwise shift left can be generated`` () =
    4 <<< 2 |> equal 16

[<Fact>]
let ``test Bitwise shift left with unsigned integer works`` () =
    1u <<< 31 |> equal 2147483648u

[<Fact>]
let ``test Bitwise shift left discards bits shifted out of the width`` () =
    // Multi-bit values distinguish a shift from a rotation: a rotation would
    // wrap bit 1 around to bit 0 and give -2147483647 here.
    3 <<< 31 |> equal -2147483648
    3y <<< 7 |> equal -128y
    3s <<< 15 |> equal -32768s
    3L <<< 63 |> equal -9223372036854775808L
    3uy <<< 7 |> equal 128uy
    3us <<< 15 |> equal 32768us
    3u <<< 31 |> equal 2147483648u
    3UL <<< 63 |> equal 9223372036854775808UL

[<Fact>]
let ``test Bitwise shift left masks the shift count to the type width`` () =
    1 <<< 32 |> equal 1
    1 <<< 33 |> equal 2
    1y <<< 8 |> equal 1y
    1s <<< 16 |> equal 1s
    1L <<< 64 |> equal 1L
    1uy <<< 9 |> equal 2uy
    1us <<< 16 |> equal 1us
    1u <<< 32 |> equal 1u

[<Fact>]
let ``test Bitwise OR on large unsigned integer works`` () =
    0x80000000u ||| 0u |> equal (0x80000000u ||| 0u >>> 0)
    0x80000000UL||| 0UL|> equal (0x80000000UL||| 0UL>>> 0)

[<Fact>]
let ``test Bitwise AND on large unsigned integer works`` () =
    0x80000000u &&& 0xffffffffu |> equal (0x80000000u &&& 0xffffffffu >>> 0)
    0x80000000UL&&& 0xffffffffUL|> equal (0x80000000UL&&& 0xffffffffUL>>> 0)

[<Fact>]
let ``test Bitwise XOR on large unsigned integer works`` () =
    0x80000000u ^^^ 0u |> equal (0x80000000u ^^^ 0u >>> 0)
    0x80000000UL^^^ 0UL|> equal (0x80000000UL^^^ 0UL>>> 0)

[<Fact>]
let ``test Bitwise NOT on large unsigned integer works`` () =
    (~~~0x80000000u >>> 0) |> equal ~~~0x80000000u
    (~~~0x80000000UL>>> 0) |> equal ~~~0x80000000UL

[<Fact>]
let ``test Bitwise shift right can be generated`` () = // See #1530
    4 >>> 2 |> equal 1

[<Fact>]
let ``test Zero fill shift right for unsigned`` () = // See #646
    0x80000000 >>> 1 |> equal -1073741824
    0x80000000u >>> 1 |> equal 1073741824u
    0x80000000UL >>> 1 |> equal 1073741824UL

[<Fact>]
let ``test Zero fill right shift is logical for unsigned integer types`` () =
    // For unsigned types, >>> is zero-fill (logical) - the high bit is NOT sign-extended
    0xFFuy >>> 1 |> equal 127uy                      // uint8:  0x7F
    0xFFFFus >>> 1 |> equal 32767us                  // uint16: 0x7FFF
    0xFFFFFFFFu >>> 1 |> equal 2147483647u           // uint32: 0x7FFFFFFF
    0xFFFFFFFFFFFFFFFFUL >>> 1 |> equal 9223372036854775807UL  // uint64: 0x7FFFFFFFFFFFFFFF

[<Fact>]
let ``test Arithmetic right shift preserves sign for signed integer types`` () =
    // For signed types, >>> is arithmetic (sign-propagating) - the sign bit IS extended
    -2y >>> 1 |> equal -1y   // int8:  0xFF = -1
    -2s >>> 1 |> equal -1s   // int16: 0xFFFF = -1
    -2 >>> 1 |> equal -1     // int32: 0xFFFFFFFF = -1
    -2L >>> 1 |> equal -1L   // int64: 0xFFFFFFFFFFFFFFFF = -1

[<Fact>]
let ``test UInt64 multiplication with 0 returns uint`` () = // See #1480
    0x0UL * 0x1UL |> equal 0x0UL

[<Fact>]
let ``test Decimal literals can be generated`` () =
    0M |> equal Decimal.Zero
    1M |> equal Decimal.One
    -1M |> equal Decimal.MinusOne
    79228162514264337593543950335M |> equal Decimal.MaxValue
    -79228162514264337593543950335M |> equal Decimal.MinValue

[<Fact>]
let ``test Decimal.ToString works`` () =
    string 001.23456M |> equal "1.23456"
    string 1.23456M |> equal "1.23456"
    string 0.12345M |> equal "0.12345"
    string 0.01234M |> equal "0.01234"
    string 0.00123M |> equal "0.00123"
    string 0.00012M |> equal "0.00012"
    string 0.00001M |> equal "0.00001"
    // FIXME:
    // string 0.00000M |> equal "0.00000"
    // string 0.12300M |> equal "0.12300"
    // string 0.0M |> equal "0.0"
    string 0M |> equal "0"
    string 1M |> equal "1"
    string -1M |> equal "-1"
    string 00000000000000000000000000000.M |> equal "0"
    // FIXME: string 0.0000000000000000000000000000M |> equal "0.0000000000000000000000000000"
    string 79228162514264337593543950335M |> equal "79228162514264337593543950335"
    string -79228162514264337593543950335M |> equal "-79228162514264337593543950335"

[<Fact>]
let ``test Decimal precision is kept`` () =
    let items = [290.8M; 290.8M; 337.12M; 6.08M; -924.8M]
    List.sum items |> equal 0M

[<Fact>]
let ``test Decimal max precision is kept`` () =
    let pi = 3.141592653589793238462643383279502884197169399375105820974944592307816406286M
    string pi |> equal "3.1415926535897932384626433833"

// [<Fact>]
// let ``test Decimal average precision is kept`` () =
//     let items = [1M; 2M; 5M]
//     List.average items |> equal 2.6666666666666666666666666667M

[<Fact>]
let ``test Decimal division precision is kept`` () =
    string (8M / 3M) |> equal "2.6666666666666666666666666667"

[<Fact>]
let ``test Decimal division works`` () =
    let a = decimal 0.00001
    let b = 1000.M
    let c = decimal 0.00000001
    a / b |> equal c

[<Fact>]
let ``test Decimal Infix add works`` () =
    4.0868M + 2.289348M |> equal 6.376148M

[<Fact>]
let ``test Decimal Infix subtract works`` () =
    4.0868M - 2.289348M |> equal 1.797452M

[<Fact>]
let ``test Decimal Infix multiply works`` () =
    4.0868M * 2.289348M |> equal 9.3561074064M

[<Fact>]
let ``test Decimal Infix divide works`` () =
    4M / 2M |> equal 2M

[<Fact>]
let ``test Decimal Infix modulo works`` () =
    4.0868M % 2.289348M |> equal 1.797452M

[<Fact>]
let ``test Decimal.Add works`` () =
    Decimal.Add(4.0868M, 2.289348M) |> equal 6.376148M

[<Fact>]
let ``test Decimal.Subtract works`` () =
    Decimal.Subtract(4.0868M, 2.289348M) |> equal 1.797452M

[<Fact>]
let ``test Decimal.Multiply works`` () =
    Decimal.Multiply(4.0868M, 2.289348M) |> equal 9.3561074064M

[<Fact>]
let ``test Decimal.Divide works`` () =
    Decimal.Divide(4M, 2M) |> equal 2M

[<Fact>]
let ``test Decimal.Remainder works`` () =
    Decimal.Remainder(4.0868M, 2.289348M) |> equal 1.797452M

[<Fact>]
let ``test Decimal.Negate works`` () =
    Decimal.Negate(4M) |> equal -4M

[<Fact>]
let ``test Decimal Evaluation order is preserved by generated code`` () =
    (4.4567M - 2.2234M) * 2.6492M + 1.2493M |> equal 7.16575836M

[<Fact>]
let ``test Decimal constructors work`` () =
    let d = 1.2493M
    let bits = Decimal.GetBits(d)
    let d2 = Decimal(bits)
    let d3 = Decimal(bits[0], bits[1], bits[2], false, 4uy)
    d2 |> equal d
    d3 |> equal d

[<Fact>]
let ``test Decimal GetBits works`` () =
    let d = Decimal([| -1; -1; -2; 0 |])
    let bits = Decimal.GetBits(d)
    let d2 = Decimal(bits)
    let d3 = Decimal(bits[0], bits[1], bits[2], true, 0uy)
    d2 |> equal d
    d3 |> equal -d

[<Fact>]
let ``test Decimal GetBits works with arithmetic operations`` () =
    let check (d: decimal) =
        let bits = Decimal.GetBits(d)
        Decimal(bits) |> equal d

    check (10M + 10M)
    check (100.5M - 0.5M)
    check (5M * 200M)
    check (-0.1M * 100M)
    check (2000M / 10M)
    check (1.5M + 0.5M)

[<Fact>]
let ``test Decimal from a float rounds like .NET`` () =
    string (decimal 0.1) |> equal "0.1"
    string (decimal -0.1) |> equal "-0.1"
    string (decimal 0.3) |> equal "0.3"
    string (decimal 1.1) |> equal "1.1"
    string (decimal 1e20) |> equal "100000000000000000000"
    string (decimal (1.0 / 3.0)) |> equal "0.333333333333333"

[<Fact>]
let ``test Decimal from a float32 rounds like .NET`` () =
    string (decimal 0.1f) |> equal "0.1"
    string (decimal -0.1f) |> equal "-0.1"
    string (decimal (1.0f / 3.0f)) |> equal "0.3333333"

[<Fact>]
let ``test Decimal abs works`` () =
    abs -4M |> equal 4M

// [<Fact>]
// let ``test Decimal round works`` () =
//     round 11.0M |> equal 11.M
//     round 11.01M |> equal 11.M
//     round 11.25M |> equal 11.M
//     round 11.50M |> equal 12.M
//     round 11.75M |> equal 12.M
//     round -11.0M |> equal -11.M
//     round -11.01M |> equal -11.M
//     round -11.25M |> equal -11.M
//     round -11.50M |> equal -12.M
//     round -11.75M |> equal -12.M
//     Math.Round 1.425M |> equal 1.M
//     Math.Round -1.425M |> equal -1.M
//     Math.Round 1.546M |> equal 2.M
//     Math.Round -1.546M |> equal -2.M

// [<Fact>]
// let ``test Decimal round half to even works`` () =
//     round 1.5M |> equal 2.M
//     round 2.5M |> equal 2.M
//     round 3.5M |> equal 4.M
//     round -1.5M |> equal -2.M
//     round -2.5M |> equal -2.M
//     round -3.5M |> equal -4.M

// [<Fact>]
// let ``test Decimal round with digits works`` () =
//     Math.Round(1.426M, 3) |> equal 1.426M
//     Math.Round(1.426M, 2) |> equal 1.43M
//     Math.Round(1.426M, 1) |> equal 1.4M
//     Math.Round(-1.426M, 3) |> equal -1.426M
//     Math.Round(-1.426M, 2) |> equal -1.43M
//     Math.Round(-1.426M, 1) |> equal -1.4M

// [<Fact>]
// let ``test Decimal truncate works`` () =
//     truncate 11.0M |> equal 11.M
//     truncate 11.01M |> equal 11.M
//     truncate 11.25M |> equal 11.M
//     truncate 11.50M |> equal 11.M
//     truncate 11.75M |> equal 11.M
//     truncate -11.0M |> equal -11.M
//     truncate -11.01M |> equal -11.M
//     truncate -11.25M |> equal -11.M
//     truncate -11.50M |> equal -11.M
//     truncate -11.75M |> equal -11.M
//     Math.Truncate -12.5M |> equal -12.M
//     Math.Truncate 1.425M |> equal 1.M
//     Math.Truncate -1.425M |> equal -1.M
//     Math.Truncate 1.546M |> equal 1.M
//     Math.Truncate -1.546M |> equal -1.M

// [<Fact>]
// let ``test Decimal ceil works`` () =
//     ceil 11.0M |> equal 11.M
//     ceil 11.01M |> equal 12.M
//     ceil 11.25M |> equal 12.M
//     ceil 11.50M |> equal 12.M
//     ceil 11.75M |> equal 12.M
//     ceil -11.0M |> equal -11.M
//     ceil -11.01M |> equal -11.M
//     ceil -11.25M |> equal -11.M
//     ceil -11.50M |> equal -11.M
//     ceil -11.75M |> equal -11.M
//     Math.Ceiling 11.25M |> equal 12.M
//     Math.Ceiling -11.25M |> equal -11.M

// [<Fact>]
// let ``test Decimal floor works`` () =
//     floor 11.0M |> equal 11.M
//     floor 11.01M |> equal 11.M
//     floor 11.25M |> equal 11.M
//     floor 11.50M |> equal 11.M
//     floor 11.75M |> equal 11.M
//     floor -11.0M |> equal -11.M
//     floor -11.01M |> equal -12.M
//     floor -11.25M |> equal -12.M
//     floor -11.50M |> equal -12.M
//     floor -11.75M |> equal -12.M
//     Math.Floor 11.25M |> equal 11.M
//     Math.Floor -11.25M |> equal -12.M

// [<Fact>]
// let ``test Decimal pown works`` () =
//     pown 2.2M 3 |> equal 10.648M

[<Fact>]
let ``test Int64 Infix add can be generated`` () =
    4L + 2L |> equal 6L

[<Fact>]
let ``test Int64 Infix subtract can be generated`` () =
    4L - 2L |> equal 2L

[<Fact>]
let ``test Int64 Infix multiply can be generated`` () =
    4L * 2L |> equal 8L

[<Fact>]
let ``test Int64 Infix divide can be generated`` () =
    4L / 2L |> equal 2L

[<Fact>]
let ``test Int64 Integer division doesn't produce floats`` () =
    5. / 2. |> equal 2.5
    5L / 2L |> equal 2L
    5L / 3L |> equal 1L
    float 5L / 2. |> equal 2.5

[<Fact>]
let ``test Int64 Infix modulo can be generated`` () =
    4L % 3L |> equal 1L
    5L % 3L |> equal 2L

[<Fact>]
let ``test Int64 Infix modulo with negative numbers`` () =
    -5L % 3L |> equal -2L
    5L % -3L |> equal 2L
    -5L % -3L |> equal -2L

[<Fact>]
let ``test Int64 Evaluation order is preserved by generated code`` () =
    (4L - 2L) * 2L + 1L |> equal 5L

[<Fact>]
let ``test Int64 Bitwise and can be generated`` () =
    6L &&& 2L |> equal 2L

[<Fact>]
let ``test Int64 Bitwise or can be generated`` () =
    4L ||| 2L |> equal 6L

[<Fact>]
let ``test Int64 Bitwise shift left can be generated`` () =
    4L <<< 2 |> equal 16L

[<Fact>]
let ``test Int64 Bitwise shift right can be generated`` () =
    4L >>> 2 |> equal 1L

[<Fact>]
let ``test UInt64 Bitwise shift right can be generated`` () = // See #1482
    15210016002388773605UL >>> 33 |> equal 1770678907UL

[<Fact>]
let ``test Int64 abs works`` () =
    abs -4L |> equal 4L

[<Fact>]
let ``test Big integers addition works`` () =
    let x = 59823749821707124891298739821798327321028091380980I
    let y = bigint 1L
    let z = 1I
    (x + y + z) |> equal 59823749821707124891298739821798327321028091380982I

[<Fact>]
let ``test BigInt Infix add can be generated`` () =
    4I + 2I |> equal 6I

[<Fact>]
let ``test BigInt Infix subtract can be generated`` () =
    4I - 2I |> equal 2I

[<Fact>]
let ``test BigInt Infix multiply can be generated`` () =
    4I * 2I |> equal 8I

[<Fact>]
let ``test BigInt Infix divide can be generated`` () =
    4I / 2I |> equal 2I

[<Fact>]
let ``test BigInt Integer division doesn't produce floats`` () =
    5. / 2. |> equal 2.5
    5I / 2I |> equal 2I
    5I / 3I |> equal 1I
    // float 5I / 2. |> equal 2.5

[<Fact>]
let ``test BigInt Infix modulo can be generated`` () =
    4I % 3I |> equal 1I
    5I % 3I |> equal 2I

[<Fact>]
let ``test BigInt Infix modulo with negative numbers`` () =
    -5I % 3I |> equal -2I
    5I % -3I |> equal 2I
    -5I % -3I |> equal -2I

[<Fact>]
let ``test BigInt.DivRem works`` () = // See #1744
    let quotient,remainder = bigint.DivRem(5I,2I)
    2I |> equal quotient
    1I |> equal remainder

[<Fact>]
let ``test BigInt Evaluation order is preserved by generated code`` () =
    (4I - 2I) * 2I + 1I |> equal 5I

[<Fact>]
let ``test BigInt Bitwise and can be generated`` () =
    6I &&& 2I |> equal 2I

[<Fact>]
let ``test BigInt Bitwise or can be generated`` () =
    4I ||| 2I |> equal 6I

[<Fact>]
let ``test BigInt Bitwise xor can be generated`` () =
    6I ^^^ 2I |> equal 4I

[<Fact>]
let ``test BigInt Bitwise shift left can be generated`` () =
    4I <<< 2 |> equal 16I

[<Fact>]
let ``test BigInt Bitwise shift right can be generated`` () =
    4I >>> 2 |> equal 1I

[<Fact>]
let ``test BigInt abs works`` () =
    abs -4I |> equal 4I

[<Fact>]
let ``test abs works`` () =
    abs -4 |> equal 4

[<Fact>]
let ``test round works`` () =
    round -12.5 |> equal -12.
    round 1.5 |> equal 2.
    round 1.535 |> equal 2.
    round 1.525 |> equal 2.

[<Fact>]
let ``test ceil works`` () =
    ceil 11.25 |> equal 12.
    ceil -11.25 |> equal -11.
    Math.Ceiling 11.25 |> equal 12.

[<Fact>]
let ``test floor works`` () =
    floor 11.75 |> equal 11.
    floor -11.75 |> equal -12.
    Math.Floor 11.25 |> equal 11.

[<Fact>]
let ``test pown works`` () =
    pown 2.2 3 |> checkTo3dp 10648.

[<Fact>]
let ``test pow works`` () =
    2.2 ** 3.0 |> checkTo3dp 10648.

[<Fact>]
let ``test sqrt works`` () =
    sqrt 4.5 |> checkTo3dp 2121.

// As per https://github.com/dotnet/corefx/blob/master/src/System.Runtime.Extensions/tests/System/Math.cs#L217
[<Fact>]
let ``test sqrt matches .NET core implementation`` () =
    checkTo3dp 1732. (sqrt 3.0)
    sqrt 0.0  |> equal 0.0
    Double.IsNaN (sqrt -3.0) |> equal true
    Double.IsNaN (sqrt Double.NaN) |> equal true
    Double.IsNaN (sqrt Double.NegativeInfinity) |> equal true
    sqrt Double.PositiveInfinity |> equal Double.PositiveInfinity

// [<Fact>]
// let ``test Single comparison works`` () =
//     let x = 5.0f
//     let y = 5.0f
//     let z = 6.0f
//     let n = Single.NaN
//     compare x y |> equal 0
//     compare y z |> equal -1
//     compare y x |> equal 0
//     compare z x |> equal 1
//     compare x n |> equal 1
//     compare n y |> equal -1
//     compare n n |> equal 0
//     n = n |> equal false

// [<Fact>]
// let ``test Double comparison works`` () =
//     let x = 5.0
//     let y = 5.0
//     let z = 6.0
//     let n = Double.NaN
//     compare x y |> equal 0
//     compare y z |> equal -1
//     compare y x |> equal 0
//     compare z x |> equal 1
//     compare x n |> equal 1
//     compare n y |> equal -1
//     compare n n |> equal 0
//     n = n |> equal false

// [<Fact>]
// let ``test Double.Parse works with IFormatProvider`` () =
//     // culture compiles to { } for now and it is ignored on the call-site
//     let culture = Globalization.CultureInfo.InvariantCulture
//     let result = Double.Parse("10.5", culture)
//     result |> equal 10.5

// [<Fact>]
// let ``test Single.Parse works with IFormatProvider`` () =
//     // culture compiles to { } for now and it is ignored on the call-site
//     let culture = Globalization.CultureInfo.InvariantCulture
//     let result = Single.Parse("10.5", culture)
//     float result |> equal 10.5

[<Fact>]
let ``test Single special values work`` () =
    Single.IsPositiveInfinity Single.PositiveInfinity |> equal true
    Single.IsNegativeInfinity Single.NegativeInfinity |> equal true
    Single.IsInfinity Single.PositiveInfinity |> equal true
    Single.IsInfinity Single.NegativeInfinity |> equal true
    Single.IsNaN Single.NaN |> equal true
    Single.PositiveInfinity > 0.0f |> equal true
    Single.NegativeInfinity < 0.0f |> equal true
    Single.PositiveInfinity |> equal infinityf
    Single.NegativeInfinity |> equal -infinityf
    Single.IsNaN nanf |> equal true

[<Fact>]
let ``test Single special values work as module bindings`` () =
    Single.IsPositiveInfinity moduleSinglePositiveInfinity |> equal true
    Single.IsNegativeInfinity moduleSingleNegativeInfinity |> equal true
    Single.IsNaN moduleSingleNaN |> equal true

[<Fact>]
let ``test Double special values work`` () =
    Double.IsPositiveInfinity Double.PositiveInfinity |> equal true
    Double.IsNegativeInfinity Double.NegativeInfinity |> equal true
    Double.IsNaN Double.NaN |> equal true
    Double.PositiveInfinity |> equal infinity
    Double.NegativeInfinity |> equal -infinity

[<Fact>]
let ``test acos works`` () =
    acos 0.25 |> checkTo3dp 1318.

[<Fact>]
let ``test asin works`` () =
    asin 0.25 |> checkTo3dp 252.

[<Fact>]
let ``test atan works`` () =
    atan 0.25 |> checkTo3dp 244.

[<Fact>]
let ``test atan2 works`` () =
    atan2 90. 15. |> checkTo3dp 1405.

[<Fact>]
let ``test cos works`` () =
    cos 0.25 |> checkTo3dp 968.

[<Fact>]
let ``test sin works`` () =
    sin 0.25 |> checkTo3dp 247.

[<Fact>]
let ``test tan works`` () =
    tan 0.25 |> checkTo3dp 255.

[<Fact>]
let ``test cosh works`` () =
    cosh 0.25 |> checkTo3dp 1031.

[<Fact>]
let ``test sinh works`` () =
    sinh 0.25 |> checkTo3dp 252.

[<Fact>]
let ``test tanh works`` () =
    tanh 0.25 |> checkTo3dp 244.

[<Fact>]
let ``test exp works`` () =
    exp 8.0 |> checkTo3dp 2980957.

// https://github.com/dotnet/corefx/blob/master/src/System.Runtime.Extensions/tests/System/Math.cs#L228
[<Fact>]
let ``test log works`` () =
    log 232.12 |> checkTo3dp 5447.
    checkTo3dp 1098. (log 3.0)
    log 0.0 |> equal Double.NegativeInfinity
    Double.IsNaN (log -2.0) |> equal true
    Double.IsNaN (log Double.NaN) |> equal true
    Double.IsNaN (log Double.NegativeInfinity) |> equal true
    log Double.PositiveInfinity |> equal Double.PositiveInfinity

// https://github.com/dotnet/corefx/blob/master/src/System.Runtime.Extensions/tests/System/Math.cs#L239
[<Fact>]
let ``test Math.Log with base works`` () =
    Math.Log(8.0, 2.0) |> equal 3.0
    Math.Log(3.0, 3.0) |> equal 1.0
    Math.Log(14., 3.0) |> checkTo3dp 2402.
    // FIXME: Math.Log(0.0, 3.0) |> equal Double.NegativeInfinity
    Math.Log(Double.PositiveInfinity, 3.0) |> equal Double.PositiveInfinity
    // FIXME: Double.IsNaN (Math.Log(-3.0, 3.0)) |> equal true
    Double.IsNaN (Math.Log(Double.NaN, 3.0)) |> equal true
    // FIXME: Double.IsNaN (Math.Log(Double.NegativeInfinity, 3.0)) |> equal true

[<Fact>]
let ``test log10 works`` () =
    log10 232.12 |> checkTo3dp 2365.

[<Fact>]
let ``test Math.PI works`` () =
    checkTo3dp 3141. Math.PI

[<Fact>]
let ``test Math.E works`` () =
    checkTo3dp 2718. Math.E

[<Fact>]
let ``test Math.Abs works`` () =
    Math.Abs -4 |> equal 4

[<Fact>]
let ``test Math.Pow works`` () =
    Math.Pow(2.2, 3.0) |> checkTo3dp 10648.

[<Fact>]
let ``test Math.Sqrt works`` () =
    Math.Sqrt 4.5 |> checkTo3dp 2121.

[<Fact>]
let ``test Math.Round works`` () =
    Math.Round -12.5 |> equal -12.
    Math.Round 1.425 |> equal 1.
    Math.Round -1.425 |> equal -1.
    Math.Round 1.546 |> equal 2.
    Math.Round -1.546 |> equal -2.

[<Fact>]
let ``test Math.Round with digits works`` () =
    Math.Round(1.426, 2) |> equal 1.43
    Math.Round(1.426, 1) |> equal 1.4
    Math.Round(-1.426, 2) |> equal -1.43
    Math.Round(-1.426, 1) |> equal -1.4

[<Fact>]
let ``test Math.Truncate works`` () =
    Math.Truncate -12.5 |> equal -12.
    Math.Truncate 1.425 |> equal 1.
    Math.Truncate -1.425 |> equal -1.
    Math.Truncate 1.546 |> equal 1.
    Math.Truncate -1.546 |> equal -1.

[<Fact>]
let ``test Math.Ceil works`` () =
    Math.Ceiling 11.25 |> equal 12.

[<Fact>]
let ``test Math.Floor works`` () =
    Math.Floor 11.75 |> equal 11.

[<Fact>]
let ``test Math.Acos works`` () =
    Math.Acos 0.25 |> checkTo3dp 1318.

[<Fact>]
let ``test Math.Asin works`` () =
    Math.Asin 0.25 |> checkTo3dp 252.

[<Fact>]
let ``test Math.Atan works`` () =
    Math.Atan 0.25 |> checkTo3dp 244.

[<Fact>]
let ``test Math.Atan2 works`` () =
    Math.Atan2(90., 15.) |> checkTo3dp 1405.

[<Fact>]
let ``test Math.Cos works`` () =
    Math.Cos(0.1 * Math.PI) |> checkTo3dp 951.

[<Fact>]
let ``test Math.Sin works`` () =
    Math.Sin(0.25 * Math.PI) |> checkTo3dp 707.

[<Fact>]
let ``test Math.Tan works`` () =
    Math.Tan(0.5) |> checkTo3dp 546.

[<Fact>]
let ``test Math.Exp works`` () =
    Math.Exp 8.0 |> checkTo3dp 2980957.

[<Fact>]
let ``test Math.Log works`` () =
    Math.Log 232.12 |> checkTo3dp 5447.

// [<Fact>]
// let ``test Math.Log2 works`` () =
//     Math.Log2 8.0 |> checkTo3dp 3000.

[<Fact>]
let ``test Math.Log10 works`` () =
    Math.Log10 232.12 |> checkTo3dp 2365.

// [<Fact>]
// let ``test BigInt.Log works`` () =
//     bigint.Log 123I |> checkTo3dp 4812.

// [<Fact>]
// let ``test BigInt.Log with base works`` () =
//     bigint.Log(123I, 10.0) |> checkTo3dp 2089.

// [<Fact>]
// let ``test BigInt.Log10 works`` () =
//     bigint.Log10 123I |> checkTo3dp 2089.

// [<Fact>]
// let ``test Numeric Log2 works`` () =
//     SByte.Log2 8y |> equal 3y
//     Int16.Log2 8s |> equal 3s
//     Int32.Log2 8  |> equal 3
//     Int64.Log2 8L |> equal 3L
//     Byte.Log2 8uy |> equal 3uy
//     UInt16.Log2 8us |> equal 3us
//     UInt32.Log2 8u  |> equal 3u
//     UInt64.Log2 8UL |> equal 3UL
//     Double.Log2 8.0 |> equal 3.0
//     Single.Log2 8.0f |> equal 3.0f
//     bigint.Log2 8I |> equal 3I

// [<Fact>]
// let ``test Numeric Min works`` () =
//     SByte.Min(-4y, 3y) |> equal -4y
//     Int16.Min(-4s, 3s) |> equal -4s
//     Int32.Min(-4, 3)  |> equal -4
//     Int64.Min(-4L, 3L) |> equal -4L
//     Byte.Min(4uy, 3uy) |> equal 3uy
//     UInt16.Min(4us, 3us) |> equal 3us
//     UInt32.Min(4u, 3u)  |> equal 3u
//     UInt64.Min(4UL, 3UL) |> equal 3UL
//     Double.Min(-4.0, 3.0) |> equal -4.0
//     Single.Min(-4.0f, 3.0f) |> equal -4.0f
//     Decimal.Min(-4.0M, 3.0M) |> equal -4.0M
//     bigint.Min(-4I, 3I) |> equal -4I

// [<Fact>]
// let ``test Numeric Max works`` () =
//     SByte.Max(-4y, 3y) |> equal 3y
//     Int16.Max(-4s, 3s) |> equal 3s
//     Int32.Max(-4, 3)  |> equal 3
//     Int64.Max(-4L, 3L) |> equal 3L
//     Byte.Max(4uy, 3uy) |> equal 4uy
//     UInt16.Max(4us, 3us) |> equal 4us
//     UInt32.Max(4u, 3u)  |> equal 4u
//     UInt64.Max(4UL, 3UL) |> equal 4UL
//     Double.Max(-4.0, 3.0) |> equal 3.0
//     Single.Max(-4.0f, 3.0f) |> equal 3.0f
//     Decimal.Max(-4.0M, 3.0M) |> equal 3.0M
//     bigint.Max(-4I, 3I) |> equal 3I

// [<Fact>]
// let ``test Numeric MinMagnitude works`` () =
//     SByte.MinMagnitude(-4y, 3y) |> equal 3y
//     Int16.MinMagnitude(-4s, 3s) |> equal 3s
//     Int32.MinMagnitude(-4, 3)  |> equal 3
//     Int64.MinMagnitude(-4L, 3L) |> equal 3L
//     Double.MinMagnitude(-4.0, 3.0) |> equal 3.0
//     Single.MinMagnitude(-4.0f, 3.0f) |> equal 3.0f
//     Decimal.MinMagnitude(-4.0M, 3.0M) |> equal 3.0M
//     bigint.MinMagnitude(-4I, 3I) |> equal 3I

// [<Fact>]
// let ``test Numeric MaxMagnitude works`` () =
//     SByte.MaxMagnitude(-4y, 3y) |> equal -4y
//     Int16.MaxMagnitude(-4s, 3s) |> equal -4s
//     Int32.MaxMagnitude(-4, 3)  |> equal -4
//     Int64.MaxMagnitude(-4L, 3L) |> equal -4L
//     Double.MaxMagnitude(-4.0, 3.0) |> equal -4.0
//     Single.MaxMagnitude(-4.0f, 3.0f) |> equal -4.0f
//     Decimal.MaxMagnitude(-4.0M, 3.0M) |> equal -4.0M
//     bigint.MaxMagnitude(-4I, 3I) |> equal -4I

// [<Fact>]
// let ``test Numeric Clamp works`` () =
//     SByte.Clamp(5y, -4y, 3y) |> equal 3y
//     Int16.Clamp(5s, -4s, 3s) |> equal 3s
//     Int32.Clamp(5, -4, 3)  |> equal 3
//     Int64.Clamp(5L, -4L, 3L) |> equal 3L
//     Byte.Clamp(5uy, 3uy, 4uy) |> equal 4uy
//     UInt16.Clamp(5us, 3us, 4us) |> equal 4us
//     UInt32.Clamp(5u, 3u, 4u)  |> equal 4u
//     UInt64.Clamp(5UL, 3UL, 4UL) |> equal 4UL
//     Double.Clamp(5.0, -4.0, 3.0) |> equal 3.0
//     Single.Clamp(5.0f, -4.0f, 3.0f) |> equal 3.0f
//     Decimal.Clamp(5.0M, -4.0M, 3.0M) |> equal 3.0M
//     bigint.Clamp(5I, -4I, 3I) |> equal 3I

[<Fact>]
let ``test Math.Clamp works`` () =
    Math.Clamp(5y, -4y, 3y) |> equal 3y
    Math.Clamp(5s, -4s, 3s) |> equal 3s
    Math.Clamp(5, -4, 3)  |> equal 3
    Math.Clamp(5L, -4L, 3L) |> equal 3L
    Math.Clamp(5uy, 3uy, 4uy) |> equal 4uy
    Math.Clamp(5us, 3us, 4us) |> equal 4us
    Math.Clamp(5u, 3u, 4u)  |> equal 4u
    Math.Clamp(5UL, 3UL, 4UL) |> equal 4UL
    Math.Clamp(5.0, -4.0, 3.0) |> equal 3.0
    Math.Clamp(5.0f, -4.0f, 3.0f) |> equal 3.0f
    Math.Clamp(5.0M, -4.0M, 3.0M) |> equal 3.0M

[<Fact>]
let ``test Math.Min works`` () =
    Math.Min(-4.0, 3.0) |> equal -4.0
    MathF.Min(-4.0f, 3.0f) |> equal -4.0f

[<Fact>]
let ``test Math.Max works`` () =
    Math.Max(-4.0, 3.0) |> equal 3.0
    MathF.Max(-4.0f, 3.0f) |> equal 3.0f

[<Fact>]
let ``test Math.Min/Max propagate NaN`` () =
    Double.IsNaN(Math.Min(nan, 1.0)) |> equal true
    Double.IsNaN(Math.Min(1.0, nan)) |> equal true
    Double.IsNaN(Math.Max(nan, 1.0)) |> equal true
    Double.IsNaN(Math.Max(1.0, nan)) |> equal true

[<Fact>]
let ``test Math.Min/Max prefer +0.0 over -0.0 regardless of operand order`` () =
    Double.IsPositiveInfinity(1.0 / Math.Max(0.0, -0.0)) |> equal true
    Double.IsPositiveInfinity(1.0 / Math.Max(-0.0, 0.0)) |> equal true
    Double.IsNegativeInfinity(1.0 / Math.Min(0.0, -0.0)) |> equal true
    Double.IsNegativeInfinity(1.0 / Math.Min(-0.0, 0.0)) |> equal true

// [<Fact>]
// let ``test Math.MinMagnitude works`` () =
//     Math.MinMagnitude(-4.0, 3.0) |> equal 3.0
//     MathF.MinMagnitude(-4.0f, 3.0f) |> equal 3.0f

// [<Fact>]
// let ``test Math.MaxMagnitude works`` () =
//     Math.MaxMagnitude(-4.0, 3.0) |> equal -4.0
//     MathF.MaxMagnitude(-4.0f, 3.0f) |> equal -4.0f

[<Fact>]
let ``test incr works`` () =
    let i = ref 5
    incr i
    i := !i + 1
    !i |> equal 7
    i.Value <- i.Value + 1
    i.Value |> equal 8

[<Fact>]
let ``test decr works`` () =
    let i = ref 5
    decr i
    i := !i - 1
    !i |> equal 3
    i.Value <- i.Value - 1
    i.Value |> equal 2

[<Fact>]
let ``test Long integer equality works`` () =
    let x = 5L
    let y = 5L
    let z = 6L
    (x = y) |> equal true
    (y = z) |> equal false
    (y = x) |> equal true
    (z = x) |> equal false

[<Fact>]
let ``test Long integer comparison works`` () =
    let x = 5L
    let y = 5L
    let z = 6L
    compare x y |> equal 0
    compare y z |> equal -1
    compare y x |> equal 0
    compare z x |> equal 1

[<Fact>]
let ``test Decimal equality works`` () =
    let x = 5m
    let y = 5m
    let z = 6m
    (x = y) |> equal true
    (y = z) |> equal false
    (y = x) |> equal true
    (z = x) |> equal false

[<Fact>]
let ``test Decimal comparison works`` () =
    let x = 5m
    let y = 5m
    let z = 6m
    compare x y |> equal 0
    compare y z |> equal -1
    compare y x |> equal 0
    compare z x |> equal 1

[<Fact>]
let ``test Big integer equality works`` () =
    let x = 59823749821707124891298739821798327321028091380980I
    let y = 59823749821707124891298739821798327321028091380980I
    let z = 59823749821707124891298739821798327321028091380981I
    (x = y) |> equal true
    (y = z) |> equal false
    (y = x) |> equal true
    (z = x) |> equal false

[<Fact>]
let ``test Big integers comparison works`` () =
    let x = 5I
    let y = 5I
    let z = 6I
    compare x y |> equal 0
    compare y z |> equal -1
    compare y x |> equal 0
    compare z x |> equal 1

// [<Fact>]
// let ``test Big integer to byte array works`` () =
//     // values with high bit both 0 and 1 for different array lengths
//     32767I.ToByteArray() |> equal [|255uy; 127uy|]
//     32768I.ToByteArray() |> equal [|0uy; 128uy; 0uy|]
//     -32768I.ToByteArray() |> equal [|0uy; 128uy|]
//     -32769I.ToByteArray() |> equal [|255uy; 127uy; 255uy|]
//     // large numbers
//     111222333444555666777888999I.ToByteArray() |> equal [|231uy; 216uy; 2uy; 164uy; 86uy; 149uy; 8uy; 199uy; 62uy; 0uy; 92uy|]
//     -111222333444555666777888999I.ToByteArray() |> equal [|25uy; 39uy; 253uy; 91uy; 169uy; 106uy; 247uy; 56uy; 193uy; 255uy; 163uy|]

// [<Fact>]
// let ``test Big integer from byte array works`` () =
//     // values with high bit both 0 and 1 for different array lengths
//     Numerics.BigInteger([|255uy; 127uy|]) |> equal 32767I
//     Numerics.BigInteger([|0uy; 128uy; 0uy|]) |> equal 32768I
//     Numerics.BigInteger([|0uy; 128uy|]) |> equal -32768I
//     Numerics.BigInteger([|255uy; 127uy; 255uy|]) |> equal -32769I
//     // large numbers
//     Numerics.BigInteger([|231uy; 216uy; 2uy; 164uy; 86uy; 149uy; 8uy; 199uy; 62uy; 0uy; 92uy|]) |> equal 111222333444555666777888999I
//     Numerics.BigInteger([|25uy; 39uy; 253uy; 91uy; 169uy; 106uy; 247uy; 56uy; 193uy; 255uy; 163uy|]) |> equal -111222333444555666777888999I

[<Fact>]
let ``test Member values of decimal type can be compared`` () = // See #747
    1M < 2M |> equal true
    1M > 2M |> equal false

[<Fact>]
let ``test Sign operator works with ints`` () = // See #1311
    sign 1 |> equal 1
    sign 2 |> equal 1
    sign 0 |> equal 0
    sign -1 |> equal -1
    sign -2 |> equal -1

[<Fact>]
let ``test Sign operator works with longs`` () =
    sign 1L |> equal 1
    sign 2L |> equal 1
    sign 0L |> equal 0
    sign -1L |> equal -1
    sign -2L |> equal -1

[<Fact>]
let ``test Sign operator works with floats`` () =
    sign 1. |> equal 1
    sign 2. |> equal 1
    sign 0. |> equal 0
    sign -1. |> equal -1
    sign -2. |> equal -1

[<Fact>]
let ``test Sign operator works with decimals`` () =
    sign 1m |> equal 1
    sign 2m |> equal 1
    sign 0m |> equal 0
    sign -1m |> equal -1
    sign -2m |> equal -1

[<Fact>]
let ``test Sign operator works with bigints`` () =
    sign 1I |> equal 1
    sign 2I |> equal 1
    sign 0I |> equal 0
    sign -1I |> equal -1
    sign -2I |> equal -1

// [<Fact>]
// let ``test Formatting of decimal works`` () =
//     let formatNumber (d:decimal) =
//         (sprintf "%.2f" d).Replace(",","").Replace(".",",")
//     formatNumber 0.0M |> equal "0,00"
//     formatNumber 0.020M |> equal "0,02"
//     formatNumber 0.20M |> equal "0,20"
//     formatNumber 2.0M |> equal "2,00"

// [<Fact>]
// let ``test Formatting of decimal works with inline`` () =
//     let inline formatNumber (d:decimal) =
//         (sprintf "%.2f" d).Replace(",","").Replace(".",",")
//     formatNumber 0.0M |> equal "0,00"
//     formatNumber 0.020M |> equal "0,02"
//     formatNumber 0.20M |> equal "0,20"
//     formatNumber 2.0M |> equal "2,00"

// [<Fact>]
// let ``test Formatting of € works with inline`` () =
//     let inline formatNumber (d:decimal) =
//         (sprintf "%.2f" d).Replace(",","").Replace(".",",")
//     let inline formatEuro (d:decimal) = (formatNumber d) + " €"
//     formatEuro 0.0M |> equal "0,00 €"
//     formatEuro 0.020M |> equal "0,02 €"
//     formatEuro 0.20M |> equal "0,20 €"
//     formatEuro 2.0M |> equal "2,00 €"

// module UnitTests =
//     open Common.Imports.Vectors

//     type [<Measure>] m

//     let square (x: float<'a>) = x * x

//     [<Fact>]
//     let ``test can square a unit`` () =
//         let d = 3.<m>
//         let dSquared = square d
//         dSquared |> equal 9.<m^2>

//     [<Fact>]
//     let ``test Can add two union vectors with same units but remove generics in output`` () =
//         let a = Vector2(2.<m>, 1.<m>)
//         let b = Vector2(3.<m>, 2.<m>)
//         let res = a + b
//         equal (Vector2(5.<m> ,3.<m>)) res

//     [<Fact>]
//     let ``test Can add two record vectors with same units but remove generics in output`` () =
//         let a = { x = 2f<m>; y = 1f<m> }
//         let b = { x = 3f<m>; y = 1f<m> }
//         let res = a + b
//         equal { x = 5f<m>; y = 2f<m> } res

[<Fact>]
let ``test extreme values work`` () =
    0.0 / 0.0 |> Double.IsNaN |> equal true
    0.0 / (-0.0) |> Double.IsNaN |> equal true
    1.0 / infinity |> equal 0
    1.0 / (-infinity) |> equal 0
    1.0 / 0.0 |> Double.IsInfinity |> equal true

    1.0 / (-0.0)
    |> Double.IsNegativeInfinity
    |> equal true

    -1.0 / (-0.0)
    |> Double.IsNegativeInfinity
    |> equal false

    1.0 / 0.0
    |> Double.IsPositiveInfinity
    |> equal true

    1.0 / (-0.0)
    |> Double.IsPositiveInfinity
    |> equal false

    -infinity < infinity |> equal true
    (-0.0) < 0.0 |> equal false

// Int32 is a plain Python `int` on the Python target, so the compiler normalizes an
// arithmetic tree back into 32 bits once at its root. A conversion to a type that is
// 32 bits or narrower re-truncates the very bits that normalization kept, so the
// compiler drops it -- but only while the tree provably still fits a signed 64-bit
// int, because the fixed-width constructors saturate beyond that. These pin the
// elision, and the cases where it must not happen, against .NET.
[<Fact>]
let ``test narrowing conversions of unnormalized int arithmetic work`` () =
    let sub (hi: int) (lo: int) = uint32 (hi - lo)
    let add (x: int) (y: int) = byte (x + y)
    let mul (x: int) (y: int) = int16 (x * y)
    let neg (x: int) = uint32 (-x)
    let shl (x: int) = uint32 (x <<< 3)

    sub (id Int32.MinValue) (id Int32.MaxValue) |> equal 1u
    add (id Int32.MaxValue) (id 1) |> equal 0uy
    mul (id 65537) (id 65537) |> equal 1s
    neg (id Int32.MinValue) |> equal 2147483648u
    shl (id Int32.MaxValue) |> equal 4294967288u

[<Fact>]
let ``test narrowing conversions of wide int arithmetic work`` () =
    // These trees can exceed a signed 64-bit int, so the normalization must survive
    let mul3 (x: int) (y: int) (z: int) = uint32 (x * y * z)
    let mulShl (x: int) (y: int) = uint32 ((x * y) <<< 20)

    mul3 (id 65537) (id 65537) (id 65537) |> equal 196609u
    mulShl (id 99991) (id 99991) |> equal 3507486720u

[<Fact>]
let ``test widening and float conversions of int arithmetic work`` () =
    // The conversion is wider than 32 bits, or is not a truncation at all, so the
    // normalization is load-bearing
    let toLong (x: int) (y: int) = int64 (x + y)
    let toFloat (x: int) (y: int) = float (x - y)
    let toShort (x: int) (y: int) = uint16 (x - y)

    toLong (id Int32.MaxValue) (id 1) |> equal -2147483648L
    toFloat (id Int32.MinValue) (id 1) |> equal 2147483647.0
    toShort (id Int32.MinValue) (id 1) |> equal 65535us

// Adding a constant to an in-range Int32 can only overflow at one end, and by at most
// that constant, so the Python target decides it with a comparison instead of a call
// into the normalizer. These check the boundary in both directions, and the shapes the
// guard does not apply to.
[<Fact>]
let ``test adding a constant to an int wraps at the boundary`` () =
    let inc (i: int) = i + 1
    let dec (i: int) = i - 1
    let incLeft (i: int) = 1 + i
    let incBig (i: int) = i + 1000
    let decBig (i: int) = i - 1000

    inc (id Int32.MaxValue) |> equal Int32.MinValue
    inc (id (Int32.MaxValue - 1)) |> equal Int32.MaxValue
    dec (id Int32.MinValue) |> equal Int32.MaxValue
    dec (id (Int32.MinValue + 1)) |> equal Int32.MinValue
    incLeft (id Int32.MaxValue) |> equal Int32.MinValue
    incBig (id Int32.MaxValue) |> equal (Int32.MinValue + 999)
    decBig (id Int32.MinValue) |> equal (Int32.MaxValue - 999)

[<Fact>]
let ``test adding an extreme constant to an int wraps at the boundary`` () =
    let addMin (i: int) = i + Int32.MinValue
    let subMin (i: int) = i - Int32.MinValue
    let subFrom (i: int) = 1 - i

    addMin (id 0) |> equal Int32.MinValue
    addMin (id -1) |> equal Int32.MaxValue
    subMin (id -1) |> equal Int32.MaxValue
    subMin (id 0) |> equal Int32.MinValue
    subFrom (id Int32.MinValue) |> equal -2147483647

// A conversion into 32 bits or fewer also makes an inner conversion redundant, but only
// when what that inner conversion reads is itself of fixed width. A float operand is not:
// truncating it to 32 bits first and converting it directly give different answers.
[<Fact>]
let ``test narrowing conversions of narrowed integers work`` () =
    let ofUInt64 (x: uint64) = uint32 (int32 x)
    let toInt32 (x: uint64) = int32 (int32 x)
    let ofInt64 (x: int64) = uint32 (int32 x)
    let toByte (x: int64) = byte (int32 x)
    let toUInt16 (x: uint64) = uint16 (int32 x)

    ofUInt64 (id 0xFFFFFFFF12345678UL) |> equal 305419896u
    ofUInt64 (id UInt64.MaxValue) |> equal 4294967295u
    toInt32 (id 0xFFFFFFFF12345678UL) |> equal 305419896
    toInt32 (id UInt64.MaxValue) |> equal -1
    ofInt64 (id -1L) |> equal 4294967295u
    ofInt64 (id Int64.MinValue) |> equal 0u
    toByte (id -1L) |> equal 255uy
    toUInt16 (id 0xFFFFFFFFFFFFUL) |> equal 65535us

[<Fact>]
let ``test narrowing conversions of truncated floats work`` () =
    let ofFloat (x: float) = uint32 (int32 x)
    let ofFloat32 (x: float32) = byte (int32 x)

    ofFloat (id 3.9) |> equal 3u
    ofFloat (id -3.9) |> equal 4294967293u
    ofFloat (id -1.5) |> equal 4294967295u
    ofFloat32 (id -3.9f) |> equal 253uy

// Where no operand of an int addition is a literal, the Python target binds the result
// to a temporary and range-tests that instead. The temporary must not collide with
// anything in scope, and several in one declaration must stay distinct.
[<Fact>]
let ``test int subtraction without a literal operand wraps at the boundary`` () =
    let sub (x: int) (y: int) = x - y
    let add (x: int) (y: int) = x + y
    let ofLength (xs: int[]) = xs.Length - 1

    sub (id Int32.MinValue) (id 1) |> equal Int32.MaxValue
    sub (id Int32.MaxValue) (id -1) |> equal Int32.MinValue
    sub (id Int32.MinValue) (id Int32.MaxValue) |> equal 1
    sub (id 10) (id 3) |> equal 7
    add (id Int32.MaxValue) (id 1) |> equal Int32.MinValue
    add (id Int32.MinValue) (id -1) |> equal Int32.MaxValue
    add (id Int32.MaxValue) (id Int32.MaxValue) |> equal -2
    ofLength (id [| 1; 2; 3 |]) |> equal 2

[<Fact>]
let ``test int arithmetic guards do not collide with bindings in scope`` () =
    // `tmp` is the name the guard's temporary is generated from
    let shadow (tmp: int) (y: int) = tmp - y
    let several (a: int) (b: int) (c: int) (d: int) = (a - b) + (c - d)

    shadow (id Int32.MinValue) (id 1) |> equal Int32.MaxValue
    shadow (id 10) (id 4) |> equal 6
    several (id Int32.MaxValue) (id -1) (id 0) (id 0) |> equal Int32.MinValue
    several (id 10) (id 4) (id 20) (id 5) |> equal 21

type ArithmeticCounter = { mutable Count: int }

// An attribute access on a local is as cheap to re-evaluate as the local itself, so
// the comparison guard covers `x.Field + 1` and not just `i + 1`. Fable models a real
// property as a call, so this can never re-run a getter.
[<Fact>]
let ``test adding a constant to an int field wraps at the boundary`` () =
    let counter = { Count = id Int32.MaxValue }
    counter.Count <- counter.Count + 1
    counter.Count |> equal Int32.MinValue

    counter.Count <- counter.Count - 1
    counter.Count |> equal Int32.MaxValue

    counter.Count <- id 10
    counter.Count <- counter.Count + 5
    counter.Count |> equal 15

// A decimal is not of fixed width, so the inner conversion truncates where the outer
// one alone would not: `int32 -3.9m` is -3, and .NET has no `uint32` of -3.9m at all.
[<Fact>]
let ``test narrowing conversions of narrowed decimals work`` () =
    let ofDecimal (x: decimal) = uint32 (int32 x)
    let toByte (x: decimal) = byte (int32 x)

    ofDecimal (id -3.9M) |> equal 4294967293u
    ofDecimal (id 3.9M) |> equal 3u
    toByte (id -1.5M) |> equal 255uy

// Two multiplications summed sit right at the edge of what a signed 64-bit int holds,
// so the width bound keeps the normalization rather than betting on the boundary.
[<Fact>]
let ``test narrowing conversions of summed products work`` () =
    let mulSum (x: int) (y: int) = uint32 (x * y + x * y)

    mulSum (id 65537) (id 65537) |> equal 262146u
    mulSum (id Int32.MinValue) (id Int32.MinValue) |> equal 0u
    mulSum (id 99991) (id 99991) |> equal 2816530978u

#if FABLE_COMPILER && !FABLE_COMPILER_ZIG // (a Python emit)

// An `[<Emit>]` macro splices its arguments into the text verbatim, and may put one in
// a comprehension's iterable -- where Python rejects an assignment expression outright.
// The normalization guard has to give up its temporary and go back to a call here.
[<Emit("[x for x in [0, $0]][-1]")>]
let private throughComprehension (n: int) : int = nativeOnly

[<Fact>]
let ``test int arithmetic inside an emit comprehension compiles`` () =
    let roundTrip (a: int) (b: int) = throughComprehension (a + b)

    roundTrip (id 2) (id 3) |> equal 5
    roundTrip (id Int32.MaxValue) (id 1) |> equal Int32.MinValue

#endif

[<Fact>]
let ``test A guard that does not rule out zero or -1 leaves the division checked`` () =
    // (the false branch of `x < 0` allows 0; of `x <= -5` allows 0 and -1)
    let f (x: int) = if x < 0 then -1 else 100 / x
    let g (x: int) = if x <= -5 then -1 else System.Int32.MinValue / x
    let h (x: int) = if x < 1 then -1 else 100 / x
    f 4 |> equal 25
    h 4 |> equal 25
    g 2 |> equal (System.Int32.MinValue / 2)
    let raised (h: unit -> int) =
        try
            h () |> ignore
            "no exception"
        with
        | :? System.DivideByZeroException -> "DivideByZeroException"
        | :? System.OverflowException -> "OverflowException"
        | e -> e.Message

    raised (fun () -> f 0) |> equal "DivideByZeroException"
    raised (fun () -> g 0) |> equal "DivideByZeroException"
    raised (fun () -> g -1) |> equal "OverflowException"

// ---- ported from tests/Js/Main (2026-11-16) ----

let negativeInfinity = Double.NegativeInfinity


let compareTo (x:'a) (y:'a) = compare x y

let equals (x:'a) (y:'a) = x = y

let isNaN = fun x -> Double.IsNaN(x)

let positiveInfinity = Double.PositiveInfinity


open System.Globalization

[<Fact>]
let ``test Negating negative literals inlined in computation expressions works`` () =
    // #4251
    let f x = x
    let result =
        [
            let x = -5.0
            f (-x)
        ]
    result |> equal [5.0]

[<Fact>]
let ``test Math.DivRem works with ints and ref`` () =
    let rem = ref -1
    Math.DivRem(5, 2, rem) |> equal 2
    rem.Value |> equal 1
    Math.DivRem(4, 2, rem) |> equal 2
    rem.Value |> equal 0

[<Fact>]
let ``test Math.DivRem works with longs and ref`` () =
    let rem = ref -1L
    Math.DivRem(5L, 2L, rem) |> equal 2L
    rem.Value |> equal 1L
    Math.DivRem(4L, 2L, rem) |> equal 2L
    rem.Value |> equal 0L

[<Fact>]
let ``test Decimal ToString keeps the sign of values below 0.1`` () =
    string (decimal -0.001) |> equal "-0.001"
    string (decimal -0.05) |> equal "-0.05"
    string (decimal -0.1) |> equal "-0.1"
    string (decimal -1.5) |> equal "-1.5"
    string -0.001M |> equal "-0.001"
    string (decimal 0) |> equal "0"

[<Fact>]
let ``test Decimal ToString round-trips negative values parsed from a string`` () =
    string (decimal "-0.000001") |> equal "-0.000001"
    string (decimal "-0.001") |> equal "-0.001"
    string (decimal "-0.05") |> equal "-0.05"
    string (decimal "-0.5") |> equal "-0.5"
    string (decimal "-0.000") |> equal "0.000"

[<Fact>]
let ``test Decimal fixed-point formatting respects the precision`` () =
    let inv = System.Globalization.CultureInfo.InvariantCulture
    (decimal 0.001).ToString("F2", inv) |> equal "0.00"
    (decimal 0.05).ToString("F1", inv) |> equal "0.1"
    (decimal 0.001).ToString("N2", inv) |> equal "0.00"
    (decimal "0.001").ToString("F2", inv) |> equal "0.00"
    sprintf "%.2f" (decimal 0.001) |> equal "0.00"

[<Fact>]
let ``test Decimal fixed-point formatting omits the sign when the result rounds to zero`` () =
    let inv = System.Globalization.CultureInfo.InvariantCulture
    (-0.001M).ToString("F2", inv) |> equal "0.00"
    (-0.1M).ToString("F0", inv) |> equal "0"
    (-0.4M).ToString("F0", inv) |> equal "0"
    (-0.001M).ToString("N2", inv) |> equal "0.00"
    (-0.6M).ToString("F0", inv) |> equal "-1"
    (-1.5M).ToString("F0", inv) |> equal "-2"

[<Fact>]
let ``test Decimal round with MidpointRounding works`` () =
    let round mode = [ 2.5M; -2.5M; 3.5M; -3.5M; 2.4M; -2.6M ] |> List.map (fun x -> Math.Round(x, (mode: MidpointRounding)))
    round MidpointRounding.ToEven |> equal [ 2.M; -2.M; 4.M; -4.M; 2.M; -3.M ]
    round MidpointRounding.AwayFromZero |> equal [ 3.M; -3.M; 4.M; -4.M; 2.M; -3.M ]
    round MidpointRounding.ToZero |> equal [ 2.M; -2.M; 3.M; -3.M; 2.M; -2.M ]
    round MidpointRounding.ToNegativeInfinity |> equal [ 2.M; -3.M; 3.M; -4.M; 2.M; -3.M ]
    round MidpointRounding.ToPositiveInfinity |> equal [ 3.M; -2.M; 4.M; -3.M; 3.M; -2.M ]
    let roundDigits mode = [ 1.25M, 1; -1.25M, 1; 1.235M, 2; -1.235M, 2; 1.426M, 2 ] |> List.map (fun (x, d) -> Math.Round(x, d, (mode: MidpointRounding)))
    roundDigits MidpointRounding.ToEven |> equal [ 1.2M; -1.2M; 1.24M; -1.24M; 1.43M ]
    roundDigits MidpointRounding.AwayFromZero |> equal [ 1.3M; -1.3M; 1.24M; -1.24M; 1.43M ]
    roundDigits MidpointRounding.ToZero |> equal [ 1.2M; -1.2M; 1.23M; -1.23M; 1.42M ]
    roundDigits MidpointRounding.ToNegativeInfinity |> equal [ 1.2M; -1.3M; 1.23M; -1.24M; 1.42M ]
    roundDigits MidpointRounding.ToPositiveInfinity |> equal [ 1.3M; -1.2M; 1.24M; -1.23M; 1.43M ]
    Decimal.Round(2.5M, MidpointRounding.AwayFromZero) |> equal 3.M
    Decimal.Round(-1.25M, 1, MidpointRounding.AwayFromZero) |> equal -1.3M

[<Fact>]
let ``test Decimal round with MidpointRounding validates its arguments`` () =
    (fun () -> Math.Round(1.5M, enum<MidpointRounding> 5)) |> throwsAnyError
    (fun () -> Math.Round(1.5M, 2, enum<MidpointRounding> -1)) |> throwsAnyError
    (fun () -> Math.Round(1.5M, 29, MidpointRounding.AwayFromZero)) |> throwsAnyError
    (fun () -> Math.Round(1.5M, -1, MidpointRounding.AwayFromZero)) |> throwsAnyError
    Math.Round(1.5M, 28, MidpointRounding.AwayFromZero) |> equal 1.5M

[<Fact>]
let ``test Decimal rounding works for values below 0.1`` () =
    Math.Floor (decimal -0.0836) |> equal -1.M
    Math.Floor (decimal (sin (-5. * Math.PI / 180.))) |> equal -1.M
    Math.Floor (decimal "-0.0836") |> equal -1.M
    Math.Floor (decimal "-0.0000123") |> equal -1.M
    Math.Floor -0.0836M |> equal -1.M
    Math.Floor (decimal 0.0836) |> equal 0.M
    Math.Ceiling (decimal 0.0836) |> equal 1.M
    Math.Ceiling (decimal "0.0000123") |> equal 1.M
    Math.Ceiling (decimal -0.0836) |> equal 0.M
    Math.Round (decimal 0.06) |> equal 0.M
    Math.Round (decimal 0.0836, 2) |> equal 0.08M
    Math.Round (decimal -0.0836, 3) |> equal -0.084M
    Math.Truncate (decimal -0.0836) |> equal 0.M
    Math.Floor (0.M - 0.0836M) |> equal -1.M

[<Fact>]
let ``test Decimal values below 0.1 hash the same however they are built`` () =
    (decimal -0.0836).GetHashCode() |> equal ((0.M - 0.0836M).GetHashCode())
    (decimal "0.05").GetHashCode() |> equal ((0.1M / 2.M).GetHashCode())
    let set = Collections.Generic.HashSet<decimal>()
    set.Add(decimal -0.0836) |> equal true
    set.Add(0.M - 0.0836M) |> equal false
    let dict = Collections.Generic.Dictionary<decimal, string>()
    dict.[decimal "0.05"] <- "a"
    dict.ContainsKey(0.1M / 2.M) |> equal true

[<Fact>]
let ``test Decimal hash ignores trailing zeros and the sign of zero`` () =
    (decimal "1.0").GetHashCode() |> equal ((decimal "1").GetHashCode())
    (decimal "0.050").GetHashCode() |> equal ((0.1M / 2.M).GetHashCode())
    (decimal "0.00").GetHashCode() |> equal ((decimal "0").GetHashCode())
    (-(0.M)).GetHashCode() |> equal ((0.M).GetHashCode())
    let set = Collections.Generic.HashSet<decimal>([ 1.M ])
    set.Contains 1.0M |> equal true
    set.Add 0.M |> equal true
    set.Add(Math.Truncate -0.0836M) |> equal false
    let dict = Collections.Generic.Dictionary<decimal, string>()
    dict.[0.050M] <- "a"
    dict.ContainsKey(0.1M / 2.M) |> equal true

[<Fact>]
let ``test Decimal parsing rounds to 28 places and keeps the scale of zero`` () =
    string (decimal "0.0000000000000000000000000000004") |> equal "0.0000000000000000000000000000"
    string (decimal "0.00000000000000000000000000005") |> equal "0.0000000000000000000000000000"
    string (decimal "0.00000000000000000000000000015") |> equal "0.0000000000000000000000000002"
    string (decimal "0.000000000000000000000000000012") |> equal "0.0000000000000000000000000000"
    Decimal.GetBits(decimal "0.0000000000000000000000000000004") |> equal [| 0; 0; 0; 1835008 |]
    Decimal.GetBits(decimal "0.00") |> equal [| 0; 0; 0; 131072 |]
    string (-(0.00M)) |> equal "0.00"
    string (abs 0.00M) |> equal "0.00"
    string (Math.Round(0.004M, 2)) |> equal "0.00"
    (0.00M).ToString("E3", System.Globalization.CultureInfo.InvariantCulture) |> equal "0.000E+000"
    (decimal "0.00").GetHashCode() |> equal (Decimal(0, 0, 0, false, 2uy).GetHashCode())

[<Fact>]
let ``test Decimal addition and subtraction keep the larger scale`` () =
    string (1.50M + 0.5M) |> equal "2.00"
    string (1.5M + 0.50M) |> equal "2.00"
    string (0.1M + 0.2M) |> equal "0.3"
    string (1M + 1M) |> equal "2"
    string (0.00M + 0M) |> equal "0.00"
    string (0.00M + 1.5M) |> equal "1.50"
    string (1.0M + (-1.0M)) |> equal "0.0"
    string (0.05M - 0.05M) |> equal "0.00"
    string (1.00M - 0.50M) |> equal "0.50"
    string (100.5M - 0.5M) |> equal "100.0"
    string (1.5M - 0.00M) |> equal "1.50"

[<Fact>]
let ``test Decimal multiplication adds the scales up to 28 places`` () =
    string (2.0M * 3.0M) |> equal "6.00"
    string (1.5M * 2M) |> equal "3.0"
    string (0.5M * 0.5M) |> equal "0.25"
    string (1.50M * 1.0M) |> equal "1.500"
    string (10M * 0.1M) |> equal "1.0"
    string (1.10M * 1.10M) |> equal "1.2100"
    string (0.0M * 5M) |> equal "0.0"
    string (0M * 1.50M) |> equal "0.00"
    string (pown 1.50M 2) |> equal "2.2500"
    string (0.1234567890123456789012345678M * 0.1M) |> equal "0.0123456789012345678901234568"
    string (0.0000000000000000000000000025M * 0.1M) |> equal "0.0000000000000000000000000002"
    string (0.0000000000000000000000000035M * 0.1M) |> equal "0.0000000000000000000000000004"
    string (123456789012345678901234567.89M * 1.1M) |> equal "135802467913580246791358024.68"

[<Fact>]
let ``test Decimal division keeps the scale of an exact quotient`` () =
    string (1.00M / 2M) |> equal "0.50"
    string (10M / 2M) |> equal "5"
    string (1M / 4M) |> equal "0.25"
    string (1.0M / 0.5M) |> equal "2"
    string (2M / 1.0M) |> equal "2"
    string (5.0M / 2.0M) |> equal "2.5"
    string (1.000M / 8M) |> equal "0.125"
    string (1.23M / 0.1M) |> equal "12.3"
    string (0.0M / 5M) |> equal "0.0"

[<Fact>]
let ``test Decimal division rounds an inexact quotient half to even to fit a decimal`` () =
    string (1M / 3M) |> equal "0.3333333333333333333333333333"
    string (2M / 3M) |> equal "0.6666666666666666666666666667"
    string (10M / 3M) |> equal "3.3333333333333333333333333333"
    string (100M / 3M) |> equal "33.333333333333333333333333333"
    string (1M / 30000M) |> equal "0.0000333333333333333333333333"
    string (1M / 7M) |> equal "0.1428571428571428571428571429"
    string (80M / 9M) |> equal "8.888888888888888888888888889"
    string (1000000000000000000000000000M / 3M) |> equal "333333333333333333333333333.33"
    string (10000000000000000000000000001M / 2M) |> equal "5000000000000000000000000000.5"
    string (0.0000000000000000000000000005M / 2M) |> equal "0.0000000000000000000000000002"
    string (0.0000000000000000000000000007M / 2M) |> equal "0.0000000000000000000000000004"
    string (0.0000000000000000000000000001M / 2M) |> equal "0"

[<Fact>]
let ``test Decimal remainder keeps the larger scale`` () =
    string (5.0M % 2M) |> equal "1.0"
    string (5M % 2.0M) |> equal "1.0"
    string (5.5M % 2M) |> equal "1.5"
    string (7.00M % 2.5M) |> equal "2.00"
    string (-5.0M % 2M) |> equal "-1.0"
    string (1.5M % 2.00M) |> equal "1.5"

[<Fact>]
let ``test Decimal arithmetic and parsing throw on overflow`` () =
    (fun () -> Decimal.MaxValue + 1M) |> throwsError ""
    (fun () -> Decimal.MaxValue + 0.5M) |> throwsError ""
    string (Decimal.MaxValue + 0.4M) |> equal "79228162514264337593543950335"
    string ((Decimal.MaxValue - 1M) + 1M) |> equal "79228162514264337593543950335"
    (fun () -> Decimal.MinValue - 1M) |> throwsError ""
    (fun () -> Decimal.MaxValue * 1.1M) |> throwsError ""
    string (Decimal.MaxValue * 1.0M) |> equal "79228162514264337593543950335"
    (fun () -> Decimal.MaxValue / 0.5M) |> throwsError ""
    (fun () -> decimal "1e30") |> throwsError ""
    (fun () -> decimal "79228162514264337593543950336") |> throwsError ""
    (fun () -> decimal "79228162514264337593543950335.5") |> throwsError ""
    string (decimal "79228162514264337593543950335.4") |> equal "79228162514264337593543950335"
    (fun () -> decimal 1e30) |> throwsError ""

[<Fact>]
let ``test Decimal from float rounds to 15 significant digits`` () =
    let inv = CultureInfo.InvariantCulture
    string (decimal 0.1) |> equal "0.1"
    string (decimal (0.1 + 0.2)) |> equal "0.3"
    string (decimal 123456789.123456789) |> equal "123456789.123457"
    string (decimal (1.0 / 3.0)) |> equal "0.333333333333333"
    string (decimal 123456789012345.6789) |> equal "123456789012346"
    string (decimal 123456789012345678.0) |> equal "123456789012346000"
    string (decimal 1e20) |> equal "100000000000000000000"
    string (decimal 1e28) |> equal "10000000000000000000000000000"
    string (decimal 1e-10) |> equal "0.0000000001"
    string (decimal 1.5e-28) |> equal "0.0000000000000000000000000002"
    string (decimal 5e-29) |> equal "0"
    string (decimal 1e-30) |> equal "0"
    string (decimal -0.0) |> equal "0"
    string (decimal 100000000000001.5) |> equal "100000000000002"
    string (decimal 100000000000002.5) |> equal "100000000000002"
    (fun () -> decimal 1e29) |> throwsError ""
    (fun () -> decimal nan) |> throwsError ""
    (fun () -> decimal infinity) |> throwsError ""

[<Fact>]
let ``test Decimal from float32 rounds to 7 significant digits`` () =
    let inv = CultureInfo.InvariantCulture
    string (decimal 1.1f) |> equal "1.1"
    string (decimal (0.1f + 0.2f)) |> equal "0.3"
    string (decimal 16777216.f) |> equal "16777220"
    string (decimal 1.23456789f) |> equal "1.234568"
    string (decimal 123456.789f) |> equal "123456.8"
    string (decimal 1000001.5f) |> equal "1000002"
    string (decimal 1000002.5f) |> equal "1000002"
    string (decimal 1e-30f) |> equal "0"
    (fun () -> decimal 3.4e38f) |> throwsError ""

[<Fact>]
let ``test Decimal G format keeps the scale without a precision`` () =
    let inv = CultureInfo.InvariantCulture
    (1.10M).ToString("G", inv) |> equal "1.10"
    (0.00M).ToString("G", inv) |> equal "0.00"
    (1.10M).ToString("G5", inv) |> equal "1.1"
    (123456M).ToString("G3", inv) |> equal "1.23E+05"
    (0.0001234M).ToString("G3", inv) |> equal "0.000123"
    (2.5M).ToString("G1", inv) |> equal "3"
    (1.5M).ToString("G1", inv) |> equal "2"

[<Fact>]
let ``test Decimal max returns the first of two equal values`` () =
    let inv = CultureInfo.InvariantCulture
    string (max 1.0M 1.00M) |> equal "1.0"
    string (min 1.0M 1.00M) |> equal "1.00"
    string (Math.Max(1.0M, 1.00M)) |> equal "1.0"
    string (Math.Min(1.0M, 1.00M)) |> equal "1.00"

[<Fact>]
let ``test Decimal static conversions truncate and check the range`` () =
    Decimal.ToInt32 2.9M |> equal 2
    Decimal.ToInt32 -2.9M |> equal -2
    Decimal.ToInt64 -2.9M |> equal -2L
    Decimal.ToInt64 9223372036854775807.5M |> equal 9223372036854775807L
    Decimal.ToUInt64 18446744073709551615M |> equal 18446744073709551615UL
    Decimal.ToInt16 32767.5M |> equal 32767s
    Decimal.ToUInt16 65535.9M |> equal 65535us
    Decimal.ToByte 255.9M |> equal 255uy
    Decimal.ToSByte -128.9M |> equal -128y
    Decimal.ToUInt32 4294967295.9M |> equal 4294967295u
    Decimal.ToDouble 0.1M |> equal 0.1
    Decimal.ToSingle 1.5M |> equal 1.5f
    (fun () -> Decimal.ToInt32 2147483648M) |> throwsError ""
    (fun () -> Decimal.ToByte -1M) |> throwsError ""
    Decimal.ToUInt64 -0.5M |> equal 0UL

[<Fact>]
let ``test Decimal rounding keeps the requested scale`` () =
    string (Math.Round(1.20001M, 2)) |> equal "1.20"
    string (Math.Round(1.2M, 3)) |> equal "1.2"
    string (Math.Round(1.99M, 1)) |> equal "2.0"
    string (Math.Floor 1.50M) |> equal "1"
    string (Math.Ceiling 1.50M) |> equal "2"
    string (Math.Truncate 1.50M) |> equal "1"

[<Fact>]
let ``test Decimal rounding is half to even when a trailing zero follows the 5`` () =
    Math.Round 2.50M |> equal 2.M
    Math.Round 0.50M |> equal 0.M
    Math.Round(1.250M, 1) |> equal 1.2M
    Math.Round(0.050M, 1) |> equal 0.0M
    Math.Round(0.0050M, 2) |> equal 0.00M

[<Fact>]
let ``test sqrt matches .net core implementation`` () =
    checkTo3dp 1732. (sqrt 3.0)
    sqrt 0.0  |> equal 0.0
    isNaN (sqrt -3.0) |> equal true
    isNaN (sqrt Double.NaN) |> equal true
    isNaN (sqrt negativeInfinity) |> equal true
    sqrt positiveInfinity |> equal positiveInfinity

[<Fact>]
let ``test float32 arithmetic rounds every operation like .NET`` () =
    let a, b, c = 1.5f, 1.2f, 3.3f
    (a + b) * c |> equal 8.9099998f
    a + b + c |> equal 6.f
    0.1f + 0.2f |> equal 0.3f
    16777216.f + 1.f |> equal 16777216.f
    1.f / 3.f |> equal 0.33333334f
    5.5f % 2.2f |> equal 1.0999999f
    -(a + b) |> equal -2.7f
    let arr = [| 0.f |]
    arr.[0] <- a * c
    arr.[0] |> equal 4.95f

[<Fact>]
let ``test Math.Round rounds the exact value`` () =
    // See #5251
    Math.Round 2.500000001 |> equal 3.
    Math.Round 3.4999999999 |> equal 3.
    Math.Round -2.500000001 |> equal -3.
    Math.Round -3.4999999999 |> equal -3.
    Math.Round 2.5 |> equal 2.
    Math.Round 3.5 |> equal 4.
    Math.Round 0.49999999999999994 |> equal 0.
    1. / Math.Round(-0.5) |> equal -infinity
    Math.Round(1.2500000001, 1) |> equal 1.3
    Math.Round(2.0000000050001, 8) |> equal 2.00000001
    Math.Round(2.675, 2) |> equal 2.68
    Math.Round(123456.785, 2) |> equal 123456.78
    round 2.500000001 |> equal 3.
    round 3.4999999999 |> equal 3.
    Convert.ToInt32 2.500000001 |> equal 3
    Convert.ToInt32 3.4999999999 |> equal 3
    MathF.Round 2.500001f |> equal 3.f
    MathF.Round 3.499999f |> equal 3.f
    MathF.Round 2.5f |> equal 2.f

[<Fact>]
let ``test Math.Round validates its digits`` () =
    (fun () -> Math.Round(1., 16)) |> throwsAnyError
    (fun () -> Math.Round(1., -1)) |> throwsAnyError
    (fun () -> MathF.Round(1.f, 7)) |> throwsAnyError
    Math.Round(1.2345678901234567, 15) |> equal 1.234567890123457
    Math.Round(1e16, 2) |> equal 1e16

[<Fact>]
let ``test Math.Round with MidpointRounding works`` () =
    let round mode = [ 2.5; -2.5; 3.5; -3.5; 2.4; -2.6; 0.5; -0.5 ] |> List.map (fun x -> Math.Round(x, (mode: MidpointRounding)))
    round MidpointRounding.ToEven |> equal [ 2.; -2.; 4.; -4.; 2.; -3.; 0.; -0. ]
    round MidpointRounding.AwayFromZero |> equal [ 3.; -3.; 4.; -4.; 2.; -3.; 1.; -1. ]
    round MidpointRounding.ToZero |> equal [ 2.; -2.; 3.; -3.; 2.; -2.; 0.; -0. ]
    round MidpointRounding.ToNegativeInfinity |> equal [ 2.; -3.; 3.; -4.; 2.; -3.; 0.; -1. ]
    round MidpointRounding.ToPositiveInfinity |> equal [ 3.; -2.; 4.; -3.; 3.; -2.; 1.; -0. ]
    Math.Round(0.49999999999999994, MidpointRounding.AwayFromZero) |> equal 0.
    Math.Round(4503599627370497., MidpointRounding.AwayFromZero) |> equal 4503599627370497.
    1. / Math.Round(-0.4, MidpointRounding.AwayFromZero) |> equal -infinity

[<Fact>]
let ``test Math.Round with digits and MidpointRounding works`` () =
    let round mode = [ 1.25, 1; -1.25, 1; 1.235, 2; 2.675, 2; -2.675, 2; 1.426, 2; 0.125, 2; -1.005, 2 ] |> List.map (fun (x, d) -> Math.Round(x, d, (mode: MidpointRounding)))
    round MidpointRounding.ToEven |> equal [ 1.2; -1.2; 1.24; 2.68; -2.68; 1.43; 0.12; -1. ]
    round MidpointRounding.AwayFromZero |> equal [ 1.3; -1.3; 1.24; 2.68; -2.68; 1.43; 0.13; -1. ]
    round MidpointRounding.ToZero |> equal [ 1.2; -1.2; 1.23; 2.67; -2.67; 1.42; 0.12; -1. ]
    round MidpointRounding.ToNegativeInfinity |> equal [ 1.2; -1.3; 1.23; 2.67; -2.68; 1.42; 0.12; -1.01 ]
    round MidpointRounding.ToPositiveInfinity |> equal [ 1.3; -1.2; 1.24; 2.68; -2.67; 1.43; 0.13; -1. ]
    Math.Round(1e17, 2, MidpointRounding.AwayFromZero) |> equal 1e17

[<Fact>]
let ``test Math.Round with MidpointRounding.ToEven rounds the exact value`` () =
    Math.Round(2.500000001, MidpointRounding.ToEven) |> equal 3.
    Math.Round(-2.500000001, MidpointRounding.ToEven) |> equal -3.
    Math.Round(2.499999999, MidpointRounding.ToEven) |> equal 2.
    Math.Round(1.015, 2, MidpointRounding.ToEven) |> equal 1.01
    Math.Round(1.015, 2, MidpointRounding.AwayFromZero) |> equal 1.01
    Math.Round(1.025, 2, MidpointRounding.ToEven) |> equal 1.02
    1. / Math.Round(-0.5, MidpointRounding.ToEven) |> equal -infinity
    1. / Math.Round(-0.04, 1, MidpointRounding.ToEven) |> equal -infinity

[<Fact>]
let ``test Math.Round with MidpointRounding keeps NaN and infinities`` () =
    let modes = [ MidpointRounding.ToEven; MidpointRounding.AwayFromZero; MidpointRounding.ToZero; MidpointRounding.ToNegativeInfinity; MidpointRounding.ToPositiveInfinity ]
    for mode in modes do
        Double.IsNaN(Math.Round(nan, mode)) |> equal true
        Double.IsNaN(Math.Round(nan, 2, mode)) |> equal true
        Math.Round(infinity, mode) |> equal infinity
        Math.Round(-infinity, 2, mode) |> equal -infinity

[<Fact>]
let ``test Math.Round with MidpointRounding validates its arguments`` () =
    (fun () -> Math.Round(1.5, enum<MidpointRounding> 5)) |> throwsAnyError
    (fun () -> Math.Round(1e17, enum<MidpointRounding> 5)) |> throwsAnyError
    (fun () -> Math.Round(nan, enum<MidpointRounding> 5)) |> throwsAnyError
    (fun () -> Math.Round(1.5, 2, enum<MidpointRounding> -1)) |> throwsAnyError
    (fun () -> Math.Round(1.5, 16, MidpointRounding.AwayFromZero)) |> throwsAnyError
    (fun () -> Math.Round(1.5, -1, MidpointRounding.ToEven)) |> throwsAnyError
    (fun () -> Math.Round(nan, 16, MidpointRounding.ToEven)) |> throwsAnyError
    Math.Round(1.5, 15, MidpointRounding.AwayFromZero) |> equal 1.5

[<Fact>]
let ``test Math.Round with digits and MidpointRounding skips mode validation for unrounded values`` () =
    Math.Round(1e17, 2, enum<MidpointRounding> 5) |> equal 1e17
    Math.Round(infinity, 2, enum<MidpointRounding> 5) |> equal infinity
    Double.IsNaN(Math.Round(nan, 2, enum<MidpointRounding> 5)) |> equal true

[<Fact>]
let ``test MathF.Round with MidpointRounding works`` () =
    MathF.Round(2.5f, MidpointRounding.AwayFromZero) |> equal 3.f
    MathF.Round(-2.5f, MidpointRounding.AwayFromZero) |> equal -3.f
    MathF.Round(2.5f, MidpointRounding.ToEven) |> equal 2.f
    MathF.Round(2.5f, MidpointRounding.ToZero) |> equal 2.f
    MathF.Round(-2.5f, MidpointRounding.ToNegativeInfinity) |> equal -3.f
    MathF.Round(-2.5f, MidpointRounding.ToPositiveInfinity) |> equal -2.f
    MathF.Round(1.5f, 6, MidpointRounding.AwayFromZero) |> equal 1.5f
    MathF.Round(1e9f, 2, enum<MidpointRounding> 5) |> equal 1e9f
    (fun () -> MathF.Round(1.5f, 7, MidpointRounding.AwayFromZero)) |> throwsAnyError
    (fun () -> MathF.Round(1e9f, enum<MidpointRounding> 5)) |> throwsAnyError

[<Fact>]
let ``test Math.log10 works`` () =
    Math.Log10 232.12 |> checkTo3dp 2365.

[<Fact>]
let ``test Numeric Min/Max/MinMagnitude/MaxMagnitude propagate NaN`` () =
    Double.IsNaN(Double.Min(nan, 1.0)) |> equal true
    Double.IsNaN(Double.Min(1.0, nan)) |> equal true
    Double.IsNaN(Double.Max(nan, 1.0)) |> equal true
    Double.IsNaN(Double.Max(1.0, nan)) |> equal true
    Double.IsNaN(Double.MinMagnitude(nan, 1.0)) |> equal true
    Double.IsNaN(Double.MinMagnitude(1.0, nan)) |> equal true
    Double.IsNaN(Double.MaxMagnitude(nan, 1.0)) |> equal true
    Double.IsNaN(Double.MaxMagnitude(1.0, nan)) |> equal true

[<Fact>]
let ``test Math.Min/Max/MinMagnitude/MaxMagnitude propagate NaN`` () =
    Double.IsNaN(Math.Min(nan, 1.0)) |> equal true
    Double.IsNaN(Math.Min(1.0, nan)) |> equal true
    Double.IsNaN(Math.Max(nan, 1.0)) |> equal true
    Double.IsNaN(Math.Max(1.0, nan)) |> equal true
    Double.IsNaN(Math.MinMagnitude(nan, 1.0)) |> equal true
    Double.IsNaN(Math.MinMagnitude(1.0, nan)) |> equal true
    Double.IsNaN(Math.MaxMagnitude(nan, 1.0)) |> equal true
    Double.IsNaN(Math.MaxMagnitude(1.0, nan)) |> equal true

[<Fact>]
let ``test Long integers equality works`` () =
    let x = 5L
    let y = 5L
    let z = 6L
    (x = y) |> equal true
    (y = z) |> equal false
    equals y x |> equal true
    equals z x |> equal false

[<Fact>]
let ``test Long integers comparison works`` () =
    let x = 5L
    let y = 5L
    let z = 6L
    compare x y |> equal 0
    compare y z |> equal -1
    compareTo y x |> equal 0
    compareTo z x |> equal 1

[<Fact>]
let ``test bigint equality works`` () =
    let a = 9007199254740992I
    let b = 9007199254740993I
    (a = b) |> equal false

[<Fact>]
let ``test Big integers equality works`` () =
    let x = 59823749821707124891298739821798327321028091380980I
    let y = 59823749821707124891298739821798327321028091380980I
    let z = 59823749821707124891298739821798327321028091380981I
    (x = y) |> equal true
    (y = z) |> equal false
    equals y x |> equal true
    equals z x |> equal false

[<Fact>]
let ``test BigInteger.GreatestCommonDivisor works with negatives`` () =
    bigint.GreatestCommonDivisor(-4I, 6I) |> equal 2I
    bigint.GreatestCommonDivisor(4I, -6I) |> equal 2I
    bigint.GreatestCommonDivisor(-4I, -6I) |> equal 2I
    bigint.GreatestCommonDivisor(0I, -5I) |> equal 5I

[<Fact>]
let ``test BigInteger.Log2 works for non-powers-of-two`` () =
    bigint.Log2 5I |> equal 2I
    bigint.Log2 8I |> equal 3I

[<Fact>]
let ``test BigInteger.GetBitLength works`` () =
    (0I).GetBitLength() |> equal 0L
    (-1I).GetBitLength() |> equal 0L
    (255I).GetBitLength() |> equal 8L
    (-8I).GetBitLength() |> equal 3L

[<Fact>]
let ``test Sign operator works`` () =
    // See #1311
    sign 1 |> equal 1
    sign 34 |> equal 1
    sign 1L |> equal 1
    sign 36L |> equal 1
    sign 1. |> equal 1
    sign 89 |> equal 1
    sign 1 |> equal 1
    sign 0 |> equal 0
    sign 0L |> equal 0
    sign 0. |> equal 0
    sign -1 |> equal -1
    sign -56 |> equal -1
    sign -1L |> equal -1
    sign -72L |> equal -1
    sign -1. |> equal -1
    sign -89. |> equal -1

[<Fact>]
let ``test Decimal.Parse follows NumberStyles`` () =
    let inv = CultureInfo.InvariantCulture
    Decimal.Parse("+5", inv) |> equal 5M
    Decimal.Parse(" 5 ", inv) |> equal 5M
    Decimal.Parse("5-", inv) |> equal -5M
    Decimal.Parse("1,234.5", inv) |> equal 1234.5M
    Decimal.Parse("1,23,4", inv) |> equal 1234M
    Decimal.Parse(".5", inv) |> equal 0.5M
    Decimal.Parse("5.", inv) |> equal 5M
    string (Decimal.Parse("-0.00", inv)) |> equal "0.00"
    (fun () -> Decimal.Parse("1e3", inv)) |> throwsError ""
    (fun () -> Decimal.Parse(",5", inv)) |> throwsError ""
    (fun () -> Decimal.Parse("1,234.5,6", inv)) |> throwsError ""
    (fun () -> Decimal.Parse("(5)", inv)) |> throwsError ""
    (fun () -> Decimal.Parse("", inv)) |> throwsError ""
    Decimal.Parse("1.5E+2", NumberStyles.Float, inv) |> equal 150M
    string (Decimal.Parse("1.50e1", NumberStyles.Float, inv)) |> equal "15.0"
    Decimal.Parse("1e3", NumberStyles.Any, inv) |> equal 1000M
    Decimal.Parse("(5)", NumberStyles.Any, inv) |> equal -5M
    (fun () -> Decimal.Parse("1,234", NumberStyles.Float, inv)) |> throwsError ""
    (fun () -> Decimal.Parse("1e30", NumberStyles.Float, inv)) |> throwsError ""
    let ok1, v1 = Decimal.TryParse("1,5", NumberStyles.Number, inv)
    ok1 |> equal true
    v1 |> equal 15M
    let ok2, _ = Decimal.TryParse("1e3", NumberStyles.Number, inv)
    ok2 |> equal false

[<Fact>]
let ``test Big integer to byte array round-trips negatives`` () =
    // See regression where -62837 corrupted the sign extension
    (bigint -62837).ToByteArray() |> equal [|0x8Buy; 0x0Auy; 0xFFuy|]
    Numerics.BigInteger((bigint -62837).ToByteArray()) |> equal -62837I
    (bigint -129).ToByteArray() |> equal [|0x7Fuy; 0xFFuy|]
    Numerics.BigInteger((bigint -129).ToByteArray()) |> equal -129I
    (bigint -256).ToByteArray() |> equal [|0x00uy; 0xFFuy|]
    Numerics.BigInteger((bigint -256).ToByteArray()) |> equal -256I
    (bigint 255).ToByteArray() |> equal [|0xFFuy; 0x00uy|]
    Numerics.BigInteger((bigint 255).ToByteArray()) |> equal 255I

[<Fact>]
let ``test BigInteger checked conversions throw on overflow`` () =
    (fun () -> int8 200I) |> throwsError ""
    (fun () -> uint8 -1I) |> throwsError ""
    (fun () -> int32 3000000000I) |> throwsError ""
    (fun () -> byte 256I) |> throwsError ""
    (fun () -> sbyte 200I) |> throwsError ""


// ---- ported from tests/Js/Main (2026-11-16, remaining) ----

[<Fact>]
let ``test float32 conversions round like .NET`` () =
    float32 2.7 |> equal 2.7f
    float32 16777217 |> equal 16777216.f
    float32 16777217L |> equal 16777216.f
    float32 2.7M |> equal 2.7f
    float32 "2.7" |> equal 2.7f
    Single.Parse("2.7", CultureInfo.InvariantCulture) |> equal 2.7f
    let mutable parsed = 0.f
    Single.TryParse("2.7", NumberStyles.Float, CultureInfo.InvariantCulture, &parsed) |> equal true
    parsed |> equal 2.7f

