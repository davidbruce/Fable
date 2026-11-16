module Fable.Tests.Zig.NullableTests

open System
open Fable.Tests.Util
open Fable.Tests.Util.Testing
open FSharp.Linq

[<Fact>]
let ``test Nullable.char works`` () =
    Nullable.char (Nullable 49uy) |> equal (Nullable '1')
    Nullable.char (Nullable 53) |> equal (Nullable '5')
    Nullable.char (Nullable 55L) |> equal (Nullable '7')
    Nullable.char (Nullable 57m) |> equal (Nullable '9')
    Nullable.char (Nullable 58.0) |> equal (Nullable ':')
    Nullable.char (Nullable 'a') |> equal (Nullable 'a')
    Nullable.char (Nullable<int>()) |> equal (Nullable<char>())

[<Fact>]
let ``test Nullable.decimal works`` () =
    Nullable.decimal (Nullable 5) |> equal (Nullable 5m)
    Nullable.decimal (Nullable 7L) |> equal (Nullable 7m)
    Nullable.decimal (Nullable 10.5) |> equal (Nullable 10.5m)
    Nullable.decimal (Nullable<float>()) |> equal (Nullable<decimal>())

[<Fact>]
let ``test Nullable.enum works`` () =
    (Nullable.enum (Nullable 2): Nullable<DayOfWeek>) |> equal (Nullable DayOfWeek.Tuesday)
    (Nullable.enum (Nullable<int>()): Nullable<DayOfWeek>) |> equal (Nullable<DayOfWeek>())

[<Fact>]
let ``test Nullable.float and Nullable.float32 work`` () =
    Nullable.float (Nullable 1uy) |> equal (Nullable 1.0)
    Nullable.float (Nullable 5) |> equal (Nullable 5.0)
    Nullable.float (Nullable 7L) |> equal (Nullable 7.0)
    Nullable.float (Nullable 9m) |> equal (Nullable 9.0)
    Nullable.float (Nullable 'c') |> equal (Nullable 99.0)
    Nullable.float (Nullable<int>()) |> equal (Nullable<float>())
    Nullable.float32 (Nullable 5) |> equal (Nullable 5.0f)
    Nullable.float32 (Nullable 10.0) |> equal (Nullable 10.0f)
    Nullable.float32 (Nullable<int>()) |> equal (Nullable<float32>())
    Nullable.double (Nullable 5) |> equal (Nullable 5.0)
    Nullable.single (Nullable 9.5) |> equal (Nullable 9.5f)

[<Fact>]
let ``test Nullable integer conversions work`` () =
    Nullable.int (Nullable 1uy) |> equal (Nullable 1)
    Nullable.int (Nullable 7L) |> equal (Nullable 7)
    Nullable.int (Nullable 9m) |> equal (Nullable 9)
    Nullable.int (Nullable 10.9) |> equal (Nullable 10)
    Nullable.int (Nullable -11.9) |> equal (Nullable -11)
    Nullable.int (Nullable 'c') |> equal (Nullable 99)
    Nullable.int (Nullable<float>()) |> equal (Nullable<int>())
    Nullable.int16 (Nullable -7L) |> equal (Nullable -7s)
    Nullable.int32 (Nullable 5L) |> equal (Nullable 5)
    Nullable.int64 (Nullable -9.9) |> equal (Nullable -9L)
    Nullable.int64 (Nullable<int>()) |> equal (Nullable<int64>())
    Nullable.int8 (Nullable 9.9) |> equal (Nullable 9y)
    Nullable.sbyte (Nullable -7.9) |> equal (Nullable -7y)
    Nullable.byte (Nullable 5) |> equal (Nullable 5uy)
    Nullable.uint8 (Nullable 7L) |> equal (Nullable 7uy)
    Nullable.uint16 (Nullable 9.9) |> equal (Nullable 9us)
    Nullable.uint (Nullable 5) |> equal (Nullable 5u)
    Nullable.uint32 (Nullable 7L) |> equal (Nullable 7u)
    Nullable.uint64 (Nullable<int>()) |> equal (Nullable<uint64>())

[<Fact>]
let ``test Nullable conversions evaluate their argument once`` () =
    let mutable calls = 0
    let next () =
        calls <- calls + 1
        Nullable 5
    Nullable.float (next ()) |> equal (Nullable 5.0)
    calls |> equal 1

// ---- ported from tests/Js/Main (2026-11-16) ----

let private none<'T when 'T: struct and 'T: (new: unit -> 'T) and 'T :> ValueType> = Nullable<'T>()


[<Fact>]
let ``test Nullable.char`` () =
    Nullable.char (Nullable 49uy) |> equal (Nullable '1')
    Nullable.char (Nullable 50y) |> equal (Nullable '2')
    Nullable.char (Nullable 51s) |> equal (Nullable '3')
    Nullable.char (Nullable 52us) |> equal (Nullable '4')
    Nullable.char (Nullable 53) |> equal (Nullable '5')
    Nullable.char (Nullable 54u) |> equal (Nullable '6')
    Nullable.char (Nullable 55L) |> equal (Nullable '7')
    Nullable.char (Nullable 56UL) |> equal (Nullable '8')
    Nullable.char (Nullable 57m) |> equal (Nullable '9')
    Nullable.char (Nullable 58.0) |> equal (Nullable ':')
    Nullable.char (Nullable 59.0f) |> equal (Nullable ';')
    Nullable.char (Nullable 'a') |> equal (Nullable 'a')
    Nullable.char none<int> |> equal none<char>

[<Fact>]
let ``test Nullable.decimal`` () =
    Nullable.decimal (Nullable 1uy) |> equal (Nullable 1m)
    Nullable.decimal (Nullable 2y) |> equal (Nullable 2m)
    Nullable.decimal (Nullable 3s) |> equal (Nullable 3m)
    Nullable.decimal (Nullable 4us) |> equal (Nullable 4m)
    Nullable.decimal (Nullable 5) |> equal (Nullable 5m)
    Nullable.decimal (Nullable 6u) |> equal (Nullable 6m)
    Nullable.decimal (Nullable 7L) |> equal (Nullable 7m)
    Nullable.decimal (Nullable 8UL) |> equal (Nullable 8m)
    Nullable.decimal (Nullable 9m) |> equal (Nullable 9m)
    Nullable.decimal (Nullable 10.5) |> equal (Nullable 10.5m)
    Nullable.decimal (Nullable 11.5f) |> equal (Nullable 11.5m)
    Nullable.decimal none<float> |> equal none<decimal>

[<Fact>]
let ``test Nullable.double`` () =
    Nullable.double (Nullable 5) |> equal (Nullable 5.0)
    Nullable.double (Nullable 7L) |> equal (Nullable 7.0)
    Nullable.double (Nullable 9m) |> equal (Nullable 9.0)
    Nullable.double (Nullable 11.5f) |> equal (Nullable 11.5)
    Nullable.double none<int> |> equal none<float>

[<Fact>]
let ``test Nullable.enum`` () =
    (Nullable.enum (Nullable 2): Nullable<DayOfWeek>) |> equal (Nullable DayOfWeek.Tuesday)
    (Nullable.enum none<int>: Nullable<DayOfWeek>) |> equal none<DayOfWeek>

[<Fact>]
let ``test Nullable.float`` () =
    Nullable.float (Nullable 1uy) |> equal (Nullable 1.0)
    Nullable.float (Nullable 2y) |> equal (Nullable 2.0)
    Nullable.float (Nullable 3s) |> equal (Nullable 3.0)
    Nullable.float (Nullable 4us) |> equal (Nullable 4.0)
    Nullable.float (Nullable 5) |> equal (Nullable 5.0)
    Nullable.float (Nullable 6u) |> equal (Nullable 6.0)
    Nullable.float (Nullable 7L) |> equal (Nullable 7.0)
    Nullable.float (Nullable 8UL) |> equal (Nullable 8.0)
    Nullable.float (Nullable 9m) |> equal (Nullable 9.0)
    Nullable.float (Nullable 10.0) |> equal (Nullable 10.0)
    Nullable.float (Nullable 11.0f) |> equal (Nullable 11.0)
    Nullable.float (Nullable 'c') |> equal (Nullable 99.0)
    Nullable.float none<int> |> equal none<float>

[<Fact>]
let ``test Nullable.float32`` () =
    Nullable.float32 (Nullable 1uy) |> equal (Nullable 1.0f)
    Nullable.float32 (Nullable 2y) |> equal (Nullable 2.0f)
    Nullable.float32 (Nullable 3s) |> equal (Nullable 3.0f)
    Nullable.float32 (Nullable 4us) |> equal (Nullable 4.0f)
    Nullable.float32 (Nullable 5) |> equal (Nullable 5.0f)
    Nullable.float32 (Nullable 6u) |> equal (Nullable 6.0f)
    Nullable.float32 (Nullable 7L) |> equal (Nullable 7.0f)
    Nullable.float32 (Nullable 8UL) |> equal (Nullable 8.0f)
    Nullable.float32 (Nullable 9m) |> equal (Nullable 9.0f)
    Nullable.float32 (Nullable 10.0) |> equal (Nullable 10.0f)
    Nullable.float32 (Nullable 11.0f) |> equal (Nullable 11.0f)
    Nullable.float32 (Nullable 'c') |> equal (Nullable 99.0f)
    Nullable.float32 none<int> |> equal none<float32>

[<Fact>]
let ``test Nullable.int`` () =
    Nullable.int (Nullable 1uy) |> equal (Nullable 1)
    Nullable.int (Nullable 2y) |> equal (Nullable 2)
    Nullable.int (Nullable 3s) |> equal (Nullable 3)
    Nullable.int (Nullable 4us) |> equal (Nullable 4)
    Nullable.int (Nullable 5) |> equal (Nullable 5)
    Nullable.int (Nullable 6u) |> equal (Nullable 6)
    Nullable.int (Nullable 7L) |> equal (Nullable 7)
    Nullable.int (Nullable 8UL) |> equal (Nullable 8)
    Nullable.int (Nullable 9m) |> equal (Nullable 9)
    Nullable.int (Nullable 10.9) |> equal (Nullable 10)
    Nullable.int (Nullable -11.9f) |> equal (Nullable -11)
    Nullable.int (Nullable 'c') |> equal (Nullable 99)
    Nullable.int none<float> |> equal none<int>

[<Fact>]
let ``test Nullable.int16`` () =
    Nullable.int16 (Nullable 5) |> equal (Nullable 5s)
    Nullable.int16 (Nullable -7L) |> equal (Nullable -7s)
    Nullable.int16 (Nullable 9.9) |> equal (Nullable 9s)
    Nullable.int16 none<int> |> equal none<int16>

[<Fact>]
let ``test Nullable.int32`` () =
    Nullable.int32 (Nullable 5L) |> equal (Nullable 5)
    Nullable.int32 (Nullable -7.9) |> equal (Nullable -7)
    Nullable.int32 (Nullable 9m) |> equal (Nullable 9)
    Nullable.int32 none<int64> |> equal none<int>

[<Fact>]
let ``test Nullable.int64`` () =
    Nullable.int64 (Nullable 5) |> equal (Nullable 5L)
    Nullable.int64 (Nullable 7UL) |> equal (Nullable 7L)
    Nullable.int64 (Nullable -9.9) |> equal (Nullable -9L)
    Nullable.int64 (Nullable 11m) |> equal (Nullable 11L)
    Nullable.int64 none<int> |> equal none<int64>

[<Fact>]
let ``test Nullable.int8`` () =
    Nullable.int8 (Nullable 5) |> equal (Nullable 5y)
    Nullable.int8 (Nullable -7L) |> equal (Nullable -7y)
    Nullable.int8 (Nullable 9.9) |> equal (Nullable 9y)
    Nullable.int8 none<int> |> equal none<sbyte>

[<Fact>]
let ``test Nullable.sbyte`` () =
    Nullable.sbyte (Nullable 5) |> equal (Nullable 5y)
    Nullable.sbyte (Nullable -7.9) |> equal (Nullable -7y)
    Nullable.sbyte none<int> |> equal none<sbyte>

[<Fact>]
let ``test Nullable.single`` () =
    Nullable.single (Nullable 5) |> equal (Nullable 5.0f)
    Nullable.single (Nullable 7L) |> equal (Nullable 7.0f)
    Nullable.single (Nullable 9.5) |> equal (Nullable 9.5f)
    Nullable.single none<int> |> equal none<float32>

[<Fact>]
let ``test Nullable.uint`` () =
    Nullable.uint (Nullable 5) |> equal (Nullable 5u)
    Nullable.uint (Nullable 7L) |> equal (Nullable 7u)
    Nullable.uint (Nullable 9.9) |> equal (Nullable 9u)
    Nullable.uint none<int> |> equal none<uint32>

[<Fact>]
let ``test Nullable.uint16`` () =
    Nullable.uint16 (Nullable 5) |> equal (Nullable 5us)
    Nullable.uint16 (Nullable 7L) |> equal (Nullable 7us)
    Nullable.uint16 (Nullable 9.9) |> equal (Nullable 9us)
    Nullable.uint16 none<int> |> equal none<uint16>

[<Fact>]
let ``test Nullable.uint32`` () =
    Nullable.uint32 (Nullable 5) |> equal (Nullable 5u)
    Nullable.uint32 (Nullable 7L) |> equal (Nullable 7u)
    Nullable.uint32 (Nullable 9.9) |> equal (Nullable 9u)
    Nullable.uint32 none<int> |> equal none<uint32>

[<Fact>]
let ``test Nullable.uint64`` () =
    Nullable.uint64 (Nullable 5) |> equal (Nullable 5UL)
    Nullable.uint64 (Nullable 7L) |> equal (Nullable 7UL)
    Nullable.uint64 (Nullable 9.9) |> equal (Nullable 9UL)
    Nullable.uint64 (Nullable 11m) |> equal (Nullable 11UL)
    Nullable.uint64 none<int> |> equal none<uint64>

[<Fact>]
let ``test Nullable.byte and Nullable.uint8`` () =
    Nullable.byte (Nullable 5) |> equal (Nullable 5uy)
    Nullable.uint8 (Nullable 7L) |> equal (Nullable 7uy)
    Nullable.uint8 (Nullable 9.9) |> equal (Nullable 9uy)
    Nullable.byte none<int> |> equal none<byte>

