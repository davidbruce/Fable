module Fable.Tests.Zig.TimeOnlyTests

open System
open Fable.Tests.Util
open Fable.Tests.Util.Testing

[<Fact>]
let ``test TimeOnly constructors work`` () =
    let t = TimeOnly(13, 23, 30)
    t.Hour |> equal 13
    t.Minute |> equal 23
    t.Second |> equal 30

[<Fact>]
let ``test TimeOnly constructor with milliseconds works`` () =
    let t = TimeOnly(13, 23, 30, 500)
    t.Hour |> equal 13
    t.Minute |> equal 23
    t.Second |> equal 30
    t.Millisecond |> equal 500

[<Fact>]
let ``test TimeOnly.MinValue works`` () =
    let t = TimeOnly.MinValue
    t.Hour |> equal 0
    t.Minute |> equal 0
    t.Second |> equal 0

[<Fact>]
let ``test TimeOnly.ToTimeSpan works`` () =
    let t = TimeOnly(13, 23, 30)
    let ts = t.ToTimeSpan()
    ts.Hours |> equal 13
    ts.Minutes |> equal 23
    ts.Seconds |> equal 30

[<Fact>]
let ``test TimeOnly.AddHours works`` () =
    let t = TimeOnly(13, 0, 0)
    let t2 = t.AddHours(2.0)
    t2.Hour |> equal 15

[<Fact>]
let ``test TimeOnly.AddMinutes works`` () =
    let t = TimeOnly(13, 30, 0)
    let t2 = t.AddMinutes(45.0)
    t2.Hour |> equal 14
    t2.Minute |> equal 15

[<Fact>]
let ``test TimeOnly.IsBetween works`` () =
    let t = TimeOnly(13, 0, 0)
    let start = TimeOnly(12, 0, 0)
    let finish = TimeOnly(14, 0, 0)
    t.IsBetween(start, finish) |> equal true
    t.IsBetween(finish, start) |> equal false

[<Fact>]
let ``test TimeOnly.ToString with format works`` () =
    let t = TimeOnly(13, 23, 30)
    t.ToString("T", System.Globalization.CultureInfo.InvariantCulture) |> equal "13:23:30"
    t.ToString("t", System.Globalization.CultureInfo.InvariantCulture) |> equal "13:23"

// ---- ported from tests/Js/Main (2026-11-16) ----







open System.Globalization

[<Fact>]
let ``test FromDateTime works`` () =
    let now = DateTime.Now
    let t = TimeOnly.FromDateTime now

    equal now.Hour t.Hour
    equal now.Minute t.Minute
    equal now.Second t.Second
    equal now.Millisecond t.Millisecond

    let now = DateTime.UtcNow
    let t = TimeOnly.FromDateTime now

    equal now.Hour t.Hour
    equal now.Minute t.Minute
    equal now.Second t.Second
    equal now.Millisecond t.Millisecond

[<Fact>]
let ``test ToTimeSpan works`` () =
    let t1 = TimeOnly.MaxValue.ToTimeSpan()
    let t2 = TimeOnly(10, 20, 30, 40).ToTimeSpan()

    t1.Hours |> equal 23
    t2.Days |> equal 0
    t2.Hours |> equal 10
    t2.Minutes |> equal 20
    t2.Seconds |> equal 30
    t2.Milliseconds |> equal 40

[<Fact>]
let ``test IsBetween works`` () =
    let start = TimeOnly (3, 0, 0)
    let end' = start
    let t = start
    t.IsBetween (start, end') |> equal false

    let start = TimeOnly (3, 0, 0)
    let end' = TimeOnly (4, 0, 0)
    let t = start
    t.IsBetween (start, end') |> equal true

    let start = TimeOnly (3, 0, 0)
    let end' = TimeOnly (4, 0, 0)
    let t = end'
    t.IsBetween (start, end') |> equal false

    let start = TimeOnly (3, 0, 0)
    let end' = TimeOnly (4, 0, 0)
    let t = TimeOnly (3, 30, 0)
    t.IsBetween (start, end') |> equal true

    let start = TimeOnly (4, 0, 0)
    let end' = TimeOnly (3, 0, 0)
    let t = TimeOnly (3, 30, 0)
    t.IsBetween (start, end') |> equal false

    let start = TimeOnly (23, 0, 0)
    let end' = TimeOnly (1, 0, 0)
    let t = TimeOnly (23, 30, 0)
    t.IsBetween (start, end') |> equal true

[<Fact>]
let ``test Add* works`` () =
    let t = TimeOnly (6, 0, 0)
    t.Add (TimeSpan.FromHours 18.) |> equal TimeOnly.MinValue
    t.Add (TimeSpan.FromHours 19.) |> equal (TimeOnly (1, 0))
    t.Add (TimeSpan.FromHours -7.) |> equal (TimeOnly (23, 0))
    // F# 6 can cast int implicitly to float,
    // but fable-standalone cannot do it until it's updated
    t.AddHours 18. |> equal TimeOnly.MinValue
    t.AddHours -31. |> equal (TimeOnly (23, 0))
    t.AddMinutes 59. |> equal (TimeOnly (6, 59))
    t.AddMinutes -361. |> equal (TimeOnly (23, 59))

[<Fact>]
let ``test Add with wrapped days works`` () =
    let t = TimeOnly (6, 0, 0)

    let newT, wrappedDays = t.Add (TimeSpan.FromHours 17.)
    equal (TimeOnly (23, 0)) newT
    equal 0 wrappedDays

    let newT, wrappedDays = t.Add (TimeSpan.FromHours 18.)
    equal TimeOnly.MinValue newT
    equal 1 wrappedDays

    let newT, wrappedDays = t.Add (TimeSpan.FromHours 19.)
    equal (TimeOnly (1, 0)) newT
    equal 1 wrappedDays

    let newT, wrappedDays = t.Add (TimeSpan.FromHours -7.)
    equal (TimeOnly (23, 0)) newT
    equal -1 wrappedDays

    let newT, wrappedDays = t.Add (TimeSpan.FromDays 3.)
    equal t newT
    equal 3 wrappedDays

[<Fact>]
let ``test Subtract works`` () =
    let left = TimeOnly (6, 0)
    let right = TimeOnly (5, 30)
    left - right |> equal (TimeSpan.FromMinutes 30.)

    let left = TimeOnly.MinValue
    let right = TimeOnly.MinValue
    left - right |> equal TimeSpan.Zero

    let left = TimeOnly.MinValue
    let right = TimeOnly (23, 59, 59, 999)
    left - right |> equal (TimeSpan.FromMilliseconds 1.)

    let left = TimeOnly (23, 59, 59, 999)
    let right = TimeOnly.MinValue
    left - right |> equal (TimeSpan (0, 23, 59, 59, 999))

    let left = TimeOnly (1, 0)
    let right = TimeOnly (23, 59, 59)
    left - right |> equal (TimeSpan (1, 0, 1))

[<Fact>]
let ``test ToString works`` () =
    let t1 = TimeOnly (5, 0, 2, 22)
    let t2 = TimeOnly (14, 2)

    // t2.ToString() |> equal "14:02"

    t1.ToString(CultureInfo.InvariantCulture) |> equal "05:00"
    t2.ToString(CultureInfo.InvariantCulture) |> equal "14:02"

    t1.ToString("r", CultureInfo.InvariantCulture) |> equal "05:00:02"
    t2.ToString("r", CultureInfo.InvariantCulture) |> equal "14:02:00"

    t1.ToString("R", CultureInfo.InvariantCulture) |> equal "05:00:02"
    t2.ToString("R", CultureInfo.InvariantCulture) |> equal "14:02:00"

    t1.ToString("o", CultureInfo.InvariantCulture) |> equal "05:00:02.0220000"
    t2.ToString("o", CultureInfo.InvariantCulture) |> equal "14:02:00.0000000"

    t1.ToString("O", CultureInfo.InvariantCulture) |> equal "05:00:02.0220000"
    t2.ToString("O", CultureInfo.InvariantCulture) |> equal "14:02:00.0000000"

    t1.ToString("t", CultureInfo.InvariantCulture) |> equal "05:00"
    t2.ToString("t", CultureInfo.InvariantCulture) |> equal "14:02"

    t1.ToString("T", CultureInfo.InvariantCulture) |> equal "05:00:02"
    t2.ToString("T", CultureInfo.InvariantCulture) |> equal "14:02:00"

[<Fact>]
let ``test Parse parses valid TimeOnly`` () =
    equal (TimeOnly (23, 0)) (TimeOnly.Parse "23:0:0")
    equal (TimeOnly (23, 0)) (TimeOnly.Parse "23:00")
    equal (TimeOnly (3, 0)) (TimeOnly.Parse "3:00")
    equal (TimeOnly (0, 0, 5)) (TimeOnly.Parse "00:0:5   ")
    equal TimeOnly.MinValue (TimeOnly.Parse "   0   :   0    : 0   ")
    equal (TimeOnly (0, 40, 5, 3)) (TimeOnly.Parse "00:40:5.003")
    // The JS-Date representation is limited to millisecond precision;
    // the Temporal one is tick-precise, like .NET.

[<Fact>]
let ``test TryParse returns false for invalid TimeOnly`` () =
    let isValid, _ = TimeOnly.TryParse "4"
    equal false isValid

    let isValid, _ = TimeOnly.TryParse "24:00"
    equal false isValid

    let isValid, _ = TimeOnly.TryParse "22:60"
    equal false isValid

    let isValid, _ = TimeOnly.TryParse "002:10"
    equal false isValid

    let isValid, _ = TimeOnly.TryParse "22:50:60"
    equal false isValid

    let isValid, _ = TimeOnly.TryParse "-04:00"
    equal false isValid

    // let isValid, _ = TimeOnly.TryParse "02:00:00,333" // not invalid in NET8_0
    // equal false isValid

    let isValid, _ = TimeOnly.TryParse "02:00:00:33"
    equal false isValid

[<Fact>]
let ``test TryParse returns true and correct TimeOnly for valid TimeOnly`` () =
    let isValid, t = TimeOnly.TryParse "23:0:0"
    equal true isValid
    equal (TimeOnly (23, 0)) t

    let isValid, t = TimeOnly.TryParse "23:00"
    equal true isValid
    equal (TimeOnly (23, 0)) t

    let isValid, t = TimeOnly.TryParse "3:00"
    equal true isValid
    equal (TimeOnly (3, 0)) t

    let isValid, t = TimeOnly.TryParse "00:0:5"
    equal true isValid
    equal (TimeOnly (0, 0, 5)) t

    let isValid, t = TimeOnly.TryParse "0:0:0"
    equal true isValid
    equal TimeOnly.MinValue t

    let isValid, t = TimeOnly.TryParse "00:40:5.003"
    equal true isValid
    equal (TimeOnly (0, 40, 5, 3)) t

    let isValid, t = TimeOnly.TryParse "00:0:59.03"
    equal true isValid
    equal (TimeOnly (0, 0, 59, 30)) t

    let isValid, t = TimeOnly.TryParse "00:03:5.3"
    equal true isValid
    equal (TimeOnly (0, 3, 5, 300)) t

    let isValid, t = TimeOnly.TryParse "02:0:5.30"
    equal true isValid
    equal (TimeOnly (2, 0, 5, 300)) t

    // The JS-Date representation is limited to millisecond precision;
    // the Temporal one is tick-precise, like .NET.

[<Fact>]
let ``test Comparison works`` () =
    equal true (TimeOnly (20, 1, 1) < TimeOnly (20, 1, 2))
    equal true (TimeOnly (20, 1, 1) <= TimeOnly (20, 1, 1))
    equal false (TimeOnly (20, 1, 1) > TimeOnly (20, 1, 1))

[<Fact>]
let ``test Can be used as map key`` () =
    let m = [ TimeOnly (20, 5, 1), () ] |> Map.ofList
    equal true (Map.containsKey (TimeOnly(20, 1, 1).AddMinutes(4.)) m)
    equal false (Map.containsKey (TimeOnly (20, 1, 1)) m)

[<Fact>]
let ``test TimeOnly.MaxValue is one tick short of a day`` () =
    TimeOnly.MaxValue.Ticks |> equal 863_999_999_999L

[<Fact>]
let ``test TimeOnly constructor keeps the microsecond argument`` () =
    TimeOnly(1, 2, 3, 4, 5).Ticks |> equal 37_230_040_050L

[<Fact>]
let ``test TimeOnly.Parse keeps all seven fractional digits`` () =
    TimeOnly.Parse("01:02:03.1234567", CultureInfo.InvariantCulture).Ticks % 10_000_000L
    |> equal 1234567L

[<Fact>]
let ``test TimeOnly.Add wraps a large TimeSpan without losing the low ticks`` () =
    // 100000 whole days plus one tick: the days wrap away and the tick must remain.
    // In nanoseconds this amount is past Number.MAX_SAFE_INTEGER.
    let big = TimeSpan.FromTicks(864_000_000_000L * 100_000L + 1L)
    TimeOnly.MinValue.Add(big).Ticks |> equal 1L

[<Fact>]
let ``test TimeOnly.Add* accept fractional values and are tick-precise`` () =
    let t = TimeOnly(1, 2, 3, 4)
    t.AddHours(1.0 / 3.0).Ticks - t.Ticks |> equal 12_000_000_000L
    t.AddMinutes(0.00001).Ticks - t.Ticks |> equal 6_000L


// ---- ported from tests/Js/Main (2026-11-16, remaining) ----
