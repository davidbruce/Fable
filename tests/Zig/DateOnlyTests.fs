module Fable.Tests.Zig.DateOnlyTests

open System
open Fable.Tests.Util
open Fable.Tests.Util.Testing

[<Fact>]
let ``test DateOnly constructors work`` () =
    let d = DateOnly(2014, 10, 9)
    d.Year |> equal 2014
    d.Month |> equal 10
    d.Day |> equal 9

[<Fact>]
let ``test DateOnly.MinValue works`` () =
    let d = DateOnly.MinValue
    d.Year |> equal 1
    d.Month |> equal 1
    d.Day |> equal 1

[<Fact>]
let ``test DateOnly.MaxValue works`` () =
    let d = DateOnly.MaxValue
    d.Year |> equal 9999
    d.Month |> equal 12
    d.Day |> equal 31

[<Fact>]
let ``test DateOnly.DayOfWeek works`` () =
    let d = DateOnly(2014, 10, 9)
    d.DayOfWeek |> equal DayOfWeek.Thursday

[<Fact>]
let ``test DateOnly.DayOfYear works`` () =
    let d = DateOnly(2014, 10, 9)
    d.DayOfYear |> equal 282

[<Fact>]
let ``test DateOnly.AddDays works`` () =
    let d = DateOnly(2014, 10, 9)
    let d2 = d.AddDays(10)
    d2.Day |> equal 19
    d2.Month |> equal 10

[<Fact>]
let ``test DateOnly.AddMonths works`` () =
    let d = DateOnly(2014, 1, 31)
    let d2 = d.AddMonths(1)
    d2.Month |> equal 2
    d2.Day |> equal 28

[<Fact>]
let ``test DateOnly.AddYears works`` () =
    let d = DateOnly(2016, 2, 29)
    let d2 = d.AddYears(1)
    d2.Year |> equal 2017
    d2.Month |> equal 2
    d2.Day |> equal 28

[<Fact>]
let ``test DateOnly.ToString works`` () =
    let d = DateOnly(2014, 10, 9)
    d.ToString("o", System.Globalization.CultureInfo.InvariantCulture) |> equal "2014-10-09"

[<Fact>]
let ``test DateOnly.FromDateTime works`` () =
    let dt = DateTime(2014, 10, 9, 13, 23, 30)
    let d = DateOnly.FromDateTime(dt)
    d.Year |> equal 2014
    d.Month |> equal 10
    d.Day |> equal 9

// ---- ported from tests/Js/Main (2026-11-16) ----

open System.Globalization

[<Fact>]
let ``test DayNumber works`` () =
    let date = DateOnly (1, 1, 2)
    date.DayNumber |> equal 1
    let date = DateOnly (2000, 1, 2)
    date.DayNumber |> equal 730120
    let date = DateOnly.MaxValue
    date.DayNumber |> equal 3652058
    let date = DateOnly.MinValue
    date.DayNumber |> equal 0

[<Fact>]
let ``test FromDayNumber works`` () =
    let number = 1
    DateOnly.FromDayNumber number |> equal (DateOnly (1, 1, 2))
    let number = 730120
    DateOnly.FromDayNumber number |> equal (DateOnly (2000, 1, 2))
    let number = 3652058
    DateOnly.FromDayNumber number |> equal DateOnly.MaxValue
    let number = 0
    DateOnly.FromDayNumber number |> equal DateOnly.MinValue

[<Fact>]
let ``test Day works`` () =
    let date = DateOnly (1, 1, 2)
    date.Day |> equal 2
    let date = DateOnly (2000, 2, 28)
    date.Day |> equal 28
    let date = DateOnly.MaxValue
    date.Day |> equal 31
    let date = DateOnly.MinValue
    date.Day |> equal 1

[<Fact>]
let ``test Month works`` () =
    let date = DateOnly (1, 1, 2)
    date.Month |> equal 1
    let date = DateOnly (2000, 2, 28)
    date.Month |> equal 2
    let date = DateOnly.MaxValue
    date.Month |> equal 12
    let date = DateOnly.MinValue
    date.Month |> equal 1

[<Fact>]
let ``test Year works`` () =
    let date = DateOnly (1, 1, 2)
    date.Year |> equal 1
    let date = DateOnly (2000, 2, 28)
    date.Year |> equal 2000
    let date = DateOnly.MaxValue
    date.Year |> equal 9999
    let date = DateOnly.MinValue
    date.Year |> equal 1

[<Fact>]
let ``test DayOfWeek works`` () =
    let date = DateOnly (1, 1, 2)
    date.DayOfWeek |> equal DayOfWeek.Tuesday
    let date = DateOnly (2000, 2, 28)
    date.DayOfWeek |> equal DayOfWeek.Monday
    let date = DateOnly.MaxValue
    date.DayOfWeek |> equal DayOfWeek.Friday
    let date = DateOnly.MinValue
    date.DayOfWeek |> equal DayOfWeek.Monday

[<Fact>]
let ``test DayOfYear works`` () =
    let date = DateOnly (1, 1, 2)
    date.DayOfYear |> equal 2
    let date = DateOnly (2000, 2, 28)
    date.DayOfYear |> equal 59
    let date = DateOnly.MaxValue
    date.DayOfYear |> equal 365
    let date = DateOnly.MinValue
    date.DayOfYear |> equal 1

[<Fact>]
let ``test FromDateTime works`` () =
    let dateTime = DateTime (2000, 2, 27, 23, 30, 0, DateTimeKind.Local)
    DateOnly.FromDateTime dateTime |> equal (DateOnly (2000, 2, 27))
    let dateTime = DateTime (2000, 2, 27, 23, 30, 0, DateTimeKind.Utc)
    DateOnly.FromDateTime dateTime |> equal (DateOnly (2000, 2, 27))
    let dateTime = DateTime (2000, 2, 28, 0, 30, 0, DateTimeKind.Local)
    DateOnly.FromDateTime dateTime |> equal (DateOnly (2000, 2, 28))
    let dateTime = DateTime (2000, 2, 28, 0, 30, 0, DateTimeKind.Utc)
    DateOnly.FromDateTime dateTime |> equal (DateOnly (2000, 2, 28))
    let dateTime = DateTime.Now
    DateOnly.FromDateTime dateTime |> equal (DateOnly (DateTime.Now.Year, DateTime.Now.Month, DateTime.Now.Day))

[<Fact>]
let ``test ToDateTime works`` () =
    let date = DateOnly (2000, 10, 10)
    let time = TimeOnly (20, 30, 40)
    date.ToDateTime (time, DateTimeKind.Utc) |> equal (DateTime (2000, 10, 10, 20, 30, 40, DateTimeKind.Utc))

    let date = DateOnly (2000, 10, 10)
    let time = TimeOnly (20, 30, 40)
    date.ToDateTime (time, DateTimeKind.Local) |> equal (DateTime (2000, 10, 10, 20, 30, 40, DateTimeKind.Local))

    let date = DateOnly (2000, 10, 10)
    let time = TimeOnly (20, 30, 40)
    date.ToDateTime time |> equal (DateTime (2000, 10, 10, 20, 30, 40))

[<Fact>]
let ``test AddYears works`` () =
    let date = DateOnly (2004, 2, 29)
    date.AddYears 3 |> equal (DateOnly (2007, 2, 28))

    let date = DateOnly (1453, 5, 29)
    date.AddYears -200 |> equal (DateOnly (1253, 5, 29))

[<Fact>]
let ``test AddMonths works`` () =
    let date = DateOnly (2001, 1, 31)
    date.AddMonths 1 |> equal (DateOnly (2001, 2, 28))

    let date = DateOnly (2001, 1, 31)
    date.AddMonths -4 |> equal (DateOnly (2000, 9, 30))

[<Fact>]
let ``test AddDays works`` () =
    let date = DateOnly (2000, 12, 31)
    date.AddDays 1 |> equal (DateOnly (2001, 1, 1))

    let date = DateOnly (1453, 5, 29)
    date.AddDays -29 |> equal (DateOnly (1453, 4, 30))

[<Fact>]
let ``test ToString works`` () =
    let date = DateOnly.MaxValue
    date.ToString(CultureInfo.InvariantCulture) |> equal "12/31/9999"
    date.ToString("d", CultureInfo.InvariantCulture) |> equal "12/31/9999"
    date.ToString("o", CultureInfo.InvariantCulture) |> equal "9999-12-31"
    date.ToString("O", CultureInfo.InvariantCulture) |> equal "9999-12-31"

    let date = DateOnly(1, 2, 3)
    date.ToString(CultureInfo.InvariantCulture) |> equal "02/03/0001"
    date.ToString("d", CultureInfo.InvariantCulture) |> equal "02/03/0001"
    date.ToString("o", CultureInfo.InvariantCulture) |> equal "0001-02-03"
    date.ToString("O", CultureInfo.InvariantCulture) |> equal "0001-02-03"

[<Fact>]
let ``test Parse parses valid DateOnly`` () =
    equal DateOnly.MaxValue (DateOnly.Parse("9999-12-31", CultureInfo.InvariantCulture))
    equal DateOnly.MaxValue (DateOnly.Parse("12/31/9999", CultureInfo.InvariantCulture))
    equal DateOnly.MinValue (DateOnly.Parse("1/01/001", CultureInfo.InvariantCulture))
    equal DateOnly.MinValue (DateOnly.Parse("001-1-01", CultureInfo.InvariantCulture))
    equal DateOnly.MinValue (DateOnly.Parse("1/01/0001", CultureInfo.InvariantCulture))
    equal DateOnly.MinValue (DateOnly.Parse("0001.1.01", CultureInfo.InvariantCulture))

    equal (DateOnly (2001, 1, 1)) (DateOnly.Parse("   01/1/01", CultureInfo.InvariantCulture))
    equal (DateOnly (2001, 1, 1)) (DateOnly.Parse("1-01-01   ", CultureInfo.InvariantCulture))
    equal (DateOnly (2005, 1, 1)) (DateOnly.Parse("01/1/5", CultureInfo.InvariantCulture))
    equal (DateOnly (2001, 5, 1)) (DateOnly.Parse("5-01-01", CultureInfo.InvariantCulture))
    equal (DateOnly (2000, 11, 30)) (DateOnly.Parse("2000-11-30", CultureInfo.InvariantCulture))
    equal (DateOnly (2000, 11, 30)) (DateOnly.Parse("11/30/2000", CultureInfo.InvariantCulture))
    equal (DateOnly (2020, 1, 3)) (DateOnly.Parse("01/03/20", CultureInfo.InvariantCulture))
    equal (DateOnly (1999, 1, 3)) (DateOnly.Parse("01,03,99", CultureInfo.InvariantCulture))

[<Fact>]
let ``test TryParse returns false for invalid DateOnly`` () =
    let isValid, _ = DateOnly.TryParse("4")
    equal false isValid

    let isValid, _ = DateOnly.TryParse("0000-2-5", CultureInfo.InvariantCulture, DateTimeStyles.None)
    equal false isValid

    let isValid, _ = DateOnly.TryParse("2000-2-30", CultureInfo.InvariantCulture, DateTimeStyles.None)
    equal false isValid

    let isValid, _ = DateOnly.TryParse("2000-2?2", CultureInfo.InvariantCulture, DateTimeStyles.None)
    equal false isValid

    let isValid, _ = DateOnly.TryParse("13/01/2000", CultureInfo.InvariantCulture, DateTimeStyles.None)
    equal false isValid

    let isValid, _ = DateOnly.TryParse("01/00/2000", CultureInfo.InvariantCulture, DateTimeStyles.None)
    equal false isValid

    let isValid, _ = DateOnly.TryParse("0/10/2000", CultureInfo.InvariantCulture, DateTimeStyles.None)
    equal false isValid

    let isValid, _ = DateOnly.TryParse("20/2000", CultureInfo.InvariantCulture, DateTimeStyles.None)
    equal false isValid

    let isValid, _ = DateOnly.TryParse("20/200", CultureInfo.InvariantCulture, DateTimeStyles.None)
    equal false isValid

    let isValid, _ = DateOnly.TryParse("200/20", CultureInfo.InvariantCulture, DateTimeStyles.None)
    equal false isValid

[<Fact>]
let ``test Comparison works`` () =
    equal true (DateOnly (2000, 1, 1) < DateOnly (2000, 1, 2))
    equal true (DateOnly (2000, 1, 1) <= DateOnly (2000, 1, 1))
    equal false (DateOnly (2000, 1, 1) > DateOnly (2000, 1, 1))

[<Fact>]
let ``test Can be used as map key`` () =
    let m = [ DateOnly (2000, 1, 2), () ] |> Map.ofList
    equal true (Map.containsKey (DateOnly(2000, 1, 1).AddDays(1)) m)
    equal false (Map.containsKey (DateOnly (1999, 1, 1)) m)

