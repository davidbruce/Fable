/// .NET's `System.DateOnly` and `System.TimeOnly`, written in F# and compiled by the Zig target
/// itself (see List.fs): a day number (days since 0001-01-01) and the ticks of a time of day,
/// with the calendar and the formats of DateTime.fs.
module Fable.Library.Zig.DateOnly

open Fable.Library.Zig.TimeSpan
open Fable.Library.Zig.DateTime

[<Struct>]
type DateOnlyOf = { dayNumber: int }

[<Struct>]
type TimeOnlyOf = { timeTicks: int64 }

let private maxDayNumber = 3652058

let private asDate (d: DateOnlyOf) : DateTimeOf =
    {
        ticks = int64 d.dayNumber * ticksPerDay
        kind = 0
    }

let private ofDate (d: DateTimeOf) : DateOnlyOf =
    { dayNumber = int (d.ticks / ticksPerDay) }

// ---- DateOnly ----

let create (y: int) (m: int) (d: int) : DateOnlyOf = ofDate (DateTime.create3 y m d)

let fromDayNumber (n: int) : DateOnlyOf =
    if n < 0 || n > maxDayNumber then
        raise (
            System.ArgumentOutOfRangeException(
                "dayNumber",
                "Day number must be between 0 and DateOnly.MaxValue.DayNumber."
            )
        )

    { dayNumber = n }

let minValue () : DateOnlyOf = { dayNumber = 0 }
let maxValue () : DateOnlyOf = { dayNumber = maxDayNumber }
let fromDateTime (d: DateTimeOf) : DateOnlyOf = ofDate d

let dayNumber (d: DateOnlyOf) = d.dayNumber
let year (d: DateOnlyOf) = DateTime.year (asDate d)
let month (d: DateOnlyOf) = DateTime.month (asDate d)
let day (d: DateOnlyOf) = DateTime.day (asDate d)
let dayOfWeek (d: DateOnlyOf) = DateTime.dayOfWeek (asDate d)
let dayOfYear (d: DateOnlyOf) = DateTime.dayOfYear (asDate d)

let addDays (d: DateOnlyOf) (days: int) : DateOnlyOf =
    let n = int64 d.dayNumber + int64 days

    if n < 0L || n > int64 maxDayNumber then
        raise (System.ArgumentOutOfRangeException("days", "The resulting DateOnly would be out of range."))

    { dayNumber = int n }

let addMonths (d: DateOnlyOf) (months: int) =
    ofDate (DateTime.addMonths (asDate d) months)

let addYears (d: DateOnlyOf) (years: int) =
    ofDate (DateTime.addYears (asDate d) years)

let compare (a: DateOnlyOf) (b: DateOnlyOf) =
    Operators.compare a.dayNumber b.dayNumber

/// `d.ToString(format)`: "d" (and none), "D", "m", "o", "r", "y", or a custom format
let toStringFormat (d: DateOnlyOf) (format: string) : string =
    match format with
    | null
    | ""
    | "d" -> formatCustom (asDate d) "MM/dd/yyyy"
    | "o"
    | "O" -> formatCustom (asDate d) "yyyy'-'MM'-'dd"
    | "r"
    | "R" -> formatCustom (asDate d) "ddd, dd MMM yyyy"
    | "D"
    | "m"
    | "M"
    | "y"
    | "Y" -> DateTime.toStringFormat (asDate d) format
    | f when f.Length = 1 -> raise (System.FormatException "Input string was not in a correct format.")
    | f -> formatCustom (asDate d) f

let toString (d: DateOnlyOf) = toStringFormat d "d"

// ---- TimeOnly ----

let private timeOf (ticks: int64) : TimeOnlyOf = { timeTicks = ticks }

let private wrap (ticks: int64) : TimeOnlyOf =
    let t = ticks % ticksPerDay

    timeOf (
        if t < 0L then
            t + ticksPerDay
        else
            t
    )

let timeOfTicks (ticks: int64) : TimeOnlyOf =
    if ticks < 0L || ticks >= ticksPerDay then
        raise (System.ArgumentOutOfRangeException("ticks", "Ticks must be between 0 and and TimeOnly.MaxValue.Ticks."))

    timeOf ticks

let private timeParts (h: int) (m: int) (s: int) (ms: int) (us: int) : TimeOnlyOf =
    if h < 0 || h > 23 || m < 0 || m > 59 || s < 0 || s > 59 then
        raise (
            System.ArgumentOutOfRangeException(
                null,
                "Hour, Minute, and Second parameters describe an un-representable DateTime."
            )
        )

    if ms < 0 || ms > 999 then
        raise (System.ArgumentOutOfRangeException("millisecond", "Valid values are between 0 and 999, inclusive."))

    if us < 0 || us > 999 then
        raise (System.ArgumentOutOfRangeException("microsecond", "Valid values are between 0 and 999, inclusive."))

    timeOf (
        int64 h * ticksPerHour
        + int64 m * ticksPerMinute
        + int64 s * ticksPerSecond
        + int64 ms * ticksPerMillisecond
        + int64 us * ticksPerMicrosecond
    )

let time2 (h: int) (m: int) = timeParts h m 0 0 0
let time3 (h: int) (m: int) (s: int) = timeParts h m s 0 0
let time4 (h: int) (m: int) (s: int) (ms: int) = timeParts h m s ms 0
let time5 (h: int) (m: int) (s: int) (ms: int) (us: int) = timeParts h m s ms us

let timeMinValue () : TimeOnlyOf = timeOf 0L
let timeMaxValue () : TimeOnlyOf = timeOf (ticksPerDay - 1L)
let timeFromDateTime (d: DateTimeOf) : TimeOnlyOf = timeOf (d.ticks % ticksPerDay)

let timeFromTimeSpan (t: TimeSpanOf) : TimeOnlyOf = timeOfTicks t.ticks

let timeTicks (t: TimeOnlyOf) = t.timeTicks
let hour (t: TimeOnlyOf) = int (t.timeTicks / ticksPerHour)

let minute (t: TimeOnlyOf) =
    int ((t.timeTicks / ticksPerMinute) % 60L)

let second (t: TimeOnlyOf) =
    int ((t.timeTicks / ticksPerSecond) % 60L)

let millisecond (t: TimeOnlyOf) =
    int ((t.timeTicks / ticksPerMillisecond) % 1000L)

let microsecond (t: TimeOnlyOf) =
    int ((t.timeTicks / ticksPerMicrosecond) % 1000L)

let nanosecond (t: TimeOnlyOf) =
    int ((t.timeTicks % ticksPerMicrosecond) * 100L)

let toTimeSpan (t: TimeOnlyOf) : TimeSpanOf = { TimeSpanOf.ticks = t.timeTicks }

/// `t.Add(span)`, `t.AddHours(h)`, `t.AddMinutes(m)`: around the clock
let timeAdd (t: TimeOnlyOf) (span: TimeSpanOf) : TimeOnlyOf =
    wrap (t.timeTicks + span.ticks % ticksPerDay)

let timeAddHours (t: TimeOnlyOf) (h: float) =
    timeAdd t { TimeSpanOf.ticks = int64 (h * float ticksPerHour) }

let timeAddMinutes (t: TimeOnlyOf) (m: float) =
    timeAdd t { TimeSpanOf.ticks = int64 (m * float ticksPerMinute) }

/// `t.Add(span, &wrappedDays)` and the hours and minutes: the time and the days it wrapped
/// (.NET's: whole days of the span, plus one when the clock went past midnight; negative for a
/// span backwards)
let private withDays (t: TimeOnlyOf) (spanTicks: int64) : TimeOnlyOf * int =
    let total = t.timeTicks + spanTicks
    let days = total / ticksPerDay

    let days =
        if total < 0L && total % ticksPerDay <> 0L then
            days - 1L
        else
            days

    wrap (t.timeTicks + spanTicks % ticksPerDay), int days

let timeAddWrapped (t: TimeOnlyOf) (span: TimeSpanOf) : TimeOnlyOf * int = withDays t span.ticks

let timeAddHoursWrapped (t: TimeOnlyOf) (h: float) : TimeOnlyOf * int =
    withDays t (int64 (h * float ticksPerHour))

let timeAddMinutesWrapped (t: TimeOnlyOf) (m: float) : TimeOnlyOf * int =
    withDays t (int64 (m * float ticksPerMinute))

/// `t1 - t2`: the span forward from `t2` to `t1`, around the clock
let timeSubtract (a: TimeOnlyOf) (b: TimeOnlyOf) : TimeSpanOf =
    let d = a.timeTicks - b.timeTicks

    {
        TimeSpanOf.ticks =
            if d < 0L then
                d + ticksPerDay
            else
                d
    }

/// `t.IsBetween(start, end)`: in [start, end), around midnight when end is before start
let isBetween (t: TimeOnlyOf) (start: TimeOnlyOf) (finish: TimeOnlyOf) : bool =
    let s = start.timeTicks
    let e = finish.timeTicks
    let x = t.timeTicks

    if s <= e then
        x >= s && x < e
    else
        x >= s || x < e

let timeCompare (a: TimeOnlyOf) (b: TimeOnlyOf) =
    Operators.compare a.timeTicks b.timeTicks

let toDateTime (d: DateOnlyOf) (t: TimeOnlyOf) (kind: int) : DateTimeOf =
    DateTime.ofTicksKind (int64 d.dayNumber * ticksPerDay + t.timeTicks) kind

/// `t.ToString(format)`: "t" (and none), "T", "o", "r", or a custom format
let timeToStringFormat (t: TimeOnlyOf) (format: string) : string =
    let asDate: DateTimeOf =
        {
            ticks = t.timeTicks
            kind = 0
        }

    match format with
    | null
    | ""
    | "t" -> formatCustom asDate "HH:mm"
    | "T" -> formatCustom asDate "HH:mm:ss"
    | "o"
    | "O" -> formatCustom asDate "HH':'mm':'ss'.'fffffff"
    | "r"
    | "R" -> formatCustom asDate "HH':'mm':'ss"
    | f when f.Length = 1 -> raise (System.FormatException "Input string was not in a correct format.")
    | f -> formatCustom asDate f

let timeToString (t: TimeOnlyOf) = timeToStringFormat t "t"

// ---- Parse and TryParse: as DateTime.Parse reads the text, without the part the type has not ----

/// (digits only, as a number; None for anything else)
let private digitsValue (s: string) : int option =
    if s.Length = 0 || s.Length > 9 then
        None
    else
        let mutable v = 0
        let mutable ok = true

        for i in 0 .. s.Length - 1 do
            let c = s.[i]

            if c >= '0' && c <= '9' then
                v <- v * 10 + int c - int '0'
            else
                ok <- false

        if ok then
            Some v
        else
            None

/// (a year of one or two digits: the invariant calendar's, 2000 to 2049 and else the 1900s)
let private fullYear (text: string) (y: int) : int =
    if text.Length <= 2 then
        if y <= 49 then
            2000 + y
        else
            1900 + y
    else
        y

/// The numeric dates of the invariant culture: `y-m-d` when the first part has three digits or
/// more, else `m/d/y`, the parts separated by one of `/`, `-`, `.` and `,`
let private numericDate (s: string) : DateOnlyOf option =
    let t = s.Trim()
    let sep = [| '/'; '-'; '.'; ',' |] |> Array.tryFind (fun c -> t.Contains c)

    match sep with
    | None -> None
    | Some c ->
        let parts = t.Split c

        if parts.Length <> 3 then
            None
        else
            match digitsValue parts.[0], digitsValue parts.[1], digitsValue parts.[2] with
            | Some a, Some b, Some cc ->
                let y, m, d =
                    if parts.[0].Length >= 3 then
                        a, b, cc
                    else
                        fullYear parts.[2] cc, a, b

                if y >= 1 && y <= 9999 && m >= 1 && m <= 12 && d >= 1 && d <= daysInMonth y m then
                    Some(create y m d)
                else
                    None
            | _ -> None

let private dateOfText (s: string) : DateOnlyOf option =
    if isNull s then
        None
    else
        match numericDate s with
        | Some d -> Some d
        | None ->
            match tryParseOption s with
            | Some d when d.ticks % ticksPerDay = 0L && not (s.Contains ":") -> Some(fromDateTime d)
            | _ -> None

/// `h:m`, `h:m:s` and `h:m:s.fraction`, white space around the parts allowed
let private numericTime (s: string) : TimeOnlyOf option =
    let parts = s.Split ':' |> Array.map (fun p -> p.Trim())

    if parts.Length < 2 || parts.Length > 3 then
        None
    else
        let secText, fraction =
            if parts.Length = 3 then
                match parts.[2].IndexOf '.' with
                | -1 -> parts.[2], ""
                | i -> parts.[2].Substring(0, i), parts.[2].Substring(i + 1)
            else
                "0", ""

        let fracTicks =
            if fraction = "" then
                Some 0L
            elif fraction.Length > 7 then
                None
            else
                digitsValue fraction
                |> Option.map (fun f -> int64 f * pown 10L (7 - fraction.Length))

        let short = parts.[0].Length <= 2 && parts.[1].Length <= 2 && secText.Length <= 2

        match digitsValue parts.[0], digitsValue parts.[1], digitsValue secText, fracTicks with
        | Some h, Some m, Some sec, Some f when short && h < 24 && m < 60 && sec < 60 ->
            Some(
                timeOfTicks (
                    int64 h * ticksPerHour
                    + int64 m * ticksPerMinute
                    + int64 sec * ticksPerSecond
                    + f
                )
            )
        | _ -> None

/// (a time of day only: no date part, which DateTime.Parse would read, in the text)
let private timeOfText (s: string) : TimeOnlyOf option =
    if isNull s || not (s.Contains ":") then
        None
    else
        let mutable hasDate = false

        for i in 0 .. s.Length - 1 do
            let c = s.[i]

            if
                c = '/'
                || c = '-'
                || c = ','
                || (System.Char.IsLetter c && not ("AaPpMm".Contains c))
            then
                hasDate <- true

        if hasDate then
            None
        else
            // (digits, colons and a fraction only: the numeric form decides)
            let mutable numeric = true

            for i in 0 .. s.Length - 1 do
                let c = s.[i]

                if not ((c >= '0' && c <= '9') || c = ':' || c = '.' || c = ' ') then
                    numeric <- false

            if numeric then
                numericTime s
            else
                match tryParseOption s with
                | Some d -> Some(timeFromDateTime d)
                | None -> None

let parse (s: string) : DateOnlyOf =
    if isNull s then
        raise (System.ArgumentNullException("s", "Value cannot be null."))

    match dateOfText s with
    | Some d -> d
    | None -> raise (System.FormatException("String '" + s + "' was not recognized as a valid DateOnly."))

let tryParse (s: string) : bool * DateOnlyOf =
    match dateOfText s with
    | Some d -> true, d
    | None -> false, minValue ()

let timeParse (s: string) : TimeOnlyOf =
    if isNull s then
        raise (System.ArgumentNullException("s", "Value cannot be null."))

    match timeOfText s with
    | Some t -> t
    | None -> raise (System.FormatException("String '" + s + "' was not recognized as a valid TimeOnly."))

let timeTryParse (s: string) : bool * TimeOnlyOf =
    match timeOfText s with
    | Some t -> true, t
    | None -> false, timeMinValue ()
