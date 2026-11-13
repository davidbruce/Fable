/// .NET's `System.DateTime`, written in F# and compiled by the Zig target itself (see List.fs):
/// ticks (100 ns since 0001-01-01) and a kind, with .NET's calendar arithmetic, the invariant
/// culture's formats (the current culture is the invariant one here, as in Fable) and its
/// custom format specifiers. Local time is the machine's zone (fable_time.zig).
module Fable.Library.Zig.DateTime

open Fable.Core
open Fable.Library.Zig.TimeSpan

// DateTimeKind: Unspecified = 0, Utc = 1, Local = 2
let private unspecified = 0
let private utc = 1
let private local = 2

/// (equal and ordered by their ticks only, as .NET's: the kind does not count)
[<Struct; CustomEquality; CustomComparison>]
type DateTimeOf =
    {
        ticks: int64
        kind: int
    }

    override d.Equals(o: obj) =
        match o with
        | :? DateTimeOf as e -> d.ticks = e.ticks
        | _ -> false

    override d.GetHashCode() = int d.ticks ^^^ int (d.ticks >>> 32)

    interface System.IComparable with
        member d.CompareTo(o: obj) =
            match o with
            | :? DateTimeOf as e -> Operators.compare d.ticks e.ticks
            | _ -> invalidArg "obj" "Object must be of type DateTime."

let maxTicks = 3155378975999999999L

#if FABLE_COMPILER
[<Emit("fable_rt.time.nowUtcTicks()")>]
let nowUtcTicks () : int64 = nativeOnly

[<Emit("fable_rt.time.localOffsetTicks($0)")>]
let localOffsetTicks (_utcTicks: int64) : int64 = nativeOnly
#else
let nowUtcTicks () : int64 = System.DateTime.UtcNow.Ticks

let localOffsetTicks (utcTicks: int64) : int64 =
    System.TimeZoneInfo.Local.GetUtcOffset(System.DateTime(utcTicks, System.DateTimeKind.Utc)).Ticks
#endif

/// The offset of local time at a local time: the offset at the instant it most likely is
let offsetAtLocal (localTicks: int64) : int64 =
    let guess = localOffsetTicks (localTicks - localOffsetTicks localTicks)
    localOffsetTicks (localTicks - guess)

// ---- the calendar ----

let private daysToMonth365 =
    [| 0; 31; 59; 90; 120; 151; 181; 212; 243; 273; 304; 334; 365 |]

let private daysToMonth366 =
    [| 0; 31; 60; 91; 121; 152; 182; 213; 244; 274; 305; 335; 366 |]

let isLeapYear (year: int) : bool =
    if year < 1 || year > 9999 then
        raise (System.ArgumentOutOfRangeException("year", "Year must be between 1 and 9999."))

    year % 4 = 0 && (year % 100 <> 0 || year % 400 = 0)

let daysInMonth (year: int) (month: int) : int =
    if month < 1 || month > 12 then
        raise (System.ArgumentOutOfRangeException("month", "Month must be between one and twelve."))

    let days =
        if isLeapYear year then
            daysToMonth366
        else
            daysToMonth365

    days.[month] - days.[month - 1]

let private dateToTicks (year: int) (month: int) (day: int) : int64 =
    if year >= 1 && year <= 9999 && month >= 1 && month <= 12 then
        let days =
            if isLeapYear year then
                daysToMonth366
            else
                daysToMonth365

        if day >= 1 && day <= days.[month] - days.[month - 1] then
            let y = year - 1
            let n = int64 (y * 365 + y / 4 - y / 100 + y / 400 + days.[month - 1] + day - 1)
            n * ticksPerDay
        else
            raise (
                System.ArgumentOutOfRangeException(
                    null,
                    "Year, Month, and Day parameters describe an un-representable DateTime."
                )
            )
    else
        raise (
            System.ArgumentOutOfRangeException(
                null,
                "Year, Month, and Day parameters describe an un-representable DateTime."
            )
        )

let private timeToTicks (hour: int) (minute: int) (second: int) : int64 =
    if
        hour >= 0
        && hour < 24
        && minute >= 0
        && minute < 60
        && second >= 0
        && second < 60
    then
        int64 (hour * 3600 + minute * 60 + second) * ticksPerSecond
    else
        raise (
            System.ArgumentOutOfRangeException(
                null,
                "Hour, Minute, and Second parameters describe an un-representable DateTime."
            )
        )

/// year, month and day of the ticks
let private datePart (ticks: int64) : int * int * int =
    let mutable n = int (ticks / ticksPerDay)
    let y400 = n / 146097
    n <- n - y400 * 146097
    let mutable y100 = n / 36524

    if y100 = 4 then
        y100 <- 3

    n <- n - y100 * 36524
    let y4 = n / 1461
    n <- n - y4 * 1461
    let mutable y1 = n / 365

    if y1 = 4 then
        y1 <- 3

    let year = y400 * 400 + y100 * 100 + y4 * 4 + y1 + 1
    n <- n - y1 * 365
    let leap = y1 = 3 && (y4 <> 24 || y100 = 3)

    let days =
        if leap then
            daysToMonth366
        else
            daysToMonth365

    let mutable m = (n >>> 5) + 1

    while n >= days.[m] do
        m <- m + 1

    year, m, n - days.[m - 1] + 1

let private checkKind (kind: int) =
    if kind < 0 || kind > 2 then
        raise (System.ArgumentException("Invalid DateTimeKind value. (Parameter 'kind')"))

let ofTicksKind (ticks: int64) (kind: int) : DateTimeOf =
    if ticks < 0L || ticks > maxTicks then
        raise (
            System.ArgumentOutOfRangeException(
                "ticks",
                "Ticks must be between DateTime.MinValue.Ticks and DateTime.MaxValue.Ticks."
            )
        )

    checkKind kind

    {
        ticks = ticks
        kind = kind
    }

let ofTicks (ticks: int64) : DateTimeOf = ofTicksKind ticks unspecified

let create3 (y: int) (m: int) (d: int) : DateTimeOf =
    {
        ticks = dateToTicks y m d
        kind = unspecified
    }

let create7Kind (y: int) (mo: int) (d: int) (h: int) (mi: int) (s: int) (ms: int) (kind: int) : DateTimeOf =
    if ms < 0 || ms >= 1000 then
        raise (System.ArgumentOutOfRangeException("millisecond", "Valid values are between 0 and 999, inclusive."))

    checkKind kind

    {
        ticks = dateToTicks y mo d + timeToTicks h mi s + int64 ms * ticksPerMillisecond
        kind = kind
    }

let create6 (y: int) (mo: int) (d: int) (h: int) (mi: int) (s: int) = create7Kind y mo d h mi s 0 unspecified
let create6Kind (y: int) (mo: int) (d: int) (h: int) (mi: int) (s: int) (kind: int) = create7Kind y mo d h mi s 0 kind

let create7 (y: int) (mo: int) (d: int) (h: int) (mi: int) (s: int) (ms: int) =
    create7Kind y mo d h mi s ms unspecified

let create8Kind (y: int) (mo: int) (d: int) (h: int) (mi: int) (s: int) (ms: int) (us: int) (kind: int) : DateTimeOf =
    if us < 0 || us >= 1000 then
        raise (System.ArgumentOutOfRangeException("microsecond", "Valid values are between 0 and 999, inclusive."))

    let t = create7Kind y mo d h mi s ms kind
    { t with ticks = t.ticks + int64 us * ticksPerMicrosecond }

let create8 (y: int) (mo: int) (d: int) (h: int) (mi: int) (s: int) (ms: int) (us: int) =
    create8Kind y mo d h mi s ms us unspecified

let minValue () : DateTimeOf =
    {
        ticks = 0L
        kind = unspecified
    }

let maxValue () : DateTimeOf =
    {
        ticks = maxTicks
        kind = unspecified
    }

let utcNow () : DateTimeOf =
    {
        ticks = nowUtcTicks ()
        kind = utc
    }

let now () : DateTimeOf =
    let t = nowUtcTicks ()

    {
        ticks = t + localOffsetTicks t
        kind = local
    }

let today () : DateTimeOf =
    let n = now ()

    {
        ticks = n.ticks - n.ticks % ticksPerDay
        kind = local
    }

// ---- parts ----

let ticks (d: DateTimeOf) = d.ticks
let kind (d: DateTimeOf) = d.kind

let year (d: DateTimeOf) =
    let y, _, _ = datePart d.ticks
    y

let month (d: DateTimeOf) =
    let _, m, _ = datePart d.ticks
    m

let day (d: DateTimeOf) =
    let _, _, dd = datePart d.ticks
    dd

let hour (d: DateTimeOf) = int ((d.ticks / ticksPerHour) % 24L)
let minute (d: DateTimeOf) = int ((d.ticks / ticksPerMinute) % 60L)
let second (d: DateTimeOf) = int ((d.ticks / ticksPerSecond) % 60L)

let millisecond (d: DateTimeOf) =
    int ((d.ticks / ticksPerMillisecond) % 1000L)

let microsecond (d: DateTimeOf) =
    int ((d.ticks / ticksPerMicrosecond) % 1000L)

let nanosecond (d: DateTimeOf) =
    int ((d.ticks % ticksPerMicrosecond) * 100L)

/// (DayOfWeek: Sunday = 0)
let dayOfWeek (d: DateTimeOf) = int ((d.ticks / ticksPerDay + 1L) % 7L)

let dayOfYear (d: DateTimeOf) =
    let y, m, dd = datePart d.ticks

    let days =
        if isLeapYear y then
            daysToMonth366
        else
            daysToMonth365

    days.[m - 1] + dd

let date (d: DateTimeOf) : DateTimeOf =
    {
        ticks = d.ticks - d.ticks % ticksPerDay
        kind = d.kind
    }

let timeOfDay (d: DateTimeOf) : TimeSpanOf =
    { TimeSpanOf.ticks = d.ticks % ticksPerDay }

let specifyKind (d: DateTimeOf) (kind: int) : DateTimeOf =
    checkKind kind

    {
        ticks = d.ticks
        kind = kind
    }

// ---- arithmetic ----

let addTicks (d: DateTimeOf) (value: int64) : DateTimeOf =
    if (value > 0L && d.ticks > maxTicks - value) || (value < 0L && d.ticks < -value) then
        raise (
            System.ArgumentOutOfRangeException(
                "value",
                "The added or subtracted value results in an un-representable DateTime."
            )
        )

    {
        ticks = d.ticks + value
        kind = d.kind
    }

let add (d: DateTimeOf) (t: TimeSpanOf) : DateTimeOf = addTicks d t.ticks

let subtract (d: DateTimeOf) (t: TimeSpanOf) : DateTimeOf =
    if t.ticks = System.Int64.MinValue then
        raise (
            System.ArgumentOutOfRangeException(
                "t",
                "The added or subtracted value results in an un-representable DateTime."
            )
        )

    addTicks d -t.ticks

let subtractDate (a: DateTimeOf) (b: DateTimeOf) : TimeSpanOf =
    { TimeSpanOf.ticks = a.ticks - b.ticks }

/// `AddDays(1.5)` and the others of a float (as .NET 7 and later: the whole units exactly,
/// then the fraction's ticks, truncated)
let private addUnits (d: DateTimeOf) (value: float) (scale: int64) : DateTimeOf =
    let limit = float (maxTicks / scale)

    if System.Double.IsNaN value || value > limit || value < -limit then
        raise (System.ArgumentOutOfRangeException("value", "Value to add was out of range."))

    let whole = int64 value
    let fraction = int64 ((value - float whole) * float scale)
    let total = decimal d.ticks + decimal whole * decimal scale + decimal fraction

    if total < 0m || total > decimal maxTicks then
        raise (
            System.ArgumentOutOfRangeException(
                "value",
                "The added or subtracted value results in an un-representable DateTime."
            )
        )

    {
        ticks = int64 total
        kind = d.kind
    }

let addDays (d: DateTimeOf) (v: float) = addUnits d v ticksPerDay
let addHours (d: DateTimeOf) (v: float) = addUnits d v ticksPerHour
let addMinutes (d: DateTimeOf) (v: float) = addUnits d v ticksPerMinute
let addSeconds (d: DateTimeOf) (v: float) = addUnits d v ticksPerSecond
let addMilliseconds (d: DateTimeOf) (v: float) = addUnits d v ticksPerMillisecond
let addMicroseconds (d: DateTimeOf) (v: float) = addUnits d v ticksPerMicrosecond

let addMonths (d: DateTimeOf) (months: int) : DateTimeOf =
    if months < -120000 || months > 120000 then
        raise (System.ArgumentOutOfRangeException("months", "Months value must be between +/-120000."))

    let y, m, dd = datePart d.ticks
    let i = m - 1 + months

    let y, m =
        if i >= 0 then
            y + i / 12, i % 12 + 1
        else
            y + (i - 11) / 12, 12 + (i + 1) % 12

    if y < 1 || y > 9999 then
        raise (
            System.ArgumentOutOfRangeException(
                "months",
                "The added or subtracted value results in an un-representable DateTime."
            )
        )

    let dd = min dd (daysInMonth y m)

    {
        ticks = dateToTicks y m dd + d.ticks % ticksPerDay
        kind = d.kind
    }

let addYears (d: DateTimeOf) (years: int) : DateTimeOf =
    if years < -10000 || years > 10000 then
        raise (System.ArgumentOutOfRangeException("years", "Years value must be between +/-10000."))

    addMonths d (years * 12)

let compare (a: DateTimeOf) (b: DateTimeOf) : int = Operators.compare a.ticks b.ticks
let equals (a: DateTimeOf) (b: DateTimeOf) : bool = a.ticks = b.ticks

// ---- local and universal time ----

let toUniversalTime (d: DateTimeOf) : DateTimeOf =
    if d.kind = utc then
        d
    else
        let t = d.ticks - offsetAtLocal d.ticks

        {
            ticks = max 0L (min maxTicks t)
            kind = utc
        }

let toLocalTime (d: DateTimeOf) : DateTimeOf =
    if d.kind = local then
        d
    else
        let t = d.ticks + localOffsetTicks d.ticks

        {
            ticks = max 0L (min maxTicks t)
            kind = local
        }

/// The offset that "z", "K" and "O" show: none for UTC, the local zone's otherwise
let private offsetOf (d: DateTimeOf) : int64 =
    if d.kind = utc then
        0L
    else
        offsetAtLocal d.ticks

// ---- text: the invariant culture's ----

let private monthNames =
    [|
        "January"
        "February"
        "March"
        "April"
        "May"
        "June"
        "July"
        "August"
        "September"
        "October"
        "November"
        "December"
    |]

let private dayNames =
    [|
        "Sunday"
        "Monday"
        "Tuesday"
        "Wednesday"
        "Thursday"
        "Friday"
        "Saturday"
    |]

let private padNum (width: int) (v: int64) = v.ToString().PadLeft(width, '0')

let private formatError () =
    raise (System.FormatException "Input string was not in a correct format.")

/// The custom format specifiers (`yyyy-MM-dd HH:mm`, quotes, `\\` and `%`); a DateTimeOffset's
/// own offset (`fixedOffset`) is the one "z" and "K" show
let formatWith (d: DateTimeOf) (fixedOffset: int64 option) (format: string) : string =
    let sb = System.Text.StringBuilder()
    let y, mo, dd = datePart d.ticks
    let h = hour d
    let fraction = d.ticks % ticksPerSecond
    let mutable i = 0
    // (after `%`: the next letter is a specifier of one letter)
    let mutable single = false

    let repeat (c: char) =
        let mutable n = 1

        while not single && i + n < format.Length && format.[i + n] = c do
            n <- n + 1

        single <- false
        n

    let offsetText (n: int) =
        let off =
            match fixedOffset with
            | Some o -> o
            | None -> offsetOf d

        let sign =
            if off < 0L then
                "-"
            else
                "+"

        let a = abs off
        let hh = a / ticksPerHour
        let mm = (a % ticksPerHour) / ticksPerMinute

        match n with
        | 1 -> sign + hh.ToString()
        | 2 -> sign + padNum 2 hh
        | _ -> sign + padNum 2 hh + ":" + padNum 2 mm

    while i < format.Length do
        let c = format.[i]

        match c with
        | 'd' ->
            let n = repeat c

            match n with
            | 1 -> sb.Append(dd) |> ignore
            | 2 -> sb.Append(padNum 2 (int64 dd)) |> ignore
            | 3 -> sb.Append(dayNames.[dayOfWeek d].Substring(0, 3)) |> ignore
            | _ -> sb.Append(dayNames.[dayOfWeek d]) |> ignore

            i <- i + n
        | 'M' ->
            let n = repeat c

            match n with
            | 1 -> sb.Append(mo) |> ignore
            | 2 -> sb.Append(padNum 2 (int64 mo)) |> ignore
            | 3 -> sb.Append(monthNames.[mo - 1].Substring(0, 3)) |> ignore
            | _ -> sb.Append(monthNames.[mo - 1]) |> ignore

            i <- i + n
        | 'y' ->
            let n = repeat c

            match n with
            | 1 -> sb.Append(y % 100) |> ignore
            | 2 -> sb.Append(padNum 2 (int64 (y % 100))) |> ignore
            | _ -> sb.Append(padNum n (int64 y)) |> ignore

            i <- i + n
        | 'h' ->
            let n = repeat c

            let h12 =
                if h % 12 = 0 then
                    12
                else
                    h % 12

            sb.Append(
                if n = 1 then
                    string h12
                else
                    padNum 2 (int64 h12)
            )
            |> ignore

            i <- i + n
        | 'H' ->
            let n = repeat c

            sb.Append(
                if n = 1 then
                    string h
                else
                    padNum 2 (int64 h)
            )
            |> ignore

            i <- i + n
        | 'm' ->
            let n = repeat c
            let v = minute d

            sb.Append(
                if n = 1 then
                    string v
                else
                    padNum 2 (int64 v)
            )
            |> ignore

            i <- i + n
        | 's' ->
            let n = repeat c
            let v = second d

            sb.Append(
                if n = 1 then
                    string v
                else
                    padNum 2 (int64 v)
            )
            |> ignore

            i <- i + n
        | 'f'
        | 'F' ->
            let n = repeat c

            if n > 7 then
                formatError ()

            let digits = (padNum 7 fraction).Substring(0, n)

            if c = 'f' then
                sb.Append(digits) |> ignore
            else
                let trimmed = digits.TrimEnd('0')

                if trimmed.Length > 0 then
                    sb.Append(trimmed) |> ignore
                elif sb.Length > 0 && sb.[sb.Length - 1] = '.' then
                    sb.Length <- sb.Length - 1

            i <- i + n
        | 't' ->
            let n = repeat c

            let designator =
                if h < 12 then
                    "AM"
                else
                    "PM"

            sb.Append(
                if n = 1 then
                    designator.Substring(0, 1)
                else
                    designator
            )
            |> ignore

            i <- i + n
        | 'z' ->
            let n = repeat c
            sb.Append(offsetText n) |> ignore
            i <- i + n
        | 'K' ->
            if fixedOffset.IsSome then
                sb.Append(offsetText 3) |> ignore
            elif d.kind = utc then
                sb.Append('Z') |> ignore
            elif d.kind = local then
                sb.Append(offsetText 3) |> ignore

            i <- i + 1
        | 'g' ->
            let n = repeat c
            sb.Append("A.D.") |> ignore
            i <- i + n
        | ':'
        | '/' ->
            sb.Append(c) |> ignore
            i <- i + 1
        | '\''
        | '"' ->
            let close = format.IndexOf(c, i + 1)

            if close < 0 then
                raise (
                    System.FormatException(
                        "Cannot find a matching quote character for the character '" + string c + "'."
                    )
                )

            sb.Append(format.Substring(i + 1, close - i - 1)) |> ignore
            i <- close + 1
        | '\\' ->
            if i + 1 >= format.Length then
                formatError ()

            sb.Append(format.[i + 1]) |> ignore
            i <- i + 2
        | '%' ->
            // (`%d`: the one specifier on its own)
            if i + 1 >= format.Length || format.[i + 1] = '%' then
                formatError ()

            single <- true
            i <- i + 1
        | _ ->
            sb.Append(c) |> ignore
            i <- i + 1

    sb.ToString()

let formatCustom (d: DateTimeOf) (format: string) : string = formatWith d None format

/// `d.ToString(format)`: the standard formats of the invariant culture, or a custom one
let toStringFormat (d: DateTimeOf) (format: string) : string =
    match format with
    | null
    | "" -> formatCustom d "MM/dd/yyyy HH:mm:ss"
    | "d" -> formatCustom d "MM/dd/yyyy"
    | "D" -> formatCustom d "dddd, dd MMMM yyyy"
    | "f" -> formatCustom d "dddd, dd MMMM yyyy HH:mm"
    | "F" -> formatCustom d "dddd, dd MMMM yyyy HH:mm:ss"
    | "g" -> formatCustom d "MM/dd/yyyy HH:mm"
    | "G" -> formatCustom d "MM/dd/yyyy HH:mm:ss"
    | "m"
    | "M" -> formatCustom d "MMMM dd"
    | "o"
    | "O" -> formatCustom d "yyyy'-'MM'-'dd'T'HH':'mm':'ss'.'fffffffK"
    | "r"
    | "R" -> formatCustom d "ddd, dd MMM yyyy HH':'mm':'ss 'GMT'"
    | "s" -> formatCustom d "yyyy'-'MM'-'dd'T'HH':'mm':'ss"
    | "t" -> formatCustom d "HH:mm"
    | "T" -> formatCustom d "HH:mm:ss"
    | "u" -> formatCustom d "yyyy'-'MM'-'dd HH':'mm':'ss'Z'"
    | "U" -> formatCustom (toUniversalTime d) "dddd, dd MMMM yyyy HH:mm:ss"
    | "y"
    | "Y" -> formatCustom d "yyyy MMMM"
    | f when f.Length = 1 -> formatError ()
    | f -> formatCustom d f

let toString (d: DateTimeOf) : string = toStringFormat d "G"
let toShortDateString (d: DateTimeOf) = toStringFormat d "d"
let toLongDateString (d: DateTimeOf) = toStringFormat d "D"
let toShortTimeString (d: DateTimeOf) = toStringFormat d "t"
let toLongTimeString (d: DateTimeOf) = toStringFormat d "T"

// ---- parsing: ISO 8601, and the invariant culture's `M/d/yyyy h:m:s [AM|PM]` ----

/// The clock time and the offset written, if one is, of ISO 8601 or `M/d/yyyy h:m:s [AM|PM]`
let parseRaw (input: string) : (int64 * int64 option) option =
    let s =
        if isNull input then
            ""
        else
            input.Trim()

    let mutable i = 0

    let peek () =
        if i < s.Length then
            s.[i]
        else
            '\000'

    let number (maxDigits: int) =
        let start = i

        while i < s.Length && i - start < maxDigits && System.Char.IsDigit s.[i] do
            i <- i + 1

        if i = start then
            None
        else
            Some(int s.[start .. i - 1])

    let expect (c: char) =
        if peek () = c then
            i <- i + 1
            true
        else
            false

    let skipSpaces () =
        while i < s.Length && s.[i] = ' ' do
            i <- i + 1

    // the time: h:m[:s[.f]] [AM|PM]; its ticks
    let time () : int64 option =
        match number 2 with
        | None -> None
        | Some h ->
            if not (expect ':') then
                None
            else
                match number 2 with
                | None -> None
                | Some m ->
                    let sec =
                        if expect ':' then
                            number 2
                        else
                            Some 0

                    match sec with
                    | None -> None
                    | Some sec ->
                        let mutable fraction = 0L

                        if peek () = '.' && i + 1 < s.Length && System.Char.IsDigit s.[i + 1] then
                            i <- i + 1
                            let start = i

                            while i < s.Length && System.Char.IsDigit s.[i] do
                                i <- i + 1

                            let digits = s.[start .. i - 1]

                            let digits =
                                if digits.Length > 7 then
                                    digits.Substring(0, 7)
                                else
                                    digits.PadRight(7, '0')

                            fraction <- int64 digits

                        let save = i
                        skipSpaces ()
                        let rest = s.Substring(i).ToUpperInvariant()

                        let h =
                            if rest.StartsWith "AM" then
                                i <- i + 2

                                Some(
                                    if h = 12 then
                                        0
                                    else
                                        h
                                )
                            elif rest.StartsWith "PM" then
                                i <- i + 2

                                Some(
                                    if h < 12 then
                                        h + 12
                                    else
                                        h
                                )
                            else
                                i <- save
                                Some h

                        match h with
                        | Some h when h < 24 && m < 60 && sec < 60 ->
                            Some(int64 (h * 3600 + m * 60 + sec) * ticksPerSecond + fraction)
                        | _ -> None

    // the zone: Z, or +hh:mm / -hh:mm / +hhmm / +hh; its offset
    let zone () : int64 option option =
        match peek () with
        | 'Z'
        | 'z' ->
            i <- i + 1
            Some(Some 0L)
        | '+'
        | '-' as sign ->
            i <- i + 1

            match number 2 with
            | Some hh ->
                let _ = expect ':'
                let mm = defaultArg (number 2) 0
                let off = int64 hh * ticksPerHour + int64 mm * ticksPerMinute

                Some(
                    Some(
                        if sign = '-' then
                            -off
                        else
                            off
                    )
                )
            | None -> None
        | _ -> Some None

    let validDate y m d =
        y >= 1 && y <= 9999 && m >= 1 && m <= 12 && d >= 1 && d <= daysInMonth y m

    // the date: yyyy-MM-dd or M/d/yyyy (or none: today)
    let date () : int64 option =
        let start = i

        match number 4 with
        | Some y when i - start = 4 && peek () = '-' ->
            i <- i + 1

            match number 2 with
            | Some m when expect '-' ->
                match number 2 with
                | Some d when validDate y m d -> Some(dateToTicks y m d)
                | _ -> None
            | _ -> None
        | Some m when peek () = '/' ->
            i <- i + 1

            match number 2 with
            | Some d when expect '/' ->
                match number 4 with
                | Some y when validDate y m d -> Some(dateToTicks y m d)
                | _ -> None
            | _ -> None
        | _ ->
            i <- start
            Some((today ()).ticks)

    let afterDate = i

    match date () with
    | None -> None
    | Some dayTicks ->
        let hadDate = i > afterDate

        if hadDate && (peek () = 'T' || peek () = ' ') then
            i <- i + 1

        let t =
            if i < s.Length then
                time ()
            elif hadDate then
                Some 0L
            else
                None

        match t with
        | None -> None
        | Some t ->
            match zone () with
            | Some z when i = s.Length -> Some(dayTicks + t, z)
            | _ -> None

let private parseWith (input: string) : DateTimeOf option =
    match parseRaw input with
    | None -> None
    | Some(ticks, z) ->
        match z with
        | None ->
            Some
                {
                    ticks = ticks
                    kind = unspecified
                }
        | Some off ->
            // (an instant: the local time it is, as .NET gives it)
            let u = ticks - off

            if u < 0L || u > maxTicks then
                None
            else
                Some(
                    toLocalTime
                        {
                            ticks = u
                            kind = utc
                        }
                )

let parse (s: string) : DateTimeOf =
    if isNull s then
        raise (System.ArgumentNullException("s", "Value cannot be null."))

    match parseWith s with
    | Some d -> d
    | None -> raise (System.FormatException("String '" + s + "' was not recognized as a valid DateTime."))

let tryParseOption (s: string) : DateTimeOf option = parseWith s

let tryParse (s: string) : bool * DateTimeOf =
    match parseWith s with
    | Some d -> true, d
    | None -> false, minValue ()
