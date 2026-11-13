/// .NET's `System.DateTimeOffset`, written in F# and compiled by the Zig target itself (see
/// List.fs): a UTC instant and an offset in minutes, equal and ordered by the instant, with the
/// clock time (`utc + offset`) for its parts, arithmetic and formats.
module Fable.Library.Zig.DateTimeOffset

open Fable.Library.Zig.TimeSpan
open Fable.Library.Zig.DateTime
open Fable.Library.Zig.DateOnly

[<Struct; CustomEquality; CustomComparison>]
type DateTimeOffsetOf =
    {
        utcTicks: int64
        offsetMinutes: int
    }

    override d.Equals(o: obj) =
        match o with
        | :? DateTimeOffsetOf as e -> d.utcTicks = e.utcTicks
        | _ -> false

    override d.GetHashCode() =
        int d.utcTicks ^^^ int (d.utcTicks >>> 32)

    interface System.IComparable with
        member d.CompareTo(o: obj) =
            match o with
            | :? DateTimeOffsetOf as e -> Operators.compare d.utcTicks e.utcTicks
            | _ -> invalidArg "obj" "Object must be of type DateTimeOffset."

let private unixEpochTicks = 621355968000000000L

/// The offset as minutes: whole, and within 14 hours
let private minutesOf (offset: TimeSpanOf) : int =
    if offset.ticks % ticksPerMinute <> 0L then
        raise (System.ArgumentException("Offset must be specified in whole minutes. (Parameter 'offset')"))

    if offset.ticks < -14L * ticksPerHour || offset.ticks > 14L * ticksPerHour then
        raise (System.ArgumentOutOfRangeException("offset", "Offset must be within plus or minus 14 hours."))

    int (offset.ticks / ticksPerMinute)

let private make (clockTicks: int64) (minutes: int) : DateTimeOffsetOf =
    let u = clockTicks - int64 minutes * ticksPerMinute

    if u < 0L || u > maxTicks then
        raise (
            System.ArgumentOutOfRangeException(
                "offset",
                "The UTC time represented when the offset is applied must be between year 0 and 10,000."
            )
        )

    {
        utcTicks = u
        offsetMinutes = minutes
    }

let private clock (d: DateTimeOffsetOf) : int64 =
    d.utcTicks + int64 d.offsetMinutes * ticksPerMinute

let private clockDate (d: DateTimeOffsetOf) : DateTimeOf =
    {
        ticks = clock d
        kind = 0
    }

let private localMinutes (utcTicks: int64) =
    int (localOffsetTicks utcTicks / ticksPerMinute)

// ---- making ----

let ofTicks (ticks: int64) (offset: TimeSpanOf) : DateTimeOffsetOf =
    if ticks < 0L || ticks > maxTicks then
        raise (
            System.ArgumentOutOfRangeException(
                "ticks",
                "Ticks must be between DateTime.MinValue.Ticks and DateTime.MaxValue.Ticks."
            )
        )

    make ticks (minutesOf offset)

let create7 (y: int) (mo: int) (d: int) (h: int) (mi: int) (s: int) (offset: TimeSpanOf) =
    make (DateTime.create6 y mo d h mi s).ticks (minutesOf offset)

let create8 (y: int) (mo: int) (d: int) (h: int) (mi: int) (s: int) (ms: int) (offset: TimeSpanOf) =
    make (DateTime.create7 y mo d h mi s ms).ticks (minutesOf offset)

let create9 (y: int) (mo: int) (d: int) (h: int) (mi: int) (s: int) (ms: int) (us: int) (offset: TimeSpanOf) =
    make (DateTime.create8 y mo d h mi s ms us).ticks (minutesOf offset)

/// `DateTimeOffset(dateTime)`: UTC's offset is zero, the others' the local zone's
let ofDateTime (d: DateTimeOf) : DateTimeOffsetOf =
    if d.kind = 1 then
        {
            utcTicks = d.ticks
            offsetMinutes = 0
        }
    else
        make d.ticks (int (offsetAtLocal d.ticks / ticksPerMinute))

/// `DateTimeOffset(dateTime, offset)`: the offset must be the kind's own
let ofDateTimeOffset (d: DateTimeOf) (offset: TimeSpanOf) : DateTimeOffsetOf =
    let minutes = minutesOf offset

    if d.kind = 1 && minutes <> 0 then
        raise (System.ArgumentException("The UTC Offset for Utc DateTime instances must be 0. (Parameter 'offset')"))

    if d.kind = 2 && int64 minutes * ticksPerMinute <> offsetAtLocal d.ticks then
        raise (
            System.ArgumentException(
                "The UTC Offset of the local dateTime parameter does not match the offset argument. (Parameter 'offset')"
            )
        )

    make d.ticks minutes

let ofDateAndTime (d: DateOnlyOf) (t: TimeOnlyOf) (offset: TimeSpanOf) : DateTimeOffsetOf =
    make (int64 d.dayNumber * ticksPerDay + t.timeTicks) (minutesOf offset)

let utcNow () : DateTimeOffsetOf =
    {
        utcTicks = nowUtcTicks ()
        offsetMinutes = 0
    }

let now () : DateTimeOffsetOf =
    let u = nowUtcTicks ()

    {
        utcTicks = u
        offsetMinutes = localMinutes u
    }

let minValue () : DateTimeOffsetOf =
    {
        utcTicks = 0L
        offsetMinutes = 0
    }

let maxValue () : DateTimeOffsetOf =
    {
        utcTicks = maxTicks
        offsetMinutes = 0
    }

let unixEpoch () : DateTimeOffsetOf =
    {
        utcTicks = unixEpochTicks
        offsetMinutes = 0
    }

let fromUnixTimeSeconds (seconds: int64) : DateTimeOffsetOf =
    if seconds < -62135596800L || seconds > 253402300799L then
        raise (
            System.ArgumentOutOfRangeException(
                "seconds",
                "Valid values are between -62135596800 and 253402300799, inclusive."
            )
        )

    {
        utcTicks = seconds * ticksPerSecond + unixEpochTicks
        offsetMinutes = 0
    }

let fromUnixTimeMilliseconds (ms: int64) : DateTimeOffsetOf =
    if ms < -62135596800000L || ms > 253402300799999L then
        raise (
            System.ArgumentOutOfRangeException(
                "milliseconds",
                "Valid values are between -62135596800000 and 253402300799999, inclusive."
            )
        )

    {
        utcTicks = ms * ticksPerMillisecond + unixEpochTicks
        offsetMinutes = 0
    }

// ---- parts: of the clock time ----

let ticks (d: DateTimeOffsetOf) = clock d
let utcTicks (d: DateTimeOffsetOf) = d.utcTicks
let year (d: DateTimeOffsetOf) = DateTime.year (clockDate d)
let month (d: DateTimeOffsetOf) = DateTime.month (clockDate d)
let day (d: DateTimeOffsetOf) = DateTime.day (clockDate d)
let hour (d: DateTimeOffsetOf) = DateTime.hour (clockDate d)
let minute (d: DateTimeOffsetOf) = DateTime.minute (clockDate d)
let second (d: DateTimeOffsetOf) = DateTime.second (clockDate d)
let millisecond (d: DateTimeOffsetOf) = DateTime.millisecond (clockDate d)
let microsecond (d: DateTimeOffsetOf) = DateTime.microsecond (clockDate d)
let nanosecond (d: DateTimeOffsetOf) = DateTime.nanosecond (clockDate d)
let dayOfWeek (d: DateTimeOffsetOf) = DateTime.dayOfWeek (clockDate d)
let dayOfYear (d: DateTimeOffsetOf) = DateTime.dayOfYear (clockDate d)
let timeOfDay (d: DateTimeOffsetOf) = DateTime.timeOfDay (clockDate d)
let date (d: DateTimeOffsetOf) : DateTimeOf = DateTime.date (clockDate d)
let dateTime (d: DateTimeOffsetOf) : DateTimeOf = clockDate d

let utcDateTime (d: DateTimeOffsetOf) : DateTimeOf =
    {
        ticks = d.utcTicks
        kind = 1
    }

let localDateTime (d: DateTimeOffsetOf) : DateTimeOf =
    DateTime.toLocalTime
        {
            ticks = d.utcTicks
            kind = 1
        }

let offset (d: DateTimeOffsetOf) : TimeSpanOf =
    { TimeSpanOf.ticks = int64 d.offsetMinutes * ticksPerMinute }

let totalOffsetMinutes (d: DateTimeOffsetOf) = d.offsetMinutes

// ---- conversions ----

let toUniversalTime (d: DateTimeOffsetOf) : DateTimeOffsetOf = { d with offsetMinutes = 0 }

let toLocalTime (d: DateTimeOffsetOf) : DateTimeOffsetOf =
    { d with offsetMinutes = localMinutes d.utcTicks }

let toOffset (d: DateTimeOffsetOf) (o: TimeSpanOf) : DateTimeOffsetOf =
    make (d.utcTicks + o.ticks) (minutesOf o)

let toUnixTimeSeconds (d: DateTimeOffsetOf) : int64 =
    d.utcTicks / ticksPerSecond - unixEpochTicks / ticksPerSecond

let toUnixTimeMilliseconds (d: DateTimeOffsetOf) : int64 =
    d.utcTicks / ticksPerMillisecond - unixEpochTicks / ticksPerMillisecond

// ---- arithmetic: on the clock time, the offset kept ----

let private onClock (d: DateTimeOffsetOf) (f: DateTimeOf -> DateTimeOf) : DateTimeOffsetOf =
    make (f (clockDate d)).ticks d.offsetMinutes

let add (d: DateTimeOffsetOf) (t: TimeSpanOf) = onClock d (fun c -> DateTime.add c t)

let subtract (d: DateTimeOffsetOf) (t: TimeSpanOf) =
    onClock d (fun c -> DateTime.subtract c t)

let subtractOffset (a: DateTimeOffsetOf) (b: DateTimeOffsetOf) : TimeSpanOf =
    { TimeSpanOf.ticks = a.utcTicks - b.utcTicks }

let addTicks (d: DateTimeOffsetOf) (v: int64) =
    onClock d (fun c -> DateTime.addTicks c v)

let addDays (d: DateTimeOffsetOf) (v: float) =
    onClock d (fun c -> DateTime.addDays c v)

let addHours (d: DateTimeOffsetOf) (v: float) =
    onClock d (fun c -> DateTime.addHours c v)

let addMinutes (d: DateTimeOffsetOf) (v: float) =
    onClock d (fun c -> DateTime.addMinutes c v)

let addSeconds (d: DateTimeOffsetOf) (v: float) =
    onClock d (fun c -> DateTime.addSeconds c v)

let addMilliseconds (d: DateTimeOffsetOf) (v: float) =
    onClock d (fun c -> DateTime.addMilliseconds c v)

let addMicroseconds (d: DateTimeOffsetOf) (v: float) =
    onClock d (fun c -> DateTime.addMicroseconds c v)

let addMonths (d: DateTimeOffsetOf) (v: int) =
    onClock d (fun c -> DateTime.addMonths c v)

let addYears (d: DateTimeOffsetOf) (v: int) =
    onClock d (fun c -> DateTime.addYears c v)

let compare (a: DateTimeOffsetOf) (b: DateTimeOffsetOf) = Operators.compare a.utcTicks b.utcTicks
let equals (a: DateTimeOffsetOf) (b: DateTimeOffsetOf) = a.utcTicks = b.utcTicks

let equalsExact (a: DateTimeOffsetOf) (b: DateTimeOffsetOf) =
    a.utcTicks = b.utcTicks && a.offsetMinutes = b.offsetMinutes

// ---- text ----

/// `d.ToString(format)`: the standard formats ("R", "r" and "u" of the UTC time), or a custom one
let toStringFormat (d: DateTimeOffsetOf) (format: string) : string =
    let off = Some(int64 d.offsetMinutes * ticksPerMinute)
    let c = clockDate d

    let u: DateTimeOf =
        {
            ticks = d.utcTicks
            kind = 1
        }

    match format with
    | null
    | "" -> formatWith c off "MM/dd/yyyy HH:mm:ss zzz"
    | "o"
    | "O" -> formatWith c off "yyyy'-'MM'-'dd'T'HH':'mm':'ss'.'fffffffK"
    | "r"
    | "R" -> formatWith u None "ddd, dd MMM yyyy HH':'mm':'ss 'GMT'"
    | "u" -> formatWith u None "yyyy'-'MM'-'dd HH':'mm':'ss'Z'"
    | "U" -> raise (System.FormatException "Input string was not in a correct format.")
    | f when f.Length = 1 -> DateTime.toStringFormat c f
    | f -> formatWith c off f

let toString (d: DateTimeOffsetOf) : string = toStringFormat d ""

/// The forms of DateTime.Parse; without an offset written, the local zone's
let private parseWith (s: string) : DateTimeOffsetOf option =
    match parseRaw s with
    | None -> None
    | Some(clockTicks, zone) ->
        let minutes =
            match zone with
            | Some o -> int (o / ticksPerMinute)
            | None -> int (offsetAtLocal clockTicks / ticksPerMinute)

        let u = clockTicks - int64 minutes * ticksPerMinute

        if u < 0L || u > maxTicks || minutes < -840 || minutes > 840 then
            None
        else
            Some
                {
                    utcTicks = u
                    offsetMinutes = minutes
                }

let parse (s: string) : DateTimeOffsetOf =
    if isNull s then
        raise (System.ArgumentNullException("input", "Value cannot be null."))

    match parseWith s with
    | Some d -> d
    | None -> raise (System.FormatException("String '" + s + "' was not recognized as a valid DateTime."))

let tryParseOption (s: string) : DateTimeOffsetOf option = parseWith s

let tryParse (s: string) : bool * DateTimeOffsetOf =
    match parseWith s with
    | Some d -> true, d
    | None -> false, minValue ()
