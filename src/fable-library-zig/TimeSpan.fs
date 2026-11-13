/// .NET's `System.TimeSpan`, written in F# and compiled by the Zig target itself (see List.fs):
/// a count of ticks (100 nanoseconds), with .NET's conversions, formats ("c", "g", "G") and
/// parsing (the invariant culture's).
module Fable.Library.Zig.TimeSpan

[<Struct>]
type TimeSpanOf = { ticks: int64 }

let ticksPerMicrosecond = 10L
let ticksPerMillisecond = 10_000L
let ticksPerSecond = 10_000_000L
let ticksPerMinute = 600_000_000L
let ticksPerHour = 36_000_000_000L
let ticksPerDay = 864_000_000_000L

let private overflow () =
    raise (System.OverflowException "TimeSpan overflowed because the duration is too long.")

let ofTicks (ticks: int64) : TimeSpanOf = { ticks = ticks }
let zero () : TimeSpanOf = { ticks = 0L }
let minValue () : TimeSpanOf = { ticks = System.Int64.MinValue }
let maxValue () : TimeSpanOf = { ticks = System.Int64.MaxValue }

/// `TimeSpan(h, m, s)` and the others: the total, which must fit
let private ofParts (days: int64) (hours: int64) (minutes: int64) (seconds: int64) (millis: int64) (micros: int64) =
    let total =
        decimal days * decimal ticksPerDay
        + decimal hours * decimal ticksPerHour
        + decimal minutes * decimal ticksPerMinute
        + decimal seconds * decimal ticksPerSecond
        + decimal millis * decimal ticksPerMillisecond
        + decimal micros * decimal ticksPerMicrosecond

    if total > decimal System.Int64.MaxValue || total < decimal System.Int64.MinValue then
        raise (System.ArgumentOutOfRangeException(null, "TimeSpan overflowed because the duration is too long."))

    { ticks = int64 total }

let create3 (h: int) (m: int) (s: int) =
    ofParts 0L (int64 h) (int64 m) (int64 s) 0L 0L

let create4 (d: int) (h: int) (m: int) (s: int) =
    ofParts (int64 d) (int64 h) (int64 m) (int64 s) 0L 0L

let create5 (d: int) (h: int) (m: int) (s: int) (ms: int) =
    ofParts (int64 d) (int64 h) (int64 m) (int64 s) (int64 ms) 0L

let create6 (d: int) (h: int) (m: int) (s: int) (ms: int) (us: int) =
    ofParts (int64 d) (int64 h) (int64 m) (int64 s) (int64 ms) (int64 us)

/// `TimeSpan.FromSeconds(1.5)` and the others of a float: the ticks, truncated
let private ofDouble (value: float) (scale: int64) : TimeSpanOf =
    if System.Double.IsNaN value then
        raise (System.ArgumentException "TimeSpan does not accept floating point Not-a-Number values.")

    let ticks = value * float scale

    if ticks > 9.2233720368547758e18 || ticks < -9.2233720368547758e18 then
        overflow ()

    { ticks = int64 ticks }

let fromDays (v: float) = ofDouble v ticksPerDay
let fromHours (v: float) = ofDouble v ticksPerHour
let fromMinutes (v: float) = ofDouble v ticksPerMinute
let fromSeconds (v: float) = ofDouble v ticksPerSecond
let fromMilliseconds (v: float) = ofDouble v ticksPerMillisecond
let fromMicroseconds (v: float) = ofDouble v ticksPerMicrosecond

let ticks (t: TimeSpanOf) = t.ticks
let days (t: TimeSpanOf) = int (t.ticks / ticksPerDay)
let hours (t: TimeSpanOf) = int ((t.ticks / ticksPerHour) % 24L)
let minutes (t: TimeSpanOf) = int ((t.ticks / ticksPerMinute) % 60L)
let seconds (t: TimeSpanOf) = int ((t.ticks / ticksPerSecond) % 60L)

let milliseconds (t: TimeSpanOf) =
    int ((t.ticks / ticksPerMillisecond) % 1000L)

let microseconds (t: TimeSpanOf) =
    int ((t.ticks / ticksPerMicrosecond) % 1000L)

let nanoseconds (t: TimeSpanOf) =
    int ((t.ticks % ticksPerMicrosecond) * 100L)

let totalDays (t: TimeSpanOf) = float t.ticks / float ticksPerDay
let totalHours (t: TimeSpanOf) = float t.ticks / float ticksPerHour
let totalMinutes (t: TimeSpanOf) = float t.ticks / float ticksPerMinute
let totalSeconds (t: TimeSpanOf) = float t.ticks / float ticksPerSecond

let totalMilliseconds (t: TimeSpanOf) =
    let ms = float t.ticks / float ticksPerMillisecond
    // (.NET keeps it within what a TimeSpan can hold in milliseconds)
    if ms > 922337203685477.0 then
        922337203685477.0
    elif ms < -922337203685477.0 then
        -922337203685477.0
    else
        ms

let totalMicroseconds (t: TimeSpanOf) =
    float t.ticks / float ticksPerMicrosecond

let totalNanoseconds (t: TimeSpanOf) = float t.ticks * 100.0

let add (a: TimeSpanOf) (b: TimeSpanOf) : TimeSpanOf =
    let r = a.ticks + b.ticks

    // (the sign of the sum differs from both of the same sign: it overflowed)
    if (a.ticks >>> 63) = (b.ticks >>> 63) && (a.ticks >>> 63) <> (r >>> 63) then
        overflow ()

    { ticks = r }

let subtract (a: TimeSpanOf) (b: TimeSpanOf) : TimeSpanOf =
    let r = a.ticks - b.ticks

    if (a.ticks >>> 63) <> (b.ticks >>> 63) && (a.ticks >>> 63) <> (r >>> 63) then
        overflow ()

    { ticks = r }

let negate (t: TimeSpanOf) : TimeSpanOf =
    if t.ticks = System.Int64.MinValue then
        raise (System.OverflowException "Negating the minimum value of a twos complement number is invalid.")

    { ticks = -t.ticks }

let duration (t: TimeSpanOf) : TimeSpanOf =
    if t.ticks = System.Int64.MinValue then
        raise (
            System.OverflowException
                "The duration cannot be returned for TimeSpan.MinValue because the absolute value of TimeSpan.MinValue exceeds the value of TimeSpan.MaxValue."
        )

    { ticks = abs t.ticks }

let multiply (t: TimeSpanOf) (factor: float) : TimeSpanOf =
    if System.Double.IsNaN factor then
        raise (
            System.ArgumentException(
                "TimeSpan does not accept floating point Not-a-Number values. (Parameter 'factor')"
            )
        )

    let ticks = System.Math.Round(float t.ticks * factor)

    if ticks > 9.2233720368547758e18 || ticks < -9.2233720368547758e18 then
        overflow ()

    { ticks = int64 ticks }

let divide (t: TimeSpanOf) (divisor: float) : TimeSpanOf =
    if System.Double.IsNaN divisor then
        raise (
            System.ArgumentException(
                "TimeSpan does not accept floating point Not-a-Number values. (Parameter 'divisor')"
            )
        )

    let ticks = System.Math.Round(float t.ticks / divisor)

    if
        ticks > 9.2233720368547758e18
        || ticks < -9.2233720368547758e18
        || System.Double.IsNaN ticks
    then
        overflow ()

    { ticks = int64 ticks }

let divideBy (a: TimeSpanOf) (b: TimeSpanOf) : float = float a.ticks / float b.ticks

let compare (a: TimeSpanOf) (b: TimeSpanOf) : int = Operators.compare a.ticks b.ticks

// ---- text ----

let private pad (width: int) (v: int64) = v.ToString().PadLeft(width, '0')

/// `t.ToString(format)`: "c" (also "t", "T" and none), "g", "G"
let toStringFormat (t: TimeSpanOf) (format: string) : string =
    let negative = t.ticks < 0L
    // (the parts of the magnitude; MinValue's is one tick more than MaxValue's)
    let magnitude =
        if negative then
            -(decimal t.ticks)
        else
            decimal t.ticks

    let part (unit: int64) =
        int64 (System.Math.Floor(magnitude / decimal unit))

    let d = part ticksPerDay
    let h = part ticksPerHour % 24L
    let m = part ticksPerMinute % 60L
    let s = part ticksPerSecond % 60L
    let f = int64 (magnitude % decimal ticksPerSecond)

    let sign =
        if negative then
            "-"
        else
            ""

    match format with
    | null
    | ""
    | "c"
    | "t"
    | "T" ->
        let days =
            if d > 0L then
                d.ToString() + "."
            else
                ""

        let fraction =
            if f > 0L then
                "." + pad 7 f
            else
                ""

        sign + days + pad 2 h + ":" + pad 2 m + ":" + pad 2 s + fraction
    | "g" ->
        let days =
            if d > 0L then
                d.ToString() + ":"
            else
                ""

        let fraction =
            if f > 0L then
                "." + (pad 7 f).TrimEnd('0')
            else
                ""

        sign + days + h.ToString() + ":" + pad 2 m + ":" + pad 2 s + fraction
    | "G" ->
        sign
        + d.ToString()
        + ":"
        + pad 2 h
        + ":"
        + pad 2 m
        + ":"
        + pad 2 s
        + "."
        + pad 7 f
    | _ -> raise (System.FormatException "Input string was not in a correct format.")

let toString (t: TimeSpanOf) : string = toStringFormat t "c"

/// The invariant culture's forms: `[-]d`, or `[-][d.]h:m[:s[.f]]`, or `[-]d:h:m:s[.f]`; the
/// error when it is not one (a FormatException, or an OverflowException for a part too big)
let private parseWith (s: string) : Result<TimeSpanOf, exn> =
    let formatError () =
        Error(System.FormatException("String '" + s + "' was not recognized as a valid TimeSpan.") :> exn)

    let overflowError () =
        Error(
            System.OverflowException(
                "The TimeSpan string '"
                + s
                + "' could not be parsed because at least one of the numeric components is out of range or contains too many digits."
            )
            :> exn
        )

    let text =
        if isNull s then
            ""
        else
            s.Trim()

    let negative, body =
        if text.StartsWith "-" then
            true, text.Substring 1
        else
            false, text

    let isDigits (p: string) =
        p.Length > 0 && p |> Seq.forall System.Char.IsDigit

    let number (p: string) =
        if p.Length > 9 then
            None
        else
            Some(int64 p)

    let finish (d: int64) (h: int64) (m: int64) (sec: int64) (fraction: string) =
        if h > 23L || m > 59L || sec > 59L || fraction.Length > 7 then
            overflowError ()
        else
            let f =
                if fraction = "" then
                    0L
                else
                    int64 (fraction.PadRight(7, '0'))

            let total =
                d * ticksPerDay
                + h * ticksPerHour
                + m * ticksPerMinute
                + sec * ticksPerSecond
                + f

            if d > 10675199L then
                overflowError ()
            else
                Ok
                    {
                        ticks =
                            if negative then
                                -total
                            else
                                total
                    }

    if body = "" then
        formatError ()
    elif isDigits body then
        match number body with
        | Some d when d <= 10675199L ->
            Ok
                {
                    ticks =
                        (if negative then
                             -1L
                         else
                             1L)
                        * d
                        * ticksPerDay
                }
        | _ -> overflowError ()
    else
        // the fraction: after the last '.' that follows a ':'
        let colon = body.IndexOf ':'

        if colon < 0 then
            formatError ()
        else
            let lastColon = body.LastIndexOf ':'
            let dot = body.IndexOf('.', lastColon)

            let main, fraction =
                if dot >= 0 then
                    body.Substring(0, dot), body.Substring(dot + 1)
                else
                    body, ""

            if dot >= 0 && not (isDigits fraction) then
                formatError ()
            else
                // a day before the first ':', as `d.` (or, with four parts, `d:`)
                let first = main.Substring(0, colon)
                let dayDot = first.IndexOf '.'

                let days, hourText, restText =
                    if dayDot >= 0 then
                        Some(first.Substring(0, dayDot)), first.Substring(dayDot + 1), main.Substring(colon + 1)
                    else
                        None, first, main.Substring(colon + 1)

                let parts = restText.Split(':')

                let all =
                    (match days with
                     | Some d -> [ d ]
                     | None -> [])
                    @ [ hourText ]
                    @ List.ofArray parts

                if all |> List.exists (fun p -> not (isDigits p)) then
                    formatError ()
                else
                    match all |> List.map number with
                    | ns when ns |> List.exists Option.isNone -> overflowError ()
                    | ns ->
                        let ns = ns |> List.map Option.get

                        match days, ns with
                        | Some _, [ d; h; m ] -> finish d h m 0L fraction
                        | Some _, [ d; h; m; sec ] -> finish d h m sec fraction
                        | None, [ h; m ] when fraction = "" -> finish 0L h m 0L ""
                        // (`24:0:0`: an hour over 23 makes it days, hours, minutes, as .NET reads it)
                        | None, [ d; h; m ] when d > 23L && fraction = "" -> finish d h m 0L ""
                        | None, [ h; m; sec ] -> finish 0L h m sec fraction
                        | None, [ d; h; m; sec ] -> finish d h m sec fraction
                        | _ -> formatError ()

let parse (s: string) : TimeSpanOf =
    if isNull s then
        raise (System.ArgumentNullException("input", "Value cannot be null."))

    match parseWith s with
    | Ok t -> t
    | Error e -> raise e

let tryParseOption (s: string) : TimeSpanOf option =
    match parseWith s with
    | Ok t -> Some t
    | Error _ -> None

let tryParse (s: string) : bool * TimeSpanOf =
    match parseWith s with
    | Ok t -> true, t
    | Error _ -> false, zero ()

/// `TimeSpan.FromDays(3)` and the other overloads of whole numbers: exact
let ofUnits (count: int64) (unit: int64) : TimeSpanOf =
    let total = decimal count * decimal unit

    if total > decimal System.Int64.MaxValue || total < decimal System.Int64.MinValue then
        overflow ()

    { ticks = int64 total }

/// `TimeSpan.FromDays(d, h, m, s, ms, us)` and the shorter ones (.NET 9): the parts that are
/// given (an optional one left out is None), each exact
let ofComponents
    (days: int64 option)
    (hours: int64 option)
    (minutes: int64 option)
    (seconds: int64 option)
    (millis: int64 option)
    (micros: int64 option)
    : TimeSpanOf
    =
    let total =
        decimal (defaultArg days 0L) * decimal ticksPerDay
        + decimal (defaultArg hours 0L) * decimal ticksPerHour
        + decimal (defaultArg minutes 0L) * decimal ticksPerMinute
        + decimal (defaultArg seconds 0L) * decimal ticksPerSecond
        + decimal (defaultArg millis 0L) * decimal ticksPerMillisecond
        + decimal (defaultArg micros 0L) * decimal ticksPerMicrosecond

    if total > decimal System.Int64.MaxValue || total < decimal System.Int64.MinValue then
        overflow ()

    { ticks = int64 total }
