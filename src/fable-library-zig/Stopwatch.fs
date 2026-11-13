/// .NET's `System.Diagnostics.Stopwatch`, written in F# and compiled by the Zig target itself
/// (see List.fs): the monotonic clock in nanoseconds (a frequency of 10^9, as .NET's on Linux and
/// macOS), and a watch that adds up the time it runs.
module Fable.Library.Zig.Stopwatch

open Fable.Library.Zig.TimeSpan

#if FABLE_COMPILER
[<Fable.Core.Emit("fable_rt.time.monotonicNs()")>]
let private monotonicNs () : int64 = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.time.sleepMilliseconds($0)")>]
let private sleepMs (_ms: int64) : unit = Fable.Core.Util.nativeOnly
#else
let private monotonicNs () : int64 =
    System.Diagnostics.Stopwatch.GetTimestamp()

let private sleepMs (ms: int64) : unit = System.Threading.Thread.Sleep(int ms)
#endif

type StopwatchOf =
    {
        /// the time of the runs that ended
        mutable elapsed: int64
        /// when the run that has not ended started
        mutable startedAt: int64
        mutable running: bool
    }

let frequency () : int64 = 1_000_000_000L
let isHighResolution () : bool = true
let getTimestamp () : int64 = monotonicNs ()

let create () : StopwatchOf =
    {
        elapsed = 0L
        startedAt = 0L
        running = false
    }

let start (w: StopwatchOf) : unit =
    if not w.running then
        w.startedAt <- monotonicNs ()
        w.running <- true

let startNew () : StopwatchOf =
    let w = create ()
    start w
    w

let stop (w: StopwatchOf) : unit =
    if w.running then
        w.elapsed <- w.elapsed + (monotonicNs () - w.startedAt)
        w.running <- false

let reset (w: StopwatchOf) : unit =
    w.elapsed <- 0L
    w.running <- false

let restart (w: StopwatchOf) : unit =
    w.elapsed <- 0L
    w.startedAt <- monotonicNs ()
    w.running <- true

let isRunning (w: StopwatchOf) : bool = w.running

/// The time it has run, in nanoseconds (its ticks)
let elapsedTicks (w: StopwatchOf) : int64 =
    if w.running then
        w.elapsed + (monotonicNs () - w.startedAt)
    else
        w.elapsed

let elapsed (w: StopwatchOf) : TimeSpanOf =
    { TimeSpanOf.ticks = elapsedTicks w / 100L }

let elapsedMilliseconds (w: StopwatchOf) : int64 = elapsedTicks w / 1_000_000L

/// `Stopwatch.GetElapsedTime(start[, end])`
let getElapsedTime (start: int64) (finish: int64) : TimeSpanOf =
    { TimeSpanOf.ticks = (finish - start) / 100L }

let getElapsedTimeSince (start: int64) : TimeSpanOf = getElapsedTime start (monotonicNs ())

/// `Thread.Sleep(ms)`
let sleep (ms: int) : unit =
    if ms < -1 then
        raise (
            System.ArgumentOutOfRangeException(
                "millisecondsTimeout",
                "Number must be either non-negative and less than or equal to Int32.MaxValue or -1."
            )
        )

    sleepMs (int64 ms)
