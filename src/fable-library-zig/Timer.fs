/// .NET's `System.Timers.Timer`, written in F# and compiled by the Zig target itself (see
/// List.fs). Its ticks are timers of the async scheduler's real clock (see Async.fs): they run
/// while a computation waits (`Async.Sleep`, `Async.RunSynchronously`), each raising `Elapsed`,
/// again after `Interval` while it is enabled and `AutoReset`.
module Fable.Library.Zig.Timer

open Fable.Library.Zig.Event

/// .NET's `ElapsedEventArgs`: when the tick was raised
type ElapsedEventArgsOf = { signalTime: Fable.Library.Zig.DateTime.DateTimeOf }

type TimerOf =
    {
        mutable interval: float
        mutable autoReset: bool
        mutable enabled: bool
        elapsed: DelegateEventOf<ElapsedEventArgsOf>
        /// (a tick scheduled before the timer was last stopped or restarted is ignored)
        mutable generation: int
    }

/// `new Timer()` (an interval of 100 milliseconds) and `new Timer(interval)`
let create (interval: float) : TimerOf =
    if interval <= 0.0 || System.Double.IsNaN interval then
        raise (System.ArgumentException("Invalid value '" + string interval + "' for parameter 'interval'."))

    {
        interval = interval
        autoReset = true
        enabled = false
        elapsed = createDelegate<ElapsedEventArgsOf>()
        generation = 0
    }

let rec private arm (t: TimerOf) : unit =
    let generation = t.generation

    Fable.Library.Zig.Async.scheduleAfter
        (int (System.Math.Ceiling t.interval))
        (fun () ->
            if t.enabled && t.generation = generation then
                if not t.autoReset then
                    t.enabled <- false

                triggerDelegate t.elapsed (box t) { signalTime = Fable.Library.Zig.DateTime.now () }

                if t.enabled && t.autoReset && t.generation = generation then
                    arm t
        )

/// `t.Enabled <- value`, `t.Start()` and `t.Stop()`
let setEnabled (t: TimerOf) (value: bool) : unit =
    t.generation <- t.generation + 1
    t.enabled <- value

    if value then
        arm t

let start (t: TimerOf) : unit = setEnabled t true
let stop (t: TimerOf) : unit = setEnabled t false

/// `t.Interval <- ms`: a timer that is running starts its interval again
let setInterval (t: TimerOf) (interval: float) : unit =
    if interval <= 0.0 || System.Double.IsNaN interval then
        raise (System.ArgumentException("Invalid value '" + string interval + "' for parameter 'value'."))

    t.interval <- interval

    if t.enabled then
        setEnabled t true

let setAutoReset (t: TimerOf) (value: bool) : unit = t.autoReset <- value

/// `t.Elapsed`
let elapsed (t: TimerOf) = publishDelegate t.elapsed
