/// F#'s `async`, written in F# and compiled by the Zig target itself (see List.fs). An async
/// computation is a function that is given what to do with its result, with an exception and
/// with a cancellation, and the token that may cancel it: continuations. There is one thread:
/// `Async.Sleep` is a timer of the real clock, run when it is due (the thread sleeps until then
/// when nothing else is ready), `Async.Parallel` interleaves the computations at their waits, and
/// a cancellation is seen where .NET looks for it, at the next bind or step of a loop. What a
/// computation gives, raises and the order of its effects are .NET's.
module Fable.Library.Zig.Async

open Fable.Library.Zig.Seq

/// .NET's `CancellationTokenSource`: whether it has been cancelled, and what to call then (in
/// the reverse order of registering, as .NET does; a removed registration is `None`)
type CancellationSource =
    {
        mutable cancelled: bool
        mutable handlers: ResizeArray<(unit -> unit) option>
        mutable disposed: bool
        /// false for `CancellationToken.None`'s, which nothing can cancel
        canCancel: bool
    }

/// .NET's `CancellationToken`: the source it reads
type CancellationTokenOf = { source: CancellationSource }

/// whether a computation has handed over to one of its continuations (see `start`)
type HandOver = { mutable handedOver: bool }

type Cont<'T> =
    {
        ok: 'T -> unit
        fail: exn -> unit
        cancel: exn -> unit
        token: CancellationTokenOf
        /// set when these continuations already note their hand-over
        handOver: HandOver option
    }

type AsyncOf<'T> = { fable_async: Cont<'T> -> unit }

// ---- cancellation ----

let newSource () : CancellationSource =
    {
        cancelled = false
        handlers = ResizeArray()
        disposed = false
        canCancel = true
    }

let private canceled () : exn =
    System.OperationCanceledException "The operation was canceled." :> exn

/// `CancellationToken.None`: a token that is never cancelled
let tokenNone () : CancellationTokenOf =
    {
        source =
            {
                cancelled = false
                handlers = ResizeArray()
                disposed = false
                canCancel = false
            }
    }

/// `new CancellationTokenSource()`
let sourceCreate () : CancellationSource = newSource ()

/// `cts.Cancel()`: the handlers run, last registered first; what they raise is raised again
/// together, as an AggregateException of them (its InnerException is the first raised)
let sourceCancel (s: CancellationSource) : unit =
    if not s.cancelled then
        s.cancelled <- true
        let errors = ResizeArray<exn>()

        for i in s.handlers.Count - 1 .. -1 .. 0 do
            match s.handlers.[i] with
            | Some f ->
                s.handlers.[i] <- None

                try
                    f ()
                with e ->
                    errors.Add e
            | None -> ()

        if errors.Count > 0 then
            raise (System.AggregateException("One or more errors occurred.", errors.ToArray()))

// ---- time: what waits is a timer of the real clock, run in the order of its time when the
// computation that started it is waited for; the thread sleeps until the earliest is due ----

type Timer =
    {
        due: int64
        order: int
        action: unit -> unit
        mutable live: bool
    }

#if FABLE_COMPILER
[<Fable.Core.Emit("fable_rt.time.sleepMilliseconds($0)")>]
let private sleepMilliseconds (_ms: int64) : unit = Fable.Core.Util.nativeOnly
#else
let private sleepMilliseconds (ms: int64) : unit = System.Threading.Thread.Sleep(int ms)
#endif

/// The real clock, in milliseconds
let private nowMs () : int64 =
    Fable.Library.Zig.DateTime.nowUtcTicks () / 10_000L

/// What one thread's scheduler keeps: its timers, and its trampoline (see `bounce`). Each thread
/// that runs async computations has its own (the runtime keeps it per thread)
type private Sched =
    {
        mutable timerOrder: int
        timers: ResizeArray<Timer>
        mutable depth: int
        pending: ResizeArray<unit -> unit>
        /// how many `drive`s are running (the outermost lets the scheduler go when it is idle)
        mutable drives: int
        /// (asked before a due timer runs: `Async.Parallel` on threads cancels a computation of
        /// its own thread there when another one failed)
        mutable poll: (unit -> unit) option
    }

#if FABLE_COMPILER
[<Fable.Core.Emit("fable_rt.asyncState()")>]
let private stateGet () : obj = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.asyncStateSet($0)")>]
let private stateSet (_s: obj) : unit = Fable.Core.Util.nativeOnly
#else
let mutable private state: obj = null
let private stateGet () : obj = state
let private stateSet (s: obj) : unit = state <- s
#endif

/// This thread's scheduler, made when it first needs one
let private sched () : Sched =
    let s = stateGet ()

    if isNull s then
        let made =
            {
                timerOrder = 0
                timers = ResizeArray()
                depth = 0
                pending = ResizeArray()
                drives = 0
                poll = None
            }

        stateSet (box made)
        made
    else
        unbox<Sched> s

/// `action` at `ms` from now
let private schedule (ms: int) (action: unit -> unit) : Timer =
    let st = sched ()

    let t =
        {
            due =
                nowMs ()
                + (if ms > 0 then
                       int64 ms
                   else
                       0L)
            order = st.timerOrder
            action = action
            live = true
        }

    st.timerOrder <- st.timerOrder + 1
    st.timers.Add t
    t

/// `action` at `ms` from now, on the scheduler's clock (System.Timers.Timer's ticks, see Timer.fs)
let scheduleAfter (ms: int) (action: unit -> unit) : unit = schedule ms action |> ignore

/// Run the earliest timer (once it is due); false when there is none
let private runNextTimer () : bool =
    let timers = (sched ()).timers
    let mutable best = -1

    for i in 0 .. timers.Count - 1 do
        let t = timers.[i]

        if
            best < 0
            || t.due < timers.[best].due
            || (t.due = timers.[best].due && t.order < timers.[best].order)
        then
            best <- i

    if best < 0 then
        false
    else
        let t = timers.[best]
        timers.RemoveAt best

        // (a timer that was cancelled is not waited for)
        if t.live then
            let wait = t.due - nowMs ()

            if wait > 0L then
                sleepMilliseconds wait

            match (sched ()).poll with
            | Some poll -> poll ()
            | None -> ()

            if t.live then
                t.live <- false
                t.action ()

        true

/// `cts.CancelAfter(ms)`: a timer that cancels it
let sourceCancelAfter (s: CancellationSource) (millisecondsDelay: int) : unit =
    if millisecondsDelay <= 0 then
        sourceCancel s
    else
        schedule millisecondsDelay (fun () -> sourceCancel s) |> ignore

/// `new CancellationTokenSource(ms)`
let sourceCreateWithDelay (millisecondsDelay: int) : CancellationSource =
    let s = newSource ()
    sourceCancelAfter s millisecondsDelay
    s

let sourceDispose (s: CancellationSource) : unit = s.disposed <- true

/// a source as the `IDisposable` it is (`use cts = new CancellationTokenSource()`)
let sourceAsDisposable (s: CancellationSource) : System.IDisposable =
    { new System.IDisposable with
        member _.Dispose() = sourceDispose s
    }

let sourceToken (s: CancellationSource) : CancellationTokenOf = { source = s }
let sourceIsCancellationRequested (s: CancellationSource) : bool = s.cancelled

let tokenIsCancellationRequested (t: CancellationTokenOf) : bool = t.source.cancelled

let tokenThrowIfCancellationRequested (t: CancellationTokenOf) : unit =
    if t.source.cancelled then
        raise (canceled ())

/// `token.Register(f)`: `f` runs when the token is cancelled (at once if it is already); the
/// registration's `Dispose` removes it
let tokenRegister (t: CancellationTokenOf) (f: unit -> unit) : System.IDisposable =
    let s = t.source

    if s.cancelled then
        f ()

        { new System.IDisposable with
            member _.Dispose() = ()
        }
    else
        let index = s.handlers.Count
        s.handlers.Add(Some f)

        { new System.IDisposable with
            member _.Dispose() =
                if index < s.handlers.Count then
                    s.handlers.[index] <- None
        }

/// `token.Register(f, state)`: `f state` when the token is cancelled
let tokenRegisterWith (t: CancellationTokenOf) (f: obj -> unit) (state: obj) : System.IDisposable =
    tokenRegister t (fun () -> f state)

// ---- running computations ----

/// The trampoline: a continuation called deeper than this many nested binds is run after the
/// stack has unwound to the entry point that started the computation (as .NET's trampoline
/// does), so that a long chain of binds runs in bounded stack. The order of effects is kept.
let private maxDepth = 200

let private bounce (f: unit -> unit) : unit =
    let st = sched ()

    if st.depth >= maxDepth then
        st.pending.Add f
    else
        st.depth <- st.depth + 1

        try
            f ()
        finally
            st.depth <- st.depth - 1

/// Run `f` from an entry point, then what it left for the trampoline, then the timers in the
/// order of their time until `finished` (what the entry point waits for) or none is left
let private drive (finished: unit -> bool) (f: unit -> unit) : unit =
    let st = sched ()
    let pending = st.pending
    let saved = st.depth
    let mark = pending.Count
    st.depth <- 0
    st.drives <- st.drives + 1

    let drain () =
        while pending.Count > mark do
            let next = pending.[mark]
            pending.RemoveAt mark
            st.depth <- 0
            next ()

    try
        f ()
        drain ()

        while not (finished ()) && runNextTimer () do
            st.depth <- 0
            drain ()
    finally
        st.depth <- saved
        st.drives <- st.drives - 1

        // (an idle thread keeps no scheduler: made again when it runs async code again)
        if st.drives = 0 && st.timers.Count = 0 && st.pending.Count = 0 then
            stateSet null

/// The time the earliest timer that is still live is due (Int64.MaxValue when there is none)
let private earliestDue () : int64 =
    let mutable due = System.Int64.MaxValue

    for t in (sched ()).timers do
        if t.live && t.due < due then
            due <- t.due

    due

/// `Thread.Sleep(ms)`: the time passes, and the timers due within it run meanwhile (they stand
/// for the other threads of .NET, which go on while this one sleeps)
let threadSleep (ms: int) : unit =
    if ms < -1 then
        raise (
            System.ArgumentOutOfRangeException(
                "millisecondsTimeout",
                "Number must be either non-negative and less than or equal to Int32.MaxValue or -1."
            )
        )

    let deadline = nowMs () + int64 ms
    drive (fun () -> earliestDue () > deadline) ignore
    let rest = deadline - nowMs ()

    if rest > 0L then
        sleepMilliseconds rest

/// What was started and is still waiting, run on (the timers due within ten seconds): what a
/// test does at its end, so that work it started (`Async.Start` and the others) finishes within
/// it rather than in a later one
let finishPending () : unit =
    let horizon = nowMs () + 10_000L
    drive (fun () -> earliestDue () > horizon) ignore

/// Run the timers (and what they leave) until `finished` or none is left; whether it finished
/// (a task waited for, as `.Result` waits: what would complete it runs meanwhile)
let waitUntil (finished: unit -> bool) : bool =
    drive finished ignore
    finished ()

let private make (run: Cont<'T> -> unit) : AsyncOf<'T> = { fable_async = run }

/// Run a computation with these continuations; what it raises before it gets to one of them
/// goes to `fail`. What is raised after it has handed over to a continuation was raised
/// downstream (the continuations run inside this call): that goes on up, as on .NET, rather
/// than to this computation's handlers.
/// (continuations passed on unchanged, as `return!` passes them, are noted once, not once per
/// level: a deep chain of them stays one call deep)
let private start (computation: AsyncOf<'T>) (k: Cont<'T>) : unit =
    let note, k' =
        match k.handOver with
        | Some note -> note, k
        | None ->
            let note = { handedOver = false }

            note,
            {
                ok =
                    fun x ->
                        note.handedOver <- true
                        k.ok x
                fail =
                    fun e ->
                        note.handedOver <- true
                        k.fail e
                cancel =
                    fun e ->
                        note.handedOver <- true
                        k.cancel e
                token = k.token
                handOver = Some note
            }

    let before = note.handedOver
    note.handedOver <- false

    try
        computation.fable_async k'
        note.handedOver <- note.handedOver || before
    with e ->
        let handedOver = note.handedOver
        note.handedOver <- handedOver || before

        if handedOver then
            reraise ()
        else
            k.fail e

/// `start` of a computation still to be made by `make`: what making it raises goes to `fail`
/// too (a binder that raises before it gives its computation, as a bind resumed by a timer
/// calls it with no other handler around)
let private startMade (make: unit -> AsyncOf<'T>) (k: Cont<'T>) : unit =
    let made =
        try
            Ok(make ())
        with e ->
            Error e

    match made with
    | Ok computation -> start computation k
    | Error e -> k.fail e

/// The same continuations for a result of another type
let private withOk (k: Cont<'U>) (ok: 'T -> unit) : Cont<'T> =
    {
        ok = ok
        fail = k.fail
        cancel = k.cancel
        token = k.token
        handOver = None
    }

let private isCancelled (k: Cont<'T>) = k.token.source.cancelled

// ---- the builder: what `async { }` is made of ----

let builderReturn<'T> (value: 'T) : AsyncOf<'T> = make (fun k -> k.ok value)

let builderReturnFrom<'T> (computation: AsyncOf<'T>) : AsyncOf<'T> = computation

let builderZero () : AsyncOf<unit> = make (fun k -> k.ok ())

/// (a cancellation is seen here, before the body runs: a computation started with a cancelled
/// token does nothing but its finalizers)
let builderDelay<'T> (generator: unit -> AsyncOf<'T>) : AsyncOf<'T> =
    make (fun k ->
        if isCancelled k then
            k.cancel (canceled ())
        else
            bounce (fun () -> startMade generator k)
    )

/// (a cancellation is seen here, before the computation runs)
let builderBind<'T, 'U> (computation: AsyncOf<'T>) (binder: 'T -> AsyncOf<'U>) : AsyncOf<'U> =
    make (fun k ->
        if isCancelled k then
            k.cancel (canceled ())
        else
            start computation (withOk k (fun x -> bounce (fun () -> startMade (fun () -> binder x) k)))
    )

let builderCombine<'T> (computation1: AsyncOf<unit>) (computation2: AsyncOf<'T>) : AsyncOf<'T> =
    builderBind computation1 (fun () -> computation2)

let builderTryWith<'T> (computation: AsyncOf<'T>) (catchHandler: exn -> AsyncOf<'T>) : AsyncOf<'T> =
    make (fun k ->
        start
            computation
            {
                ok = k.ok
                fail = fun e -> bounce (fun () -> startMade (fun () -> catchHandler e) k)
                cancel = k.cancel
                token = k.token
                handOver = None
            }
    )

/// (the compensation runs on each way out: a result, an exception, a cancellation; if it raises,
/// that exception goes on instead, except on a cancellation, which goes on. Started with a
/// cancelled token, it runs its compensation and cancels without starting the body.)
let builderTryFinally<'T> (computation: AsyncOf<'T>) (compensation: unit -> unit) : AsyncOf<'T> =
    make (fun k ->
        let finish (cancelling: bool) (next: unit -> unit) =
            let compensated =
                try
                    compensation ()
                    None
                with e ->
                    Some e

            match compensated with
            | Some e when not cancelling -> bounce (fun () -> k.fail e)
            | _ -> bounce next

        if isCancelled k then
            finish true (fun () -> k.cancel (canceled ()))
        else
            start
                computation
                {
                    ok = fun x -> finish false (fun () -> k.ok x)
                    fail = fun e -> finish false (fun () -> k.fail e)
                    cancel = fun e -> finish true (fun () -> k.cancel e)
                    token = k.token
                    handOver = None
                }
    )

/// `use x = resource` in `async { }`: the body, then `dispose` of the resource on each way out
let builderUsing<'T, 'U> (resource: 'T) (dispose: System.IDisposable) (binder: 'T -> AsyncOf<'U>) : AsyncOf<'U> =
    builderTryFinally (builderDelay (fun () -> binder resource)) (fun () -> dispose.Dispose())

let builderWhile (guard: unit -> bool) (computation: AsyncOf<unit>) : AsyncOf<unit> =
    let rec loop () : AsyncOf<unit> =
        make (fun k ->
            if isCancelled k then
                k.cancel (canceled ())
            elif guard () then
                start computation (withOk k (fun () -> bounce (fun () -> start (loop ()) k)))
            else
                k.ok ()
        )

    loop ()

let builderFor<'T> (sequence: SeqOf<'T>) (body: 'T -> AsyncOf<unit>) : AsyncOf<unit> =
    let rec loop (rest: 'T list) : AsyncOf<unit> =
        make (fun k ->
            if isCancelled k then
                k.cancel (canceled ())
            else
                match rest with
                | x :: tail ->
                    startMade (fun () -> body x) (withOk k (fun () -> bounce (fun () -> start (loop tail) k)))
                | [] -> k.ok ()
        )

    make (fun k -> start (loop (Seq.toList sequence)) k)

// ---- the Async module ----

/// Run a computation to its end here: what it gave or raised, and whether it was cancelled
let private runHere<'T> (computation: AsyncOf<'T>) (token: CancellationTokenOf) : Result<'T, exn> option * bool =
    let mutable result: Result<'T, exn> option = None
    let mutable cancelled = false

    drive
        (fun () -> result.IsSome)
        (fun () ->
            start
                computation
                {
                    ok = (fun x -> result <- Some(Ok x))
                    fail = (fun e -> result <- Some(Error e))
                    cancel =
                        (fun e ->
                            result <- Some(Error e)
                            cancelled <- true
                        )
                    token = token
                    handOver = None
                }
        )

    result, cancelled

let private runSynchronouslyWith<'T> (computation: AsyncOf<'T>) (token: CancellationTokenOf) : 'T =
    match runHere computation token with
    | Some(Ok x), _ -> x
    | Some(Error e), _ -> raise e
    | None, _ -> failwith "The computation did not finish: Async.RunSynchronously needs one that does, here"

/// `Async.RunSynchronously`: the result, or the exception (or the cancellation) raised again.
let runSynchronously<'T> (computation: AsyncOf<'T>) : 'T =
    runSynchronouslyWith computation (tokenNone ())

/// `Async.RunSynchronously(c, timeout, token)` (the token is F#'s optional argument)
let runSynchronouslyToken<'T> (computation: AsyncOf<'T>) (token: CancellationTokenOf option) : 'T =
    runSynchronouslyWith computation (defaultArg token (tokenNone ()))

/// `Async.StartImmediate` and `Async.Start` (with a token): an exception is raised again; a
/// cancellation ends it quietly, as on .NET
/// (as .NET's `StartImmediate` returns at the computation's first wait, the timers are left
/// for what waits: RunSynchronously, a task's result, Thread.Sleep)
let private startImmediateWith (computation: AsyncOf<unit>) (token: CancellationTokenOf) : unit =
    let mutable finished = false

    drive
        (fun () -> true)
        (fun () ->
            start
                computation
                {
                    ok = (fun () -> finished <- true)
                    fail =
                        (fun e ->
                            finished <- true
                            raise e
                        )
                    cancel = (fun _ -> finished <- true)
                    token = token
                    handOver = None
                }
        )

let startImmediate (computation: AsyncOf<unit>) : unit =
    startImmediateWith computation (tokenNone ())

let startImmediateToken (computation: AsyncOf<unit>) (token: CancellationTokenOf option) : unit =
    startImmediateWith computation (defaultArg token (tokenNone ()))

let startAsync (computation: AsyncOf<unit>) : unit = startImmediate computation

/// `Async.StartWithContinuations(c, ok, fail, cancel[, token])`
let startWithContinuationsToken<'T>
    (computation: AsyncOf<'T>)
    (ok: 'T -> unit)
    (fail: exn -> unit)
    (cancel: exn -> unit)
    (token: CancellationTokenOf option)
    : unit
    =
    let token = defaultArg token (tokenNone ())
    let mutable finished = false

    // (it runs until it waits: what is left goes on when something waits for the timers)
    drive
        (fun () -> true)
        (fun () ->
            start
                computation
                {
                    ok =
                        fun x ->
                            finished <- true
                            ok x
                    fail =
                        fun e ->
                            finished <- true
                            fail e
                    cancel =
                        fun e ->
                            finished <- true
                            cancel e
                    token = token
                    handOver = None
                }
        )

let startWithContinuations<'T>
    (computation: AsyncOf<'T>)
    (ok: 'T -> unit)
    (fail: exn -> unit)
    (cancel: exn -> unit)
    : unit
    =
    startWithContinuationsToken computation ok fail cancel None

/// `Async.FromContinuations(fun (ok, fail, cancel) -> ...)`
/// (a second completion is refused, as .NET refuses it)
let fromContinuations<'T> (f: ('T -> unit) * (exn -> unit) * (exn -> unit) -> unit) : AsyncOf<'T> =
    make (fun k ->
        let mutable completed = false

        let once (g: 'U -> unit) (x: 'U) =
            if completed then
                raise (
                    System.InvalidOperationException
                        "The continuation of Async.FromContinuations was called more than once."
                )

            completed <- true
            g x

        f (once k.ok, once k.fail, once k.cancel)
    )

/// `Async.CancellationToken`: the token of the computation that runs it
let cancellationToken () : AsyncOf<CancellationTokenOf> = make (fun k -> k.ok k.token)

/// `Async.TryCancelled(c, compensation)`: on a cancellation, the compensation first (also when
/// the token was cancelled before it started)
let tryCancelled<'T> (computation: AsyncOf<'T>) (compensation: exn -> unit) : AsyncOf<'T> =
    make (fun k ->
        start
            computation
            {
                ok = k.ok
                fail = k.fail
                // (what the compensation raises is ignored, as FSharp.Core does: the
                // cancellation goes on)
                cancel =
                    fun e ->
                        try
                            compensation e
                        with _ ->
                            ()

                        bounce (fun () -> k.cancel e)
                token = k.token
                handOver = None
            }
    )

/// `Async.StartChild(c[, timeout])`: the child starts now and runs alongside (until it waits,
/// then on its timers); awaiting it gives what it ended with, or a TimeoutException when the
/// timeout came first
let startChildWith<'T> (computation: AsyncOf<'T>) (timeout: int option) : AsyncOf<AsyncOf<'T>> =
    make (fun k ->
        let mutable outcome: (Result<'T, exn> * bool) option = None
        let waiters = ResizeArray<Cont<'T>>()
        // (the child's own source, cancelled with the caller's token or when a timeout expires)
        let inner = sourceCreate ()
        let link = tokenRegister k.token (fun () -> sourceCancel inner)

        let deliver (o: Result<'T, exn> * bool) (k2: Cont<'T>) =
            match o with
            | Ok x, _ -> k2.ok x
            | Error e, true -> k2.cancel e
            | Error e, false -> k2.fail e

        let complete (o: Result<'T, exn> * bool) =
            if outcome.IsNone then
                outcome <- Some o
                link.Dispose()
                let ws = waiters.ToArray()
                waiters.Clear()

                for w in ws do
                    deliver o w

        start
            computation
            {
                ok = fun x -> complete (Ok x, false)
                fail = fun e -> complete (Error e, false)
                cancel = fun e -> complete (Error e, true)
                token = sourceToken inner
                handOver = None
            }

        let timedOut () =
            System.TimeoutException "The operation has timed out." :> exn

        // (the timeout runs while the result is awaited: when it expires the awaiter gets a
        // TimeoutException and the child is cancelled; a timeout of 0 leaves it running)
        k.ok (
            make (fun k2 ->
                match outcome, timeout with
                | Some o, _ -> deliver o k2
                | None, Some 0 -> k2.fail (timedOut ())
                | None, Some ms when ms > 0 ->
                    let mutable settled = false

                    let once (f: unit -> unit) =
                        if not settled then
                            settled <- true
                            f ()

                    waiters.Add
                        {
                            ok = fun x -> once (fun () -> k2.ok x)
                            fail = fun e -> once (fun () -> k2.fail e)
                            cancel = fun e -> once (fun () -> k2.cancel e)
                            token = k2.token
                            handOver = None
                        }

                    schedule
                        ms
                        (fun () ->
                            once (fun () ->
                                let failure =
                                    try
                                        sourceCancel inner
                                        timedOut ()
                                    with e ->
                                        e

                                k2.fail failure
                            )
                        )
                    |> ignore
                | None, _ -> waiters.Add k2
            )
        )
    )

let startChild<'T> (computation: AsyncOf<'T>) : AsyncOf<AsyncOf<'T>> = startChildWith computation None

/// `Async.Sleep(ms)`: a timer on the virtual clock; a cancellation of its token while it
/// waits ends it at once
let sleep (millisecondsDueTime: int) : AsyncOf<unit> =
    make (fun k ->
        if isCancelled k then
            k.cancel (canceled ())
        else
            let mutable registration: System.IDisposable option = None

            let timer =
                schedule
                    millisecondsDueTime
                    (fun () ->
                        match registration with
                        | Some r -> r.Dispose()
                        | None -> ()

                        k.ok ()
                    )

            registration <-
                Some(
                    tokenRegister
                        k.token
                        (fun () ->
                            // (the cancellation goes on at the scheduler's next turn, as .NET
                            // queues it: the token's other callbacks run first)
                            if timer.live then
                                timer.live <- false
                                schedule 0 (fun () -> k.cancel (canceled ())) |> ignore
                        )
                )
    )

let ignoreAsync<'T> (computation: AsyncOf<'T>) : AsyncOf<unit> =
    builderBind computation (fun _ -> builderZero ())

let catch<'T> (computation: AsyncOf<'T>) : AsyncOf<Choice<'T, exn>> =
    make (fun k ->
        start
            computation
            {
                ok = (fun x -> k.ok (Choice1Of2 x))
                fail = (fun e -> k.ok (Choice2Of2 e))
                cancel = k.cancel
                token = k.token
                handOver = None
            }
    )

/// `Async.Parallel` and `Async.Sequential`: one after the other, the results in order.
/// `Async.Sequential`: one after the other, the results in order
let sequential<'T> (computations: SeqOf<AsyncOf<'T>>) : AsyncOf<'T[]> =
    let rec loop (rest: AsyncOf<'T> list) (acc: 'T list) : AsyncOf<'T[]> =
        make (fun k ->
            match rest with
            | c :: tail -> start c (withOk k (fun x -> start (loop tail (x :: acc)) k))
            | [] -> k.ok (Array.ofList (List.rev acc))
        )

    make (fun k -> start (loop (Seq.toList computations) []) k)

#if FABLE_COMPILER
[<Fable.Core.Emit("fable_rt.tryMarkShared($0)")>]
let private tryShare (_x: 'a) : bool = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("(comptime !fable_rt.holdsCyclic(@TypeOf($0)))")>]
let private holdsNoCycles (_x: 'a) : bool = Fable.Core.Util.nativeOnly

/// (a message the receiver alone holds now: its own again, see fable_rt.adoptShared)
[<Fable.Core.Emit("fable_rt.adoptShared($0)")>]
let private adoptShared (_x: 'a) : unit = Fable.Core.Util.nativeOnly
#else
let private adoptShared (_x: 'a) : unit = ()
let private tryShare (_x: 'a) : bool = false
let private holdsNoCycles (_x: 'a) : bool = false
#endif

/// `Async.Parallel`: the results in order; the first failure is the result, as on .NET. Where
/// the computations can be shared between threads (nothing they reach is followed by the cycle
/// collector) and their results can come back (a type that holds no such cells), each runs on
/// a thread of its own, on its own scheduler, and this one waits for all of them; a failure
/// there does not stop the others early (their results are left). Otherwise they run here:
/// all start (each runs until it waits, then they go on as their timers come due), and the
/// first failure cancels the others.
let private parallelWith<'T> (computations: SeqOf<AsyncOf<'T>>) (maxDegree: int option) : AsyncOf<'T[]> =
    make (fun k ->
        let cs = Array.ofList (Seq.toList computations)
        let n = cs.Length

        if n = 0 then
            k.ok [||]
        else
            let results: Result<'T, exn> option[] = Array.create n None
            // (which failed first, in time)
            let firstFail: int[] = [| -1 |]

            // (only the type of the results decides: an exception is checked when it comes back)
            let resultType: 'T[] = [||]

            // (on threads only when nothing can cancel the computations: a cancellation of the
            // caller's token reaches them where they run here, one thread)
            if
                n > 1
                && not k.token.source.canCancel
                && holdsNoCycles resultType
                && tryShare cs
                && tryShare results
                && tryShare firstFail
            then
                // (at most eight threads, as Parallel.For: each takes the next computation that
                // no thread has taken until none is left)
                let next: int[] = [| 0 |]

                if not (tryShare next) then
                    failwith "unreachable"

                let take () =
                    lock
                        next
                        (fun () ->
                            let i = next.[0]
                            next.[0] <- i + 1
                            i
                        )

                // (a computation of another thread failed: the others are cancelled where they
                // run, at their next timer)
                let failed: bool[] = [| false |]

                if not (tryShare failed) then
                    failwith "unreachable"

                let hasFailed () = lock failed (fun () -> failed.[0])

                let threads =
                    Array.init
                        (System.Math.Min(System.Math.Min(n, 8), defaultArg maxDegree 8))
                        (fun _ ->
                            System.Threading.Thread(fun () ->
                                let mutable i = take ()

                                while i < n do
                                    let local = sourceCreate ()
                                    let st = sched ()

                                    st.poll <-
                                        Some(fun () ->
                                            if not local.cancelled && hasFailed () then
                                                try
                                                    sourceCancel local
                                                with _ ->
                                                    ()
                                        )

                                    let r, _ =
                                        if hasFailed () then
                                            Some(Error(canceled ())), true
                                        else
                                            runHere cs.[i] (sourceToken local)

                                    // (an exception that reaches what cannot be shared comes back as
                                    // a new one with its message)
                                    let r =
                                        match r with
                                        | Some(Error e) when not (tryShare e) ->
                                            Some(Error(System.Exception(e.Message)))
                                        | _ -> r

                                    match r with
                                    | Some(Error e) when not (e :? System.OperationCanceledException) ->
                                        lock
                                            firstFail
                                            (fun () ->
                                                if firstFail.[0] < 0 then
                                                    firstFail.[0] <- i
                                            )

                                        lock failed (fun () -> failed.[0] <- true)
                                    | _ -> ()

                                    results.[i] <- r
                                    i <- take ()
                            )
                        )

                for t in threads do
                    t.Start()

                for t in threads do
                    t.Join()

                if isCancelled k then
                    k.cancel (canceled ())
                elif firstFail.[0] >= 0 then
                    match results.[firstFail.[0]] with
                    | Some(Error e) -> k.fail e
                    | _ -> k.fail (System.InvalidOperationException "Async.Parallel" :> exn)
                elif results |> Array.forall (fun r -> r.IsSome) then
                    k.ok (
                        results
                        |> Array.map (fun r ->
                            match r with
                            | Some(Ok x) -> x
                            | _ -> failwith "unreachable"
                        )
                    )
                else
                    k.fail (
                        System.InvalidOperationException "A computation of Async.Parallel did not finish on its thread"
                        :> exn
                    )
            else
                let results: 'T option[] = Array.create n None
                let mutable remaining = n
                let mutable finished = false
                // (the computations' own source: cancelled with the caller's token, or by a failure)
                let inner = sourceCreate ()
                let link = tokenRegister k.token (fun () -> sourceCancel inner)

                let finish (f: unit -> unit) =
                    if not finished then
                        finished <- true
                        link.Dispose()
                        f ()

                // (with a degree: that many at once, the next started when one ends)
                let degree = defaultArg maxDegree n
                let mutable nextToStart = 0

                let rec startNext () =
                    if nextToStart < n && not finished then
                        let i = nextToStart
                        nextToStart <- nextToStart + 1
                        startOne i

                and startOne (i: int) =
                    start
                        cs.[i]
                        {
                            ok =
                                fun x ->
                                    results.[i] <- Some x
                                    remaining <- remaining - 1

                                    if remaining = 0 then
                                        finish (fun () -> k.ok (results |> Array.map Option.get))
                                    else
                                        startNext ()
                            fail =
                                fun e ->
                                    finish (fun () ->
                                        sourceCancel inner
                                        k.fail e
                                    )
                            cancel = fun e -> finish (fun () -> k.cancel e)
                            token = sourceToken inner
                            handOver = None
                        }

                for _ in 1 .. System.Math.Min(degree, n) do
                    startNext ()
    )

let parallelAll<'T> (computations: SeqOf<AsyncOf<'T>>) : AsyncOf<'T[]> = parallelWith computations None


/// `Async.OnCancel(interruption)`: the interruption runs if the computation's token is cancelled
/// while what this gives is not disposed (what it raises is ignored, as FSharp.Core does)
let onCancel (interruption: unit -> unit) : AsyncOf<System.IDisposable> =
    make (fun k ->
        let registration =
            tokenRegister
                k.token
                (fun () ->
                    try
                        interruption ()
                    with _ ->
                        ()
                )

        k.ok registration
    )

/// `Async.Choice(computations)`: they all start; the first that gives `Some` wins and the others
/// are cancelled; `None` when every one gives `None`; the first exception, the others cancelled
let choice<'T> (computations: SeqOf<AsyncOf<'T option>>) : AsyncOf<'T option> =
    make (fun k ->
        let cs = Array.ofList (Seq.toList computations)
        let n = cs.Length

        if n = 0 then
            k.ok None
        else
            let mutable remaining = n
            let mutable finished = false
            let inner = sourceCreate ()
            let link = tokenRegister k.token (fun () -> sourceCancel inner)

            let finish (f: unit -> unit) =
                if not finished then
                    finished <- true
                    link.Dispose()
                    f ()

            let cancelOthers () =
                try
                    sourceCancel inner
                with _ ->
                    ()

            for c in cs do
                start
                    c
                    {
                        ok =
                            fun r ->
                                match r with
                                | Some _ ->
                                    finish (fun () ->
                                        cancelOthers ()
                                        k.ok r
                                    )
                                | None ->
                                    remaining <- remaining - 1

                                    if remaining = 0 then
                                        finish (fun () -> k.ok None)
                        fail =
                            fun e ->
                                finish (fun () ->
                                    cancelOthers ()
                                    k.fail e
                                )
                        cancel =
                            fun e ->
                                remaining <- remaining - 1

                                if remaining = 0 then
                                    finish (fun () -> k.cancel e)
                        token = sourceToken inner
                        handOver = None
                    }
    )

/// `Async.Parallel(computations, maxDegreeOfParallelism)`: the degree checked where the call is
/// made, as .NET does (the computations then run as `Async.Parallel` runs them)
let parallelAllMax<'T> (computations: SeqOf<AsyncOf<'T>>) (maxDegree: int option) : AsyncOf<'T[]> =
    match maxDegree with
    | Some d when d < 1 ->
        raise (
            System.ArgumentException(
                "maxDegreeOfParallelism must be positive, was " + string d,
                "maxDegreeOfParallelism"
            )
        )
    | _ -> ()

    parallelWith computations maxDegree

let returnValue<'T> (value: 'T) : AsyncOf<'T> = builderReturn value

// ---- MailboxProcessor ----

/// `AsyncReplyChannel<'R>`: what replying does
type ReplyChannelOf<'R> = { reply: 'R -> unit }

let replyChannelReply<'R> (c: ReplyChannelOf<'R>) (value: 'R) : unit = c.reply value

#if FABLE_COMPILER
[<Fable.Core.Emit("fable_rt.isShared($0)")>]
let private isCellShared (_x: 'a) : bool = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.shareStored($0)")>]
let private shareValue (_x: 'a) : unit = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.waitUntilSet(&($0).ready)")>]
let private waitReplyReady (_x: 'a) : unit = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.setAndWakeAll(&($0).ready)")>]
let private wakeReplyReady (_x: 'a) : unit = Fable.Core.Util.nativeOnly

/// (a message boxed as it is sent: see MessageQueue; isolated, it is not marked shared)
[<Fable.Core.Emit("$iso_send($0)")>]
let private sendBox (_x: 'a) : Fable.Core.Zig.Iso<'a> = Fable.Core.Util.nativeOnly

/// (a message boxed as it is, by the thread that holds it)
[<Fable.Core.Emit("$iso_hold($0)")>]
let private holdBox (_x: 'a) : Fable.Core.Zig.Iso<'a> = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("try fable_rt.isoUnpack($0)")>]
let private unbox' (_x: Fable.Core.Zig.Iso<'a>) : 'a = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.isoPeek($0)")>]
let private peekBox (_x: Fable.Core.Zig.Iso<'a>) : 'a = Fable.Core.Util.nativeOnly
#else
let private sendBox (x: 'a) : Fable.Core.Zig.Iso<'a> = Fable.Core.Zig.Iso<'a>(x)
let private holdBox (x: 'a) : Fable.Core.Zig.Iso<'a> = Fable.Core.Zig.Iso<'a>(x)
let private unbox' (x: Fable.Core.Zig.Iso<'a>) : 'a = x.Take()

let private peekBox (_x: Fable.Core.Zig.Iso<'a>) : 'a =
    failwith "the library's .NET build does not run"

let private isCellShared (_x: 'a) : bool = false
let private shareValue (_x: 'a) : unit = ()
let private waitReplyReady (_x: 'a) : unit = ()
let private wakeReplyReady (_x: 'a) : unit = ()
#endif

/// A mailbox's messages, in order: those of `items` from `head` on. Taking the first leaves None
/// in its place and moves `head`; the part before `head` goes once it is half of `items`. Taking
/// is O(1) amortised, where removing the first of a ResizeArray moves all the others. Each
/// message is in a box (fable_rt.Iso): one that crossed from another thread was boxed by its
/// poster before the mailbox's lock (`sendBox`), so the poster holds only the box afterwards and
/// its last references, given up after the lock, never touch the message's cells; an isolated
/// message is not marked shared at all (Pony's `iso` sent, Verona's region moved).
type MessageQueue<'Msg> =
    {
        items: ResizeArray<Fable.Core.Zig.Iso<'Msg> option>
        mutable head: int
    }

let private queueCount (q: MessageQueue<'Msg>) = q.items.Count - q.head

let private queueAddBox (q: MessageQueue<'Msg>) (box: Fable.Core.Zig.Iso<'Msg>) = q.items.Add(Some box)

let private queueAdd (q: MessageQueue<'Msg>) (msg: 'Msg) = queueAddBox q (holdBox msg)

/// The `i`th message (of those waiting), left in the queue
let private queueItem (q: MessageQueue<'Msg>) (i: int) : 'Msg =
    match q.items.[q.head + i] with
    | Some box -> peekBox box
    | None -> failwith "a message queue's slot is empty"

let private queueBox (q: MessageQueue<'Msg>) (i: int) : Fable.Core.Zig.Iso<'Msg> =
    match q.items.[q.head + i] with
    | Some box -> box
    | None -> failwith "a message queue's slot is empty"

let private queueCompact (q: MessageQueue<'Msg>) =
    if q.head > 0 && q.head * 2 >= q.items.Count then
        q.items.RemoveRange(0, q.head)
        q.head <- 0

/// The `i`th message, taken out
let private queueRemoveAt (q: MessageQueue<'Msg>) (i: int) : 'Msg =
    let box = queueBox q i

    if i = 0 then
        q.items.[q.head] <- None
        q.head <- q.head + 1
        queueCompact q
    else
        q.items.RemoveAt(q.head + i)

    unbox' box

/// A `MailboxProcessor<'Msg>`: its messages, the `Receive` that waits for one (if any), and its
/// body, which starts with `Start`
type MailboxOf<'Msg> =
    {
        body: MailboxOf<'Msg> -> AsyncOf<unit>
        queue: MessageQueue<'Msg>
        mutable waiting: ('Msg -> unit) option
        mutable started: bool
        mutable begun: bool
        mutable running: bool
        mutable turnToken: int
        token: CancellationTokenOf
        errorHandlers: ResizeArray<exn -> unit>
    }

let mailboxCreate<'Msg> (body: MailboxOf<'Msg> -> AsyncOf<unit>) (token: CancellationTokenOf option) : MailboxOf<'Msg> =
    {
        body = body
        queue =
            {
                items = ResizeArray()
                head = 0
            }
        waiting = None
        started = false
        begun = false
        running = false
        turnToken = 0
        token = defaultArg token (tokenNone ())
        errorHandlers = ResizeArray()
    }

let private beginMailboxBody<'Msg> (mb: MailboxOf<'Msg>) : unit =
    let finish () =
        if isCellShared mb then
            lock
                mb
                (fun () ->
                    mb.running <- false
                    mb.waiting <- None
                )

    start
        (mb.body mb)
        {
            ok = fun () -> finish ()
            fail =
                fun e ->
                    finish ()

                    let handlers =
                        if isCellShared mb then
                            lock mb (fun () -> mb.errorHandlers.ToArray())
                        else
                            mb.errorHandlers.ToArray()

                    for h in handlers do
                        h e
            cancel = fun _ -> finish ()
            token = mb.token
            handOver = None
        }

type private PostAction<'Msg> =
    | BeginBody of int
    | Resume of ('Msg -> unit) * int
    | Queued

let private runMailboxTurn<'Msg> (mb: MailboxOf<'Msg>) (turn: int) (action: unit -> unit) : unit =
    drive (fun () -> lock mb (fun () -> not mb.running || mb.turnToken <> turn)) action

/// `mb.Start()`: the body runs as the mailbox's own (from a timer, as .NET runs it on the thread
/// pool); what it raises goes to the Error event
let mailboxStart<'Msg> (mb: MailboxOf<'Msg>) : unit =
    let alreadyStarted =
        if isCellShared mb then
            lock
                mb
                (fun () ->
                    if mb.started then
                        true
                    else
                        mb.started <- true
                        false
                )
        else if mb.started then
            true
        else
            mb.started <- true
            false

    if alreadyStarted then
        raise (System.InvalidOperationException "The MailboxProcessor has already been started.")

    schedule
        0
        (fun () ->
            if isCellShared mb then
                let shouldBegin, turn =
                    lock
                        mb
                        (fun () ->
                            if mb.begun then
                                false, 0
                            else
                                mb.begun <- true
                                mb.running <- true
                                mb.turnToken <- mb.turnToken + 1
                                true, mb.turnToken
                        )

                if shouldBegin then
                    runMailboxTurn mb turn (fun () -> beginMailboxBody mb)
            else if not mb.begun then
                mb.begun <- true
                beginMailboxBody mb
        )
    |> ignore

let mailboxStartNew<'Msg>
    (body: MailboxOf<'Msg> -> AsyncOf<unit>)
    (token: CancellationTokenOf option)
    : MailboxOf<'Msg>
    =
    let mb = mailboxCreate body token
    mailboxStart mb
    mb

/// `mb.Post(msg)`: to the Receive that waits (it goes on from a timer when local, or directly
/// in the poster's turn when shared across threads), or to the queue
let mailboxPost<'Msg> (mb: MailboxOf<'Msg>) (msg: 'Msg) : unit =
    if isCellShared mb then
        // (the message's last use here: boxed, and only the box is held from now on)
        let box = sendBox msg

        let action =
            lock
                mb
                (fun () ->
                    if mb.started && not mb.begun then
                        mb.begun <- true
                        mb.running <- true
                        mb.turnToken <- mb.turnToken + 1
                        queueAddBox mb.queue box
                        BeginBody mb.turnToken
                    else
                        match mb.waiting with
                        | Some resume ->
                            mb.waiting <- None
                            mb.running <- true
                            mb.turnToken <- mb.turnToken + 1
                            Resume(resume, mb.turnToken)
                        | None ->
                            queueAddBox mb.queue box
                            Queued
                )

        match action with
        | BeginBody turn -> runMailboxTurn mb turn (fun () -> beginMailboxBody mb)
        | Resume(resume, turn) -> runMailboxTurn mb turn (fun () -> resume (unbox' box))
        | Queued -> ()
    else
        match mb.waiting with
        | Some resume ->
            mb.waiting <- None
            schedule 0 (fun () -> resume msg) |> ignore
        | None -> queueAdd mb.queue msg

let mailboxQueueLength<'Msg> (mb: MailboxOf<'Msg>) : int =
    if isCellShared mb then
        lock mb (fun () -> queueCount mb.queue)
    else
        queueCount mb.queue

let mailboxAddError<'Msg> (mb: MailboxOf<'Msg>) (handler: exn -> unit) : unit =
    if isCellShared mb then
        shareValue handler
        lock mb (fun () -> mb.errorHandlers.Add handler)
    else
        mb.errorHandlers.Add handler

/// `inbox.TryReceive(timeout)`: the next message, or None when the time is up first (-1: no limit)
let mailboxTryReceive<'Msg> (mb: MailboxOf<'Msg>) (timeout: int option) : AsyncOf<'Msg option> =
    let timeout = defaultArg timeout -1

    make (fun k ->
        if isCellShared mb then
            let mutable done' = false
            let mutable timer: Timer option = None
            let mutable registration: System.IDisposable option = None

            let immediate =
                lock
                    mb
                    (fun () ->
                        if queueCount mb.queue > 0 then
                            let msg = queueRemoveAt mb.queue 0
                            Some msg
                        else
                            mb.running <- false

                            if timeout >= 0 then
                                timer <-
                                    Some(
                                        schedule
                                            timeout
                                            (fun () ->
                                                let won, regOpt =
                                                    lock
                                                        mb
                                                        (fun () ->
                                                            if not done' then
                                                                done' <- true
                                                                mb.waiting <- None
                                                                true, registration
                                                            else
                                                                false, None
                                                        )

                                                if won then
                                                    match regOpt with
                                                    | Some d -> d.Dispose()
                                                    | None -> ()

                                                    k.ok None
                                            )
                                    )

                            mb.waiting <-
                                Some(fun msg ->
                                    let won, timerOpt, regOpt =
                                        lock
                                            mb
                                            (fun () ->
                                                if not done' then
                                                    done' <- true
                                                    true, timer, registration
                                                else
                                                    queueAdd mb.queue msg
                                                    false, None, None
                                            )

                                    if won then
                                        match timerOpt with
                                        | Some t -> t.live <- false
                                        | None -> ()

                                        match regOpt with
                                        | Some d -> d.Dispose()
                                        | None -> ()

                                        k.ok (Some msg)
                                )

                            registration <-
                                Some(
                                    tokenRegister
                                        k.token
                                        (fun () ->
                                            let won, timerOpt =
                                                lock
                                                    mb
                                                    (fun () ->
                                                        if not done' then
                                                            done' <- true
                                                            mb.waiting <- None
                                                            true, timer
                                                        else
                                                            false, None
                                                    )

                                            if won then
                                                match timerOpt with
                                                | Some t -> t.live <- false
                                                | None -> ()

                                                k.cancel (canceled ())
                                        )
                                )

                            None
                    )

            match immediate with
            | Some msg ->
                adoptShared msg
                k.ok (Some msg)
            | None -> ()
        else if queueCount mb.queue > 0 then
            let msg = queueRemoveAt mb.queue 0
            k.ok (Some msg)
        else
            let mutable done' = false

            let timer =
                if timeout >= 0 then
                    Some(
                        schedule
                            timeout
                            (fun () ->
                                if not done' then
                                    done' <- true
                                    mb.waiting <- None
                                    k.ok None
                            )
                    )
                else
                    None

            // (cancelled while it waits: it reports the cancellation, and what is posted later
            // is queued)
            let mutable registration: System.IDisposable option = None

            mb.waiting <-
                Some(fun msg ->
                    if not done' then
                        done' <- true

                        match timer with
                        | Some t -> t.live <- false
                        | None -> ()

                        match registration with
                        | Some d -> d.Dispose()
                        | None -> ()

                        k.ok (Some msg)
                    else
                        queueAdd mb.queue msg
                )

            if not done' then
                registration <-
                    Some(
                        tokenRegister
                            k.token
                            (fun () ->
                                if not done' then
                                    done' <- true
                                    mb.waiting <- None

                                    match timer with
                                    | Some t -> t.live <- false
                                    | None -> ()

                                    k.cancel (canceled ())
                            )
                    )
    )

/// `inbox.Receive([timeout])`: the next message (TimeoutException when the time is up first)
let mailboxReceive<'Msg> (mb: MailboxOf<'Msg>) (timeout: int option) : AsyncOf<'Msg> =
    builderBind
        (mailboxTryReceive mb timeout)
        (fun m ->
            match m with
            | Some msg -> builderReturn msg
            | None -> make (fun k -> k.fail (System.TimeoutException "The operation has timed out."))
        )

/// `inbox.Scan(f)`: the first message, in order, that `f` takes (the others stay); waiting for one
let mailboxScan<'Msg, 'T> (mb: MailboxOf<'Msg>) (f: 'Msg -> AsyncOf<'T> option) : AsyncOf<'T> =
    let rec look () : AsyncOf<'T> =
        make (fun k ->
            if isCellShared mb then
                let found =
                    lock
                        mb
                        (fun () ->
                            let mutable res = None
                            let mutable i = 0

                            while res.IsNone && i < queueCount mb.queue do
                                match f (queueItem mb.queue i) with
                                | Some c ->
                                    queueRemoveAt mb.queue i |> ignore
                                    res <- Some c
                                | None -> i <- i + 1

                            if res.IsNone then
                                mb.running <- false

                                mb.waiting <-
                                    Some(fun msg ->
                                        lock mb (fun () -> queueAdd mb.queue msg)
                                        start (look ()) k
                                    )

                            res
                        )

                match found with
                | Some c -> start c k
                | None -> ()
            else
                let mutable found = None
                let mutable i = 0

                while found.IsNone && i < queueCount mb.queue do
                    match f (queueItem mb.queue i) with
                    | Some c ->
                        queueRemoveAt mb.queue i |> ignore
                        found <- Some c
                    | None -> i <- i + 1

                match found with
                | Some c -> start c k
                | None ->
                    mb.waiting <-
                        Some(fun msg ->
                            queueAdd mb.queue msg
                            start (look ()) k
                        )
        )

    look ()

type private ReplyBox<'R> =
    {
        mutable value: 'R option
        mutable ready: uint32
        waiters: ResizeArray<'R -> unit>
    }

let private makeReplyChannel<'Msg, 'R> (mb: MailboxOf<'Msg>) : ReplyBox<'R> * ReplyChannelOf<'R> =
    let replyBox =
        {
            value = None
            ready = 0u
            waiters = ResizeArray()
        }

    if isCellShared mb then
        shareValue replyBox

    let channel =
        {
            reply =
                fun r ->
                    if isCellShared mb || isCellShared replyBox then
                        shareValue r

                        let ws =
                            lock
                                replyBox
                                (fun () ->
                                    if replyBox.value.IsNone then
                                        replyBox.value <- Some r
                                        let arr = replyBox.waiters.ToArray()
                                        replyBox.waiters.Clear()
                                        wakeReplyReady replyBox
                                        arr
                                    else
                                        [||]
                                )

                        for w in ws do
                            schedule 0 (fun () -> w r) |> ignore
                    else if replyBox.value.IsNone then
                        replyBox.value <- Some r
                        let ws = replyBox.waiters.ToArray()
                        replyBox.waiters.Clear()

                        // (those waiting go on from a timer, as on another thread)
                        for w in ws do
                            schedule 0 (fun () -> w r) |> ignore
        }

    replyBox, channel

/// `mb.PostAndAsyncReply(build)`: the message, made with a reply channel, is posted now (as
/// FSharp.Core posts it); the computation waits for the reply (each time it runs: the same one)
let mailboxPostAndAsyncReply<'Msg, 'R> (mb: MailboxOf<'Msg>) (build: ReplyChannelOf<'R> -> 'Msg) : AsyncOf<'R> =
    let replyBox, channel = makeReplyChannel mb
    mailboxPost mb (build channel)

    make (fun k ->
        if isCellShared mb || isCellShared replyBox then
            waitReplyReady replyBox
            let r = lock replyBox (fun () -> replyBox.value.Value)
            k.ok r
        else
            match replyBox.value with
            | Some r -> k.ok r
            | None -> replyBox.waiters.Add k.ok
    )

/// `mb.PostAndReply(build)`: the same, waited for here
let mailboxPostAndReply<'Msg, 'R> (mb: MailboxOf<'Msg>) (build: ReplyChannelOf<'R> -> 'Msg) : 'R =
    if isCellShared mb then
        let replyBox, channel = makeReplyChannel mb
        mailboxPost mb (build channel)
        waitReplyReady replyBox
        lock replyBox (fun () -> replyBox.value.Value)
    else
        runSynchronously (mailboxPostAndAsyncReply mb build)

let mailboxPostAndTryAsyncReply<'Msg, 'R>
    (mb: MailboxOf<'Msg>)
    (build: ReplyChannelOf<'R> -> 'Msg)
    (timeout: int option)
    : AsyncOf<'R option>
    =
    builderBind
        (startChildWith (mailboxPostAndAsyncReply mb build) timeout)
        (fun child ->
            make (fun k ->
                start
                    child
                    {
                        ok = fun r -> k.ok (Some r)
                        fail =
                            fun e ->
                                match e with
                                | :? System.TimeoutException -> k.ok None
                                | _ -> k.fail e
                        cancel = k.cancel
                        token = k.token
                        handOver = None
                    }
            )
        )

// ---- Async.AwaitEvent ----

/// `Async.AwaitEvent(e[, cancelAction])`: the next time the event fires (then it is no longer
/// listened to); cancelled, it stops listening and calls `cancelAction`, or is cancelled when
/// there is none, as in FSharp.Core
let awaitEvent<'Del, 'T when 'Del: delegate<'T, unit> and 'Del :> System.Delegate>
    (source: IEvent<'Del, 'T>)
    (cancelAction: (unit -> unit) option)
    : AsyncOf<'T>
    =
    make (fun k ->
        let mutable fired = false
        let mutable subscription: System.IDisposable option = None
        let mutable registration: System.IDisposable option = None

        let stop () =
            fired <- true

            match subscription with
            | Some d -> d.Dispose()
            | None -> ()

            match registration with
            | Some d -> d.Dispose()
            | None -> ()

        subscription <-
            Some(
                source.Subscribe(
                    { new System.IObserver<'T> with
                        member _.OnNext v =
                            if not fired then
                                stop ()
                                k.ok v

                        member _.OnError _ = ()
                        member _.OnCompleted() = ()
                    }
                )
            )

        if not fired then
            registration <-
                Some(
                    tokenRegister
                        k.token
                        (fun () ->
                            if not fired then
                                stop ()

                                match cancelAction with
                                | Some f -> f ()
                                | None -> k.cancel (canceled ())
                        )
                )
    )

/// `Async.Sleep(timeSpan)`: its whole milliseconds
let sleepSpan (span: Fable.Library.Zig.TimeSpan.TimeSpanOf) : AsyncOf<unit> =
    let ms = span.ticks / 10_000L

    if ms < -1L || ms > int64 System.Int32.MaxValue then
        raise (
            System.ArgumentOutOfRangeException(
                "dueTime",
                "The value needs to translate in milliseconds to -1 (signifying an infinite timeout), 0, or a positive integer less than or equal to the maximum allowed timer duration."
            )
        )

    sleep (int ms)
