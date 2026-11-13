/// F#'s `async`, written in F# and compiled by the Zig target itself (see List.fs). An async
/// computation is a function that is given what to do with its result, with an exception and
/// with a cancellation, and the token that may cancel it: continuations. There is one thread,
/// and nothing waits: `Async.Sleep` returns at once, `Async.Parallel` runs the computations one
/// after the other, and a cancellation is seen where .NET looks for it, at the next bind or step
/// of a loop. What a computation gives, raises and the order of its effects are .NET's.
module Fable.Library.Zig.Async

open Fable.Library.Zig.Seq

/// .NET's `CancellationTokenSource`: whether it has been cancelled, and what to call then (in
/// the reverse order of registering, as .NET does; a removed registration is `None`)
type CancellationSource =
    {
        mutable cancelled: bool
        mutable handlers: ResizeArray<(unit -> unit) option>
        mutable disposed: bool
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
    }

let private canceled () : exn =
    System.OperationCanceledException "The operation was canceled." :> exn

/// `CancellationToken.None`: a token that is never cancelled
let tokenNone () : CancellationTokenOf = { source = newSource () }

/// `new CancellationTokenSource()`
let sourceCreate () : CancellationSource = newSource ()

/// `cts.Cancel()`: the handlers run, last registered first; what they raise is raised again
/// together, as an AggregateException whose InnerException is the first raised
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
            raise (System.AggregateException("One or more errors occurred.", errors.[0]))

// ---- virtual time: what waits is a timer, run in the order of its time when the computation
// that started it is waited for (one thread: no time passes but this clock's) ----

type Timer =
    {
        due: int64
        order: int
        action: unit -> unit
        mutable live: bool
    }

let mutable private now = 0L
let mutable private timerOrder = 0
let private timers = ResizeArray<Timer>()

/// `action` at `ms` from now
let private schedule (ms: int) (action: unit -> unit) : Timer =
    let t =
        {
            due =
                now
                + (if ms > 0 then
                       int64 ms
                   else
                       0L)
            order = timerOrder
            action = action
            live = true
        }

    timerOrder <- timerOrder + 1
    timers.Add t
    t

/// Run the earliest timer (its time becomes the clock's); false when there is none
let private runNextTimer () : bool =
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

        if t.due > now then
            now <- t.due

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

// ---- running computations ----

/// The trampoline: a continuation called deeper than this many nested binds is run after the
/// stack has unwound to the entry point that started the computation (as .NET's trampoline
/// does), so that a long chain of binds runs in bounded stack. The order of effects is kept.
let mutable private depth = 0
let private maxDepth = 200
let private pending = ResizeArray<unit -> unit>()

let private bounce (f: unit -> unit) : unit =
    if depth >= maxDepth then
        pending.Add f
    else
        depth <- depth + 1

        try
            f ()
        finally
            depth <- depth - 1

/// Run `f` from an entry point, then what it left for the trampoline, then the timers in the
/// order of their time until `finished` (what the entry point waits for) or none is left
let private drive (finished: unit -> bool) (f: unit -> unit) : unit =
    let saved = depth
    let mark = pending.Count
    depth <- 0

    let drain () =
        while pending.Count > mark do
            let next = pending.[mark]
            pending.RemoveAt mark
            depth <- 0
            next ()

    try
        f ()
        drain ()

        while not (finished ()) && runNextTimer () do
            depth <- 0
            drain ()
    finally
        depth <- saved

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
            bounce (fun () -> start (generator ()) k)
    )

/// (a cancellation is seen here, before the computation runs)
let builderBind<'T, 'U> (computation: AsyncOf<'T>) (binder: 'T -> AsyncOf<'U>) : AsyncOf<'U> =
    make (fun k ->
        if isCancelled k then
            k.cancel (canceled ())
        else
            start computation (withOk k (fun x -> bounce (fun () -> start (binder x) k)))
    )

let builderCombine<'T> (computation1: AsyncOf<unit>) (computation2: AsyncOf<'T>) : AsyncOf<'T> =
    builderBind computation1 (fun () -> computation2)

let builderTryWith<'T> (computation: AsyncOf<'T>) (catchHandler: exn -> AsyncOf<'T>) : AsyncOf<'T> =
    make (fun k ->
        start
            computation
            {
                ok = k.ok
                fail = fun e -> bounce (fun () -> start (catchHandler e) k)
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
                | x :: tail -> start (body x) (withOk k (fun () -> bounce (fun () -> start (loop tail) k)))
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
let private startImmediateWith (computation: AsyncOf<unit>) (token: CancellationTokenOf) : unit =
    let mutable finished = false

    drive
        (fun () -> finished)
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

    drive
        (fun () -> finished)
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

        let deliver (o: Result<'T, exn> * bool) (k2: Cont<'T>) =
            match o with
            | Ok x, _ -> k2.ok x
            | Error e, true -> k2.cancel e
            | Error e, false -> k2.fail e

        let complete (o: Result<'T, exn> * bool) =
            if outcome.IsNone then
                outcome <- Some o
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
                token = k.token
                handOver = None
            }

        match timeout with
        | Some ms when ms >= 0 ->
            schedule
                ms
                (fun () -> complete (Error(System.TimeoutException "The operation has timed out." :> exn), false))
            |> ignore
        | _ -> ()

        k.ok (
            make (fun k2 ->
                match outcome with
                | Some o -> deliver o k2
                | None -> waiters.Add k2
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
                            if timer.live then
                                timer.live <- false
                                k.cancel (canceled ())
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
let parallelAll<'T> (computations: SeqOf<AsyncOf<'T>>) : AsyncOf<'T[]> =
    let rec loop (rest: AsyncOf<'T> list) (acc: 'T list) : AsyncOf<'T[]> =
        make (fun k ->
            match rest with
            | c :: tail -> start c (withOk k (fun x -> start (loop tail (x :: acc)) k))
            | [] -> k.ok (Array.ofList (List.rev acc))
        )

    make (fun k -> start (loop (Seq.toList computations) []) k)

let sequential<'T> (computations: SeqOf<AsyncOf<'T>>) : AsyncOf<'T[]> = parallelAll computations

let returnValue<'T> (value: 'T) : AsyncOf<'T> = builderReturn value
