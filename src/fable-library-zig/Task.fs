/// F#'s `task`, written in F# and compiled by the Zig target itself (see List.fs). There is one
/// thread: a task of `task { }` runs to its end where it is made (on .NET it starts there too),
/// so it is what it ended with: its result or its exception. A task of a TaskCompletionSource
/// or of `Task.Delay` is pending until it is set or due; waiting for one (`let!`, `.Result`,
/// `GetResult()`) runs the timers of Async.fs until it completes. `let!` and `GetResult()` of a
/// faulted task raise the exception again; `.Result` and `.Wait()` an AggregateException, as on
/// .NET.
module Fable.Library.Zig.Task

open Fable.Library.Zig.Seq

#if FABLE_COMPILER
[<Fable.Core.Emit("fable_rt.poolNew($0)")>]
let private poolNew (_start: unit -> unit) : System.Threading.Thread = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.threadId()")>]
let private currentThreadId () : int = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.isShared($0)")>]
let private isCellShared (_x: 'a) : bool = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.tryReclaimHomeCell($0)")>]
let private tryReclaimHomeCell (_x: 'a) : bool = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.tryMarkShared($0)")>]
let private tryShare (_x: 'a) : bool = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.adoptShared($0)")>]
let private adoptShared (_x: 'a) : unit = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("$iso_send($0)")>]
let private sendBox (_x: 'a) : Fable.Core.Zig.Iso<'a> = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("try fable_rt.isoUnpack($0)")>]
let private unbox' (_x: Fable.Core.Zig.Iso<'a>) : 'a = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.lockEnter(@intFromPtr($0))")>]
let private lockEnter (_x: 'a) : unit = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.lockExit(@intFromPtr($0))")>]
let private lockExit (_x: 'a) : unit = Fable.Core.Util.nativeOnly
#else
let private poolNew (start: unit -> unit) : System.Threading.Thread = System.Threading.Thread(start)

let private currentThreadId () : int =
    System.Threading.Thread.CurrentThread.ManagedThreadId

let private isCellShared (_x: 'a) : bool = false
let private tryReclaimHomeCell (_x: 'a) : bool = true
let private tryShare (_x: 'a) : bool = false
let private adoptShared (_x: 'a) : unit = ()
let private sendBox (x: 'a) : Fable.Core.Zig.Iso<'a> = Fable.Core.Zig.Iso.pack x
let private unbox' (x: Fable.Core.Zig.Iso<'a>) : 'a = Fable.Core.Zig.Iso.unpack x
let private lockEnter (x: 'a) : unit = System.Threading.Monitor.Enter(box x)
let private lockExit (x: 'a) : unit = System.Threading.Monitor.Exit(box x)
#endif

/// (None while pending)
/// (a task of `Task.Run` runs on the shared worker pool: `fable_thread`, which waiting joins
/// before its `Iso` outcome is unpacked on the home thread)
type TaskOf<'T> =
    {
        mutable fable_task: Result<'T, exn> option
        mutable fable_iso: Fable.Core.Zig.Iso<Result<'T, exn>> option
        mutable fable_thread: System.Threading.Thread option
        fable_owner: int
    }

/// What the builder makes of the body of `task { }` before it runs.
type TaskCode<'T> = { code: unit -> 'T }

let rec private unpackTaskResult<'T> (t: TaskOf<'T>) : Result<'T, exn> =
    if
        not (isCellShared t)
        || (t.fable_owner = currentThreadId () && tryReclaimHomeCell t)
    then
        match t.fable_task with
        | Some r ->
            t.fable_thread <- None
            r
        | None ->
            match t.fable_iso with
            | Some iso ->
                let r = unbox' iso
                t.fable_iso <- None
                adoptShared r
                t.fable_task <- Some r
                t.fable_thread <- None
                r
            | None ->
                while t.fable_task.IsNone
                      && t.fable_iso.IsNone
                      && Fable.Library.Zig.Async.stepPending () do
                    ()

                if t.fable_task.IsSome || t.fable_iso.IsSome then
                    unpackTaskResult t
                else
                    // (nothing left that could complete it: .NET would wait for ever)
                    Error(
                        System.InvalidOperationException "The task can never complete: nothing is left to complete it."
                        :> exn
                    )
    else
        lockEnter t

        try
            match t.fable_task with
            | Some r -> r
            | None ->
                match t.fable_iso with
                | Some iso ->
                    let r = unbox' iso
                    t.fable_iso <- None
                    t.fable_task <- Some r
                    r
                | None ->
                    while t.fable_task.IsNone
                          && t.fable_iso.IsNone
                          && Fable.Library.Zig.Async.stepPending () do
                        ()

                    if t.fable_task.IsSome || t.fable_iso.IsSome then
                        unpackTaskResult t
                    else
                        Error(
                            System.InvalidOperationException
                                "The task can never complete: nothing is left to complete it."
                            :> exn
                        )
        finally
            lockExit t

/// What the task ended with, once it has (the timers run until then)
let private outcome (t: TaskOf<'T>) : Result<'T, exn> =
    match t.fable_thread with
    | Some th -> th.Join()
    | None -> ()

    unpackTaskResult t

let private value (t: TaskOf<'T>) : 'T =
    match outcome t with
    | Ok v -> v
    | Error e -> raise e

let private done' (r: Result<'T, exn>) : TaskOf<'T> =
    {
        fable_task = Some r
        fable_iso = None
        fable_thread = None
        fable_owner = 0
    }

let builderRun<'T> (c: TaskCode<'T>) : TaskOf<'T> =
    try
        done' (Ok(c.code ()))
    with e ->
        done' (Error e)

let builderDelay<'T> (generator: unit -> TaskCode<'T>) : TaskCode<'T> =
    { code = fun () -> (generator ()).code() }

let builderReturn<'T> (value: 'T) : TaskCode<'T> = { code = fun () -> value }

let builderZero () : TaskCode<unit> = { code = fun () -> () }

let builderBind<'T, 'U> (task: TaskOf<'T>) (continuation: 'T -> TaskCode<'U>) : TaskCode<'U> =
    { code = fun () -> (continuation (value task)).code() }

let builderReturnFrom<'T> (task: TaskOf<'T>) : TaskCode<'T> = { code = fun () -> value task }

let builderCombine<'T> (task1: TaskCode<unit>) (task2: TaskCode<'T>) : TaskCode<'T> =
    {
        code =
            fun () ->
                task1.code ()
                task2.code ()
    }

let builderWhile (condition: unit -> bool) (body: TaskCode<unit>) : TaskCode<unit> =
    {
        code =
            fun () ->
                while condition () do
                    body.code ()
    }

let builderFor<'T> (sequence: SeqOf<'T>) (body: 'T -> TaskCode<unit>) : TaskCode<unit> =
    { code = fun () -> Seq.iterate (fun x -> (body x).code()) sequence }

let builderTryWith<'T> (body: TaskCode<'T>) (handler: exn -> TaskCode<'T>) : TaskCode<'T> =
    {
        code =
            fun () ->
                try
                    body.code ()
                with e ->
                    (handler e).code()
    }

/// `use x = resource` (and `use!`): disposed of when the body has ended, as it ends
let builderUsing<'T, 'U> (resource: 'T) (dispose: System.IDisposable) (binder: 'T -> TaskCode<'U>) : TaskCode<'U> =
    {
        code =
            fun () ->
                try
                    (binder resource).code()
                finally
                    dispose.Dispose()
    }

let builderTryFinally<'T> (body: TaskCode<'T>) (compensation: unit -> unit) : TaskCode<'T> =
    {
        code =
            fun () ->
                try
                    body.code ()
                finally
                    compensation ()
    }

let private aggregate (e: exn) =
    raise (System.AggregateException("One or more errors occurred.", e))

/// `t.Result`
let resultOf<'T> (task: TaskOf<'T>) : 'T =
    match outcome task with
    | Ok v -> v
    | Error e -> aggregate e

/// `t.GetAwaiter().GetResult()`: the result, or the exception itself
let getResult<'T> (task: TaskOf<'T>) : 'T = value task

/// `t.Wait()`
let waitFor<'T> (task: TaskOf<'T>) : unit =
    match outcome task with
    | Ok _ -> ()
    | Error e -> aggregate e

let isCompleted<'T> (task: TaskOf<'T>) : bool =
    match task.fable_thread with
    | Some th when th.IsAlive -> false
    | _ -> task.fable_task.IsSome || task.fable_iso.IsSome

/// `Task.Run(fun () -> ...)`: on the runtime worker pool (what the function captured is
/// transferred whole when unaliased or shared otherwise, and results return via Iso)
let run<'T> (f: unit -> 'T) : TaskOf<'T> =
    let t: TaskOf<'T> =
        {
            fable_task = None
            fable_iso = None
            fable_thread = None
            fable_owner = currentThreadId ()
        }

    let th =
        poolNew (fun () ->
            let r =
                try
                    Ok(f ())
                with e ->
                    Error e

            let r =
                match r with
                | Error e when not (tryShare e) -> Error(System.Exception(e.Message))
                | _ -> r

            t.fable_iso <- Some(sendBox r)
        )

    t.fable_thread <- Some th
    th.Start()
    t

let isFaulted<'T> (task: TaskOf<'T>) : bool =
    if not (isCompleted task) then
        false
    else
        match task.fable_task with
        | Some(Error _) -> true
        | Some(Ok _) -> false
        | None ->
            if task.fable_iso.IsSome then
                match outcome task with
                | Error _ -> true
                | Ok _ -> false
            else
                false

let fromResult<'T> (result: 'T) : TaskOf<'T> = done' (Ok result)

let fromException<'T> (e: exn) : TaskOf<'T> = done' (Error e)

/// `Task.Delay ms`: pending until the time is up (a timer of Async.fs)
let delay (millisecondsDelay: int) : TaskOf<unit> =
    if millisecondsDelay <= 0 then
        done' (Ok())
    else
        let t: TaskOf<unit> =
            {
                fable_task = None
                fable_iso = None
                fable_thread = None
                fable_owner = 0
            }

        Fable.Library.Zig.Async.startImmediate (
            Fable.Library.Zig.Async.builderBind
                (Fable.Library.Zig.Async.sleep millisecondsDelay)
                (fun () ->
                    t.fable_task <- Some(Ok())
                    Fable.Library.Zig.Async.builderReturn ()
                )
        )

        t

/// `Task.Delay(ms, token)`: cancelled by the token (a TaskCanceledException when awaited)
let delayToken (millisecondsDelay: int) (token: Fable.Library.Zig.Async.CancellationTokenOf) : TaskOf<unit> =
    let t: TaskOf<unit> =
        {
            fable_task = None
            fable_iso = None
            fable_thread = None
            fable_owner = 0
        }

    Fable.Library.Zig.Async.startWithContinuationsToken
        (Fable.Library.Zig.Async.sleep millisecondsDelay)
        (fun () -> t.fable_task <- Some(Ok()))
        (fun e -> t.fable_task <- Some(Error e))
        (fun _ ->
            t.fable_task <- Some(Error(System.Threading.Tasks.TaskCanceledException "A task was canceled." :> exn))
        )
        (Some token)

    t

let completedTask () : TaskOf<unit> = done' (Ok())

let whenAll<'T> (tasks: SeqOf<TaskOf<'T>>) : TaskOf<'T[]> =
    try
        done' (Ok(Array.ofList (List.map value (Seq.toList tasks))))
    with e ->
        done' (Error e)

// ---- TaskCompletionSource ----

type TaskSourceOf<'T> = { task: TaskOf<'T> }

let sourceCreate<'T> () : TaskSourceOf<'T> =
    {
        task =
            {
                fable_task = None
                fable_iso = None
                fable_thread = None
                fable_owner = 0
            }
    }

let sourceTask<'T> (s: TaskSourceOf<'T>) : TaskOf<'T> = s.task

let private alreadyCompleted () =
    raise (
        System.InvalidOperationException
            "An attempt was made to transition a task to a final state when it had already completed."
    )

let trySetResult<'T> (s: TaskSourceOf<'T>) (result: 'T) : bool =
    if s.task.fable_task.IsSome then
        false
    else
        s.task.fable_task <- Some(Ok result)
        true

let setResult<'T> (s: TaskSourceOf<'T>) (result: 'T) : unit =
    if not (trySetResult s result) then
        alreadyCompleted ()

let trySetException<'T> (s: TaskSourceOf<'T>) (e: exn) : bool =
    if s.task.fable_task.IsSome then
        false
    else
        s.task.fable_task <- Some(Error e)
        true

let setException<'T> (s: TaskSourceOf<'T>) (e: exn) : unit =
    if not (trySetException s e) then
        alreadyCompleted ()

let trySetCanceled<'T> (s: TaskSourceOf<'T>) : bool =
    trySetException s (System.OperationCanceledException "A task was canceled." :> exn)

let setCanceled<'T> (s: TaskSourceOf<'T>) : unit =
    if not (trySetCanceled s) then
        alreadyCompleted ()

// ---- between tasks and async ----

/// `Async.AwaitTask`: what the task ended with
let awaitTask<'T> (t: TaskOf<'T>) : Fable.Library.Zig.Async.AsyncOf<'T> =
    {
        fable_async =
            fun k ->
                match outcome t with
                | Ok v -> k.ok v
                | Error e -> k.fail e
    }

/// `Async.StartAsTask(c[, token])`: the computation starts and runs until it waits; the task
/// completes when it ends (cancelled: a TaskCanceledException)
let startAsTaskToken<'T>
    (computation: Fable.Library.Zig.Async.AsyncOf<'T>)
    (token: Fable.Library.Zig.Async.CancellationTokenOf option)
    : TaskOf<'T>
    =
    let t: TaskOf<'T> =
        {
            fable_task = None
            fable_iso = None
            fable_thread = None
            fable_owner = 0
        }

    Fable.Library.Zig.Async.startWithContinuationsToken
        computation
        (fun v -> t.fable_task <- Some(Ok v))
        (fun e -> t.fable_task <- Some(Error e))
        (fun _ ->
            t.fable_task <- Some(Error(System.Threading.Tasks.TaskCanceledException "A task was canceled." :> exn))
        )
        token

    t

let startAsTask<'T> (computation: Fable.Library.Zig.Async.AsyncOf<'T>) : TaskOf<'T> = startAsTaskToken computation None
