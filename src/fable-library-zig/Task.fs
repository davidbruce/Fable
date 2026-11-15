/// F#'s `task`, written in F# and compiled by the Zig target itself (see List.fs). There is one
/// thread: a task of `task { }` runs to its end where it is made (on .NET it starts there too),
/// so it is what it ended with: its result or its exception. A task of a TaskCompletionSource
/// or of `Task.Delay` is pending until it is set or due; waiting for one (`let!`, `.Result`,
/// `GetResult()`) runs the timers of Async.fs until it completes. `let!` and `GetResult()` of a
/// faulted task raise the exception again; `.Result` and `.Wait()` an AggregateException, as on
/// .NET.
module Fable.Library.Zig.Task

open Fable.Library.Zig.Seq

/// (None while pending)
/// (a task of `Task.Run` runs on a thread of its own: `fable_thread`, which waiting joins before
/// what it ended with is read)
type TaskOf<'T> =
    {
        mutable fable_task: Result<'T, exn> option
        mutable fable_thread: System.Threading.Thread option
    }

/// What the builder makes of the body of `task { }` before it runs.
type TaskCode<'T> = { code: unit -> 'T }

/// What the task ended with, once it has (the timers run until then)
let private outcome (t: TaskOf<'T>) : Result<'T, exn> =
    match t.fable_thread with
    | Some th -> th.Join()
    | None -> ()

    match t.fable_task with
    | Some r -> r
    | None ->
        if Fable.Library.Zig.Async.waitUntil (fun () -> t.fable_task.IsSome) then
            t.fable_task.Value
        else
            // (nothing left that could complete it: .NET would wait for ever)
            Error(
                System.InvalidOperationException "The task can never complete: nothing is left to complete it." :> exn
            )

let private value (t: TaskOf<'T>) : 'T =
    match outcome t with
    | Ok v -> v
    | Error e -> raise e

let private done' (r: Result<'T, exn>) : TaskOf<'T> =
    {
        fable_task = Some r
        fable_thread = None
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
    raise (System.AggregateException("One or more errors occurred. (" + e.Message + ")"))

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
    | _ -> task.fable_task.IsSome

/// `Task.Run(fun () -> ...)`: on a thread of its own (what the function captured is shared)
let run<'T> (f: unit -> 'T) : TaskOf<'T> =
    let t: TaskOf<'T> =
        {
            fable_task = None
            fable_thread = None
        }

    let th =
        System.Threading.Thread(fun () ->
            let r =
                try
                    Ok(f ())
                with e ->
                    Error e

            t.fable_task <- Some r
        )

    t.fable_thread <- Some th
    th.Start()
    t

let isFaulted<'T> (task: TaskOf<'T>) : bool =
    match task.fable_task with
    | Some(Error _) -> true
    | _ -> false

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
                fable_thread = None
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
                fable_thread = None
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
            fable_thread = None
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
