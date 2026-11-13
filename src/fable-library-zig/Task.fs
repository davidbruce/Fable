/// F#'s `task`, written in F# and compiled by the Zig target itself (see List.fs). There is one
/// thread: a task runs to its end where it is made (on .NET it starts there too), so a task is
/// what it ended with: its result or its exception. `let!` of a faulted task raises the
/// exception again; `.Result` and `.Wait()` of one raise an AggregateException, as on .NET.
module Fable.Library.Zig.Task

open Fable.Library.Zig.Seq

type TaskOf<'T> = { fable_task: Result<'T, exn> }

/// What the builder makes of the body of `task { }` before it runs.
type TaskCode<'T> = { code: unit -> 'T }

let private value (t: TaskOf<'T>) : 'T =
    match t.fable_task with
    | Ok v -> v
    | Error e -> raise e

let builderRun<'T> (c: TaskCode<'T>) : TaskOf<'T> =
    try
        { fable_task = Ok(c.code ()) }
    with e ->
        { fable_task = Error e }

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
    match task.fable_task with
    | Ok v -> v
    | Error e -> aggregate e

/// `t.Wait()`
let waitFor<'T> (task: TaskOf<'T>) : unit =
    match task.fable_task with
    | Ok _ -> ()
    | Error e -> aggregate e

let isCompleted<'T> (task: TaskOf<'T>) : bool = true

let isFaulted<'T> (task: TaskOf<'T>) : bool =
    match task.fable_task with
    | Ok _ -> false
    | Error _ -> true

let fromResult<'T> (result: 'T) : TaskOf<'T> = { fable_task = Ok result }

/// `Task.Delay ms`: (one thread, nothing waits) a task that has finished
let delay (millisecondsDelay: int) : TaskOf<unit> = { fable_task = Ok() }

let completedTask () : TaskOf<unit> = { fable_task = Ok() }

let whenAll<'T> (tasks: SeqOf<TaskOf<'T>>) : TaskOf<'T[]> =
    try
        { fable_task = Ok(Array.ofList (List.map value (Seq.toList tasks))) }
    with e ->
        { fable_task = Error e }
