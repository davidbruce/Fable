/// F#'s `async`, written in F# and compiled by the Zig target itself (see List.fs). An async
/// computation is a function that is given what to do with its result and with an exception:
/// continuations. There is one thread, and nothing waits: `Async.Sleep` returns at once, and
/// `Async.Parallel` runs the computations one after the other. What a computation gives, raises
/// and the order of its effects are .NET's.
module Fable.Library.Zig.Async

open Fable.Library.Zig.Seq

type Cont<'T> =
    {
        ok: 'T -> unit
        fail: exn -> unit
    }

type AsyncOf<'T> = { fable_async: Cont<'T> -> unit }

let private make (run: Cont<'T> -> unit) : AsyncOf<'T> = { fable_async = run }

/// Run a computation with these continuations; what it raises before it gets to one of them
/// goes to `fail`.
let private start (computation: AsyncOf<'T>) (k: Cont<'T>) : unit =
    try
        computation.fable_async k
    with e ->
        k.fail e

// ---- the builder: what `async { }` is made of ----

let builderReturn<'T> (value: 'T) : AsyncOf<'T> = make (fun k -> k.ok value)

let builderReturnFrom<'T> (computation: AsyncOf<'T>) : AsyncOf<'T> = computation

let builderZero () : AsyncOf<unit> = make (fun k -> k.ok ())

let builderDelay<'T> (generator: unit -> AsyncOf<'T>) : AsyncOf<'T> = make (fun k -> start (generator ()) k)

let builderBind<'T, 'U> (computation: AsyncOf<'T>) (binder: 'T -> AsyncOf<'U>) : AsyncOf<'U> =
    make (fun k ->
        start
            computation
            {
                ok = fun x -> start (binder x) k
                fail = k.fail
            }
    )

let builderCombine<'T> (computation1: AsyncOf<unit>) (computation2: AsyncOf<'T>) : AsyncOf<'T> =
    builderBind computation1 (fun () -> computation2)

let builderTryWith<'T> (computation: AsyncOf<'T>) (catchHandler: exn -> AsyncOf<'T>) : AsyncOf<'T> =
    make (fun k ->
        start
            computation
            {
                ok = k.ok
                fail = fun e -> start (catchHandler e) k
            }
    )

let builderTryFinally<'T> (computation: AsyncOf<'T>) (compensation: unit -> unit) : AsyncOf<'T> =
    make (fun k ->
        start
            computation
            {
                ok =
                    fun x ->
                        compensation ()
                        k.ok x
                fail =
                    fun e ->
                        compensation ()
                        k.fail e
            }
    )

let builderWhile (guard: unit -> bool) (computation: AsyncOf<unit>) : AsyncOf<unit> =
    let rec loop () : AsyncOf<unit> =
        make (fun k ->
            if guard () then
                start
                    computation
                    {
                        ok = (fun () -> start (loop ()) k)
                        fail = k.fail
                    }
            else
                k.ok ()
        )

    loop ()

let builderFor<'T> (sequence: SeqOf<'T>) (body: 'T -> AsyncOf<unit>) : AsyncOf<unit> =
    let rec loop (rest: 'T list) : AsyncOf<unit> =
        make (fun k ->
            match rest with
            | x :: tail ->
                start
                    (body x)
                    {
                        ok = (fun () -> start (loop tail) k)
                        fail = k.fail
                    }
            | [] -> k.ok ()
        )

    make (fun k -> start (loop (Seq.toList sequence)) k)

// ---- the Async module ----

/// `Async.RunSynchronously`: the result, or the exception raised again.
let runSynchronously<'T> (computation: AsyncOf<'T>) : 'T =
    let mutable result: 'T option = None
    let mutable failure: exn option = None

    start
        computation
        {
            ok = (fun x -> result <- Some x)
            fail = (fun e -> failure <- Some e)
        }

    match failure, result with
    | Some e, _ -> raise e
    | None, Some x -> x
    | None, None -> failwith "The computation did not finish: Async.RunSynchronously needs one that does, here"

let startImmediate (computation: AsyncOf<unit>) : unit =
    start
        computation
        {
            ok = ignore
            fail = (fun e -> raise e)
        }

let startAsync (computation: AsyncOf<unit>) : unit = startImmediate computation

/// (there is one thread and nothing waits: the time is not waited for)
let sleep (millisecondsDueTime: int) : AsyncOf<unit> = make (fun k -> k.ok ())

let ignoreAsync<'T> (computation: AsyncOf<'T>) : AsyncOf<unit> =
    builderBind computation (fun _ -> builderZero ())

let catch<'T> (computation: AsyncOf<'T>) : AsyncOf<Choice<'T, exn>> =
    make (fun k ->
        start
            computation
            {
                ok = (fun x -> k.ok (Choice1Of2 x))
                fail = (fun e -> k.ok (Choice2Of2 e))
            }
    )

/// `Async.Parallel`: one after the other, the results in order.
let parallelAll<'T> (computations: SeqOf<AsyncOf<'T>>) : AsyncOf<'T[]> =
    let rec loop (rest: AsyncOf<'T> list) (acc: 'T list) : AsyncOf<'T[]> =
        make (fun k ->
            match rest with
            | c :: tail ->
                start
                    c
                    {
                        ok = (fun x -> start (loop tail (x :: acc)) k)
                        fail = k.fail
                    }
            | [] -> k.ok (Array.ofList (List.rev acc))
        )

    make (fun k -> start (loop (Seq.toList computations) []) k)

let returnValue<'T> (value: 'T) : AsyncOf<'T> = builderReturn value
