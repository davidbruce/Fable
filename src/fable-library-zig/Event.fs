/// F#'s `Event<'T>` and the `Event` module, written in F# and compiled by the Zig target itself
/// (see List.fs). An event keeps its handlers; what it publishes is .NET's `IEvent<'T>`, whose
/// handlers are delegates and which is also an observable.
module Fable.Library.Zig.Event

open System

type EventOf<'T> = { mutable handlers: ResizeArray<Handler<'T>> }

let create<'T> () : EventOf<'T> =
    { handlers = ResizeArray<Handler<'T>>() }

/// `e.Trigger(args)`: each handler, in the order they were added (those added meanwhile wait for
/// the next time)
let trigger<'T> (e: EventOf<'T>) (args: 'T) : unit =
    let now = e.handlers.ToArray()

    for h in now do
        h.Invoke(null, args)

let publish<'T> (e: EventOf<'T>) : IEvent<'T> =
    { new IEvent<'T> with
        member _.AddHandler h = e.handlers.Add h
        member _.RemoveHandler h = e.handlers.Remove h |> ignore
      interface IObservable<'T> with
          member _.Subscribe w =
              let h = Handler<'T>(fun _ v -> w.OnNext v)
              e.handlers.Add h

              { new IDisposable with
                  member _.Dispose() = e.handlers.Remove h |> ignore
              }
    }

/// .NET's `Event<'Delegate, 'Args>`, of a delegate that takes the sender and the arguments
/// (`Action<obj, 'T>`, as `[<CLIEvent>]` members declare them): its handlers
type DelegateEventOf<'T> = { mutable dhandlers: ResizeArray<Action<obj, 'T>> }

let createDelegate<'T> () : DelegateEventOf<'T> =
    { dhandlers = ResizeArray<Action<obj, 'T>>() }

/// `e.Trigger(sender, args)`
let triggerDelegate<'T> (e: DelegateEventOf<'T>) (sender: obj) (args: 'T) : unit =
    let now = e.dhandlers.ToArray()

    for h in now do
        h.Invoke(sender, args)

let publishDelegate<'T> (e: DelegateEventOf<'T>) : IEvent<Action<obj, 'T>, 'T> =
    { new IEvent<Action<obj, 'T>, 'T> with
        member _.AddHandler h = e.dhandlers.Add h
        member _.RemoveHandler h = e.dhandlers.Remove h |> ignore
      interface IObservable<'T> with
          member _.Subscribe w =
              let h = Action<obj, 'T>(fun _ v -> w.OnNext v)
              e.dhandlers.Add h

              { new IDisposable with
                  member _.Dispose() = e.dhandlers.Remove h |> ignore
              }
    }

/// `RuntimeHelpers.CreateEvent`, as F# makes a `[<CLIEvent>]` member of these functions
let createEvent<'Del, 'T when 'Del: delegate<'T, unit> and 'Del :> Delegate>
    (addHandler: 'Del -> unit)
    (removeHandler: 'Del -> unit)
    (createHandler: (obj -> 'T -> unit) -> 'Del)
    : IEvent<'Del, 'T>
    =
    { new IEvent<'Del, 'T> with
        member _.AddHandler h = addHandler h
        member _.RemoveHandler h = removeHandler h
      interface IObservable<'T> with
          member _.Subscribe w =
              let h = createHandler (fun _ v -> w.OnNext v)
              addHandler h

              { new IDisposable with
                  member _.Dispose() = removeHandler h
              }
    }

/// (FSharp.Core's functions take an event of any delegate type `'Del`: what they need of it is
/// that it is an observable)
let add<'Del, 'T when 'Del: delegate<'T, unit> and 'Del :> Delegate>
    (callback: 'T -> unit)
    (source: IEvent<'Del, 'T>)
    : unit
    =
    source.Subscribe(
        { new IObserver<'T> with
            member _.OnNext v = callback v
            member _.OnError _ = ()
            member _.OnCompleted() = ()
        }
    )
    |> ignore

let private derived<'Del, 'T, 'U when 'Del: delegate<'T, unit> and 'Del :> Delegate>
    (source: IEvent<'Del, 'T>)
    (onValue: EventOf<'U> -> 'T -> unit)
    : IEvent<'U>
    =
    let e = create<'U>()
    add (fun v -> onValue e v) source
    publish e

let choose<'Del, 'T, 'U when 'Del: delegate<'T, unit> and 'Del :> Delegate>
    (chooser: 'T -> 'U option)
    (source: IEvent<'Del, 'T>)
    : IEvent<'U>
    =
    derived
        source
        (fun e v ->
            match chooser v with
            | Some u -> trigger e u
            | None -> ()
        )

let filter<'Del, 'T when 'Del: delegate<'T, unit> and 'Del :> Delegate>
    (predicate: 'T -> bool)
    (source: IEvent<'Del, 'T>)
    : IEvent<'T>
    =
    derived
        source
        (fun e v ->
            if predicate v then
                trigger e v
        )

let map<'Del, 'T, 'U when 'Del: delegate<'T, unit> and 'Del :> Delegate>
    (mapping: 'T -> 'U)
    (source: IEvent<'Del, 'T>)
    : IEvent<'U>
    =
    derived source (fun e v -> trigger e (mapping v))

let merge<'Del1, 'Del2, 'T
    when 'Del1: delegate<'T, unit> and 'Del1 :> Delegate and 'Del2: delegate<'T, unit> and 'Del2 :> Delegate>
    (source1: IEvent<'Del1, 'T>)
    (source2: IEvent<'Del2, 'T>)
    : IEvent<'T>
    =
    let e = create<'T>()
    add (fun v -> trigger e v) source1
    add (fun v -> trigger e v) source2
    publish e

let pairwise<'Del, 'T when 'Del: delegate<'T, unit> and 'Del :> Delegate> (source: IEvent<'Del, 'T>) : IEvent<'T * 'T> =
    let mutable last = None

    derived
        source
        (fun e v ->
            match last with
            | Some previous -> trigger e (previous, v)
            | None -> ()

            last <- Some v
        )

let scan<'Del, 'T, 'U when 'Del: delegate<'T, unit> and 'Del :> Delegate>
    (collector: 'U -> 'T -> 'U)
    (state: 'U)
    (source: IEvent<'Del, 'T>)
    : IEvent<'U>
    =
    let mutable acc = state

    derived
        source
        (fun e v ->
            acc <- collector acc v
            trigger e acc
        )

let partition<'Del, 'T when 'Del: delegate<'T, unit> and 'Del :> Delegate>
    (predicate: 'T -> bool)
    (source: IEvent<'Del, 'T>)
    : IEvent<'T> * IEvent<'T>
    =
    filter predicate source, filter (fun v -> not (predicate v)) source

let split<'Del, 'T, 'U1, 'U2 when 'Del: delegate<'T, unit> and 'Del :> Delegate>
    (splitter: 'T -> Choice<'U1, 'U2>)
    (source: IEvent<'Del, 'T>)
    : IEvent<'U1> * IEvent<'U2>
    =
    choose
        (fun v ->
            match splitter v with
            | Choice1Of2 x -> Some x
            | Choice2Of2 _ -> None
        )
        source,
    choose
        (fun v ->
            match splitter v with
            | Choice2Of2 x -> Some x
            | Choice1Of2 _ -> None
        )
        source
