/// F#'s `Observable` module, written in F# and compiled by the Zig target itself (see List.fs):
/// observables and observers are .NET's interfaces, and these are FSharp.Core's functions over
/// them (an error or the end is passed on to the observer).
module Fable.Library.Zig.Observable

open System

/// An observer that gives each value to `next` and passes the rest on to `downstream`
let private forward (next: 'T -> unit) (downstream: IObserver<'U>) : IObserver<'T> =
    { new IObserver<'T> with
        member _.OnNext v = next v
        member _.OnError e = downstream.OnError e
        member _.OnCompleted() = downstream.OnCompleted()
    }

let private observable (subscribe: IObserver<'T> -> IDisposable) : IObservable<'T> =
    { new IObservable<'T> with
        member _.Subscribe w = subscribe w
    }

let subscribe<'T> (callback: 'T -> unit) (source: IObservable<'T>) : IDisposable =
    source.Subscribe(
        { new IObserver<'T> with
            member _.OnNext v = callback v
            member _.OnError _ = ()
            member _.OnCompleted() = ()
        }
    )

let add<'T> (callback: 'T -> unit) (source: IObservable<'T>) : unit = subscribe callback source |> ignore

let choose<'T, 'U> (chooser: 'T -> 'U option) (source: IObservable<'T>) : IObservable<'U> =
    observable (fun w ->
        source.Subscribe(
            forward
                (fun v ->
                    match chooser v with
                    | Some u -> w.OnNext u
                    | None -> ()
                )
                w
        )
    )

let filter<'T> (predicate: 'T -> bool) (source: IObservable<'T>) : IObservable<'T> =
    observable (fun w ->
        source.Subscribe(
            forward
                (fun v ->
                    if predicate v then
                        w.OnNext v
                )
                w
        )
    )

let map<'T, 'U> (mapping: 'T -> 'U) (source: IObservable<'T>) : IObservable<'U> =
    observable (fun w -> source.Subscribe(forward (fun v -> w.OnNext(mapping v)) w))

let merge<'T> (source1: IObservable<'T>) (source2: IObservable<'T>) : IObservable<'T> =
    observable (fun w ->
        let d1 = source1.Subscribe(forward (fun v -> w.OnNext v) w)
        let d2 = source2.Subscribe(forward (fun v -> w.OnNext v) w)

        { new IDisposable with
            member _.Dispose() =
                d1.Dispose()
                d2.Dispose()
        }
    )

let pairwise<'T> (source: IObservable<'T>) : IObservable<'T * 'T> =
    observable (fun w ->
        let mutable last = None

        source.Subscribe(
            forward
                (fun v ->
                    match last with
                    | Some previous -> w.OnNext((previous, v))
                    | None -> ()

                    last <- Some v
                )
                w
        )
    )

let scan<'U, 'T> (collector: 'U -> 'T -> 'U) (state: 'U) (source: IObservable<'T>) : IObservable<'U> =
    observable (fun w ->
        let mutable acc = state

        source.Subscribe(
            forward
                (fun v ->
                    acc <- collector acc v
                    w.OnNext acc
                )
                w
        )
    )

let partition<'T> (predicate: 'T -> bool) (source: IObservable<'T>) : IObservable<'T> * IObservable<'T> =
    filter predicate source, filter (fun v -> not (predicate v)) source

let split<'T, 'U1, 'U2>
    (splitter: 'T -> Choice<'U1, 'U2>)
    (source: IObservable<'T>)
    : IObservable<'U1> * IObservable<'U2>
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
