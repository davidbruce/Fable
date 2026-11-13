/// .NET's `Queue<T>`, written in F# and compiled by the Zig target itself (see List.fs). The
/// items from `head` on are the queue, the first to leave first; the room before `head` is
/// given back when it is half of what is kept.
module Fable.Library.Zig.Queue

module LibSeq = Fable.Library.Zig.Seq

type QueueOf<'T> =
    {
        mutable items: ResizeArray<'T>
        mutable head: int
    }

let private empty () =
    raise (System.InvalidOperationException "Queue empty.")

let create<'T> () : QueueOf<'T> =
    {
        items = ResizeArray<'T>()
        head = 0
    }

let ofSeq<'T> (items: LibSeq.SeqOf<'T>) : QueueOf<'T> =
    let q = create<'T>()
    items |> LibSeq.iterate (fun x -> q.items.Add x)
    q

let count<'T> (q: QueueOf<'T>) : int = q.items.Count - q.head

let enqueue<'T> (q: QueueOf<'T>) (item: 'T) : unit = q.items.Add item

let private compact<'T> (q: QueueOf<'T>) =
    if q.head > 16 && q.head * 2 > q.items.Count then
        let kept = ResizeArray<'T>()

        for i in q.head .. q.items.Count - 1 do
            kept.Add q.items.[i]

        q.items <- kept
        q.head <- 0

let dequeue<'T> (q: QueueOf<'T>) : 'T =
    if count q = 0 then
        empty ()

    let first = q.items.[q.head]
    q.head <- q.head + 1

    if q.head = q.items.Count then
        q.items.Clear()
        q.head <- 0
    else
        compact q

    first

let peek<'T> (q: QueueOf<'T>) : 'T =
    if count q = 0 then
        empty ()

    q.items.[q.head]

let tryDequeue<'T> (q: QueueOf<'T>) : 'T option =
    if count q = 0 then
        None
    else
        Some(dequeue q)

let tryPeek<'T> (q: QueueOf<'T>) : 'T option =
    if count q = 0 then
        None
    else
        Some(peek q)

let contains<'T when 'T: equality> (q: QueueOf<'T>) (item: 'T) : bool =
    let mutable found = false

    for i in q.head .. q.items.Count - 1 do
        if q.items.[i] = item then
            found <- true

    found

let clear<'T> (q: QueueOf<'T>) : unit =
    q.items.Clear()
    q.head <- 0

let trimExcess<'T> (q: QueueOf<'T>) : unit = compact q

/// What a walk over a queue gives: the first to leave first
let toList<'T> (q: QueueOf<'T>) : 'T list =
    let mutable acc = []

    for i in q.items.Count - 1 .. -1 .. q.head do
        acc <- q.items.[i] :: acc

    acc

let toArray<'T> (q: QueueOf<'T>) : 'T[] = toList q |> List.toArray
