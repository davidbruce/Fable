/// .NET's `Stack<T>`, written in F# and compiled by the Zig target itself (see List.fs). The
/// items are kept bottom first; the top is the last.
module Fable.Library.Zig.Stack

module LibSeq = Fable.Library.Zig.Seq

type StackOf<'T> = { mutable items: ResizeArray<'T> }

let private empty () =
    raise (System.InvalidOperationException "Stack empty.")

let create<'T> () : StackOf<'T> = { items = ResizeArray<'T>() }

/// `Stack(items)`: they are pushed in turn, so the last is on top
let ofSeq<'T> (items: LibSeq.SeqOf<'T>) : StackOf<'T> =
    let s = create<'T>()
    items |> LibSeq.iterate (fun x -> s.items.Add x)
    s

let count<'T> (s: StackOf<'T>) : int = s.items.Count

let push<'T> (s: StackOf<'T>) (item: 'T) : unit = s.items.Add item

let pop<'T> (s: StackOf<'T>) : 'T =
    if s.items.Count = 0 then
        empty ()

    let top = s.items.[s.items.Count - 1]
    s.items.RemoveAt(s.items.Count - 1)
    top

let peek<'T> (s: StackOf<'T>) : 'T =
    if s.items.Count = 0 then
        empty ()

    s.items.[s.items.Count - 1]

let tryPop<'T> (s: StackOf<'T>) : 'T option =
    if s.items.Count = 0 then
        None
    else
        Some(pop s)

let tryPeek<'T> (s: StackOf<'T>) : 'T option =
    if s.items.Count = 0 then
        None
    else
        Some(peek s)

let contains<'T when 'T: equality> (s: StackOf<'T>) (item: 'T) : bool = s.items.Contains item

let clear<'T> (s: StackOf<'T>) : unit = s.items.Clear()

let trimExcess<'T> (_: StackOf<'T>) : unit = ()

/// What a walk over a stack gives: the top first
let toList<'T> (s: StackOf<'T>) : 'T list =
    let mutable acc = []

    for i in 0 .. s.items.Count - 1 do
        acc <- s.items.[i] :: acc

    acc

let toArray<'T> (s: StackOf<'T>) : 'T[] = toList s |> List.toArray
