/// F#'s `ListCollector<'T>` (what list expressions and `List.map` build with), written in F# and
/// compiled by the Zig target itself (see List.fs): the items so far, made a list at `Close`,
/// which leaves the collector empty, as .NET's does.
module Fable.Library.Zig.ListCollector

module LibSeq = Fable.Library.Zig.Seq

type ListCollectorOf<'T> = { items: ResizeArray<'T> }

let create<'T> () : ListCollectorOf<'T> = { items = ResizeArray<'T>() }

let add<'T> (c: ListCollectorOf<'T>) (value: 'T) : unit = c.items.Add value

let addMany<'T> (c: ListCollectorOf<'T>) (values: LibSeq.SeqOf<'T>) : unit =
    values |> LibSeq.iterate (fun x -> c.items.Add x)

let close<'T> (c: ListCollectorOf<'T>) : 'T list =
    let mutable acc: 'T list = []

    for i in c.items.Count - 1 .. -1 .. 0 do
        acc <- c.items.[i] :: acc

    c.items.Clear()
    acc

let addManyAndClose<'T> (c: ListCollectorOf<'T>) (values: LibSeq.SeqOf<'T>) : 'T list =
    addMany c values
    close c
