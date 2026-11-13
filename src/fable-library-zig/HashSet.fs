/// The members of .NET's `HashSet<T>` that combine it with a sequence, written in F# and compiled
/// by the Zig target itself (see List.fs). The set comes first.
module Fable.Library.Zig.HashSet

open System.Collections.Generic

module LibSeq = Fable.Library.Zig.Seq

let private ofItems<'T when 'T: equality> (items: LibSeq.SeqOf<'T>) : HashSet<'T> =
    let s = HashSet<'T>()
    items |> LibSeq.iterate (fun x -> s.Add x |> ignore)
    s

let ofSeq<'T when 'T: equality> (items: LibSeq.SeqOf<'T>) : HashSet<'T> = ofItems items

let unionWith<'T when 'T: equality> (s: HashSet<'T>) (other: LibSeq.SeqOf<'T>) : unit =
    other |> LibSeq.iterate (fun x -> s.Add x |> ignore)

let exceptWith<'T when 'T: equality> (s: HashSet<'T>) (other: LibSeq.SeqOf<'T>) : unit =
    other |> LibSeq.iterate (fun x -> s.Remove x |> ignore)

let intersectWith<'T when 'T: equality> (s: HashSet<'T>) (other: LibSeq.SeqOf<'T>) : unit =
    let o = ofItems other
    let gone = ResizeArray<'T>()

    for x in s do
        if not (o.Contains x) then
            gone.Add x

    for i in 0 .. gone.Count - 1 do
        s.Remove gone.[i] |> ignore

let symmetricExceptWith<'T when 'T: equality> (s: HashSet<'T>) (other: LibSeq.SeqOf<'T>) : unit =
    let o = ofItems other

    for x in o do
        if not (s.Remove x) then
            s.Add x |> ignore

let overlaps<'T when 'T: equality> (s: HashSet<'T>) (other: LibSeq.SeqOf<'T>) : bool =
    other |> LibSeq.exists (fun x -> s.Contains x)

let private countIn<'T when 'T: equality> (s: HashSet<'T>) (o: HashSet<'T>) : int =
    let mutable n = 0

    for x in s do
        if o.Contains x then
            n <- n + 1

    n

let setEquals<'T when 'T: equality> (s: HashSet<'T>) (other: LibSeq.SeqOf<'T>) : bool =
    let o = ofItems other
    o.Count = s.Count && countIn s o = s.Count

let isSubsetOf<'T when 'T: equality> (s: HashSet<'T>) (other: LibSeq.SeqOf<'T>) : bool =
    let o = ofItems other
    countIn s o = s.Count

let isProperSubsetOf<'T when 'T: equality> (s: HashSet<'T>) (other: LibSeq.SeqOf<'T>) : bool =
    let o = ofItems other
    countIn s o = s.Count && o.Count > s.Count

let isSupersetOf<'T when 'T: equality> (s: HashSet<'T>) (other: LibSeq.SeqOf<'T>) : bool =
    other |> LibSeq.forAll (fun x -> s.Contains x)

let isProperSupersetOf<'T when 'T: equality> (s: HashSet<'T>) (other: LibSeq.SeqOf<'T>) : bool =
    let o = ofItems other
    countIn o s = o.Count && s.Count > o.Count

/// `s.CopyTo(array)` and `s.CopyTo(array, index)`
let copyTo<'T when 'T: equality> (s: HashSet<'T>) (array: 'T[]) (index: int) : unit =
    if index < 0 || index + s.Count > array.Length then
        raise (
            System.ArgumentException
                "Destination array is not long enough to copy all the items in the collection. Check array index and length."
        )

    let mutable i = index

    for x in s do
        array.[i] <- x
        i <- i + 1

/// `s.CopyTo(array, index, count)`: the first `count` items
let copyToCount<'T when 'T: equality> (s: HashSet<'T>) (array: 'T[]) (index: int) (count: int) : unit =
    if index < 0 || count < 0 || index + count > array.Length then
        raise (
            System.ArgumentException
                "Destination array is not long enough to copy all the items in the collection. Check array index and length."
        )

    let mutable i = index

    for x in s do
        if i < index + count then
            array.[i] <- x
            i <- i + 1
