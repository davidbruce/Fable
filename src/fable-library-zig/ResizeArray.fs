/// The members of .NET's `List<T>` (F#'s `ResizeArray`) that take functions or ranges, written
/// in F# and compiled by the Zig target itself (see List.fs). The object comes first; the
/// runtime holds the items (`fable_rt.raGet` and the others).
module Fable.Library.Zig.ResizeArray

module LibSeq = Fable.Library.Zig.Seq

let private outOfRange (name: string) =
    raise (
        System.ArgumentOutOfRangeException(
            name,
            "Index was out of range. Must be non-negative and less than the size of the collection."
        )
    )

let private badRange () =
    raise (
        System.ArgumentException
            "Offset and length were out of bounds for the array or count is greater than the number of elements from index to the end of the source collection."
    )

/// `r.Find(p)` gives the item or `default(T)`: this is the item, if any (the target supplies the
/// default)
let tryFind<'T> (r: ResizeArray<'T>) (predicate: 'T -> bool) : 'T option =
    let mutable i = 0
    let mutable found = None

    while found.IsNone && i < r.Count do
        if predicate r.[i] then
            found <- Some r.[i]

        i <- i + 1

    found

let tryFindLast<'T> (r: ResizeArray<'T>) (predicate: 'T -> bool) : 'T option =
    let mutable i = r.Count - 1
    let mutable found = None

    while found.IsNone && i >= 0 do
        if predicate r.[i] then
            found <- Some r.[i]

        i <- i - 1

    found

let findAll<'T> (r: ResizeArray<'T>) (predicate: 'T -> bool) : ResizeArray<'T> =
    let result = ResizeArray<'T>()

    for i in 0 .. r.Count - 1 do
        if predicate r.[i] then
            result.Add r.[i]

    result

let findIndex<'T> (r: ResizeArray<'T>) (predicate: 'T -> bool) : int =
    let mutable i = 0
    let mutable found = -1

    while found < 0 && i < r.Count do
        if predicate r.[i] then
            found <- i

        i <- i + 1

    found

let findLastIndex<'T> (r: ResizeArray<'T>) (predicate: 'T -> bool) : int =
    let mutable i = r.Count - 1
    let mutable found = -1

    while found < 0 && i >= 0 do
        if predicate r.[i] then
            found <- i

        i <- i - 1

    found

let exists<'T> (r: ResizeArray<'T>) (predicate: 'T -> bool) : bool = findIndex r predicate >= 0

let trueForAll<'T> (r: ResizeArray<'T>) (predicate: 'T -> bool) : bool =
    findIndex r (fun x -> not (predicate x)) < 0

let forEach<'T> (r: ResizeArray<'T>) (action: 'T -> unit) : unit =
    for i in 0 .. r.Count - 1 do
        action r.[i]

/// `r.RemoveAll(p)`: how many were removed
let removeAll<'T> (r: ResizeArray<'T>) (predicate: 'T -> bool) : int =
    let kept = ResizeArray<'T>()

    for i in 0 .. r.Count - 1 do
        if not (predicate r.[i]) then
            kept.Add r.[i]

    let removed = r.Count - kept.Count
    r.Clear()

    for i in 0 .. kept.Count - 1 do
        r.Add kept.[i]

    removed

let removeRange<'T> (r: ResizeArray<'T>) (index: int) (count: int) : unit =
    if index < 0 then
        outOfRange "index"

    if count < 0 then
        outOfRange "count"

    if index + count > r.Count then
        badRange ()

    for _ in 1..count do
        r.RemoveAt index

let getRange<'T> (r: ResizeArray<'T>) (index: int) (count: int) : ResizeArray<'T> =
    if index < 0 then
        outOfRange "index"

    if count < 0 then
        outOfRange "count"

    if index + count > r.Count then
        badRange ()

    let result = ResizeArray<'T>()

    for i in index .. index + count - 1 do
        result.Add r.[i]

    result

let insertRange<'T> (r: ResizeArray<'T>) (index: int) (items: LibSeq.SeqOf<'T>) : unit =
    if index < 0 || index > r.Count then
        outOfRange "index"

    let mutable at = index

    items
    |> LibSeq.iterate (fun x ->
        r.Insert(at, x)
        at <- at + 1
    )

let addRange<'T> (r: ResizeArray<'T>) (items: LibSeq.SeqOf<'T>) : unit =
    items |> LibSeq.iterate (fun x -> r.Add x)

let ofSeq<'T> (items: LibSeq.SeqOf<'T>) : ResizeArray<'T> =
    let r = ResizeArray<'T>()
    addRange r items
    r

/// `r.IndexOf(x, start, count)`
let indexOfRange<'T when 'T: equality> (r: ResizeArray<'T>) (item: 'T) (start: int) (count: int) : int =
    if start < 0 || start > r.Count then
        outOfRange "startIndex"

    if count < 0 || start + count > r.Count then
        outOfRange "count"

    let mutable i = start
    let mutable found = -1

    while found < 0 && i < start + count do
        if r.[i] = item then
            found <- i

        i <- i + 1

    found

/// `r.IndexOf(x, start)`
let indexOfFrom<'T when 'T: equality> (r: ResizeArray<'T>) (item: 'T) (start: int) : int =
    if start < 0 || start > r.Count then
        outOfRange "startIndex"

    let mutable i = start
    let mutable found = -1

    while found < 0 && i < r.Count do
        if r.[i] = item then
            found <- i

        i <- i + 1

    found

/// `r.BinarySearch(x)`: the index of the item, or the complement of where it would go
let binarySearch<'T when 'T: comparison> (r: ResizeArray<'T>) (item: 'T) : int =
    let mutable lo = 0
    let mutable hi = r.Count - 1
    let mutable found = -1

    while found < 0 && lo <= hi do
        let mid = lo + (hi - lo) / 2
        let c = compare r.[mid] item

        if c = 0 then
            found <- mid
        elif c < 0 then
            lo <- mid + 1
        else
            hi <- mid - 1

    if found >= 0 then
        found
    else
        ~~~lo
