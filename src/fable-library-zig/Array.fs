/// The rest of F#'s `Array` module, written in F# and compiled by the Zig target itself (see
/// List.fs), on what the runtime has: `Array.init`, indexing and the length. Each function is
/// named as FSharp.Core compiles it, with a small first letter, and raises what it raises.
module Fable.Library.Zig.Array

let private emptyArray () =
    invalidArg "array" "The input array was empty."

let private notFound () =
    raise (
        System.Collections.Generic.KeyNotFoundException
            "An index satisfying the predicate was not found in the collection."
    )

let private differentLengths (a: int) (b: int) =
    invalidArg
        "array1"
        ("The arrays have different lengths.\narray1.Length = "
         + string a
         + ", array2.Length = "
         + string b)

let private tooFew () =
    raise (System.InvalidOperationException "The input sequence has an insufficient number of elements.")

let ofList<'T> (list: 'T list) : 'T[] = Array.ofList list

let singleton<'T> (value: 'T) : 'T[] = [| value |]

let replicate<'T> (count: int) (initial: 'T) : 'T[] =
    if count < 0 then
        invalidArg "count" ("The input must be non-negative.\ncount = " + string count)

    Array.init count (fun _ -> initial)

let head<'T> (array: 'T[]) : 'T =
    if array.Length = 0 then
        emptyArray ()
    else
        array.[0]

let tryHead<'T> (array: 'T[]) : 'T option =
    if array.Length = 0 then
        None
    else
        Some array.[0]

let last<'T> (array: 'T[]) : 'T =
    if array.Length = 0 then
        emptyArray ()
    else
        array.[array.Length - 1]

let tryLast<'T> (array: 'T[]) : 'T option =
    if array.Length = 0 then
        None
    else
        Some array.[array.Length - 1]

let item<'T> (index: int) (array: 'T[]) : 'T = array.[index]

let tryItem<'T> (index: int) (array: 'T[]) : 'T option =
    if index < 0 || index >= array.Length then
        None
    else
        Some array.[index]

let exactlyOne<'T> (array: 'T[]) : 'T =
    if array.Length = 1 then
        array.[0]
    elif array.Length = 0 then
        invalidArg "array" "The input sequence was empty."
    else
        invalidArg "array" "The input sequence contains more than one element."

let tryFindIndex<'T> (predicate: 'T -> bool) (array: 'T[]) : int option =
    let mutable i = 0
    let mutable found = None

    while found.IsNone && i < array.Length do
        if predicate array.[i] then
            found <- Some i

        i <- i + 1

    found

let findIndex<'T> (predicate: 'T -> bool) (array: 'T[]) : int =
    match tryFindIndex predicate array with
    | Some i -> i
    | None -> notFound ()

let tryFind<'T> (predicate: 'T -> bool) (array: 'T[]) : 'T option =
    match tryFindIndex predicate array with
    | Some i -> Some array.[i]
    | None -> None

let find<'T> (predicate: 'T -> bool) (array: 'T[]) : 'T =
    match tryFindIndex predicate array with
    | Some i -> array.[i]
    | None -> notFound ()

let tryFindBack<'T> (predicate: 'T -> bool) (array: 'T[]) : 'T option =
    let mutable i = array.Length - 1
    let mutable found = None

    while found.IsNone && i >= 0 do
        if predicate array.[i] then
            found <- Some array.[i]

        i <- i - 1

    found

let tryPick<'T, 'U> (chooser: 'T -> 'U option) (array: 'T[]) : 'U option =
    let mutable i = 0
    let mutable found = None

    while found.IsNone && i < array.Length do
        found <- chooser array.[i]
        i <- i + 1

    found

let pick<'T, 'U> (chooser: 'T -> 'U option) (array: 'T[]) : 'U =
    match tryPick chooser array with
    | Some x -> x
    | None -> notFound ()

let choose<'T, 'U> (chooser: 'T -> 'U option) (array: 'T[]) : 'U[] =
    Array.ofList (List.choose chooser (Array.toList array))

let collect<'T, 'U> (mapping: 'T -> 'U[]) (array: 'T[]) : 'U[] =
    Array.ofList (List.collect (fun x -> Array.toList (mapping x)) (Array.toList array))

let concat<'T> (arrays: 'T[] list) : 'T[] =
    Array.ofList (List.collect Array.toList arrays)

let foldBack<'State, 'T> (folder: 'T -> 'State -> 'State) (array: 'T[]) (state: 'State) : 'State =
    let mutable acc = state

    for i in array.Length - 1 .. -1 .. 0 do
        acc <- folder array.[i] acc

    acc

let reduce<'T> (reduction: 'T -> 'T -> 'T) (array: 'T[]) : 'T =
    if array.Length = 0 then
        emptyArray ()

    let mutable acc = array.[0]

    for i in 1 .. array.Length - 1 do
        acc <- reduction acc array.[i]

    acc

let scan<'State, 'T> (folder: 'State -> 'T -> 'State) (state: 'State) (array: 'T[]) : 'State[] =
    Array.ofList (List.scan folder state (Array.toList array))

let max<'T when 'T: comparison> (array: 'T[]) : 'T =
    if array.Length = 0 then
        emptyArray ()

    reduce
        (fun a b ->
            if compare b a > 0 then
                b
            else
                a
        )
        array

let min<'T when 'T: comparison> (array: 'T[]) : 'T =
    if array.Length = 0 then
        emptyArray ()

    reduce
        (fun a b ->
            if compare b a < 0 then
                b
            else
                a
        )
        array

let maxBy<'T, 'U when 'U: comparison> (projection: 'T -> 'U) (array: 'T[]) : 'T =
    if array.Length = 0 then
        emptyArray ()

    reduce
        (fun a b ->
            if compare (projection b) (projection a) > 0 then
                b
            else
                a
        )
        array

let minBy<'T, 'U when 'U: comparison> (projection: 'T -> 'U) (array: 'T[]) : 'T =
    if array.Length = 0 then
        emptyArray ()

    reduce
        (fun a b ->
            if compare (projection b) (projection a) < 0 then
                b
            else
                a
        )
        array

let sortWith<'T> (comparer: 'T -> 'T -> int) (array: 'T[]) : 'T[] =
    Array.ofList (List.sortWith comparer (Array.toList array))

let sort<'T when 'T: comparison> (array: 'T[]) : 'T[] = sortWith compare array

let sortBy<'Key, 'T when 'Key: comparison> (projection: 'T -> 'Key) (array: 'T[]) : 'T[] =
    sortWith (fun a b -> compare (projection a) (projection b)) array

let sortDescending<'T when 'T: comparison> (array: 'T[]) : 'T[] = sortWith (fun a b -> compare b a) array

let sortByDescending<'Key, 'T when 'Key: comparison> (projection: 'T -> 'Key) (array: 'T[]) : 'T[] =
    sortWith (fun a b -> compare (projection b) (projection a)) array

/// `Array.sortInPlace`: the array itself, in order.
let sortInPlaceWith<'T> (comparer: 'T -> 'T -> int) (array: 'T[]) : unit =
    let sorted = sortWith comparer array

    for i in 0 .. array.Length - 1 do
        array.[i] <- sorted.[i]

let sortInPlace<'T when 'T: comparison> (array: 'T[]) : unit = sortInPlaceWith compare array

let sortInPlaceBy<'Key, 'T when 'Key: comparison> (projection: 'T -> 'Key) (array: 'T[]) : unit =
    sortInPlaceWith (fun a b -> compare (projection a) (projection b)) array

let distinct<'T when 'T: equality> (array: 'T[]) : 'T[] =
    Array.ofList (List.distinct (Array.toList array))

let distinctBy<'Key, 'T when 'Key: equality> (projection: 'T -> 'Key) (array: 'T[]) : 'T[] =
    Array.ofList (List.distinctBy projection (Array.toList array))

let groupBy<'Key, 'T when 'Key: equality> (projection: 'T -> 'Key) (array: 'T[]) : ('Key * 'T[])[] =
    Array.ofList (
        List.map
            (fun (k: 'Key, items: 'T list) -> (k, Array.ofList items))
            (List.groupBy projection (Array.toList array))
    )

let countBy<'Key, 'T when 'Key: equality> (projection: 'T -> 'Key) (array: 'T[]) : ('Key * int)[] =
    Array.ofList (List.countBy projection (Array.toList array))

let indexed<'T> (array: 'T[]) : (int * 'T)[] =
    Array.init array.Length (fun i -> (i, array.[i]))

let zip<'T1, 'T2> (array1: 'T1[]) (array2: 'T2[]) : ('T1 * 'T2)[] =
    if array1.Length <> array2.Length then
        differentLengths array1.Length array2.Length

    Array.init array1.Length (fun i -> (array1.[i], array2.[i]))

let unzip<'T1, 'T2> (array: ('T1 * 'T2)[]) : 'T1[] * 'T2[] =
    Array.init array.Length (fun i -> fst array.[i]), Array.init array.Length (fun i -> snd array.[i])

let map2<'T1, 'T2, 'U> (mapping: 'T1 -> 'T2 -> 'U) (array1: 'T1[]) (array2: 'T2[]) : 'U[] =
    if array1.Length <> array2.Length then
        differentLengths array1.Length array2.Length

    Array.init array1.Length (fun i -> mapping array1.[i] array2.[i])

let iterate2<'T1, 'T2> (action: 'T1 -> 'T2 -> unit) (array1: 'T1[]) (array2: 'T2[]) : unit =
    if array1.Length <> array2.Length then
        differentLengths array1.Length array2.Length

    for i in 0 .. array1.Length - 1 do
        action array1.[i] array2.[i]

let fold2<'State, 'T1, 'T2>
    (folder: 'State -> 'T1 -> 'T2 -> 'State)
    (state: 'State)
    (array1: 'T1[])
    (array2: 'T2[])
    : 'State
    =
    if array1.Length <> array2.Length then
        differentLengths array1.Length array2.Length

    let mutable acc = state

    for i in 0 .. array1.Length - 1 do
        acc <- folder acc array1.[i] array2.[i]

    acc

let exists2<'T1, 'T2> (predicate: 'T1 -> 'T2 -> bool) (array1: 'T1[]) (array2: 'T2[]) : bool =
    if array1.Length <> array2.Length then
        differentLengths array1.Length array2.Length

    let mutable found = false
    let mutable i = 0

    while not found && i < array1.Length do
        found <- predicate array1.[i] array2.[i]
        i <- i + 1

    found

let forAll2<'T1, 'T2> (predicate: 'T1 -> 'T2 -> bool) (array1: 'T1[]) (array2: 'T2[]) : bool =
    not (exists2 (fun a b -> not (predicate a b)) array1 array2)

let partition<'T> (predicate: 'T -> bool) (array: 'T[]) : 'T[] * 'T[] =
    Array.filter predicate array, Array.filter (fun x -> not (predicate x)) array

let take<'T> (count: int) (array: 'T[]) : 'T[] =
    if count < 0 then
        invalidArg "count" ("The input must be non-negative.\ncount = " + string count)

    if count > array.Length then
        tooFew ()

    Array.init count (fun i -> array.[i])

let truncate<'T> (count: int) (array: 'T[]) : 'T[] =
    let n =
        if count < 0 then
            0
        elif count > array.Length then
            array.Length
        else
            count

    Array.init n (fun i -> array.[i])

let skip<'T> (count: int) (array: 'T[]) : 'T[] =
    if count > array.Length then
        invalidArg "count" "outOfRange"

    let start =
        if count < 0 then
            0
        else
            count

    Array.init (array.Length - start) (fun i -> array.[start + i])

let takeWhile<'T> (predicate: 'T -> bool) (array: 'T[]) : 'T[] =
    let mutable n = 0

    while n < array.Length && predicate array.[n] do
        n <- n + 1

    Array.init n (fun i -> array.[i])

let skipWhile<'T> (predicate: 'T -> bool) (array: 'T[]) : 'T[] =
    let mutable n = 0

    while n < array.Length && predicate array.[n] do
        n <- n + 1

    Array.init (array.Length - n) (fun i -> array.[n + i])

let splitAt<'T> (index: int) (array: 'T[]) : 'T[] * 'T[] =
    if index < 0 then
        invalidArg "index" ("The input must be non-negative.\nindex = " + string index)

    if index > array.Length then
        tooFew ()

    Array.init index (fun i -> array.[i]), Array.init (array.Length - index) (fun i -> array.[index + i])

let chunkBySize<'T> (chunkSize: int) (array: 'T[]) : 'T[][] =
    if chunkSize <= 0 then
        invalidArg "chunkSize" ("The input must be positive.\nchunkSize = " + string chunkSize)

    let n = (array.Length + chunkSize - 1) / chunkSize

    Array.init
        n
        (fun c ->
            let start = c * chunkSize

            let len =
                if start + chunkSize > array.Length then
                    array.Length - start
                else
                    chunkSize

            Array.init len (fun i -> array.[start + i])
        )

let windowed<'T> (windowSize: int) (array: 'T[]) : 'T[][] =
    if windowSize <= 0 then
        invalidArg "windowSize" ("The input must be positive.\nwindowSize = " + string windowSize)

    let n =
        if array.Length < windowSize then
            0
        else
            array.Length - windowSize + 1

    Array.init n (fun s -> Array.init windowSize (fun i -> array.[s + i]))

let pairwise<'T> (array: 'T[]) : ('T * 'T)[] =
    let n =
        if array.Length < 2 then
            0
        else
            array.Length - 1

    Array.init n (fun i -> (array.[i], array.[i + 1]))

let allPairs<'T1, 'T2> (array1: 'T1[]) (array2: 'T2[]) : ('T1 * 'T2)[] =
    Array.init (array1.Length * array2.Length) (fun k -> (array1.[k / array2.Length], array2.[k % array2.Length]))

let except<'T when 'T: equality> (itemsToExclude: 'T list) (array: 'T[]) : 'T[] =
    distinct (Array.filter (fun x -> not (List.contains x itemsToExclude)) array)

let blit<'T> (source: 'T[]) (sourceIndex: int) (target: 'T[]) (targetIndex: int) (count: int) : unit =
    if sourceIndex < 0 || count < 0 || sourceIndex + count > source.Length then
        invalidArg
            "sourceArray"
            "Source array was not long enough. Check the source index, length, and the array's lower bounds."

    if targetIndex < 0 || targetIndex + count > target.Length then
        invalidArg
            "destinationArray"
            "Destination array was not long enough. Check the destination index, length, and the array's lower bounds."

    let items = Array.init count (fun i -> source.[sourceIndex + i])

    for i in 0 .. count - 1 do
        target.[targetIndex + i] <- items.[i]
