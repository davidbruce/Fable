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

#if FABLE_COMPILER
[<Fable.Core.Emit("try fable_rt.arraySortWith($0, $1)")>]
let private nativeSortWith (_comparer: 'T -> 'T -> int) (_array: 'T[]) : 'T[] = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.arraySort($0)")>]
let private nativeSort (_array: 'T[]) : 'T[] = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.arraySortDesc($0)")>]
let private nativeSortDesc (_array: 'T[]) : 'T[] = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("try fable_rt.arraySortInPlaceWith($0, $1)")>]
let private nativeSortInPlaceWith (_comparer: 'T -> 'T -> int) (_array: 'T[]) : unit = Fable.Core.Util.nativeOnly

[<Fable.Core.Emit("fable_rt.arraySortInPlace($0)")>]
let private nativeSortInPlace (_array: 'T[]) : unit = Fable.Core.Util.nativeOnly
#endif

let sortWith<'T> (comparer: 'T -> 'T -> int) (array: 'T[]) : 'T[] =
#if FABLE_COMPILER
    nativeSortWith comparer array
#else
    Array.ofList (List.sortWith comparer (Array.toList array))
#endif

let sort<'T when 'T: comparison> (array: 'T[]) : 'T[] =
#if FABLE_COMPILER
    nativeSort array
#else
    sortWith compare array
#endif

let sortBy<'Key, 'T when 'Key: comparison> (projection: 'T -> 'Key) (array: 'T[]) : 'T[] =
    sortWith (fun a b -> compare (projection a) (projection b)) array

let sortDescending<'T when 'T: comparison> (array: 'T[]) : 'T[] =
#if FABLE_COMPILER
    nativeSortDesc array
#else
    sortWith (fun a b -> compare b a) array
#endif

let sortByDescending<'Key, 'T when 'Key: comparison> (projection: 'T -> 'Key) (array: 'T[]) : 'T[] =
    sortWith (fun a b -> compare (projection b) (projection a)) array

/// `Array.sortInPlace`: the array itself, in order.
let sortInPlaceWith<'T> (comparer: 'T -> 'T -> int) (array: 'T[]) : unit =
#if FABLE_COMPILER
    nativeSortInPlaceWith comparer array
#else
    let sorted = sortWith comparer array

    for i in 0 .. array.Length - 1 do
        array.[i] <- sorted.[i]
#endif

let sortInPlace<'T when 'T: comparison> (array: 'T[]) : unit =
#if FABLE_COMPILER
    nativeSortInPlace array
#else
    sortInPlaceWith compare array
#endif

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
        raise (System.ArgumentOutOfRangeException("count", "outOfRange"))

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
    // (as System.Array.Copy, which FSharp.Core's blit calls: negative is out of range)
    if count < 0 then
        raise (System.ArgumentOutOfRangeException("length", "Non-negative number required."))

    if sourceIndex < 0 then
        raise (
            System.ArgumentOutOfRangeException(
                "sourceIndex",
                "Index was less than the array's lower bound in the first dimension."
            )
        )

    if targetIndex < 0 then
        raise (
            System.ArgumentOutOfRangeException(
                "destinationIndex",
                "Index was less than the array's lower bound in the first dimension."
            )
        )

    if sourceIndex + count > source.Length then
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

let private outsideIndex () =
    invalidArg "index" "index must be within bounds of the array"

let insertAt<'T> (index: int) (value: 'T) (source: 'T[]) : 'T[] =
    if index < 0 || index > source.Length then
        outsideIndex ()

    Array.init
        (source.Length + 1)
        (fun i ->
            if i < index then
                source.[i]
            elif i = index then
                value
            else
                source.[i - 1]
        )

let insertManyAt<'T> (index: int) (values: 'T list) (source: 'T[]) : 'T[] =
    if index < 0 || index > source.Length then
        outsideIndex ()

    let more = Array.ofList values

    Array.init
        (source.Length + more.Length)
        (fun i ->
            if i < index then
                source.[i]
            elif i < index + more.Length then
                more.[i - index]
            else
                source.[i - more.Length]
        )

let removeAt<'T> (index: int) (source: 'T[]) : 'T[] =
    if index < 0 || index >= source.Length then
        outsideIndex ()

    Array.init
        (source.Length - 1)
        (fun i ->
            if i < index then
                source.[i]
            else
                source.[i + 1]
        )

let removeManyAt<'T> (index: int) (count: int) (source: 'T[]) : 'T[] =
    if index < 0 || index + count > source.Length then
        outsideIndex ()

    Array.init
        (source.Length - count)
        (fun i ->
            if i < index then
                source.[i]
            else
                source.[i + count]
        )

let updateAt<'T> (index: int) (value: 'T) (source: 'T[]) : 'T[] =
    if index < 0 || index >= source.Length then
        outsideIndex ()

    Array.init
        source.Length
        (fun i ->
            if i = index then
                value
            else
                source.[i]
        )

let private differentLengths3 (a: int) (b: int) (c: int) =
    invalidArg
        "array1, array2, array3"
        ("The arrays have different lengths.\n array1.Length = "
         + string a
         + ", array2.Length = "
         + string b
         + ", array3.Length = "
         + string c)

let where<'T> (predicate: 'T -> bool) (array: 'T[]) : 'T[] = Array.filter predicate array

let tail<'T> (array: 'T[]) : 'T[] =
    if array.Length = 0 then
        invalidArg "array" "The input sequence has an insufficient number of elements."

    Array.init (array.Length - 1) (fun i -> array.[i + 1])

let tryExactlyOne<'T> (array: 'T[]) : 'T option =
    if array.Length = 1 then
        Some array.[0]
    else
        None

let tryFindIndexBack<'T> (predicate: 'T -> bool) (array: 'T[]) : int option =
    let mutable i = array.Length - 1
    let mutable found = None

    while found.IsNone && i >= 0 do
        if predicate array.[i] then
            found <- Some i

        i <- i - 1

    found

let findIndexBack<'T> (predicate: 'T -> bool) (array: 'T[]) : int =
    match tryFindIndexBack predicate array with
    | Some i -> i
    | None -> notFound ()

let findBack<'T> (predicate: 'T -> bool) (array: 'T[]) : 'T =
    match tryFindIndexBack predicate array with
    | Some i -> array.[i]
    | None -> notFound ()

let reduceBack<'T> (reduction: 'T -> 'T -> 'T) (array: 'T[]) : 'T =
    if array.Length = 0 then
        emptyArray ()

    let mutable acc = array.[array.Length - 1]

    for i in array.Length - 2 .. -1 .. 0 do
        acc <- reduction array.[i] acc

    acc

let scanBack<'State, 'T> (folder: 'T -> 'State -> 'State) (array: 'T[]) (state: 'State) : 'State[] =
    let result = Array.create (array.Length + 1) state

    for i in array.Length - 1 .. -1 .. 0 do
        result.[i] <- folder array.[i] result.[i + 1]

    result

let mapFold<'Result, 'State, 'T>
    (mapping: 'State -> 'T -> 'Result * 'State)
    (state: 'State)
    (array: 'T[])
    : 'Result[] * 'State
    =
    let mutable acc = state

    let result =
        Array.init
            array.Length
            (fun i ->
                let y, next = mapping acc array.[i]
                acc <- next
                y
            )

    result, acc

let mapFoldBack<'Result, 'State, 'T>
    (mapping: 'T -> 'State -> 'Result * 'State)
    (array: 'T[])
    (state: 'State)
    : 'Result[] * 'State
    =
    let mutable acc = state
    let result: 'Result option[] = Array.create array.Length None

    for i in array.Length - 1 .. -1 .. 0 do
        let y, next = mapping array.[i] acc
        result.[i] <- Some y
        acc <- next

    Array.map (fun (x: 'Result option) -> x.Value) result, acc

let map3<'T1, 'T2, 'T3, 'U> (mapping: 'T1 -> 'T2 -> 'T3 -> 'U) (array1: 'T1[]) (array2: 'T2[]) (array3: 'T3[]) : 'U[] =
    if array1.Length <> array2.Length || array2.Length <> array3.Length then
        differentLengths3 array1.Length array2.Length array3.Length

    Array.init array1.Length (fun i -> mapping array1.[i] array2.[i] array3.[i])

let mapIndexed2<'T1, 'T2, 'U> (mapping: int -> 'T1 -> 'T2 -> 'U) (array1: 'T1[]) (array2: 'T2[]) : 'U[] =
    if array1.Length <> array2.Length then
        differentLengths array1.Length array2.Length

    Array.init array1.Length (fun i -> mapping i array1.[i] array2.[i])

let iterateIndexed2<'T1, 'T2> (action: int -> 'T1 -> 'T2 -> unit) (array1: 'T1[]) (array2: 'T2[]) : unit =
    if array1.Length <> array2.Length then
        differentLengths array1.Length array2.Length

    for i in 0 .. array1.Length - 1 do
        action i array1.[i] array2.[i]

let foldBack2<'State, 'T1, 'T2>
    (folder: 'T1 -> 'T2 -> 'State -> 'State)
    (array1: 'T1[])
    (array2: 'T2[])
    (state: 'State)
    : 'State
    =
    if array1.Length <> array2.Length then
        differentLengths array1.Length array2.Length

    let mutable acc = state

    for i in array1.Length - 1 .. -1 .. 0 do
        acc <- folder array1.[i] array2.[i] acc

    acc

let zip3<'T1, 'T2, 'T3> (array1: 'T1[]) (array2: 'T2[]) (array3: 'T3[]) : ('T1 * 'T2 * 'T3)[] =
    if array1.Length <> array2.Length || array2.Length <> array3.Length then
        differentLengths3 array1.Length array2.Length array3.Length

    Array.init array1.Length (fun i -> array1.[i], array2.[i], array3.[i])

let unzip3<'T1, 'T2, 'T3> (array: ('T1 * 'T2 * 'T3)[]) : 'T1[] * 'T2[] * 'T3[] =
    Array.map (fun (a, _, _) -> a) array, Array.map (fun (_, b, _) -> b) array, Array.map (fun (_, _, c) -> c) array

/// (FSharp.Core takes a sequence of arrays: the target gives the library the list of them)
let transpose<'T> (rows: 'T[] list) : 'T[][] =
    let arrays = Array.ofList rows

    if arrays.Length = 0 then
        [||]
    else
        let n = arrays.[0].Length

        for i in 1 .. arrays.Length - 1 do
            if arrays.[i].Length <> n then
                invalidArg
                    "array.[0]"
                    ("The arrays have different lengths.\narray.[0].Length = "
                     + string n
                     + ", array.["
                     + string i
                     + "].Length = "
                     + string arrays.[i].Length)

        Array.init n (fun j -> Array.init arrays.Length (fun i -> arrays.[i].[j]))

let splitInto<'T> (count: int) (array: 'T[]) : 'T[][] =
    if count <= 0 then
        invalidArg "count" ("The input must be positive.\ncount = " + string count)

    let n = array.Length

    let parts =
        if n < count then
            n
        else
            count

    let size =
        if parts = 0 then
            0
        else
            n / parts

    let extra =
        if parts = 0 then
            0
        else
            n % parts

    Array.init
        parts
        (fun k ->
            let start =
                k * size
                + (if k < extra then
                       k
                   else
                       extra)

            let len =
                if k < extra then
                    size + 1
                else
                    size

            Array.sub array start len
        )

let permute<'T> (indexMap: int -> int) (array: 'T[]) : 'T[] =
    let n = array.Length
    let result: 'T option[] = Array.create n None

    for i in 0 .. n - 1 do
        let j = indexMap i

        if j < 0 || j >= n || result.[j].IsSome then
            invalidArg "indexMap" "The function did not compute a permutation."

        result.[j] <- Some array.[i]

    Array.map (fun (x: 'T option) -> x.Value) result

let compareWith<'T> (comparer: 'T -> 'T -> int) (array1: 'T[]) (array2: 'T[]) : int =
    let n =
        if array1.Length < array2.Length then
            array1.Length
        else
            array2.Length

    let mutable i = 0
    let mutable c = 0

    while c = 0 && i < n do
        c <- comparer array1.[i] array2.[i]
        i <- i + 1

    if c <> 0 then
        c
    elif array1.Length < array2.Length then
        -1
    elif array1.Length > array2.Length then
        1
    else
        0

// ---- the random functions (F# 9): FSharp.Core's algorithms, so that with a seeded `Random`
// they give what .NET gives ----

/// What the randomizer gives, which must be in [0, 1) (NaN is not)
let randomized (randomizer: unit -> float) : float =
    let value = randomizer ()

    if not (value >= 0.0 && value < 1.0) then
        raise (
            System.ArgumentOutOfRangeException(
                "randomizer",
                "The index is outside the legal range.\nrandomizer returned "
                + string value
                + ", should be in range [0.0, 1.0)."
            )
        )

    value

let negativeCount (count: int) =
    invalidArg "count" ("The input must be non-negative.\ncount = " + string count)

/// (`emptyText`: what the module says of an empty input)
let private choiceIndex (next: int -> int) (emptyText: string) (length: int) : int =
    if length = 0 then
        invalidArg "source" emptyText

    next length

let private shuffleInPlace (next: int -> int -> int) (array: 'T[]) : unit =
    let n = array.Length

    for i in 0 .. n - 2 do
        let j = next i n

        if j <> i then
            let t = array.[i]
            array.[i] <- array.[j]
            array.[j] <- t

/// (how many a sample keeps in a pool, below which it draws from a copy of the input)
let sampleSetSize (count: int) : int =
    if count > 5 then
        21 + pown 4 (int (ceil (System.Math.Log(float (count * 3), 4.0))))
    else
        21

let private sampleOf (next: int -> int -> int) (count: int) (source: 'T[]) : 'T[] =
    let n = source.Length

    if count < 0 then
        negativeCount count

    if count > n then
        invalidArg "count" "The input sequence has an insufficient number of elements."

    let setSize = sampleSetSize count

    if count = 0 then
        [||]
    elif n <= setSize then
        let pool = Array.copy source
        let result = Array.create count source.[0]

        for i in 0 .. count - 1 do
            let j = next 0 (n - i)
            result.[i] <- pool.[j]
            pool.[j] <- pool.[n - i - 1]

        result
    else
        let selected = System.Collections.Generic.HashSet<int>()
        let result = Array.create count source.[0]

        for i in 0 .. count - 1 do
            let mutable j = next 0 n

            while not (selected.Add j) do
                j <- next 0 n

            result.[i] <- source.[j]

        result

let private withRandom (random: System.Random) : int -> int -> int = fun lo hi -> random.Next(lo, hi)

let private byRandomizer (randomizer: unit -> float) : int -> int -> int =
    fun lo hi -> int (float (hi - lo) * randomized randomizer + float lo)

let randomShuffleInPlaceWith<'T> (random: System.Random) (source: 'T[]) : unit =
    shuffleInPlace (withRandom random) source

let randomShuffleInPlaceBy<'T> (randomizer: unit -> float) (source: 'T[]) : unit =
    shuffleInPlace (byRandomizer randomizer) source

let randomShuffleInPlace<'T> (source: 'T[]) : unit =
    randomShuffleInPlaceWith System.Random.Shared source

let randomShuffleWith<'T> (random: System.Random) (source: 'T[]) : 'T[] =
    let result = Array.copy source
    randomShuffleInPlaceWith random result
    result

let randomShuffleBy<'T> (randomizer: unit -> float) (source: 'T[]) : 'T[] =
    let result = Array.copy source
    randomShuffleInPlaceBy randomizer result
    result

let randomShuffle<'T> (source: 'T[]) : 'T[] =
    randomShuffleWith System.Random.Shared source

/// (the index of one item, and its text for an empty input: `randomChoice` of the List and Seq
/// modules uses them too)
let randomIndexWith (random: System.Random) (emptyText: string) (length: int) : int =
    choiceIndex (fun n -> random.Next n) emptyText length

let randomIndexBy (randomizer: unit -> float) (emptyText: string) (length: int) : int =
    choiceIndex (fun n -> int (float n * randomized randomizer)) emptyText length

let randomChoiceWith<'T> (random: System.Random) (source: 'T[]) : 'T =
    source.[randomIndexWith random "The input array was empty." source.Length]

let randomChoiceBy<'T> (randomizer: unit -> float) (source: 'T[]) : 'T =
    source.[randomIndexBy randomizer "The input array was empty." source.Length]

let randomChoice<'T> (source: 'T[]) : 'T =
    randomChoiceWith System.Random.Shared source

let randomChoicesWith<'T> (random: System.Random) (count: int) (source: 'T[]) : 'T[] =
    if count < 0 then
        negativeCount count

    if source.Length = 0 then
        invalidArg "source" "The input sequence was empty."

    Array.init count (fun _ -> source.[random.Next source.Length])

let randomChoicesBy<'T> (randomizer: unit -> float) (count: int) (source: 'T[]) : 'T[] =
    if count < 0 then
        negativeCount count

    if source.Length = 0 then
        invalidArg "source" "The input sequence was empty."

    Array.init count (fun _ -> source.[int (float source.Length * randomized randomizer)])

let randomChoices<'T> (count: int) (source: 'T[]) : 'T[] =
    randomChoicesWith System.Random.Shared count source

let randomSampleWith<'T> (random: System.Random) (count: int) (source: 'T[]) : 'T[] =
    sampleOf (withRandom random) count source

let randomSampleBy<'T> (randomizer: unit -> float) (count: int) (source: 'T[]) : 'T[] =
    sampleOf (fun lo hi -> int (float (hi - lo) * randomized randomizer + float lo)) count source

let randomSample<'T> (count: int) (source: 'T[]) : 'T[] =
    randomSampleWith System.Random.Shared count source

// ---- the random functions of the List module (they are here, where Array is: List.fs
// cannot use Array.fs, which uses it) ----

let private listRandomized (randomizer: unit -> float) : float =
    let value = randomizer ()

    if not (value >= 0.0 && value < 1.0) then
        raise (
            System.ArgumentOutOfRangeException(
                "randomizer",
                "The index is outside the legal range.\nrandomizer returned "
                + string value
                + ", should be in range [0.0, 1.0)."
            )
        )

    value

let private listEmptySource () =
    invalidArg "source" "The input sequence was empty."

let listRandomShuffleWith<'T> (random: System.Random) (source: 'T list) : 'T list =
    randomShuffleWith random (Array.ofList source) |> Array.toList

let listRandomShuffleBy<'T> (randomizer: unit -> float) (source: 'T list) : 'T list =
    randomShuffleBy randomizer (Array.ofList source) |> Array.toList

let listRandomShuffle<'T> (source: 'T list) : 'T list =
    listRandomShuffleWith System.Random.Shared source

let listRandomChoiceWith<'T> (random: System.Random) (source: 'T list) : 'T =
    let n = List.length source

    if n = 0 then
        listEmptySource ()

    List.item (random.Next n) source

let listRandomChoiceBy<'T> (randomizer: unit -> float) (source: 'T list) : 'T =
    let n = List.length source

    if n = 0 then
        listEmptySource ()

    List.item (int (float n * listRandomized randomizer)) source

let listRandomChoice<'T> (source: 'T list) : 'T =
    listRandomChoiceWith System.Random.Shared source

let listRandomChoicesWith<'T> (random: System.Random) (count: int) (source: 'T list) : 'T list =
    randomChoicesWith random count (Array.ofList source) |> Array.toList

let listRandomChoicesBy<'T> (randomizer: unit -> float) (count: int) (source: 'T list) : 'T list =
    randomChoicesBy randomizer count (Array.ofList source) |> Array.toList

let listRandomChoices<'T> (count: int) (source: 'T list) : 'T list =
    listRandomChoicesWith System.Random.Shared count source

let listRandomSampleWith<'T> (random: System.Random) (count: int) (source: 'T list) : 'T list =
    randomSampleWith random count (Array.ofList source) |> Array.toList

let listRandomSampleBy<'T> (randomizer: unit -> float) (count: int) (source: 'T list) : 'T list =
    randomSampleBy randomizer count (Array.ofList source) |> Array.toList

let listRandomSample<'T> (count: int) (source: 'T list) : 'T list =
    listRandomSampleWith System.Random.Shared count source

// ---- System.Array.BinarySearch ----

/// .NET's search of a sorted range: the index of an element equal to `value` (the comparer is
/// given the array's element first), or the complement of where it would go
let private searchBy (order: 'T -> 'T -> int) (array: 'T[]) (index: int) (length: int) (value: 'T) : int =
    if index < 0 then
        raise (System.ArgumentOutOfRangeException("index", "Non-negative number required."))

    if length < 0 then
        raise (System.ArgumentOutOfRangeException("length", "Non-negative number required."))

    if array.Length - index < length then
        raise (
            System.ArgumentException(
                "Offset and length were out of bounds for the array or count is greater than the number of elements from index to the end of the source collection."
            )
        )

    let mutable lo = index
    let mutable hi = index + length - 1
    let mutable found = -1

    while found < 0 && lo <= hi do
        let i = lo + ((hi - lo) >>> 1)
        let c = order array.[i] value

        if c = 0 then
            found <- i
        elif c < 0 then
            lo <- i + 1
        else
            hi <- i - 1

    if found >= 0 then
        found
    else
        ~~~lo

/// `Array.BinarySearch(array, [index, length,] value)`: by F#'s comparison
let binarySearch (array: 'T[]) (index: int) (length: int) (value: 'T) : int =
    searchBy compare array index length value

/// The same of strings: by the culture, as .NET's default comparer of strings
let binarySearchStrings (array: string[]) (index: int) (length: int) (value: string) : int =
    searchBy (fun (a: string) (b: string) -> System.String.Compare(a, b)) array index length value

/// The same by a comparer
let binarySearchWith
    (array: 'T[])
    (index: int)
    (length: int)
    (value: 'T)
    (comparer: System.Collections.Generic.IComparer<'T>)
    : int
    =
    searchBy (fun a b -> comparer.Compare(a, b)) array index length value

/// `ComparisonIdentity.FromFunction(f)`: a comparer of `f`
let comparerOfFunction (f: 'T -> 'T -> int) : System.Collections.Generic.IComparer<'T> =
    { new System.Collections.Generic.IComparer<'T> with
        member _.Compare(a, b) = f a b
    }

/// `Comparer<'T>.Create(comparison)`: an IComparer of the delegate
let comparerOfDelegate (f: System.Comparison<'T>) : System.Collections.Generic.IComparer<'T> =
    { new System.Collections.Generic.IComparer<'T> with
        member _.Compare(a, b) = f.Invoke(a, b)
    }

/// `c.Compare(a, b)` of a `Comparer<'T>` (an IComparer here: `Default` or one made by `Create`)
let comparerCompare (c: System.Collections.Generic.IComparer<'T>) (a: 'T) (b: 'T) : int = c.Compare(a, b)

/// `ComparisonIdentity.Structural`: F#'s comparison
let structuralComparer<'T when 'T: comparison> () : System.Collections.Generic.IComparer<'T> =
    { new System.Collections.Generic.IComparer<'T> with
        member _.Compare(a, b) = compare a b
    }

let binarySearchAll (array: 'T[]) (value: 'T) : int = binarySearch array 0 array.Length value

let binarySearchStringsAll (array: string[]) (value: string) : int =
    binarySearchStrings array 0 array.Length value

let binarySearchWithAll (array: 'T[]) (value: 'T) (comparer: System.Collections.Generic.IComparer<'T>) : int =
    binarySearchWith array 0 array.Length value comparer
