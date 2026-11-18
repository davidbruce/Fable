/// F#'s `List` module, written in F# and compiled by the Zig target itself. Every function has
/// the name FSharp.Core compiles it to (with a small first letter: `mapIndexed` for
/// `List.mapi`), takes what it takes and raises what it raises.
///
/// The type parameters of each function are declared, and in the order of their names: a
/// call from a program finds them by name (the names are FSharp.Core's).
module Fable.Library.Zig.List

let private emptyList () =
    invalidArg "list" "The input list was empty."

let private notFound () =
    raise (
        System.Collections.Generic.KeyNotFoundException
            "An index satisfying the predicate was not found in the collection."
    )

let length<'T> (list: 'T list) : int =
    let rec go (n: int) (rest: 'T list) : int =
        match rest with
        | [] -> n
        | _ :: tail -> go (n + 1) tail

    go 0 list

let head<'T> (list: 'T list) : 'T =
    match list with
    | x :: _ -> x
    | [] -> emptyList ()

let tail<'T> (list: 'T list) : 'T list =
    match list with
    | _ :: rest -> rest
    | [] -> emptyList ()

let tryHead<'T> (list: 'T list) : 'T option =
    match list with
    | x :: _ -> Some x
    | [] -> None

let rec last<'T> (list: 'T list) : 'T =
    match list with
    | [ x ] -> x
    | _ :: rest -> last rest
    | [] -> emptyList ()

let rec tryLast<'T> (list: 'T list) : 'T option =
    match list with
    | [ x ] -> Some x
    | _ :: rest -> tryLast rest
    | [] -> None

let rec tryItem<'T> (index: int) (list: 'T list) : 'T option =
    match list with
    | x :: rest ->
        if index = 0 then
            Some x
        elif index < 0 then
            None
        else
            tryItem (index - 1) rest
    | [] -> None

let item<'T> (index: int) (list: 'T list) : 'T =
    match tryItem index list with
    | Some x -> x
    | None -> invalidArg "index" "The index was outside the range of elements in the list."

/// `list.[index]`
let getItem<'T> (list: 'T list) (index: int) : 'T =
    match tryItem index list with
    | Some x -> x
    | None -> invalidArg "n" "The index was outside the range of elements in the list."

let singleton<'T> (value: 'T) : 'T list = [ value ]

let reverse<'T> (list: 'T list) : 'T list =
    let rec go (acc: 'T list) (rest: 'T list) : 'T list =
        match rest with
        | [] -> acc
        | x :: tail -> go (x :: acc) tail

    go [] list

let rec append<'T> (list1: 'T list) (list2: 'T list) : 'T list =
    match list1 with
    | [] -> list2
    | x :: rest -> x :: append rest list2

let rec concat<'T> (lists: 'T list list) : 'T list =
    match lists with
    | [] -> []
    | first :: rest -> append first (concat rest)

let rec map<'T, 'U> (mapping: 'T -> 'U) (list: 'T list) : 'U list =
    match list with
    | [] -> []
    | x :: rest -> mapping x :: map mapping rest

let mapIndexed<'T, 'U> (mapping: int -> 'T -> 'U) (list: 'T list) : 'U list =
    let rec go (i: int) (list: 'T list) : 'U list =
        match list with
        | [] -> []
        | x :: rest -> mapping i x :: go (i + 1) rest

    go 0 list

let private differentLengths (shorter: string) (other: string) (by: int) =
    let elements =
        if by = 1 then
            "element"
        else
            "elements"

    invalidArg
        shorter
        ("The lists had different lengths.\n"
         + shorter
         + " is "
         + string by
         + " "
         + elements
         + " shorter than "
         + other)

let map2<'T1, 'T2, 'U> (mapping: 'T1 -> 'T2 -> 'U) (list1: 'T1 list) (list2: 'T2 list) : 'U list =
    let rec go (a: 'T1 list) (b: 'T2 list) : 'U list =
        match a, b with
        | x :: restA, y :: restB -> mapping x y :: go restA restB
        | [], [] -> []
        | [], rest -> differentLengths "list1" "list2" (length rest)
        | rest, [] -> differentLengths "list2" "list1" (length rest)

    go list1 list2

let rec iterate<'T> (action: 'T -> unit) (list: 'T list) : unit =
    match list with
    | [] -> ()
    | x :: rest ->
        action x
        iterate action rest

let iterateIndexed<'T> (action: int -> 'T -> unit) (list: 'T list) : unit =
    let rec go (i: int) (rest: 'T list) : unit =
        match rest with
        | [] -> ()
        | x :: tail ->
            action i x
            go (i + 1) tail

    go 0 list

let rec fold<'State, 'T> (folder: 'State -> 'T -> 'State) (state: 'State) (list: 'T list) : 'State =
    match list with
    | [] -> state
    | x :: rest -> fold folder (folder state x) rest

let foldBack<'State, 'T> (folder: 'T -> 'State -> 'State) (list: 'T list) (state: 'State) : 'State =
    fold (fun acc x -> folder x acc) state (reverse list)

let reduce<'T> (reduction: 'T -> 'T -> 'T) (list: 'T list) : 'T =
    match list with
    | [] -> emptyList ()
    | first :: rest -> fold reduction first rest

let rec filter<'T> (predicate: 'T -> bool) (list: 'T list) : 'T list =
    match list with
    | [] -> []
    | x :: rest ->
        if predicate x then
            x :: filter predicate rest
        else
            filter predicate rest

let rec choose<'T, 'U> (chooser: 'T -> 'U option) (list: 'T list) : 'U list =
    match list with
    | [] -> []
    | x :: rest ->
        match chooser x with
        | Some y -> y :: choose chooser rest
        | None -> choose chooser rest

let rec collect<'T, 'U> (mapping: 'T -> 'U list) (list: 'T list) : 'U list =
    match list with
    | [] -> []
    | x :: rest -> append (mapping x) (collect mapping rest)

let rec exists<'T> (predicate: 'T -> bool) (list: 'T list) : bool =
    match list with
    | [] -> false
    | x :: rest -> predicate x || exists predicate rest

let rec forAll<'T> (predicate: 'T -> bool) (list: 'T list) : bool =
    match list with
    | [] -> true
    | x :: rest -> predicate x && forAll predicate rest

let rec contains<'T when 'T: equality> (value: 'T) (source: 'T list) : bool =
    match source with
    | [] -> false
    | x :: rest -> x = value || contains value rest

let rec tryFind<'T> (predicate: 'T -> bool) (list: 'T list) : 'T option =
    match list with
    | [] -> None
    | x :: rest ->
        if predicate x then
            Some x
        else
            tryFind predicate rest

let find<'T> (predicate: 'T -> bool) (list: 'T list) : 'T =
    match tryFind predicate list with
    | Some x -> x
    | None -> notFound ()

let tryFindIndex<'T> (predicate: 'T -> bool) (list: 'T list) : int option =
    let rec go (i: int) (list: 'T list) : int option =
        match list with
        | [] -> None
        | x :: rest ->
            if predicate x then
                Some i
            else
                go (i + 1) rest

    go 0 list

let findIndex<'T> (predicate: 'T -> bool) (list: 'T list) : int =
    match tryFindIndex predicate list with
    | Some i -> i
    | None -> notFound ()

let rec tryPick<'T, 'U> (chooser: 'T -> 'U option) (list: 'T list) : 'U option =
    match list with
    | [] -> None
    | x :: rest ->
        match chooser x with
        | Some y -> Some y
        | None -> tryPick chooser rest

let pick<'T, 'U> (chooser: 'T -> 'U option) (list: 'T list) : 'U =
    match tryPick chooser list with
    | Some y -> y
    | None -> notFound ()

let initialize<'T> (length: int) (initializer: int -> 'T) : 'T list =
    if length < 0 then
        invalidArg "count" ("The input must be non-negative.\ncount = " + string length)

    let rec go (i: int) : 'T list =
        if i = length then
            []
        else
            initializer i :: go (i + 1)

    go 0

let replicate<'T> (count: int) (initial: 'T) : 'T list =
    if count < 0 then
        invalidArg "count" "The input must be non-negative."

    let rec go (n: int) (acc: 'T list) : 'T list =
        if n <= 0 then
            acc
        else
            go (n - 1) (initial :: acc)

    go count []

let rec zip<'T1, 'T2> (list1: 'T1 list) (list2: 'T2 list) : ('T1 * 'T2) list =
    match list1, list2 with
    | x :: restA, y :: restB -> (x, y) :: zip restA restB
    | [], [] -> []
    | [], rest -> differentLengths "list1" "list2" (length rest)
    | rest, [] -> differentLengths "list2" "list1" (length rest)

let unzip<'T1, 'T2> (list: ('T1 * 'T2) list) : 'T1 list * 'T2 list = map fst list, map snd list

let take<'T> (count: int) (list: 'T list) : 'T list =
    if count < 0 then
        invalidArg "count" ("The input must be non-negative.\ncount = " + string count)

    let rec go (n: int) (list: 'T list) : 'T list =
        if n = 0 then
            []
        else
            match list with
            | x :: rest -> x :: go (n - 1) rest
            | [] ->
                let short =
                    if n = 1 then
                        "The list was 1 element shorter than the index"
                    else
                        "The list was " + string n + " elements shorter than the index"

                raise (
                    System.InvalidOperationException(
                        "The input sequence has an insufficient number of elements.\n" + short
                    )
                )

    go count list

let rec truncate<'T> (count: int) (list: 'T list) : 'T list =
    match list with
    | x :: rest when count > 0 -> x :: truncate (count - 1) rest
    | _ -> []

let skip<'T> (count: int) (list: 'T list) : 'T list =
    let rec go (n: int) (list: 'T list) : 'T list =
        if n <= 0 then
            list
        else
            match list with
            | _ :: rest -> go (n - 1) rest
            | [] ->
                raise (
                    System.ArgumentOutOfRangeException(
                        "count",
                        "The index is outside the legal range.\ncount = "
                        + string count
                        + ", distance past the list = "
                        + string n
                    )
                )

    go count list

let rec takeWhile<'T> (predicate: 'T -> bool) (list: 'T list) : 'T list =
    match list with
    | x :: rest when predicate x -> x :: takeWhile predicate rest
    | _ -> []

let rec skipWhile<'T> (predicate: 'T -> bool) (list: 'T list) : 'T list =
    match list with
    | x :: rest when predicate x -> skipWhile predicate rest
    | _ -> list

let partition<'T> (predicate: 'T -> bool) (list: 'T list) : 'T list * 'T list =
    let rec go trues falses xs =
        match xs with
        | [] -> reverse trues, reverse falses
        | x :: rest ->
            if predicate x then
                go (x :: trues) falses rest
            else
                go trues (x :: falses) rest

    go [] [] list

let indexed<'T> (list: 'T list) : (int * 'T) list = mapIndexed (fun i x -> (i, x)) list

let rec pairwise<'T> (list: 'T list) : ('T * 'T) list =
    match list with
    | a :: (b :: _ as rest) -> (a, b) :: pairwise rest
    | _ -> []

let distinct<'T when 'T: equality> (list: 'T list) : 'T list =
    let rec go (seen: 'T list) (list: 'T list) : 'T list =
        match list with
        | [] -> []
        | x :: rest ->
            if contains x seen then
                go seen rest
            else
                x :: go (x :: seen) rest

    go [] list

let exactlyOne<'T> (list: 'T list) : 'T =
    match list with
    | [ x ] -> x
    | [] -> invalidArg "list" "The input sequence was empty."
    | _ -> invalidArg "source" "The input sequence contains more than one element."

let ofArray<'T> (array: 'T[]) : 'T list = Array.toList array

let toArray<'T> (list: 'T list) : 'T[] = Array.ofList list

// ---- order ----

/// A merge sort: equal items keep their order, as `List.sortWith` promises.
let sortWith<'T> (comparer: 'T -> 'T -> int) (list: 'T list) : 'T list =
    let rec merge (a: 'T list) (b: 'T list) : 'T list =
        match a, b with
        | [], rest -> rest
        | rest, [] -> rest
        | x :: restA, y :: restB ->
            if comparer x y <= 0 then
                x :: merge restA b
            else
                y :: merge a restB

    let rec pairs (lists: 'T list list) : 'T list list =
        match lists with
        | a :: b :: rest -> merge a b :: pairs rest
        | _ -> lists

    let rec all (lists: 'T list list) : 'T list =
        match lists with
        | [] -> []
        | [ one ] -> one
        | _ -> all (pairs lists)

    all (map (fun x -> [ x ]) list)

let private mergeSortByKey<'Key, 'T when 'Key: comparison>
    (desc: bool)
    (projection: 'T -> 'Key)
    (list: 'T list)
    : 'T list
    =
    let rec merge (a: 'T list) (b: 'T list) : 'T list =
        match a, b with
        | [], rest -> rest
        | rest, [] -> rest
        | x :: restA, y :: restB ->
            let cmp =
                if desc then
                    compare (projection y) (projection x)
                else
                    compare (projection x) (projection y)

            if cmp <= 0 then
                x :: merge restA b
            else
                y :: merge a restB

    let rec pairs (lists: 'T list list) : 'T list list =
        match lists with
        | a :: b :: rest -> merge a b :: pairs rest
        | _ -> lists

    let rec all (lists: 'T list list) : 'T list =
        match lists with
        | [] -> []
        | [ one ] -> one
        | _ -> all (pairs lists)

    all (map (fun x -> [ x ]) list)

let sort<'T when 'T: comparison> (list: 'T list) : 'T list = sortWith (fun a b -> compare a b) list

let sortBy<'Key, 'T when 'Key: comparison> (projection: 'T -> 'Key) (list: 'T list) : 'T list =
    mergeSortByKey false projection list

let sortDescending<'T when 'T: comparison> (list: 'T list) : 'T list = sortWith (fun a b -> compare b a) list

let sortByDescending<'Key, 'T when 'Key: comparison> (projection: 'T -> 'Key) (list: 'T list) : 'T list =
    mergeSortByKey true projection list

let private emptySequence () =
    invalidArg "list" "The input sequence was empty."

let max<'T when 'T: comparison> (list: 'T list) : 'T =
    match list with
    | [] -> emptySequence ()
    | first :: rest ->
        fold
            (fun best x ->
                if compare x best > 0 then
                    x
                else
                    best
            )
            first
            rest

let min<'T when 'T: comparison> (list: 'T list) : 'T =
    match list with
    | [] -> emptySequence ()
    | first :: rest ->
        fold
            (fun best x ->
                if compare x best < 0 then
                    x
                else
                    best
            )
            first
            rest

let maxBy<'T, 'U when 'U: comparison> (projection: 'T -> 'U) (list: 'T list) : 'T =
    match list with
    | [] -> emptySequence ()
    | first :: rest ->
        let rec go (best: 'T) (bestKey: 'U) (xs: 'T list) : 'T =
            match xs with
            | [] -> best
            | x :: tail ->
                let k = projection x

                if compare k bestKey > 0 then
                    go x k tail
                else
                    go best bestKey tail

        go first (projection first) rest

let minBy<'T, 'U when 'U: comparison> (projection: 'T -> 'U) (list: 'T list) : 'T =
    match list with
    | [] -> emptySequence ()
    | first :: rest ->
        let rec go (best: 'T) (bestKey: 'U) (xs: 'T list) : 'T =
            match xs with
            | [] -> best
            | x :: tail ->
                let k = projection x

                if compare k bestKey < 0 then
                    go x k tail
                else
                    go best bestKey tail

        go first (projection first) rest

// ---- by key ----

let distinctBy<'Key, 'T when 'Key: equality> (projection: 'T -> 'Key) (list: 'T list) : 'T list =
    let rec go (seen: 'Key list) (list: 'T list) : 'T list =
        match list with
        | [] -> []
        | x :: rest ->
            let key = projection x

            if contains key seen then
                go seen rest
            else
                x :: go (key :: seen) rest

    go [] list

/// The groups in the order their keys first appear, the items of each in their order.
let groupBy<'Key, 'T when 'Key: equality> (projection: 'T -> 'Key) (list: 'T list) : ('Key * 'T list) list =
    let rec tag (xs: 'T list) : ('Key * 'T) list =
        match xs with
        | [] -> []
        | x :: rest -> (projection x, x) :: tag rest

    let tagged = tag list
    let keys = distinct (map fst tagged)

    map
        (fun key ->
            (key,
             choose
                 (fun (k, x) ->
                     if k = key then
                         Some x
                     else
                         None
                 )
                 tagged)
        )
        keys

let countBy<'Key, 'T when 'Key: equality> (projection: 'T -> 'Key) (list: 'T list) : ('Key * int) list =
    map (fun (key: 'Key, items: 'T list) -> (key, length items)) (groupBy projection list)

let except<'T when 'T: equality> (itemsToExclude: 'T list) (list: 'T list) : 'T list =
    distinct (filter (fun x -> not (contains x itemsToExclude)) list)

// ---- more shapes ----

let scan<'State, 'T> (folder: 'State -> 'T -> 'State) (state: 'State) (list: 'T list) : 'State list =
    let rec go (state: 'State) (list: 'T list) : 'State list =
        match list with
        | [] -> []
        | x :: rest ->
            let next = folder state x
            next :: go next rest

    state :: go state list

let splitAt<'T> (index: int) (list: 'T list) : 'T list * 'T list =
    if index < 0 then
        invalidArg "index" "The input must be non-negative."

    take index list, skip index list

let chunkBySize<'T> (chunkSize: int) (list: 'T list) : 'T list list =
    if chunkSize <= 0 then
        invalidArg "chunkSize" ("The input must be positive.\nchunkSize = " + string chunkSize)

    let rec takeChunk (n: int) (acc: 'T list) (rest: 'T list) : 'T list * 'T list =
        if n = 0 then
            reverse acc, rest
        else
            match rest with
            | [] -> reverse acc, []
            | x :: tail -> takeChunk (n - 1) (x :: acc) tail

    let rec go (chunks: 'T list list) (rest: 'T list) : 'T list list =
        match rest with
        | [] -> reverse chunks
        | _ ->
            let chunk, next = takeChunk chunkSize [] rest
            go (chunk :: chunks) next

    go [] list

let windowed<'T> (windowSize: int) (list: 'T list) : 'T list list =
    if windowSize <= 0 then
        invalidArg "windowSize" ("The input must be positive.\nwindowSize = " + string windowSize)

    let rec advance (n: int) (xs: 'T list) : 'T list =
        if n = 0 then
            xs
        else
            match xs with
            | [] -> []
            | _ :: tail -> advance (n - 1) tail

    let rec takeN (n: int) (acc: 'T list) (xs: 'T list) : 'T list =
        if n = 0 then
            reverse acc
        else
            match xs with
            | [] -> reverse acc
            | x :: tail -> takeN (n - 1) (x :: acc) tail

    let rec go (windows: 'T list list) (rest: 'T list) (lead: 'T list) : 'T list list =
        match lead, rest with
        | _ :: leadTail, _ :: restTail -> go (takeN windowSize [] rest :: windows) restTail leadTail
        | _ -> reverse windows

    go [] list (advance (windowSize - 1) list)

let rec iterate2<'T1, 'T2> (action: 'T1 -> 'T2 -> unit) (list1: 'T1 list) (list2: 'T2 list) : unit =
    match list1, list2 with
    | x :: restA, y :: restB ->
        action x y
        iterate2 action restA restB
    | [], [] -> ()
    | [], rest -> differentLengths "list1" "list2" (length rest)
    | rest, [] -> differentLengths "list2" "list1" (length rest)

let rec forAll2<'T1, 'T2> (predicate: 'T1 -> 'T2 -> bool) (list1: 'T1 list) (list2: 'T2 list) : bool =
    match list1, list2 with
    | x :: restA, y :: restB -> predicate x y && forAll2 predicate restA restB
    | [], [] -> true
    | [], rest -> differentLengths "list1" "list2" (length rest)
    | rest, [] -> differentLengths "list2" "list1" (length rest)

let rec exists2<'T1, 'T2> (predicate: 'T1 -> 'T2 -> bool) (list1: 'T1 list) (list2: 'T2 list) : bool =
    match list1, list2 with
    | x :: restA, y :: restB -> predicate x y || exists2 predicate restA restB
    | [], [] -> false
    | [], rest -> differentLengths "list1" "list2" (length rest)
    | rest, [] -> differentLengths "list2" "list1" (length rest)

let rec fold2<'State, 'T1, 'T2>
    (folder: 'State -> 'T1 -> 'T2 -> 'State)
    (state: 'State)
    (list1: 'T1 list)
    (list2: 'T2 list)
    : 'State
    =
    match list1, list2 with
    | x :: restA, y :: restB -> fold2 folder (folder state x y) restA restB
    | [], [] -> state
    | [], rest -> differentLengths "list1" "list2" (length rest)
    | rest, [] -> differentLengths "list2" "list1" (length rest)

let allPairs<'T1, 'T2> (list1: 'T1 list) (list2: 'T2 list) : ('T1 * 'T2) list =
    collect (fun x -> map (fun y -> (x, y)) list2) list1

let tryExactlyOne<'T> (list: 'T list) : 'T option =
    match list with
    | [ x ] -> Some x
    | _ -> None

let where<'T> (predicate: 'T -> bool) (list: 'T list) : 'T list = filter predicate list

let get<'T> (list: 'T list) (index: int) : 'T = item index list

let cons<'T> (head: 'T) (tail: 'T list) : 'T list = head :: tail

/// `List.ofSeq` of what is a list here already (a list, `Map.keys`, ...).
let ofSeq<'T> (source: 'T list) : 'T list = source

let mapFold<'Result, 'State, 'T>
    (mapping: 'State -> 'T -> 'Result * 'State)
    (state: 'State)
    (list: 'T list)
    : 'Result list * 'State
    =
    let rec go (acc: 'Result list) (state: 'State) (list: 'T list) : 'Result list * 'State =
        match list with
        | [] -> reverse acc, state
        | x :: rest ->
            let y, next = mapping state x
            go (y :: acc) next rest

    go [] state list

let mapFoldBack<'Result, 'State, 'T>
    (mapping: 'T -> 'State -> 'Result * 'State)
    (list: 'T list)
    (state: 'State)
    : 'Result list * 'State
    =
    let rec go (acc: 'Result list) (state: 'State) (list: 'T list) : 'Result list * 'State =
        match list with
        | [] -> acc, state
        | x :: rest ->
            let y, next = mapping x state
            go (y :: acc) next rest

    go [] state (reverse list)

let unzip3<'T1, 'T2, 'T3> (list: ('T1 * 'T2 * 'T3) list) : 'T1 list * 'T2 list * 'T3 list =
    let rec go (a: 'T1 list) (b: 'T2 list) (c: 'T3 list) (list: ('T1 * 'T2 * 'T3) list) =
        match list with
        | [] -> reverse a, reverse b, reverse c
        | (x, y, z) :: rest -> go (x :: a) (y :: b) (z :: c) rest

    go [] [] [] list

let unfold<'State, 'T> (generator: 'State -> ('T * 'State) option) (state: 'State) : 'T list =
    let rec go (acc: 'T list) (state: 'State) : 'T list =
        match generator state with
        | Some(x, next) -> go (x :: acc) next
        | None -> reverse acc

    go [] state

let tryFindIndexBack<'T> (predicate: 'T -> bool) (list: 'T list) : int option =
    let rec go (i: int) (found: int option) (list: 'T list) : int option =
        match list with
        | [] -> found
        | x :: rest ->
            go
                (i + 1)
                (if predicate x then
                     Some i
                 else
                     found)
                rest

    go 0 None list

let findIndexBack<'T> (predicate: 'T -> bool) (list: 'T list) : int =
    match tryFindIndexBack predicate list with
    | Some i -> i
    | None -> notFound ()

let tryFindBack<'T> (predicate: 'T -> bool) (list: 'T list) : 'T option =
    let rec go (found: 'T option) (list: 'T list) : 'T option =
        match list with
        | [] -> found
        | x :: rest ->
            go
                (if predicate x then
                     Some x
                 else
                     found)
                rest

    go None list

let findBack<'T> (predicate: 'T -> bool) (list: 'T list) : 'T =
    match tryFindBack predicate list with
    | Some x -> x
    | None -> notFound ()

let splitInto<'T> (count: int) (list: 'T list) : 'T list list =
    if count <= 0 then
        invalidArg "count" ("The input must be positive.\ncount = " + string count)

    let n = length list

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

    let rec go (k: int) (list: 'T list) : 'T list list =
        if k = parts then
            []
        else
            let here =
                if k < extra then
                    size + 1
                else
                    size

            let chunk, rest = splitAt here list
            chunk :: go (k + 1) rest

    go 0 list

let scanBack<'State, 'T> (folder: 'T -> 'State -> 'State) (list: 'T list) (state: 'State) : 'State list =
    let rec go (acc: 'State list) (state: 'State) (list: 'T list) : 'State list =
        match list with
        | [] -> acc
        | x :: rest ->
            let next = folder x state
            go (next :: acc) next rest

    go [ state ] state (reverse list)

let reduceBack<'T> (reduction: 'T -> 'T -> 'T) (list: 'T list) : 'T =
    match reverse list with
    | [] -> emptyList ()
    | last :: rest -> fold (fun acc x -> reduction x acc) last rest

let mapIndexed2<'T1, 'T2, 'U> (mapping: int -> 'T1 -> 'T2 -> 'U) (list1: 'T1 list) (list2: 'T2 list) : 'U list =
    let rec go (i: int) (a: 'T1 list) (b: 'T2 list) : 'U list =
        match a, b with
        | x :: restA, y :: restB -> mapping i x y :: go (i + 1) restA restB
        | [], [] -> []
        | [], rest -> differentLengths "list1" "list2" (length rest)
        | rest, [] -> differentLengths "list2" "list1" (length rest)

    go 0 list1 list2

let iterateIndexed2<'T1, 'T2> (action: int -> 'T1 -> 'T2 -> unit) (list1: 'T1 list) (list2: 'T2 list) : unit =
    let rec go (i: int) (a: 'T1 list) (b: 'T2 list) : unit =
        match a, b with
        | x :: restA, y :: restB ->
            action i x y
            go (i + 1) restA restB
        | [], [] -> ()
        | [], rest -> differentLengths "list1" "list2" (length rest)
        | rest, [] -> differentLengths "list2" "list1" (length rest)

    go 0 list1 list2

let foldBack2<'State, 'T1, 'T2>
    (folder: 'T1 -> 'T2 -> 'State -> 'State)
    (list1: 'T1 list)
    (list2: 'T2 list)
    (state: 'State)
    : 'State
    =
    let n1 = length list1
    let n2 = length list2

    if n1 <> n2 then
        invalidArg
            "list1, list2"
            ("The lists had different lengths.\nlist1.Length = "
             + string n1
             + ", list2.Length = "
             + string n2)

    let rec go (acc: 'State) (a: 'T1 list) (b: 'T2 list) : 'State =
        match a, b with
        | x :: restA, y :: restB -> go (folder x y acc) restA restB
        | _ -> acc

    go state (reverse list1) (reverse list2)

/// `list.[lo..hi]`: what of it is inside the list
let getSlice<'T> (list: 'T list) (lower: int option) (upper: int option) : 'T list =
    let n = length list

    let lo =
        match lower with
        | Some l when l > 0 -> l
        | _ -> 0

    let hi =
        match upper with
        | Some h when h < n - 1 -> h
        | _ -> n - 1

    if hi < lo then
        []
    else
        take (hi - lo + 1) (skip lo list)

let private outsideList () =
    invalidArg "index" "index must be within bounds of the list"

let insertAt<'T> (index: int) (value: 'T) (source: 'T list) : 'T list =
    if index < 0 || index > length source then
        outsideList ()

    let before, after = splitAt index source
    append before (value :: after)

let insertManyAt<'T> (index: int) (values: 'T list) (source: 'T list) : 'T list =
    if index < 0 || index > length source then
        outsideList ()

    let before, after = splitAt index source
    append before (append values after)

let removeAt<'T> (index: int) (source: 'T list) : 'T list =
    if index < 0 || index >= length source then
        outsideList ()

    let before, after = splitAt index source
    append before after.Tail

let removeManyAt<'T> (index: int) (count: int) (source: 'T list) : 'T list =
    if index < 0 || index + count > length source then
        outsideList ()

    let before, after = splitAt index source
    append before (skip count after)

let updateAt<'T> (index: int) (value: 'T) (source: 'T list) : 'T list =
    if index < 0 || index >= length source then
        outsideList ()

    let before, after = splitAt index source
    append before (value :: after.Tail)

let empty<'T> () : 'T list = []

let isEmpty<'T> (list: 'T list) : bool =
    match list with
    | [] -> true
    | _ -> false

let private differentLengths3 (n1: int) (n2: int) (n3: int) =
    invalidArg
        "list1, list2, list3"
        ("The lists had different lengths.\n list1.Length = "
         + string n1
         + ", list2.Length = "
         + string n2
         + ", list3.Length = "
         + string n3)

let map3<'T1, 'T2, 'T3, 'U>
    (mapping: 'T1 -> 'T2 -> 'T3 -> 'U)
    (list1: 'T1 list)
    (list2: 'T2 list)
    (list3: 'T3 list)
    : 'U list
    =
    // (as FSharp.Core: the common prefix is mapped before the lengths are found to differ)
    let rec go (a: 'T1 list) (b: 'T2 list) (c: 'T3 list) : 'U list =
        match a, b, c with
        | x :: ra, y :: rb, z :: rc ->
            let y = mapping x y z
            y :: go ra rb rc
        | [], [], [] -> []
        | _ -> differentLengths3 (length list1) (length list2) (length list3)

    go list1 list2 list3

let zip3<'T1, 'T2, 'T3> (list1: 'T1 list) (list2: 'T2 list) (list3: 'T3 list) : ('T1 * 'T2 * 'T3) list =
    let rec go (a: 'T1 list) (b: 'T2 list) (c: 'T3 list) : ('T1 * 'T2 * 'T3) list =
        match a, b, c with
        | x :: ra, y :: rb, z :: rc -> (x, y, z) :: go ra rb rc
        | [], [], [] -> []
        | _ -> differentLengths3 (length a) (length b) (length c)

    go list1 list2 list3

let permute<'T> (indexMap: int -> int) (list: 'T list) : 'T list =
    let items = toArray list
    let n = items.Length
    let result: 'T option[] = Array.create n None

    for i in 0 .. n - 1 do
        let j = indexMap i

        if j < 0 || j >= n || result.[j].IsSome then
            invalidArg "indexMap" "The function did not compute a permutation."

        result.[j] <- Some items.[i]

    ofArray (Array.map (fun (x: 'T option) -> x.Value) result)

let transpose<'T> (lists: 'T list list) : 'T list list =
    match lists with
    | [] -> []
    | first :: _ ->
        let n = length first

        lists
        |> iterateIndexed (fun i l ->
            let m = length l

            if m < n then
                differentLengths ("list.[" + string i + "]") "list.[0]" (n - m)
            elif m > n then
                differentLengths "list.[0]" ("list.[" + string i + "]") (m - n)
        )

        let rec go (rows: 'T list list) : 'T list list =
            match rows with
            | [] :: _ -> []
            | _ -> map head rows :: go (map tail rows)

        go lists
