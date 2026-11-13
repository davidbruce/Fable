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
    let mutable n = 0
    let mutable rest = list

    while not rest.IsEmpty do
        n <- n + 1
        rest <- rest.Tail

    n

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
    let mutable acc = []
    let mutable rest = list

    while not rest.IsEmpty do
        acc <- rest.Head :: acc
        rest <- rest.Tail

    acc

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
    let mutable i = 0
    let mutable rest = list

    while not rest.IsEmpty do
        action i rest.Head
        i <- i + 1
        rest <- rest.Tail

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

    let mutable acc = []

    for _ in 1..count do
        acc <- initial :: acc

    acc

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
    filter predicate list, filter (fun x -> not (predicate x)) list

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
