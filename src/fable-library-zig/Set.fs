/// F#'s `Set`, written in F# and compiled by the Zig target itself (see Map.fs).
module Fable.Library.Zig.Set

type SetTree<'T> =
    | SetEmpty
    | SetNode of key: 'T * left: SetTree<'T> * right: SetTree<'T> * height: int

let private height (t: SetTree<'T>) : int =
    match t with
    | SetEmpty -> 0
    | SetNode(_, _, _, h) -> h

let inline private node (k: 'T) (l: SetTree<'T>) (r: SetTree<'T>) : SetTree<'T> =
    SetNode(k, l, r, max (height l) (height r) + 1)

let private rebalance (k: 'T) (l: SetTree<'T>) (r: SetTree<'T>) : SetTree<'T> =
    let hl = height l
    let hr = height r

    if hr > hl + 1 then
        match r with
        | SetNode(rk, rl, rr, _) ->
            if height rl > height rr then
                match rl with
                | SetNode(rlk, rll, rlr, _) -> node rlk (node k l rll) (node rk rlr rr)
                | SetEmpty -> node k l r
            else
                node rk (node k l rl) rr
        | SetEmpty -> node k l r
    elif hl > hr + 1 then
        match l with
        | SetNode(lk, ll, lr, _) ->
            if height lr > height ll then
                match lr with
                | SetNode(lrk, lrl, lrr, _) -> node lrk (node lk ll lrl) (node k lrr r)
                | SetEmpty -> node k l r
            else
                node lk ll (node k lr r)
        | SetEmpty -> node k l r
    else
        node k l r

let empty<'T when 'T: comparison> () : SetTree<'T> = SetEmpty

let isEmpty<'T when 'T: comparison> (set: SetTree<'T>) : bool =
    match set with
    | SetEmpty -> true
    | _ -> false

let rec add<'T when 'T: comparison> (value: 'T) (set: SetTree<'T>) : SetTree<'T> =
    match set with
    | SetEmpty -> SetNode(value, SetEmpty, SetEmpty, 1)
    | SetNode(k, l, r, _) ->
        let c = compare value k

        if c < 0 then
            rebalance k (add value l) r
        elif c > 0 then
            rebalance k l (add value r)
        else
            set

let singleton<'T when 'T: comparison> (value: 'T) : SetTree<'T> = SetNode(value, SetEmpty, SetEmpty, 1)

let rec contains<'T when 'T: comparison> (element: 'T) (set: SetTree<'T>) : bool =
    match set with
    | SetEmpty -> false
    | SetNode(k, l, r, _) ->
        let c = compare element k

        if c < 0 then
            contains element l
        elif c > 0 then
            contains element r
        else
            true

let rec private spliceOutMin (t: SetTree<'T>) : 'T * SetTree<'T> =
    match t with
    | SetNode(k, SetEmpty, r, _) -> k, r
    | SetNode(k, l, r, _) ->
        let k2, l2 = spliceOutMin l
        k2, rebalance k l2 r
    | SetEmpty -> failwith "unreachable"

let rec remove<'T when 'T: comparison> (value: 'T) (set: SetTree<'T>) : SetTree<'T> =
    match set with
    | SetEmpty -> SetEmpty
    | SetNode(k, l, r, _) ->
        let c = compare value k

        if c < 0 then
            rebalance k (remove value l) r
        elif c > 0 then
            rebalance k l (remove value r)
        else
            match l, r with
            | SetEmpty, _ -> r
            | _, SetEmpty -> l
            | _ ->
                let sk, r2 = spliceOutMin r
                rebalance sk l r2

let rec iterate<'T when 'T: comparison> (action: 'T -> unit) (set: SetTree<'T>) : unit =
    match set with
    | SetEmpty -> ()
    | SetNode(k, l, r, _) ->
        iterate action l
        action k
        iterate action r

let rec fold<'State, 'T when 'T: comparison>
    (folder: 'State -> 'T -> 'State)
    (state: 'State)
    (set: SetTree<'T>)
    : 'State
    =
    match set with
    | SetEmpty -> state
    | SetNode(k, l, r, _) -> fold folder (folder (fold folder state l) k) r

let rec foldBack<'State, 'T when 'T: comparison>
    (folder: 'T -> 'State -> 'State)
    (set: SetTree<'T>)
    (state: 'State)
    : 'State
    =
    match set with
    | SetEmpty -> state
    | SetNode(k, l, r, _) -> foldBack folder l (folder k (foldBack folder r state))

let toList<'T when 'T: comparison> (set: SetTree<'T>) : 'T list = foldBack (fun k acc -> k :: acc) set []

let toArray<'T when 'T: comparison> (set: SetTree<'T>) : 'T[] = Array.ofList (toList set)

let ofList<'T when 'T: comparison> (elements: 'T list) : SetTree<'T> =
    List.fold (fun acc x -> add x acc) SetEmpty elements

let ofArray<'T when 'T: comparison> (array: 'T[]) : SetTree<'T> =
    Array.fold (fun acc x -> add x acc) SetEmpty array

let rec count<'T when 'T: comparison> (set: SetTree<'T>) : int =
    match set with
    | SetEmpty -> 0
    | SetNode(_, l, r, _) -> count l + 1 + count r

let rec exists<'T when 'T: comparison> (predicate: 'T -> bool) (set: SetTree<'T>) : bool =
    match set with
    | SetEmpty -> false
    | SetNode(k, l, r, _) -> exists predicate l || predicate k || exists predicate r

let rec forAll<'T when 'T: comparison> (predicate: 'T -> bool) (set: SetTree<'T>) : bool =
    match set with
    | SetEmpty -> true
    | SetNode(k, l, r, _) -> forAll predicate l && predicate k && forAll predicate r

let filter<'T when 'T: comparison> (predicate: 'T -> bool) (set: SetTree<'T>) : SetTree<'T> =
    fold
        (fun acc x ->
            if predicate x then
                add x acc
            else
                acc
        )
        SetEmpty
        set

let partition<'T when 'T: comparison> (predicate: 'T -> bool) (set: SetTree<'T>) : SetTree<'T> * SetTree<'T> =
    filter predicate set, filter (fun x -> not (predicate x)) set

let map<'T, 'U when 'T: comparison and 'U: comparison> (mapping: 'T -> 'U) (set: SetTree<'T>) : SetTree<'U> =
    fold (fun acc x -> add (mapping x) acc) SetEmpty set

let union<'T when 'T: comparison> (set1: SetTree<'T>) (set2: SetTree<'T>) : SetTree<'T> =
    fold (fun acc x -> add x acc) set1 set2

let unionMany<'T when 'T: comparison> (sets: SetTree<'T> list) : SetTree<'T> = List.fold union SetEmpty sets

let intersect<'T when 'T: comparison> (set1: SetTree<'T>) (set2: SetTree<'T>) : SetTree<'T> =
    filter (fun x -> contains x set2) set1

let difference<'T when 'T: comparison> (set1: SetTree<'T>) (set2: SetTree<'T>) : SetTree<'T> =
    filter (fun x -> not (contains x set2)) set1

let isSubset<'T when 'T: comparison> (set1: SetTree<'T>) (set2: SetTree<'T>) : bool =
    forAll (fun x -> contains x set2) set1

let isSuperset<'T when 'T: comparison> (set1: SetTree<'T>) (set2: SetTree<'T>) : bool = isSubset set2 set1

let isProperSubset<'T when 'T: comparison> (set1: SetTree<'T>) (set2: SetTree<'T>) : bool =
    isSubset set1 set2 && count set1 < count set2

let isProperSuperset<'T when 'T: comparison> (set1: SetTree<'T>) (set2: SetTree<'T>) : bool = isProperSubset set2 set1

let rec minElement<'T when 'T: comparison> (set: SetTree<'T>) : 'T =
    match set with
    | SetNode(k, SetEmpty, _, _) -> k
    | SetNode(_, l, _, _) -> minElement l
    | SetEmpty -> invalidArg "s" "Set contains no elements."

let rec maxElement<'T when 'T: comparison> (set: SetTree<'T>) : 'T =
    match set with
    | SetNode(k, _, SetEmpty, _) -> k
    | SetNode(_, _, r, _) -> maxElement r
    | SetEmpty -> invalidArg "s" "Set contains no elements."

// ---- the members of a set (the object first) ----

let memberAdd<'T when 'T: comparison> (set: SetTree<'T>) (value: 'T) : SetTree<'T> = add value set
let memberRemove<'T when 'T: comparison> (set: SetTree<'T>) (value: 'T) : SetTree<'T> = remove value set
let memberContains<'T when 'T: comparison> (set: SetTree<'T>) (value: 'T) : bool = contains value set
let memberCount<'T when 'T: comparison> (set: SetTree<'T>) : int = count set
let memberIsEmpty<'T when 'T: comparison> (set: SetTree<'T>) : bool = isEmpty set
let memberMinimumElement<'T when 'T: comparison> (set: SetTree<'T>) : 'T = minElement set
let memberMaximumElement<'T when 'T: comparison> (set: SetTree<'T>) : 'T = maxElement set
let memberIsSubsetOf<'T when 'T: comparison> (set: SetTree<'T>) (other: SetTree<'T>) : bool = isSubset set other
let memberIsSupersetOf<'T when 'T: comparison> (set: SetTree<'T>) (other: SetTree<'T>) : bool = isSuperset set other
let opAddition<'T when 'T: comparison> (set1: SetTree<'T>) (set2: SetTree<'T>) : SetTree<'T> = union set1 set2
let opSubtraction<'T when 'T: comparison> (set1: SetTree<'T>) (set2: SetTree<'T>) : SetTree<'T> = difference set1 set2

let memberIsProperSubsetOf<'T when 'T: comparison> (set: SetTree<'T>) (other: SetTree<'T>) : bool =
    isProperSubset set other

let memberIsProperSupersetOf<'T when 'T: comparison> (set: SetTree<'T>) (other: SetTree<'T>) : bool =
    isProperSuperset set other

/// `Set.intersectMany sets`: what all of them hold (FSharp.Core raises for no set)
let intersectMany<'T when 'T: comparison> (sets: SetTree<'T> list) : SetTree<'T> =
    match sets with
    | [] -> invalidArg "sets" "The input sequence was empty."
    | first :: rest -> List.fold intersect first rest

/// `Set.toSeq set`: its elements, in order
let toSeq<'T when 'T: comparison> (set: SetTree<'T>) : Fable.Library.Zig.Seq.SeqOf<'T> =
    Fable.Library.Zig.Seq.ofList (toList set)
