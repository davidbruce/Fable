/// F#'s `Map`, written in F# and compiled by the Zig target itself (see List.fs): a balanced
/// tree ordered by `compare` on the keys, as FSharp.Core's. A program's `Map<'Key, 'Value>`
/// is this `MapTree`. The runtime treats it as a collection: two maps are equal when they
/// hold the same entries, and `%A` writes `map [...]`.
module Fable.Library.Zig.Map

type MapTree<'Key, 'Value> =
    | MapEmpty
    | MapNode of key: 'Key * value: 'Value * left: MapTree<'Key, 'Value> * right: MapTree<'Key, 'Value> * height: int

let private notFound () =
    raise (System.Collections.Generic.KeyNotFoundException "The given key was not present in the dictionary.")

let private noIndex () =
    raise (
        System.Collections.Generic.KeyNotFoundException
            "An index satisfying the predicate was not found in the collection."
    )

let private height (t: MapTree<'Key, 'Value>) : int =
    match t with
    | MapEmpty -> 0
    | MapNode(_, _, _, _, h) -> h

let inline private node
    (k: 'Key)
    (v: 'Value)
    (l: MapTree<'Key, 'Value>)
    (r: MapTree<'Key, 'Value>)
    : MapTree<'Key, 'Value>
    =
    MapNode(k, v, l, r, max (height l) (height r) + 1)

let private rebalance
    (k: 'Key)
    (v: 'Value)
    (l: MapTree<'Key, 'Value>)
    (r: MapTree<'Key, 'Value>)
    : MapTree<'Key, 'Value>
    =
    let hl = height l
    let hr = height r

    if hr > hl + 1 then
        match r with
        | MapNode(rk, rv, rl, rr, _) ->
            if height rl > height rr then
                match rl with
                | MapNode(rlk, rlv, rll, rlr, _) -> node rlk rlv (node k v l rll) (node rk rv rlr rr)
                | MapEmpty -> node k v l r
            else
                node rk rv (node k v l rl) rr
        | MapEmpty -> node k v l r
    elif hl > hr + 1 then
        match l with
        | MapNode(lk, lv, ll, lr, _) ->
            if height lr > height ll then
                match lr with
                | MapNode(lrk, lrv, lrl, lrr, _) -> node lrk lrv (node lk lv ll lrl) (node k v lrr r)
                | MapEmpty -> node k v l r
            else
                node lk lv ll (node k v lr r)
        | MapEmpty -> node k v l r
    else
        node k v l r

let empty<'Key, 'T when 'Key: comparison> () : MapTree<'Key, 'T> = MapEmpty

let isEmpty<'Key, 'T when 'Key: comparison> (table: MapTree<'Key, 'T>) : bool =
    match table with
    | MapEmpty -> true
    | _ -> false

let rec add<'Key, 'T when 'Key: comparison> (key: 'Key) (value: 'T) (table: MapTree<'Key, 'T>) : MapTree<'Key, 'T> =
    match table with
    | MapEmpty -> MapNode(key, value, MapEmpty, MapEmpty, 1)
    | MapNode(k, v, l, r, h) ->
        let c = compare key k

        if c < 0 then
            rebalance k v (add key value l) r
        elif c > 0 then
            rebalance k v l (add key value r)
        else
            MapNode(key, value, l, r, h)

let rec tryFind<'Key, 'T when 'Key: comparison> (key: 'Key) (table: MapTree<'Key, 'T>) : 'T option =
    match table with
    | MapEmpty -> None
    | MapNode(k, v, l, r, _) ->
        let c = compare key k

        if c < 0 then
            tryFind key l
        elif c > 0 then
            tryFind key r
        else
            Some v

let find<'Key, 'T when 'Key: comparison> (key: 'Key) (table: MapTree<'Key, 'T>) : 'T =
    match tryFind key table with
    | Some v -> v
    | None -> notFound ()

let containsKey<'Key, 'T when 'Key: comparison> (key: 'Key) (table: MapTree<'Key, 'T>) : bool =
    match tryFind key table with
    | Some _ -> true
    | None -> false

let rec private spliceOutMin (t: MapTree<'Key, 'T>) : 'Key * 'T * MapTree<'Key, 'T> =
    match t with
    | MapNode(k, v, MapEmpty, r, _) -> k, v, r
    | MapNode(k, v, l, r, _) ->
        let k2, v2, l2 = spliceOutMin l
        k2, v2, rebalance k v l2 r
    | MapEmpty -> failwith "unreachable"

let rec remove<'Key, 'T when 'Key: comparison> (key: 'Key) (table: MapTree<'Key, 'T>) : MapTree<'Key, 'T> =
    match table with
    | MapEmpty -> MapEmpty
    | MapNode(k, v, l, r, _) ->
        let c = compare key k

        if c < 0 then
            rebalance k v (remove key l) r
        elif c > 0 then
            rebalance k v l (remove key r)
        else
            match l, r with
            | MapEmpty, _ -> r
            | _, MapEmpty -> l
            | _ ->
                let sk, sv, r2 = spliceOutMin r
                rebalance sk sv l r2

let change<'Key, 'T when 'Key: comparison>
    (key: 'Key)
    (f: 'T option -> 'T option)
    (table: MapTree<'Key, 'T>)
    : MapTree<'Key, 'T>
    =
    match f (tryFind key table) with
    | Some v -> add key v table
    | None -> remove key table

let rec iterate<'Key, 'T when 'Key: comparison> (action: 'Key -> 'T -> unit) (table: MapTree<'Key, 'T>) : unit =
    match table with
    | MapEmpty -> ()
    | MapNode(k, v, l, r, _) ->
        iterate action l
        action k v
        iterate action r

let rec fold<'Key, 'State, 'T when 'Key: comparison>
    (folder: 'State -> 'Key -> 'T -> 'State)
    (state: 'State)
    (table: MapTree<'Key, 'T>)
    : 'State
    =
    match table with
    | MapEmpty -> state
    | MapNode(k, v, l, r, _) ->
        let s1 = fold folder state l
        fold folder (folder s1 k v) r

let rec foldBack<'Key, 'State, 'T when 'Key: comparison>
    (folder: 'Key -> 'T -> 'State -> 'State)
    (table: MapTree<'Key, 'T>)
    (state: 'State)
    : 'State
    =
    match table with
    | MapEmpty -> state
    | MapNode(k, v, l, r, _) ->
        let s1 = foldBack folder r state
        foldBack folder l (folder k v s1)

let toList<'Key, 'T when 'Key: comparison> (table: MapTree<'Key, 'T>) : ('Key * 'T) list =
    foldBack (fun k v acc -> (k, v) :: acc) table []

let toArray<'Key, 'T when 'Key: comparison> (table: MapTree<'Key, 'T>) : ('Key * 'T)[] = Array.ofList (toList table)

let ofList<'Key, 'T when 'Key: comparison> (elements: ('Key * 'T) list) : MapTree<'Key, 'T> =
    List.fold (fun acc (k: 'Key, v: 'T) -> add k v acc) MapEmpty elements

let ofArray<'Key, 'T when 'Key: comparison> (elements: ('Key * 'T)[]) : MapTree<'Key, 'T> =
    Array.fold (fun acc (k: 'Key, v: 'T) -> add k v acc) MapEmpty elements

let rec count<'Key, 'T when 'Key: comparison> (table: MapTree<'Key, 'T>) : int =
    match table with
    | MapEmpty -> 0
    | MapNode(_, _, l, r, _) -> count l + 1 + count r

let rec exists<'Key, 'T when 'Key: comparison> (predicate: 'Key -> 'T -> bool) (table: MapTree<'Key, 'T>) : bool =
    match table with
    | MapEmpty -> false
    | MapNode(k, v, l, r, _) -> exists predicate l || predicate k v || exists predicate r

let rec forAll<'Key, 'T when 'Key: comparison> (predicate: 'Key -> 'T -> bool) (table: MapTree<'Key, 'T>) : bool =
    match table with
    | MapEmpty -> true
    | MapNode(k, v, l, r, _) -> forAll predicate l && predicate k v && forAll predicate r

let filter<'Key, 'T when 'Key: comparison>
    (predicate: 'Key -> 'T -> bool)
    (table: MapTree<'Key, 'T>)
    : MapTree<'Key, 'T>
    =
    fold
        (fun acc k v ->
            if predicate k v then
                add k v acc
            else
                acc
        )
        MapEmpty
        table

let partition<'Key, 'T when 'Key: comparison>
    (predicate: 'Key -> 'T -> bool)
    (table: MapTree<'Key, 'T>)
    : MapTree<'Key, 'T> * MapTree<'Key, 'T>
    =
    filter predicate table, filter (fun k v -> not (predicate k v)) table

let rec map<'Key, 'T, 'U when 'Key: comparison>
    (mapping: 'Key -> 'T -> 'U)
    (table: MapTree<'Key, 'T>)
    : MapTree<'Key, 'U>
    =
    match table with
    | MapEmpty -> MapEmpty
    | MapNode(k, v, l, r, h) -> MapNode(k, mapping k v, map mapping l, map mapping r, h)

let rec tryPick<'Key, 'T, 'U when 'Key: comparison>
    (chooser: 'Key -> 'T -> 'U option)
    (table: MapTree<'Key, 'T>)
    : 'U option
    =
    match table with
    | MapEmpty -> None
    | MapNode(k, v, l, r, _) ->
        match tryPick chooser l with
        | Some x -> Some x
        | None ->
            match chooser k v with
            | Some x -> Some x
            | None -> tryPick chooser r

let pick<'Key, 'T, 'U when 'Key: comparison> (chooser: 'Key -> 'T -> 'U option) (table: MapTree<'Key, 'T>) : 'U =
    match tryPick chooser table with
    | Some x -> x
    | None -> noIndex ()

let tryFindKey<'Key, 'T when 'Key: comparison>
    (predicate: 'Key -> 'T -> bool)
    (table: MapTree<'Key, 'T>)
    : 'Key option
    =
    tryPick
        (fun k v ->
            if predicate k v then
                Some k
            else
                None
        )
        table

let findKey<'Key, 'T when 'Key: comparison> (predicate: 'Key -> 'T -> bool) (table: MapTree<'Key, 'T>) : 'Key =
    match tryFindKey predicate table with
    | Some k -> k
    | None -> noIndex ()

let keys<'Key, 'T when 'Key: comparison> (table: MapTree<'Key, 'T>) : 'Key list =
    foldBack (fun k _ acc -> k :: acc) table []

let values<'Key, 'T when 'Key: comparison> (table: MapTree<'Key, 'T>) : 'T list =
    foldBack (fun _ v acc -> v :: acc) table []

let rec minKeyValue<'Key, 'T when 'Key: comparison> (table: MapTree<'Key, 'T>) : 'Key * 'T =
    match table with
    | MapNode(k, v, MapEmpty, _, _) -> (k, v)
    | MapNode(_, _, l, _, _) -> minKeyValue l
    | MapEmpty -> invalidArg "table" "The input sequence was empty."

let rec maxKeyValue<'Key, 'T when 'Key: comparison> (table: MapTree<'Key, 'T>) : 'Key * 'T =
    match table with
    | MapNode(k, v, _, MapEmpty, _) -> (k, v)
    | MapNode(_, _, _, r, _) -> maxKeyValue r
    | MapEmpty -> invalidArg "table" "The input sequence was empty."

// ---- the members of a map (the object first) ----

let getItem<'Key, 'Value when 'Key: comparison> (table: MapTree<'Key, 'Value>) (key: 'Key) : 'Value = find key table

let memberAdd<'Key, 'Value when 'Key: comparison>
    (table: MapTree<'Key, 'Value>)
    (key: 'Key)
    (value: 'Value)
    : MapTree<'Key, 'Value>
    =
    add key value table

let memberRemove<'Key, 'Value when 'Key: comparison>
    (table: MapTree<'Key, 'Value>)
    (key: 'Key)
    : MapTree<'Key, 'Value>
    =
    remove key table

let memberContainsKey<'Key, 'Value when 'Key: comparison> (table: MapTree<'Key, 'Value>) (key: 'Key) : bool =
    containsKey key table

let memberTryFind<'Key, 'Value when 'Key: comparison> (table: MapTree<'Key, 'Value>) (key: 'Key) : 'Value option =
    tryFind key table

let memberCount<'Key, 'Value when 'Key: comparison> (table: MapTree<'Key, 'Value>) : int = count table

let memberIsEmpty<'Key, 'Value when 'Key: comparison> (table: MapTree<'Key, 'Value>) : bool = isEmpty table

let memberChange<'Key, 'Value when 'Key: comparison>
    (table: MapTree<'Key, 'Value>)
    (key: 'Key)
    (f: 'Value option -> 'Value option)
    : MapTree<'Key, 'Value>
    =
    change key f table

/// `Map.toSeq table`: its entries, in the order of the keys
let toSeq<'Key, 'T when 'Key: comparison> (table: MapTree<'Key, 'T>) : Fable.Library.Zig.Seq.SeqOf<'Key * 'T> =
    Fable.Library.Zig.Seq.ofList (toList table)
