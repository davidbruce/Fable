/// .NET's `ConditionalWeakTable<'K, 'V>`, written in F# and compiled by the Zig target itself
/// (see List.fs): keys are held through weak references and found by identity, so the table
/// does not keep them alive; an entry whose key is gone is dropped when the table next grows.
/// (Unlike .NET's, a value that refers to its own key keeps the key alive while it is in the
/// table: there are no ephemerons here.)
module Fable.Library.Zig.ConditionalWeakTable

type ConditionalWeakTableOf<'K, 'V when 'K: not struct> =
    {
        keys: ResizeArray<System.WeakReference<'K>>
        values: ResizeArray<'V>
    }

let create<'K, 'V when 'K: not struct> () : ConditionalWeakTableOf<'K, 'V> =
    {
        keys = ResizeArray()
        values = ResizeArray()
    }

/// The index of `key`'s entry, or -1
let private indexOf<'K, 'V when 'K: not struct> (t: ConditionalWeakTableOf<'K, 'V>) (key: 'K) : int =
    let mutable found = -1
    let mutable i = 0

    while found < 0 && i < t.keys.Count do
        let mutable k = Unchecked.defaultof<'K>

        if t.keys.[i].TryGetTarget(&k) && LanguagePrimitives.PhysicalEquality k key then
            found <- i

        i <- i + 1

    found

/// (the entries whose keys are gone)
let private prune<'K, 'V when 'K: not struct> (t: ConditionalWeakTableOf<'K, 'V>) : unit =
    for i in t.keys.Count - 1 .. -1 .. 0 do
        let mutable k = Unchecked.defaultof<'K>

        if not (t.keys.[i].TryGetTarget(&k)) then
            t.keys.RemoveAt i
            t.values.RemoveAt i

let add<'K, 'V when 'K: not struct> (t: ConditionalWeakTableOf<'K, 'V>) (key: 'K) (value: 'V) : unit =
    if indexOf t key >= 0 then
        raise (System.ArgumentException "An item with the same key has already been added.")

    prune t
    t.keys.Add(System.WeakReference<'K>(key))
    t.values.Add value

let tryFind<'K, 'V when 'K: not struct> (t: ConditionalWeakTableOf<'K, 'V>) (key: 'K) : 'V option =
    match indexOf t key with
    | -1 -> None
    | i -> Some t.values.[i]

let remove<'K, 'V when 'K: not struct> (t: ConditionalWeakTableOf<'K, 'V>) (key: 'K) : bool =
    match indexOf t key with
    | -1 -> false
    | i ->
        t.keys.RemoveAt i
        t.values.RemoveAt i
        true

let clear<'K, 'V when 'K: not struct> (t: ConditionalWeakTableOf<'K, 'V>) : unit =
    t.keys.Clear()
    t.values.Clear()

/// `GetValue(key, createValue)`: the value of `key`, made and added if it has none
let getValue<'K, 'V when 'K: not struct> (t: ConditionalWeakTableOf<'K, 'V>) (key: 'K) (create: 'K -> 'V) : 'V =
    match indexOf t key with
    | -1 ->
        let v = create key
        add t key v
        v
    | i -> t.values.[i]

/// `AddOrUpdate(key, value)`
let addOrUpdate<'K, 'V when 'K: not struct> (t: ConditionalWeakTableOf<'K, 'V>) (key: 'K) (value: 'V) : unit =
    match indexOf t key with
    | -1 -> add t key value
    | i -> t.values.[i] <- value
