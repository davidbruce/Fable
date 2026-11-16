module Fable.Tests.Zig.DictionaryTests

open System
open System.Collections.Generic
open Fable.Tests.Util
open Fable.Tests.Util.Testing


type MyRefType(i: int) =
    member x.Value = i

type MyRecord = { a: int }

type CountingDictionary() =
    inherit Dictionary<string, int>()

    member this.Increment(key: string) =
        this.[key] <- (if this.ContainsKey key then this.[key] else 0) + 1

type ArrayKeyDictionary() =
    inherit Dictionary<int[], int>()

type R = { i: int; s: string }

[<Fact>]
let ``test Dictionary KeyValuePattern works`` () = // See #509
    let dic = Dictionary<_, _>()

    for i in 1. .. 10. do
        dic.Add(i, i * i)

    let i = ref 0.

    for KeyValue (x, y) in dic do
        i.Value <- y + i.Value

    equal 385. i.Value

[<Fact>]
let ``test Dictionary creation works`` () =
    let dic = Dictionary<_, _>()
    equal 0 dic.Count

[<Fact>]
let ``test Interface IDictionary creation works`` () =
    let dic =
        dict
        <| seq { for i in 1. .. 10. -> i.ToString(), i * i }

    equal 4. dic.["2"]


[<Fact>]
let ``test Dictionary creation from IDictionary works`` () =
    let idic =
        dict
        <| seq { for i in 1..10 -> i.ToString(), i * i }

    let dic = Dictionary<_, _>(idic)
    dic.Add("100", 100)
    equal 10 idic.Count
    equal 11 dic.Count

[<Fact>]
let ``test Dictionaries with IEqualityComparer work`` () =
    let x = MyRefType(4)
    let y = MyRefType(4)
    let z = MyRefType(6)
    let dic = Dictionary<_,_>()
    dic.Add(x, "foo")
    dic.ContainsKey(x) |> equal true
    dic.ContainsKey(y) |> equal false

    let comparer =
        { new IEqualityComparer<MyRefType> with
            member _.Equals(x, y) = x.Value = y.Value
            member _.GetHashCode(x) = x.Value }
    let dic2 = Dictionary<_,_>(comparer)
    dic2.Add(x, "bar")
    dic2.ContainsKey(x) |> equal true
    dic2.ContainsKey(y) |> equal true
    dic2.ContainsKey(z) |> equal false

[<Fact>]
let ``test Interface IDictionary iteration works`` () =
    let dic =
        dict
        <| seq { for i in 1. .. 10. -> i.ToString(), i * i }

    let i = ref 0.

    for kv in dic do
        i.Value <- kv.Value + i.Value

    equal 385. i.Value

[<Fact>]
let ``test Interface IDictionary folding works`` () =
    let dic = dict [ ("A", 1.); ("B", 2.); ("C", 3.) ]

    dic
    |> Seq.fold (fun acc item -> acc + item.Value) 0.
    |> equal 6.

[<Fact>]
let ``test Dictionary iteration works`` () =
    let dic = Dictionary<_, _>()

    for i in 1. .. 10. do
        dic.Add(i, i * i)

    let i = ref 0.

    for kv in dic do
        i.Value <- kv.Value + i.Value

    i.Value + dic.[1.] |> equal 386.

[<Fact>]
let ``test Dictionary folding works`` () =
    let dic = Dictionary<_, _>()

    for i in 1. .. 10. do
        dic.Add(i, i * i)

    dic
    |> Seq.fold (fun acc item -> acc + item.Value) 0.
    |> equal 385.

[<Fact>]
let ``test Dictionary.Count works`` () =
    let dic = Dictionary<_, _>()

    for i in 1. .. 10. do
        dic.Add(i, i * i)

    dic.Count |> equal 10

[<Fact>]
let ``test Dictionary indexer works`` () =
    let dic = Dictionary<string, obj>()
    dic.["A"] <- "Hello"
    dic.["B"] <- 2
    dic.["B"].ToString() |> equal "2"

[<Fact>]
let ``test Dictionary.TryGetValue works`` () =
    let dic1 = dict [ "A", 1 ]
    let dic2 = dict [ "B", "2" ]
    let success1, val1 = dic1.TryGetValue("A")
    let success2, val2 = dic1.TryGetValue("B")
    let success3, val3 = dic2.TryGetValue("B")
    let success4, val4 = dic2.TryGetValue("C")
    equal success1 true
    equal success2 false
    equal success3 true
    equal success4 false
    equal val1 1
    equal val2 0
    equal val3 "2"
    equal val4 null

[<Fact>]
let ``test Dictionary.Keys works`` () =
    let dic = Dictionary<_, _>()
    dic.Add("A", 1)
    dic.Add("B", 2)

    dic.Keys
    |> Seq.fold (fun acc k -> acc + dic.[k]) 0
    |> equal 3

[<Fact>]
let ``test Dictionary.Keys.Count works`` () =
    let dic = Dictionary<_, _>()
    dic.Add("A", 1)
    dic.Add("B", 2)
    dic.Keys.Count |> equal 2

[<Fact>]
let ``test Dictionary.Values works`` () =
    let dic = Dictionary<_, _>()
    dic.Add("A", 1)
    dic.Add("B", 2)
    let i = ref 0

    for value in dic.Values do
        i.Value <- value + i.Value

    i.Value |> equal 3

[<Fact>]
let ``test Dictionary.Values.Count works`` () =
    let dic = Dictionary<_, _>()
    dic.Add("A", 1)
    dic.Add("B", 2)
    dic.Values.Count |> equal 2

[<Fact>]
let ``test Dictionary.Clear works`` () =
    let dic = Dictionary<_, _>()
    dic.Add("A", 1)
    dic.Add("B", 2)
    dic.Clear()
    dic.Count |> equal 0

[<Fact>]
let ``test IDictionary.Clear works`` () = // see #1120
    let dic: IDictionary<_, _> = upcast Dictionary()
    dic.Add("A", 1)
    dic.Add("B", 2)
    dic.Clear()
    dic.Count |> equal 0

[<Fact>]
let ``test Dictionary.Add works`` () =
    let dic = Dictionary<_, _>()
    dic.Add("A", "Hello")
    dic.Add("B", "World!")
    dic.Count |> equal 2

[<Fact>]
let ``test Dictionary.ContainsKey works`` () =
    let dic = Dictionary<_, _>()
    dic.Add("A", "Hello")
    dic.Add("B", "World!")
    dic.ContainsKey("A") |> equal true
    dic.ContainsKey("C") |> equal false

[<Fact>]
let ``test Dictionary.ContainsValue works`` () =
    let dic = Dictionary<_, _>()
    dic.Add("A", "Hello")
    dic.Add("B", "World!")
    dic.ContainsValue("Hello") |> equal true
    dic.ContainsValue("Everybody!") |> equal false

[<Fact>]
let ``test Dictionary.Remove works`` () =
    let dic = Dictionary<_, _>()
    dic.Add("A", "Hello")
    dic.Add("B", "World!")
    dic.ContainsValue("Hello") |> equal true
    dic.Remove("A") |> equal true
    dic.ContainsValue("Hello") |> equal false
    dic.Count |> equal 1

[<Fact>]
let ``test Dictionary.Remove with complex keys works`` () =
    let dic = Dictionary<_, _>()
    dic.Add((0,"A"), "Hello")
    dic.Add((1,"B"), "World!")
    dic.Remove((0,"A")) |> equal true
    dic.Remove((1,"B")) |> equal true
    dic.Count |> equal 0

[<Fact>]
let ``test Dictionary.Remove with records as keys works`` () =
    let x1 = { a = 5 }
    let x2 = { a = 5 }
    let x3 = { a = 10 }
    let x4 = { a = 15 }
    let dict = Dictionary<_, _>()
    dict.Add(x1, "Hello")
    dict.Add(x3, "World!")
    dict.Remove(x2) |> equal true
    dict.Remove(x4) |> equal false
    dict.Count |> equal 1

[<Fact>]
let ``test Dictionary.Remove works with tuples as keys`` () =
    let my_dict = Dictionary((Map [for i in 0..10 do yield (i,i), sprintf "Number: %i" i]))
    my_dict.ContainsKey((0,0)) |> equal true
    my_dict.Remove((0,0)) |> equal true
    my_dict.ContainsKey((0,0)) |> equal false

[<Fact>]
let ``test Dictionary enumeration to KeyValuePair arrays and lists works`` () =
    let dic = Dictionary<string, int>()
    dic.["one"] <- 1
    dic.["two"] <- 2
    dic.["three"] <- 3

    // Test Seq.toArray - this was broken before the fix
    let arrayResult = dic |> Seq.toArray
    arrayResult.Length |> equal 3

    // Test that we get proper KeyValuePair objects, not just keys
    let firstKvp = arrayResult.[0]
    firstKvp.Key |> String.length |> equal (String.length firstKvp.Key) // Key should be a proper string
    firstKvp.Value |> (fun v -> v > 0) |> equal true // Value should be a proper integer

    // Test specific key-value pair access
    let oneKvp = arrayResult |> Array.find (fun kvp -> kvp.Key = "one")
    oneKvp.Key |> equal "one"
    oneKvp.Value |> equal 1

    // Test Seq.toList - this should still work as before
    let listResult = dic |> Seq.toList
    listResult.Length |> equal 3

    let oneKvpFromList = listResult |> List.find (fun kvp -> kvp.Key = "one")
    oneKvpFromList.Key |> equal "one"
    oneKvpFromList.Value |> equal 1

    // Test that both array and list contain the same key-value pairs
    let arrayKeys = arrayResult |> Array.map (fun kvp -> kvp.Key) |> Array.sort
    let listKeys = listResult |> List.map (fun kvp -> kvp.Key) |> List.sort |> List.toArray
    arrayKeys |> equal listKeys

// ---- ported from tests/Js/Main (2026-11-16) ----

type Table<'K, 'V when 'K: equality and 'K: not null> () =

    let dic = new Dictionary<'K,'V>()

    let addKeyValue key value =
        dic.[key] <- value

    member _.add key value =
        addKeyValue key value

    member _.Dic = dic


type DictKey =
    | Int of int
    | Str of string

[<Fact>]
let ``test Dictionary works when keys share a hash`` () =
    let comparer =
        { new IEqualityComparer<string> with
            member _.Equals(x, y) = x = y
            member _.GetHashCode(_) = 1 }
    let dic = Dictionary<_,_>(comparer)
    dic.Add("A", 1)
    dic.Add("B", 2)
    dic.Add("C", 3)
    dic.Count |> equal 3
    dic.["C"] |> equal 3
    dic.ContainsKey("B") |> equal true
    dic.ContainsKey("D") |> equal false
    dic.Remove("B") |> equal true
    dic.Remove("B") |> equal false
    dic.ContainsKey("C") |> equal true
    dic.Count |> equal 2
    throwsAnyError (fun _ -> dic.Add("A", 4))

[<Fact>]
let ``test Dictionary.Count works with indexer insert`` () =
    let dic = Dictionary<string,int>()
    dic.["A"] <- 1
    dic.["B"] <- 2
    dic.Count |> equal 2

[<Fact>]
let ``test Dictionary.Count works with indexer replace`` () =
    let dic = Dictionary<string,int>()
    dic.Add("A", 1)
    dic.["A"] <- 2
    dic.Count |> equal 1
    dic.["A"] |> equal 2

[<Fact>]
let ``test Dictionary works with union keys`` () =
    let dic = Dictionary<DictKey, int>()
    dic.Add(Int 1, 1)
    dic.Add(Str "a", 2)
    dic.[Int 1] |> equal 1
    dic.[Str "a"] |> equal 2
    dic.ContainsKey(Int 1) |> equal true
    dic.ContainsKey(Int 2) |> equal false
    dic.ContainsKey(Str "b") |> equal false
    dic.[Int 1] <- 3
    dic.[Int 1] |> equal 3
    dic.Count |> equal 2
    dic.Remove(Str "a") |> equal true
    dic.ContainsKey(Str "a") |> equal false
    dic.Count |> equal 1

[<Fact>]
let ``test Interface IDictionary.Count works`` () =
    let dic = dict <| seq { for i in 1. .. 10. -> i.ToString(), i*i }
    dic.Count |> equal 10

[<Fact>]
let ``test Interface IDictionary indexer getter works`` () =
    let dic = dict <| seq { for i in 1. .. 10. -> i.ToString(), i*i }
    dic.["2"] |> equal 4.

[<Fact>]
let ``test Interface IDictionary.Keys works`` () =
    let dic = dict <| seq { for i in 1. .. 10. -> i.ToString(), i*i }
    let i = ref ""
    for key in dic.Keys do
       i := key + !i
    !i |> equal "10987654321"

[<Fact>]
let ``test Interface IDictionary.Values works`` () =
    let dic = dict <| seq { for i in 1. .. 10. -> i.ToString(), i*i }
    let i = ref 0.
    for value in dic.Values do
       i := value + !i
    !i |> equal 385.

[<Fact>]
let ``test Interface IDictionary.ContainsKey works`` () =
    let dic = dict <| [ ("A", 1.); ("B", 2.) ]
    dic.ContainsKey("A") |> equal true
    dic.ContainsKey("C") |> equal false

[<Fact>]
let ``test Adding 2 items with the same key throws`` () =
    let dic = Dictionary<_,_>()
    dic.Add("A", 65)
    // throwsError "An item with the same key has already been added. Key: A" (fun _ -> dic.Add("A", 95))
    throwsAnyError (fun _ -> dic.Add("A", 95))

[<Fact>]
let ``test Indexer throws when key not found`` () =
    let dic = Dictionary<_,_>()
    dic.Add("A", 65)
    // throwsError "The given key 'B' was not present in the dictionary." (fun _ -> dic.["B"] |> ignore)
    throwsAnyError (fun () -> dic.["B"])

[<Fact>]
let ``test conversion from array works`` () =
    let dic = [| "A",1; "B",2 |] |> dict
    dic.Values.Count
    |> equal 2

[<Fact>]
let ``test conversion from array works with duplicates`` () =
    let dic = [| "A",1; "A",3; "B",2 |] |> dict
    dic.Values.Count
    |> equal 2

// ---- ported from tests/Js/Main (2026-11-16) ----

[<Fact>]
let ``test Dictionary subclasses work`` () =
    let dic = CountingDictionary()
    dic.Increment "a"
    dic.Increment "a"
    dic.Increment "b"
    dic.["a"] |> equal 2
    dic.Count |> equal 2
    dic.ContainsKey "b" |> equal true
    dic.Remove "b" |> equal true
    dic |> Seq.map (fun kv -> kv.Key, kv.Value) |> List.ofSeq |> equal [ "a", 2 ]

[<Fact>]
let ``test Dictionary compares array keys by reference`` () =
    // See #5165
    let key = [| 1 |]
    let dic = Dictionary<int[], int>()
    dic.[key] <- 1
    dic.[[| 1 |]] <- 2
    dic.Count |> equal 2
    dic.ContainsKey key |> equal true
    dic.ContainsKey [| 1 |] |> equal false
    dic.[key] |> equal 1
    let copy = Dictionary<int[], int>(dic)
    copy.Count |> equal 2
    copy.ContainsKey key |> equal true
    copy.ContainsKey [| 1 |] |> equal false

[<Fact>]
let ``test Dictionary subclasses compare array keys by reference`` () =
    let key = [| 1 |]
    let dic = ArrayKeyDictionary()
    dic.[key] <- 1
    dic.ContainsKey key |> equal true
    dic.ContainsKey [| 1 |] |> equal false

[<Fact>]
let ``test Dictionary compares ResizeArray keys by reference`` () =
    let key = ResizeArray [ 1 ]
    let dic = Dictionary<ResizeArray<int>, int>()
    dic.[key] <- 1
    dic.[ResizeArray [ 1 ]] <- 2
    dic.Count |> equal 2
    dic.ContainsKey key |> equal true
    dic.ContainsKey(ResizeArray [ 1 ]) |> equal false


// ---- ported from tests/Js/Main (2026-11-16, remaining) ----

[<Fact>]
let ``test Dictionary with type as key works`` () =
    // See #2202
    let cache = Dictionary<Type, int>()
    cache.Add(typeof<int>, 1)
    cache.Add(typeof<string>, 2)
    cache.Add(typeof<int64>, 3)
    equal 3 cache.Count
    equal cache.[typeof<int>] 1
    equal cache.[typeof<string>] 2
    equal cache.[typeof<int64>] 3

[<Fact>]
let ``test Check that generics are not duplicated `` () =
    // See #3911
    let table = Table<_,_>()
    table.add "A" 1
    table.add "B" 2
    table.add "C" 3
    table.Dic.Count |> equal 3

[<Fact>]
let ``test Dictionary IReadOnlyCollection.Count works`` () =
    let xs = [| ("A", 1); ("B", 2); ("C", 3) |] |> Array.map KeyValuePair
    let coll = (Dictionary xs) :> IReadOnlyCollection<_>
    coll.Count |> equal 3

[<Fact>]
let ``test Dictionary ICollection.IsReadOnly works`` () =
    let xs = [| ("A", 1); ("B", 2); ("C", 3) |] |> Array.map KeyValuePair
    let coll = (Dictionary xs) :> ICollection<KeyValuePair<_,_>>
    coll.IsReadOnly |> equal false

[<Fact>]
let ``test Dictionary ICollection.Count works`` () =
    let xs = [| ("A", 1); ("B", 2); ("C", 3) |] |> Array.map KeyValuePair
    let coll = (Dictionary xs) :> ICollection<KeyValuePair<_,_>>
    coll.Count |> equal 3

[<Fact>]
let ``test Dictionary ICollection.Contains works`` () =
    let xs = [| ("A", 1); ("B", 2); ("C", 3) |] |> Array.map KeyValuePair
    let coll = (Dictionary xs) :> ICollection<KeyValuePair<_,_>>
    coll.Contains(KeyValuePair("B", 3)) |> equal false
    coll.Contains(KeyValuePair("D", 3)) |> equal false
    coll.Contains(KeyValuePair("B", 2)) |> equal true

[<Fact>]
let ``test Dictionary ICollection.CopyTo works`` () =
    // See #3914
    let xs = [| ("A", 1); ("B", 2); ("C", 3) |] |> Array.map KeyValuePair
    let coll = (Dictionary xs) :> ICollection<KeyValuePair<_,_>>
    let ys = [| ("D", 4); ("E", 5); ("F", 6) |] |> Array.map KeyValuePair
    coll.CopyTo(ys, 0)
    ys = xs |> equal true

[<Fact>]
let ``test Dictionary ICollection.Clear works`` () =
    let xs = [| ("A", 1); ("B", 2); ("C", 3) |] |> Array.map KeyValuePair
    let coll = (Dictionary xs) :> ICollection<KeyValuePair<_,_>>
    coll.Clear()
    coll.Count |> equal 0

[<Fact>]
let ``test Dictionary ICollection.Add works`` () =
    // See #3914
    let xs = [| ("A", 1); ("B", 2); ("C", 3) |] |> Array.map KeyValuePair
    let coll = (Dictionary xs) :> ICollection<KeyValuePair<_,_>>
    throwsAnyError (fun _ -> coll.Add(KeyValuePair("A", 1)))
    throwsAnyError (fun _ -> coll.Add(KeyValuePair("A", 2)))
    coll.Add(KeyValuePair("D", 4))
    coll.Count |> equal 4

[<Fact>]
let ``test Dictionary ICollection.Remove works`` () =
    // See #3914
    let xs = [| ("A", 1); ("B", 2); ("C", 3) |] |> Array.map KeyValuePair
    let coll = (Dictionary xs) :> ICollection<KeyValuePair<_,_>>
    coll.Remove(KeyValuePair("B", 3)) |> equal false
    coll.Remove(KeyValuePair("D", 3)) |> equal false
    coll.Remove(KeyValuePair("B", 2)) |> equal true
    coll.Count |> equal 2

[<Fact>]
let ``test Dictionary with a structural comparer compares array keys by value`` () =
    let dic = Dictionary<int[], int>(HashIdentity.Structural)
    dic.[[| 1 |]] <- 1
    dic.ContainsKey [| 1 |] |> equal true
    (dict [ [| 1 |], 1 ]).ContainsKey [| 1 |] |> equal true
    (readOnlyDict [ [| 1 |], 1 ]).ContainsKey [| 1 |] |> equal true

