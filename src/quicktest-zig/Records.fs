module Records

// Records with mutable fields and records that contain themselves: references to counted
// cells, with an identity, as on .NET. And `ref` cells, which closures can share.
// `run` returns the number of failed checks.

open Helpers

open Fable.Core.Zig

let liveCells () : int = Counters.liveCells ()
let counted () : int = Counters.sharedCounts ()
let counting () : bool = Counters.isCounting ()

let expect (expected: int) (actual: int) : int =
    if actual = expected then
        0
    else
        1

type Counter = { mutable Count: int }

type Holder =
    {
        Target: Counter
        Tag: int
    }

type Node =
    {
        Id: int
        mutable Next: Node option
    }

/// (a record that contains itself and cannot be assigned)
type Chain =
    {
        Value: int
        Rest: Chain option
    }

type Shelf =
    {
        mutable Items: IntList
        mutable Label: int
    }

let bump (c: Counter) : unit = c.Count <- c.Count + 1

// 1. two records hold the same counter: a change through one is seen through the other
let aliasing () : int =
    let c = { Count = 0 }

    let h1 =
        {
            Target = c
            Tag = 1
        }

    let h2 =
        {
            Target = c
            Tag = 2
        }

    bump h1.Target
    bump h2.Target
    bump c
    c.Count * 7 + h1.Tag + h2.Tag - 1

let rec buildChain (n: int) : Node =
    if n = 0 then
        {
            Id = 0
            Next = None
        }
    else
        {
            Id = n
            Next = Some(buildChain (n - 1))
        }

let rec chainSum (n: Node) : int =
    match n.Next with
    | None -> n.Id
    | Some m -> n.Id + chainSum m

let rec last (n: Node) : Node =
    match n.Next with
    | None -> n
    | Some m -> last m

// 2. cutting a chain releases the rest
let relink () : int =
    let head = buildChain 4
    let before = chainSum head
    head.Next <- None
    before * 10 + chainSum head

// 3. a value that was read from a field outlives the field's next value
let valueOutlivesItsField () : int =
    let head = buildChain 3
    let tail = last head

    head.Next <-
        Some
            {
                Id = 100
                Next = None
            }

    tail.Next <-
        Some
            {
                Id = 7
                Next = None
            }

    chainSum tail * 100 + chainSum head * 10 - 30

// 4. appending in place
let appendInPlace () : int =
    let a = buildChain 2
    let b = buildChain 4
    let endOfA = last a
    endOfA.Next <- Some b
    chainSum a + chainSum b - 8

let cut (n: Node) : unit = n.Next <- None

// 5. a value is read from a field, and then a function that is called assigns that field
let readThenCalleeStores () : int =
    let head = buildChain 3

    match head.Next with
    | Some second ->
        cut head
        chainSum second
    | None -> 0

// 6. a walk that only reads does no reference counting
let readOnlyWalk () : int =
    let head = buildChain 50
    let before = counted ()
    let total = chainSum head
    let walked = counted () - before

    total
    + (if counting () then
           walked
       else
           0)

// 7. a record that contains itself and is never assigned
let rec countDown (n: int) : Chain =
    if n = 0 then
        {
            Value = 0
            Rest = None
        }
    else
        {
            Value = n
            Rest = Some(countDown (n - 1))
        }

let rec chainTotal (c: Chain) (acc: int) : int =
    match c.Rest with
    | None -> acc + c.Value
    | Some r -> chainTotal r (acc + c.Value)

let immutableChain () : int =
    let c = countDown 100
    let same = countDown 100 = c
    let other = countDown 99 = c

    chainTotal c 0
    + (if same then
           1
       else
           0)
    + (if other then
           10
       else
           0)

// 8. fields that own a list: assigning gives up the old list
let shelves () : int =
    let s =
        {
            Items = rangeFrom 1 10
            Label = 1
        }

    let first = sumList s.Items
    s.Items <- rangeFrom 1 3
    s.Label <- s.Label + 41
    let kept = s.Items
    s.Items <- Cons(100, s.Items)
    first * 1000 + sumList s.Items + sumList kept + s.Label

// 9. ref cells
let refCells () : int =
    let total = ref 0
    let items = ref Nil

    for i in 1..5 do
        total.Value <- total.Value + i
        items.Value <- Cons(i, items.Value)

    incr total
    let alias = total
    alias := !alias * 2
    total.Value + sumList items.Value

// 10. closures that share a cell, and one that outlives the function that made it
let makeCounter (start: int) : (unit -> int) =
    let n = ref start

    fun () ->
        n.Value <- n.Value + 1
        n.Value

let rec forEach (f: int -> unit) (xs: IntList) : unit =
    match xs with
    | Nil -> ()
    | Cons(h, t) ->
        f h
        forEach f t

let sharedCells () : int =
    let next = makeCounter 10
    let a = next ()
    let b = next ()
    let sum = ref 0
    let seen = ref Nil

    forEach
        (fun x ->
            sum.Value <- sum.Value + x
            seen.Value <- Cons(x * 2, seen.Value)
        )
        (rangeFrom 1 4)

    a * 100 + b + sum.Value * 1000 + sumList seen.Value

// 11. an exception passes a function that holds records
exception Stop of at: int

let rec walkUntil (limit: int) (n: Node) (visited: Counter) : int =
    visited.Count <- visited.Count + 1

    if n.Id = limit then
        raise (Stop n.Id)

    match n.Next with
    | None -> visited.Count
    | Some m -> walkUntil limit m visited

let recordsAndExceptions () : int =
    let visited = { Count = 0 }

    let all = walkUntil -1 (buildChain 5) visited

    let stopped =
        try
            walkUntil 2 (buildChain 5) visited
        with Stop at ->
            at * 100

    all + stopped + visited.Count

let run () : int =
    let before = liveCells ()

    let failed =
        expect 23 (aliasing ())
        + expect 104 (relink ())
        + expect 1700 (valueOutlivesItsField ())
        + expect 15 (appendInPlace ())
        + expect 3 (readThenCalleeStores ())
        + expect 1275 (readOnlyWalk ())
        + expect 5051 (immutableChain ())
        + expect 55154 (shelves ())
        + expect 47 (refCells ())
        + expect 11132 (sharedCells ())
        + expect 216 (recordsAndExceptions ())

    failed
    + (if counting () then
           expect 0 (liveCells () - before)
       else
           0)
