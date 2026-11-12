module Cycles

// Structures that reach themselves: reference counting alone never frees them, the cycle
// collector does. A structure is freed when the last reference to it from outside goes.
// `run` returns the number of failed checks.

open Helpers

#if FABLE_COMPILER
open Fable.Core

[<Emit("@as(i32, @intCast(fable_rt.live()))")>]
let liveCells () : int = nativeOnly

/// free every cycle that is dead now
[<Emit("_ = fable_rt.collect()")>]
let collect () : unit = nativeOnly

[<Emit("fable_rt.track")>]
let counting () : bool = nativeOnly
#else
let liveCells () : int = 0
let collect () : unit = ()
let counting () : bool = false
#endif

let expect (expected: int) (actual: int) : int =
    if actual = expected then
        0
    else
        1

/// A doubly linked node: the classic cycle.
type Node =
    {
        Id: int
        mutable Next: Node option
        mutable Prev: Node option
    }

let link (a: Node) (b: Node) : unit =
    a.Next <- Some b
    b.Prev <- Some a

let rec extend (first: Node) (prev: Node) (k: int) (n: int) : unit =
    if k > n then
        link prev first
    else
        let node =
            {
                Id = k
                Next = None
                Prev = None
            }

        link prev node
        extend first node (k + 1) n

/// A doubly linked ring of n nodes: every node is on two cycles.
let ring (n: int) : Node =
    let first =
        {
            Id = 1
            Next = None
            Prev = None
        }

    extend first first 2 n
    first

let rec walk (cur: Node) (steps: int) : int =
    if steps = 0 then
        0
    else
        match cur.Next with
        | Some nx -> cur.Id + walk nx (steps - 1)
        | None -> cur.Id

// 1. a node that points at itself
let selfLoop () : int =
    let n =
        {
            Id = 7
            Next = None
            Prev = None
        }

    n.Next <- Some n

    match n.Next with
    | Some m -> m.Id
    | None -> 0

// 2. a ring
let rings () : int =
    let r = ring 5
    walk r 10

// 3. a cycle that is still referenced survives a collection
let liveCycleSurvives () : int =
    let r = ring 4
    collect ()
    let a = walk r 4
    collect ()
    a + walk r 8

type Peer =
    {
        Name: int
        Notes: IntList
        mutable Other: Peer option
    }

// 4. a dead cycle gives up what it holds outside itself
let deadCycleReleasesWhatItHolds () : int =
    let notes = rangeFrom 1 3

    let a =
        {
            Name = 1
            Notes = notes
            Other = None
        }

    let b =
        {
            Name = 2
            Notes = notes
            Other = None
        }

    a.Other <- Some b
    b.Other <- Some a
    a.Name + b.Name + sumList notes

let makeDeadPairPointingAt (keeper: Node) : int =
    let a =
        {
            Id = 1
            Next = None
            Prev = Some keeper
        }

    let b =
        {
            Id = 2
            Next = Some a
            Prev = None
        }

    a.Next <- Some b
    a.Id + b.Id

// 5. a dead cycle points at something that lives on
let deadCyclePointsAtLiveObject () : int =
    let keeper =
        {
            Id = 100
            Next = None
            Prev = None
        }

    let s = makeDeadPairPointingAt keeper
    collect ()
    s + keeper.Id

let rec churn (k: int) (acc: int) : int =
    if k = 0 then
        acc
    else
        let r = ring 4
        let id = r.Id
        churn (k - 1) (acc + id)

// 6. garbage cycles do not pile up: no collection is asked for here
let automatic () : int =
    let before = liveCells ()
    let total = churn 2000 0
    let left = liveCells () - before

    total
    + (if left < 1000 then
           1
       else
           0)

let rec buildChain (n: int) : Node =
    if n = 0 then
        {
            Id = 0
            Next = None
            Prev = None
        }
    else
        {
            Id = n
            Next = Some(buildChain (n - 1))
            Prev = None
        }

let rec chainSum (n: Node) : int =
    match n.Next with
    | None -> n.Id
    | Some m -> n.Id + chainSum m

let chainTotal (n: int) : int =
    let chain = buildChain n
    chainSum chain

// 7. a type that can form cycles, used without any, is freed at once by its counts
let acyclicUse () : int =
    let before = liveCells ()
    let s = chainTotal 50
    s + (liveCells () - before) * 1000

// 8. a generic reference record, a cycle, and an exception that leaves the function that
//    owns the cycle
type Cell<'T> =
    {
        mutable Value: 'T
        mutable Link: Cell<'T> option
    }

exception Broken of size: int

let tie (a: Cell<'T>) (b: Cell<'T>) : unit =
    a.Link <- Some b
    b.Link <- Some a

let risky (k: int) : int =
    let a =
        {
            Value = rangeFrom 1 k
            Link = None
        }

    let b =
        {
            Value = Nil
            Link = None
        }

    tie a b

    if k > 3 then
        raise (Broken k)

    sumList a.Value

let genericCycleAndException () : int =
    let ok = risky 3

    let bad =
        try
            risky 5
        with Broken k ->
            k * 10

    ok + bad

// 9. a tree whose nodes know their parent, with the children in an F# list
type Folder =
    {
        Size: int
        mutable Parent: Folder option
        mutable Children: Folder list
    }

let addChild (parent: Folder) (size: int) : Folder =
    let child =
        {
            Size = size
            Parent = Some parent
            Children = []
        }

    parent.Children <- child :: parent.Children
    child

let rec totalSize (f: Folder) : int =
    let rec sumAll (fs: Folder list) (acc: int) : int =
        match fs with
        | [] -> acc
        | h :: t -> sumAll t (acc + totalSize h)

    sumAll f.Children f.Size

let rec depthOf (f: Folder) : int =
    match f.Parent with
    | None -> 0
    | Some p -> 1 + depthOf p

let folders () : int =
    let root =
        {
            Size = 1
            Parent = None
            Children = []
        }

    let a = addChild root 10
    let b = addChild root 20
    let c = addChild a 100
    totalSize root + depthOf c * 1000 + depthOf b * 10000

// 10. an object that holds a function which uses the object
type Button =
    {
        Label: int
        mutable Clicks: int
        mutable OnClick: (int -> int) option
    }

let click (b: Button) (x: int) : int =
    match b.OnClick with
    | Some f -> f x
    | None -> -1

let buttons () : int =
    let b =
        {
            Label = 5
            Clicks = 0
            OnClick = None
        }

    b.OnClick <-
        Some(fun x ->
            b.Clicks <- b.Clicks + 1
            x + b.Label + b.Clicks
        )

    let first = click b 10
    let second = click b 10
    first * 100 + second + b.Clicks * 10000

// 11. a function that refers to itself through a ref cell
let selfReferringFunction () : int =
    let self: (int -> int) option ref = ref None

    let countDown n =
        if n = 0 then
            0
        else
            match self.Value with
            | Some f -> 1 + f (n - 1)
            | None -> -100

    self.Value <- Some countDown
    countDown 5

// 12. a cycle that an exception carries out of the function that made it
exception Carrying of Node

let raiseRing (n: int) : int = raise (Carrying(ring n))

let exceptionHoldsCycle () : int =
    try
        raiseRing 6
    with Carrying r ->
        walk r 12

let run () : int =
    let before = liveCells ()

    let failed =
        expect 7 (selfLoop ())
        + expect 30 (rings ())
        + expect 30 (liveCycleSurvives ())
        + expect 9 (deadCycleReleasesWhatItHolds ())
        + expect 103 (deadCyclePointsAtLiveObject ())
        + expect 1275 (acyclicUse ())
        + expect 56 (genericCycleAndException ())
        + expect 12131 (folders ())
        + expect 21617 (buttons ())
        + expect 5 (selfReferringFunction ())
        + expect 42 (exceptionHoldsCycle ())
        + (if counting () then
               expect 2001 (automatic ())
           else
               expect 2000 (automatic () - 1))

    collect ()

    failed
    + (if counting () then
           expect 0 (liveCells () - before)
       else
           0)
