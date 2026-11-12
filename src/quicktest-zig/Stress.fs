module Stress

// Ownership corner cases: values used several times, consumed on one path only, borrowed
// results that outlive their owners, fields moved out of records, unions, options and tuples,
// loops that overwrite what they hold. Every test also has to free everything it allocated.
// `run` returns the number of failed checks.

#if FABLE_COMPILER
open Fable.Core

[<Emit("@as(i32, @intCast(fable_rt.live()))")>]
let liveCells () : int = nativeOnly

/// (the recursion that builds a list is a loop here; .NET needs a list its stack can hold)
let deep = 100000
#else
let liveCells () : int = 0
let deep = 5000
#endif

type IntList =
    | Nil
    | Cons of head: int * tail: IntList

type Tree =
    | Leaf
    | Node of left: Tree * key: int * right: Tree

/// Non-recursive DU holding a heap list → value union with lifted hooks.
type Msg =
    | Ping
    | Batch of id: int * items: IntList
    | Pair of a: IntList * b: IntList

/// Record holding two heap values → lifted hooks on a value record.
type Bag =
    {
        Name: int
        Left: IntList
        Right: IntList
    }

let rec range (lo: int) (hi: int) : IntList =
    if lo > hi then
        Nil
    else
        Cons(lo, range (lo + 1) hi)

let rec sumList (acc: int) (xs: IntList) : int =
    match xs with
    | Nil -> acc
    | Cons(h, t) -> sumList (acc + h) t

let rec lengthAcc (n: int) (xs: IntList) : int =
    match xs with
    | Nil -> n
    | Cons(_, t) -> lengthAcc (n + 1) t

let length (xs: IntList) : int = lengthAcc 0 xs

let rec append (xs: IntList) (ys: IntList) : IntList =
    match xs with
    | Nil -> ys
    | Cons(h, t) -> Cons(h, append t ys)

let rec rev (acc: IntList) (xs: IntList) : IntList =
    match xs with
    | Nil -> acc
    | Cons(h, t) -> rev (Cons(h, acc)) t

/// Returns a field of a borrowed parameter → must dup the field.
let tailOf (xs: IntList) : IntList =
    match xs with
    | Nil -> Nil
    | Cons(_, t) -> t

/// Returns the parameter itself on one path only.
let pick (flag: bool) (a: IntList) (b: IntList) : IntList =
    if flag then
        a
    else
        b

let headOr (d: int) (xs: IntList) : int =
    match xs with
    | Nil -> d
    | Cons(h, _) -> h

// 1. A borrowed child outlives its parent's last direct use.
let verifyChildOutlivesParent () : int =
    let xs = range 1 10
    let t = tailOf xs // dup'd field; xs dropped right after
    let n = length t
    let ys = append t (range 100 101) // t consumed
    n * 100 + sumList 0 ys + headOr 0 ys

// 2. Same value used in owning position several times in one expression.
let verifyMultiUse () : int =
    let xs = range 1 3
    let ys = append xs (append xs xs) // two dups + one move
    sumList 0 ys + length ys * 10

// 3. Branch-specific consumption with a value used after the branch.
let verifyBranchMix () : int =
    let a = range 1 5 // 15
    let b = range 10 12 // 33
    let chosen = pick (length a > 3) a b // a consumed on one path, b on the other
    let extra = sumList 0 b // b still needed afterwards → must have been dup'd
    sumList 0 chosen * 10 + extra + length chosen * 12

// 4. Value union with heap payloads (lifted union hooks).
let msgWeight (m: Msg) : int =
    match m with
    | Ping -> 1
    | Batch(id, items) -> id * 1000 + sumList 0 items
    | Pair(a, b) -> length a + length b

let unwrap (m: Msg) : IntList =
    match m with
    | Ping -> Nil
    | Batch(_, items) -> items
    | Pair(a, _) -> a // b must be dropped

let verifyValueUnionHooks () : int =
    let m1 = Batch(7, range 1 10)
    let m2 = Pair(range 1 3, range 1 4)
    let w = msgWeight m1 + msgWeight m2 + msgWeight Ping
    let xs = unwrap m2 // moves `a` out of m2, drops `b`
    let ys = unwrap m1
    w + sumList 0 xs + length ys

// 5. Record with two heap fields: read one, move the other out.
let leftOf (b: Bag) : IntList = b.Left

let verifyRecordFields () : int =
    let bag =
        {
            Name = 3
            Left = range 1 5
            Right = range 1 100
        }

    let l = leftOf bag
    let r = bag.Right
    bag.Name * 1000 + sumList 0 l + sumList 0 r

// 6. Options and tuples of heap values.
let splitAt (n: int) (xs: IntList) : IntList * IntList =
    let mutable left = Nil
    let mutable rest = xs

    for _ in 1..n do
        match rest with
        | Nil -> ()
        | Cons(h, t) ->
            left <- Cons(h, left)
            rest <- t

    (rev Nil left, rest)

let tryHead (xs: IntList) : IntList option =
    match xs with
    | Nil -> None
    | Cons(_, _) -> Some xs

let verifyOptionsAndTuples () : int =
    let (a, b) = splitAt 4 (range 1 10)
    let o = tryHead b

    let fromOpt =
        match o with
        | Some ys -> sumList 0 ys
        | None -> 0

    sumList 0 a * 1000
    + fromOpt
    + length b * 10
    + (
        match tryHead Nil with
        | Some _ -> 1
        | None -> 0
    )

// 7. Mutable heap variable overwritten without reading the old value.
let verifyOverwrite () : int =
    let mutable xs = range 1 50
    xs <- range 1 10 // old 50 cells must be dropped first
    let mutable total = 0
    let mutable i = 0

    while i < 3 do
        xs <- rev Nil xs // in-place reuse each round
        total <- total + headOr 0 xs
        i <- i + 1

    total * 100 + sumList 0 xs * 2

// 8. Persistent sharing: an old version stays alive while a new one is built.
let rec insert (k: int) (t: Tree) : Tree =
    match t with
    | Leaf -> Node(Leaf, k, Leaf)
    | Node(l, x, r) ->
        if k < x then
            Node(insert k l, x, r)
        elif x < k then
            Node(l, x, insert k r)
        else
            Node(l, x, r)

let rec treeSum (t: Tree) : int =
    match t with
    | Leaf -> 0
    | Node(l, x, r) -> treeSum l + x + treeSum r

let rec build (lo: int) (hi: int) (t: Tree) : Tree =
    if lo > hi then
        t
    else
        build (lo + 1) hi (insert ((lo * 7) % 31) t)

let verifyPersistence () : int =
    let t1 = build 1 30 Leaf
    let t2 = insert 500 t1 // t1 used again below → path copy
    let t3 = insert 250 t1
    treeSum t1 * 1000 + treeSum t2 - treeSum t3 + 250


// 10. A dead value whose only reference is in a loop body that never runs.
let verifyLoopNeverRuns () : int =
    let xs = range 1 10
    let mutable acc = 0

    for i in 1..0 do
        acc <- acc + sumList i xs

    acc + sumList 0 xs

// 11. Deep structures: drop of a 100k-element list must not overflow the stack.
let verifyDeepDrop () : int =
    let xs = range 1 deep
    let n = length (tailOf (tailOf xs)) + 2
    n

// 12. Borrowed returns (Ante): a borrow of two owners that is consumed later.
let verifyBorrowPromotion () : int =
    let a = range 1 4
    let b = range 10 12
    let c = pick true a b // borrows a and b
    let n = sumList 0 b // b's last direct use
    let d = append c (range 20 21) // c consumed: promoted to owned when its owners die
    sumList 0 d * 100 + n

// 13. A borrowed result escaping through an owned return.
let keepTail () : IntList =
    let xs = range 1 6
    tailOf xs // borrow of a local → must be retained before xs is dropped

let secondTail (xs: IntList) : IntList = tailOf (tailOf xs) // borrowed return through two calls

let verifyBorrowEscapes () : int =
    let t = keepTail ()
    let u = secondTail t
    let v = append u Nil // consumes a borrow of t
    sumList 0 v * 1000 + length t * 10 + length u

// 14. Borrowed field of a value union handed to a consumer, owner dropped early.
let verifyUnionBorrowConsumed () : int =
    let m = Pair(range 1 3, range 4 9)
    let left = unwrap m
    let w = msgWeight m // last direct use of m
    let r = rev Nil left // consumes the borrow
    headOr 0 r * 100 + w


// 15. A value that only a loop uses is freed when the loop has ended.
let verifyLoopIsLastUser () : int =
    let xs = range 1 10
    let mutable total = 0
    let mutable i = 0

    while i < 3 do
        total <- total + sumList 0 xs
        i <- i + 1

    total

// 16. A loop that walks a list it owns and stops early: what is left is freed.
let verifyLoopStopsEarly () : int =
    let mutable cur = range 1 100
    let mutable total = 0

    while headOr 0 cur < 10 do
        total <- total + headOr 0 cur
        cur <- tailOf cur

    total

// 17. An assignment whose value is never read.
let verifyDeadStore () : int =
    let mutable xs = range 1 5
    let n = length xs
    xs <- range 1 20
    n

// 18. A value that is kept on one path of a loop body and given up on the other.
let verifyKeptOnOnePath () : int =
    let mutable best = Nil

    for i in 1..10 do
        let cand = range 1 i

        if length cand % 3 = 0 then
            best <- cand

    length best

// 19. Nested patterns over a list that the function owns: pairs are swapped in place.
let rec swapPairs (xs: IntList) : IntList =
    match xs with
    | Cons(a, Cons(b, rest)) -> Cons(b, Cons(a, swapPairs rest))
    | _ -> xs

let verifyNestedPatterns () : int =
    let xs = swapPairs (range 1 7)
    let shared = range 1 4
    let ys = swapPairs shared
    headOr 0 xs * 1000 + sumList 0 xs * 10 + headOr 0 ys + headOr 0 shared


// 20. A name for part of a value is still read after the variable was given another value.
let verifyNameOutlivesAssignment () : int =
    let mutable cur = range 1 10

    match cur with
    | Nil -> 0
    | Cons(h, t) ->
        cur <- range 1 3
        h + sumList 0 t + sumList 0 t + length cur

// 21. What a test told about a variable no longer holds once the variable is assigned.
let verifyTestThenAssign () : int =
    let mutable cur = Nil
    let mutable n = 0

    for i in 1..4 do
        match cur with
        | Nil -> cur <- range 1 i
        | Cons _ ->
            n <- n + length cur
            cur <- Nil

    n + length cur


let expect (expected: int) (actual: int) : int =
    if actual = expected then
        0
    else
        1

let run () : int =
    let before = liveCells ()

    let failed =
        0
        + expect 1157 (verifyChildOutlivesParent ())
        + expect 108 (verifyMultiUse ())
        + expect 243 (verifyBranchMix ())
        + expect 7079 (verifyValueUnionHooks ())
        + expect 8065 (verifyRecordFields ())
        + expect 10105 (verifyOptionsAndTuples ())
        + expect 2210 (verifyOverwrite ())
        + expect 465500 (verifyPersistence ())
        + expect 55 (verifyLoopNeverRuns ())
        + expect deep (verifyDeepDrop ())
        + expect 5133 (verifyBorrowPromotion ())
        + expect 15053 (verifyBorrowEscapes ())
        + expect 309 (verifyUnionBorrowConsumed ())
        + expect 165 (verifyLoopIsLastUser ())
        + expect 45 (verifyLoopStopsEarly ())
        + expect 5 (verifyDeadStore ())
        + expect 9 (verifyKeptOnOnePath ())
        + expect 2283 (verifyNestedPatterns ())
        + expect 112 (verifyNameOutlivesAssignment ())
        + expect 4 (verifyTestThenAssign ())

    failed + expect 0 (liveCells () - before)
