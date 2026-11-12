module Heap

// Recursive unions: reference-counted cells, with borrowed parameters, moves instead of
// copies, and cells that are built in again when their last owner takes them apart.
// `run` returns the number of failed checks.

open Helpers

open Fable.Core.Zig

let liveCells () : int = Counters.liveCells ()
let allocs () : int = Counters.allocations ()
let reuses () : int = Counters.reuses ()
let counted () : int = Counters.sharedCounts ()
let counting () : bool = Counters.isCounting ()
#if FABLE_COMPILER
let native = true
#else
let native = false
#endif

let check (ok: bool) : int =
    if ok then
        0
    else
        1

/// a check on the runtime's counters: under .NET there is nothing to count
let checkCount (actual: int) (expected: int) : int =
    if counting () && actual <> expected then
        1
    else
        0

// ---- lists ----

let rec length (acc: int) (xs: IntList) : int =
    match xs with
    | Nil -> acc
    | Cons(_, t) -> length (acc + 1) t

let rec sumAcc (acc: int) (xs: IntList) : int =
    match xs with
    | Nil -> acc
    | Cons(h, t) -> sumAcc (acc + h) t

let rec mapDouble (xs: IntList) : IntList =
    match xs with
    | Nil -> Nil
    | Cons(h, t) -> Cons(h * 2, mapDouble t)

let rec revOnto (acc: IntList) (xs: IntList) : IntList =
    match xs with
    | Nil -> acc
    | Cons(h, t) -> revOnto (Cons(h, acc)) t

let rec append (xs: IntList) (ys: IntList) : IntList =
    match xs with
    | Nil -> ys
    | Cons(h, t) -> Cons(h, append t ys)

let rec keepEven (xs: IntList) : IntList =
    match xs with
    | Nil -> Nil
    | Cons(h, t) ->
        if h % 2 = 0 then
            Cons(h, keepEven t)
        else
            keepEven t

let isNil (xs: IntList) : bool =
    match xs with
    | Nil -> true
    | Cons _ -> false

let headOr (d: int) (xs: IntList) : int =
    match xs with
    | Nil -> d
    | Cons(h, _) -> h

/// (the result is a borrow of the argument)
let secondTail (xs: IntList) : IntList = tailOf (tailOf xs)

let uncons (xs: IntList) : (int * IntList) option =
    match xs with
    | Nil -> None
    | Cons(h, t) -> Some(h, t)

let buildDown (n: int) : IntList =
    let mutable acc = Nil

    for i in 1..n do
        acc <- Cons(i, acc)

    acc

let sumByLoop (xs: IntList) : int =
    let mutable cur = xs
    let mutable total = 0

    while not (isNil cur) do
        total <- total + headOr 0 cur
        cur <- tailOf cur

    total

let lists () : int =
    let before = liveCells ()
    let xs = rangeFrom 1 100
    // sumList is in another file and borrows its argument: nothing is counted for the call
    let c0 = counted ()
    let total = sumList xs
    let acrossFiles = counted () - c0
    let n = length 0 xs
    // xs is still needed below, so mapDouble works on a shared list and must copy
    let a0 = allocs ()
    let doubled = mapDouble xs
    let copied = allocs () - a0
    let s2 = sumAcc 0 doubled
    let s1 = sumAcc 0 xs
    // this list has one owner, which gives it up: every cell is built in again
    let a1 = allocs ()
    let r1 = reuses ()
    let again = mapDouble (rangeFrom 1 50)
    let fresh = allocs () - a1
    let reused = reuses () - r1
    let s3 = sumAcc 0 again
    let rev = revOnto Nil (rangeFrom 1 5)
    let joined = append (rangeFrom 1 3) (rangeFrom 4 6)
    let evens = keepEven (rangeFrom 1 10)

    check (total = 5050 && n = 100)
    + checkCount acrossFiles 0
    + check (s2 = 10100 && s1 = 5050)
    + checkCount copied 100
    + check (s3 = 2550)
    + checkCount fresh 50
    + checkCount reused 50
    + check (headOr 0 rev = 5 && sumAcc 0 rev = 15 && length 0 rev = 5)
    + check (length 0 joined = 6 && sumAcc 0 joined = 21)
    + check (length 0 evens = 5 && sumAcc 0 evens = 30)
    + check (headOr -1 Nil = -1 && isNil Nil && not (isNil rev))
    + check (headOr 0 (secondTail (rangeFrom 1 5)) = 3)
    + check (sumByLoop (buildDown 10) = 55 && headOr 0 (buildDown 10) = 10)
    + check (
        match uncons (rangeFrom 7 9) with
        | Some(h, t) -> h = 7 && sumAcc 0 t = 17
        | None -> false
    )
    + check (uncons Nil = None)
    + check (
        rangeFrom 1 5 = rangeFrom 1 5
        && rangeFrom 1 5 <> rangeFrom 1 6
        && rangeFrom 1 0 = Nil
    )
    // a value is freed after its last use, not at the end of its scope: only the two lists
    // that this line still reads are allocated now
    + checkCount (liveCells () - before - length 0 xs - length 0 doubled) 0

/// Long lists: building, measuring and freeing one takes loops, not recursion. (.NET does
/// not build a list in a loop, so it gets a shorter one.)
let longLists () : int =
    let n =
        if native then
            1000000
        else
            5000

    let xs = rangeFrom 1 n
    let ys = incAll xs
    check (length 0 ys = n) + check (headOr 0 ys = 2)

// ---- trees ----

type Tree =
    | Leaf
    | Node of left: Tree * value: int * right: Tree

let rec insert (x: int) (t: Tree) : Tree =
    match t with
    | Leaf -> Node(Leaf, x, Leaf)
    | Node(l, v, r) ->
        if x < v then
            Node(insert x l, v, r)
        elif x > v then
            Node(l, v, insert x r)
        else
            t

let rec sumTree (t: Tree) : int =
    match t with
    | Leaf -> 0
    | Node(l, v, r) -> sumTree l + v + sumTree r

let rec depth (t: Tree) : int =
    match t with
    | Leaf -> 0
    | Node(l, _, r) ->
        let dl = depth l
        let dr = depth r

        1
        + (if dl > dr then
               dl
           else
               dr)

let rec mirror (t: Tree) : Tree =
    match t with
    | Leaf -> Leaf
    | Node(l, v, r) -> Node(mirror r, v, mirror l)

let rec contains (x: int) (t: Tree) : bool =
    match t with
    | Leaf -> false
    | Node(l, v, r) ->
        if x = v then
            true
        elif x < v then
            contains x l
        else
            contains x r

let rec toList (t: Tree) (acc: IntList) : IntList =
    match t with
    | Leaf -> acc
    | Node(l, v, r) -> toList l (Cons(v, toList r acc))

let treeOf (n: int) : Tree =
    let mutable t = Leaf
    let mutable x = 7

    for _ in 1..n do
        t <- insert x t
        x <- (x * 31 + 11) % 1009

    t

let trees () : int =
    let before = liveCells ()
    let t = treeOf 200
    let total = sumTree t
    let d = depth t
    let sorted = toList t Nil
    // a tree with one owner is updated in place: the cells on the path are built in again
    let t1 = treeOf 200
    let r0 = reuses ()
    let a1 = allocs ()
    let t2 = insert 2000 t1
    let reusedOnPath = reuses () - r0
    let insertAllocs = allocs () - a1
    let a0 = allocs ()
    let m = mirror (treeOf 200)
    let mirrorAllocs = allocs () - a0

    check (contains 7 t && not (contains 5000 t))
    + check (sumAcc 0 sorted = total && length 0 sorted > 100)
    + check (d > 5 && d < 200)
    + check (contains 2000 t2 && sumTree t2 = total + 2000)
    + check (not (counting ()) || reusedOnPath > 0)
    + checkCount insertAllocs 1
    + check (sumTree m = total && depth m = d)
    // (mirroring allocates nothing beyond what building the tree did)
    + checkCount (mirrorAllocs - length 0 sorted) 0
    + check (insert 1 Leaf = Node(Leaf, 1, Leaf) && insert 1 Leaf <> Leaf)
    // (the trees were freed after their last use; only `sorted` is still read here)
    + checkCount (liveCells () - before) (length 0 sorted)

// ---- nested patterns, several types ----

type Expr =
    | Num of int
    | Add of Expr * Expr
    | Mul of Expr * Expr
    | Neg of Expr

let rec eval (e: Expr) : int =
    match e with
    | Num n -> n
    | Add(a, b) -> eval a + eval b
    | Mul(a, b) -> eval a * eval b
    | Neg a -> -(eval a)

let rec simplify (e: Expr) : Expr =
    match e with
    | Add(Num 0, x) -> simplify x
    | Add(x, Num 0) -> simplify x
    | Mul(Num 1, x) -> simplify x
    | Mul(x, Num 1) -> simplify x
    | Mul(Num 0, _) -> Num 0
    | Neg(Neg x) -> simplify x
    | Add(a, b) -> Add(simplify a, simplify b)
    | Mul(a, b) -> Mul(simplify a, simplify b)
    | Neg a -> Neg(simplify a)
    | Num n -> Num n

let rec size (e: Expr) : int =
    match e with
    | Num _ -> 1
    | Add(a, b) -> 1 + size a + size b
    | Mul(a, b) -> 1 + size a + size b
    | Neg a -> 1 + size a

/// (two types that contain each other)
type Rose = | Rose of label: int * children: Forest

and Forest =
    | NoTrees
    | Trees of first: Rose * rest: Forest

let rec sumRose (r: Rose) : int =
    match r with
    | Rose(n, kids) -> n + sumForest kids

and sumForest (f: Forest) : int =
    match f with
    | NoTrees -> 0
    | Trees(r, rest) -> sumRose r + sumForest rest

/// (plain values that hold cells)
type Stack =
    {
        Items: IntList
        Count: int
    }

type Batch =
    | Many of IntList
    | One of int
    | Nothing

let push (x: int) (s: Stack) : Stack =
    {
        Items = Cons(x, s.Items)
        Count = s.Count + 1
    }

let pop (s: Stack) : (int * Stack) option =
    match s.Items with
    | Nil -> None
    | Cons(h, t) ->
        Some(
            h,
            {
                Items = t
                Count = s.Count - 1
            }
        )

let batchSum (b: Batch) : int =
    match b with
    | Many xs -> sumAcc 0 xs
    | One x -> x
    | Nothing -> 0

let firstOrEmpty (xs: IntList option) : IntList =
    match xs with
    | Some l -> l
    | None -> Nil

let mixed () : int =
    let before = liveCells ()
    let e = Add(Mul(Num 1, Add(Num 0, Num 5)), Neg(Neg(Mul(Num 3, Num 4))))
    let v = eval e
    let n = size e
    let s = simplify e

    let rose =
        Rose(1, Trees(Rose(2, NoTrees), Trees(Rose(3, Trees(Rose(4, NoTrees), NoTrees)), NoTrees)))

    let empty =
        {
            Items = Nil
            Count = 0
        }

    let st = push 3 (push 2 (push 1 empty))

    let popped =
        match pop st with
        | Some(top, rest) -> top * 10 + rest.Count
        | None -> -1

    check (v = 17 && n = 11)
    + check (eval s = 17 && size s = 5)
    + check (s = Add(Num 5, Mul(Num 3, Num 4)))
    + check (sumRose rose = 10)
    + check (st.Count = 3 && sumAcc 0 st.Items = 6 && popped = 32)
    + check (pop empty = None)
    + check (
        batchSum (Many(rangeFrom 1 4)) = 10
        && batchSum (One 5) = 5
        && batchSum Nothing = 0
    )
    + check (Many(rangeFrom 1 2) = Many(rangeFrom 1 2) && Many Nil <> Nothing)
    + check (sumAcc 0 (firstOrEmpty (Some(rangeFrom 1 3))) = 6 && isNil (firstOrEmpty None))
    + checkCount (liveCells () - before - size e - size s) 0

/// Everything the tests above allocated has been freed again.
let run () : int =
    let before = liveCells ()
    let failed = lists () + longLists () + trees () + mixed ()
    failed + checkCount (liveCells () - before) 0
