module Generics

// Generic types and functions. A generic function is compiled once, for any type; the Zig
// compiler makes the instances.
// `run` returns the number of failed checks.

open Helpers

open Fable.Core.Zig

let liveCells () : int = Counters.liveCells ()
let allocs () : int = Counters.allocations ()
let counting () : bool = Counters.isCounting ()

let check (ok: bool) : int =
    if ok then
        0
    else
        1

let checkCount (actual: int) (expected: int) : int =
    if counting () && actual <> expected then
        1
    else
        0

// ---- generic types ----

type Chain<'T> =
    | End
    | Link of head: 'T * tail: Chain<'T>

type Pair<'A, 'B> =
    {
        First: 'A
        Second: 'B
    }

type Tree<'T> =
    | Leaf
    | Node of left: Tree<'T> * value: 'T * right: Tree<'T>

type Either<'L, 'R> =
    | Left of 'L
    | Right of 'R

// ---- generic functions ----

let identity (x: 'T) : 'T = x

let rec length (xs: Chain<'T>) : int =
    match xs with
    | End -> 0
    | Link(_, t) -> 1 + length t

let rec map (f: 'T -> 'U) (xs: Chain<'T>) : Chain<'U> =
    match xs with
    | End -> End
    | Link(h, t) -> Link(f h, map f t)

let rec fold (f: 'S -> 'T -> 'S) (acc: 'S) (xs: Chain<'T>) : 'S =
    match xs with
    | End -> acc
    | Link(h, t) -> fold f (f acc h) t

let rec revOnto (acc: Chain<'T>) (xs: Chain<'T>) : Chain<'T> =
    match xs with
    | End -> acc
    | Link(h, t) -> revOnto (Link(h, acc)) t

/// (copies `x`: for a value that holds cells, every copy shares them)
let rec replicate (n: int) (x: 'T) : Chain<'T> =
    if n = 0 then
        End
    else
        Link(x, replicate (n - 1) x)

let rec range (lo: int) (hi: int) : Chain<int> =
    if lo > hi then
        End
    else
        Link(lo, range (lo + 1) hi)

let swap (p: Pair<'A, 'B>) : Pair<'B, 'A> =
    {
        First = p.Second
        Second = p.First
    }

let firstOf (p: Pair<'A, 'B>) : 'A = p.First

let orElse (fallback: 'T) (o: 'T option) : 'T =
    match o with
    | Some x -> x
    | None -> fallback

let either (onLeft: 'L -> 'T) (onRight: 'R -> 'T) (e: Either<'L, 'R>) : 'T =
    match e with
    | Left l -> onLeft l
    | Right r -> onRight r

let rec treeSize (t: Tree<'T>) : int =
    match t with
    | Leaf -> 0
    | Node(l, _, r) -> treeSize l + 1 + treeSize r

let rec mapTree (f: 'T -> 'U) (t: Tree<'T>) : Tree<'U> =
    match t with
    | Leaf -> Leaf
    | Node(l, v, r) -> Node(mapTree f l, f v, mapTree f r)

let rec sumTree (t: Tree<int>) : int =
    match t with
    | Leaf -> 0
    | Node(l, v, r) -> sumTree l + v + sumTree r

/// (a function declared inside a generic function)
let countIf (p: 'T -> bool) (xs: Chain<'T>) : int =
    let rec go (n: int) (rest: Chain<'T>) : int =
        match rest with
        | End -> n
        | Link(h, t) ->
            if p h then
                go (n + 1) t
            else
                go n t

    go 0 xs

/// (a function value that captures a value of the type parameter)
let constantly (x: 'T) : int -> 'T = fun _ -> x

let sum (xs: Chain<int>) : int = fold (fun acc x -> acc + x) 0 xs

let compose (f: 'A -> 'B) (g: 'B -> 'C) : 'A -> 'C = fun x -> g (f x)

let applyTwice (f: 'T -> 'T) (x: 'T) : 'T = f (f x)

let pairWith (a: 'A) (b: 'B) : Pair<'A, 'B> =
    {
        First = a
        Second = b
    }

/// (functions declared inside a function that are generic themselves, used at two types)
let innerGenerics (n: int) (flag: bool) : int =
    let twice x = Link(x, Link(x, End))
    let second (p: Pair<'X, 'Y>) : 'Y = p.Second

    let rec count (xs: Chain<'E>) (acc: int) : int =
        match xs with
        | End -> acc
        | Link(_, t) -> count t (acc + 1)

    let numbers = twice n
    let flags = twice flag

    count numbers 0
    + count flags 10
    + second (pairWith flag n)
    + count (twice (twice 'c')) 100

/// (a generic function with a generic function inside)
let lastOr (fallback: 'T) (xs: Chain<'T>) : 'T =
    let rec go (best: 'T) (rest: Chain<'T>) : 'T =
        match rest with
        | End -> best
        | Link(h, t) -> go h t

    let wrap (x: 'W) : 'W option = Some x
    orElse fallback (wrap (go fallback xs))

/// Generic functions used as values: what their type parameters stand for follows from the
/// type they are used at.
let asValues () : int =
    let before = liveCells ()
    let xs = range 1 4
    let pairs = map (pairWith 'k') xs
    let lengths = map length (Link(xs, Link(range 1 2, End)))
    let incThenShow = compose (fun x -> x + 1) (fun x -> x > 3)
    let nested = applyTwice (map (fun x -> x * 2)) xs

    check (sum (map identity xs) = 10 && sum (map (applyTwice (fun x -> x + 1)) xs) = 18)
    + check (sum (map firstOf (map swap pairs)) = 10 && length (map firstOf pairs) = 4)
    + check (sum lengths = 6)
    + check (incThenShow 3 && not (incThenShow 2) && (compose identity identity) 5 = 5)
    + check (sum nested = 40 && applyTwice identity 'z' = 'z')
    + check (fold (fun acc b -> acc + b.Tag) 0 (map (boxOf 3) xs) = 12)
    + check (innerGenerics 5 true = 121)
    + check (lastOr 0 xs = 4 && lastOr 'a' End = 'a')
    + checkCount (liveCells () - before) 0

let numbers () : int =
    let xs = range 1 4
    let doubled = map (fun x -> x * 2) xs

    let pairs =
        map
            (fun x ->
                {
                    First = x
                    Second = x * 100
                }
            )
            (range 1 3)

    let flipped = map (fun (p: Pair<int, int>) -> swap p) pairs
    // `map` over a list nobody else holds rebuilds it in the same cells, when the new
    // elements are laid out as the old ones (decided when the Zig is compiled)
    let a0 = allocs ()
    let bumped = map (fun x -> x + 1) (range 1 8)
    let sameLayout = allocs () - a0 - 8
    let flags = map (fun x -> x > 4) (range 1 8)
    // (a cell with a 64-bit element is bigger: the old cells cannot be used)
    let a1 = allocs ()
    let wide = map (fun x -> int64 x) (range 1 8)
    let otherLayout = allocs () - a1 - 8

    check (sum doubled + length xs = 24)
    + check (fold (fun acc (p: Pair<int, int>) -> acc + p.First * 2 + p.Second) 0 flipped = 1206)
    + check (sum bumped = 44)
    + checkCount sameLayout 0
    + check (countIf identity flags = 4 && length flags = 8)
    + check (fold (fun acc x -> acc + x) 0L wide = 36L)
    + checkCount otherLayout 8
    + check (
        identity 5 = 5
        && identity true
        && firstOf (
            swap
                {
                    First = 1
                    Second = 'x'
                }
        )
            =
            'x'
    )
    + check (orElse 3 (Some 4) = 4 && orElse 3 None = 3)
    + check (
        either
            (fun x -> x + 1)
            (fun b ->
                if b then
                    1
                else
                    0
            )
            (Left 4) =
            5
    )
    + check (
        either
            (fun x -> x + 1)
            (fun b ->
                if b then
                    1
                else
                    0
            )
            (Right true) =
            1
    )
    + check (countIf (fun x -> x % 2 = 0) xs = 2)
    + check (sum (map identity xs) = 10 && (constantly 7) 0 = 7)

/// Elements that are themselves reference counted, a unit element, functions as elements.
let elements () : int =
    let before = liveCells ()
    let a = range 1 3
    let chains = Link(a, Link(Link(9, a), Link(End, End)))
    let again = revOnto End chains
    let copies = replicate 2 (range 1 2)
    let units = replicate 3 ()
    let fns = Link((fun x -> x + 1), Link((fun x -> x * 10), End))
    let tree = Node(Node(Leaf, 1, Leaf), 2, Node(Leaf, 3, Leaf))
    let scaled = mapTree (fun x -> x * 4) tree
    let flags = mapTree (fun x -> x > 4) scaled
    let keep = constantly (range 1 5)

    check (fold (fun acc s -> acc + length s) 0 again = 7 && length chains = 3)
    + check (fold (fun acc s -> acc + length s) 0 copies = 4)
    + check (length units = 3 && length (map (fun () -> 1) units) = 3)
    + check (fold (fun acc f -> f acc) 1 fns = 20)
    + check (sumTree scaled = 24 && treeSize flags = 3)
    + check (sum (keep 0) = 15 && length (keep 1) = 5)
    + check (range 1 3 = range 1 3 && Link(Some 1, End) <> Link(None, End))
    + checkCount (liveCells () - before) 0

/// A generic type and generic functions of another file.
let acrossFiles () : int =
    let before = liveCells ()
    let b = boxOf 7 (range 1 3)
    let lengths = mapBox length b
    let c = mapBox (fun n -> n + 1) (boxOf 1 41)

    check (lengths.Value = 3 && lengths.Tag = 7)
    + check (c.Value = 42 && (boxOf 2 true).Value)
    + checkCount (liveCells () - before) 0

// ---- F#'s own list ----

let rec listLength (xs: 'T list) : int =
    match xs with
    | [] -> 0
    | _ :: t -> 1 + listLength t

let rec listMap (f: 'T -> 'U) (xs: 'T list) : 'U list =
    match xs with
    | [] -> []
    | h :: t -> f h :: listMap f t

let rec listFold (f: 'S -> 'T -> 'S) (acc: 'S) (xs: 'T list) : 'S =
    match xs with
    | [] -> acc
    | h :: t -> listFold f (f acc h) t

let rec listRev (acc: 'T list) (xs: 'T list) : 'T list =
    match xs with
    | [] -> acc
    | h :: t -> listRev (h :: acc) t

let rec upTo (lo: int) (hi: int) : int list =
    if lo > hi then
        []
    else
        lo :: upTo (lo + 1) hi

let firstTwo (xs: int list) : int =
    match xs with
    | a :: b :: _ -> a * 10 + b
    | [ a ] -> a
    | [] -> -1

let lists () : int =
    let before = liveCells ()
    let xs = [ 1; 2; 3; 4 ]
    let doubled = listMap (fun x -> x * 2) xs
    let nested = [ xs; 9 :: xs; [] ]
    let a0 = allocs ()
    let bumped = listMap (fun x -> x + 1) (upTo 1 8)
    let inPlace = allocs () - a0 - 8
    let big = upTo 1 100000

    check (listFold (fun acc x -> acc + x) 0 doubled + listLength xs = 24)
    + check (listFold (fun acc l -> acc + listLength l) 0 nested = 9)
    + check (listRev [] xs = [ 4; 3; 2; 1 ] && listRev [] [] = ([]: int list))
    + check (firstTwo xs = 12 && firstTwo [ 7 ] = 7 && firstTwo [] = -1)
    + check (
        not xs.IsEmpty
        && xs.Head = 1
        && xs.Tail.Head = 2
        && List.isEmpty xs.Tail.Tail.Tail.Tail
    )
    + check (listFold (fun acc x -> acc + x) 0 bumped = 44)
    + checkCount inPlace 0
    + check (listFold (fun acc _ -> acc + 1) 0 big = 100000)
    + check ([ Some 1; None ] = [ Some 1; None ] && [ 1; 2 ] <> [ 1; 3 ] && xs <> [])
    + checkCount (liveCells () - before) 0

let run () : int =
    let before = liveCells ()

    numbers ()
    + asValues ()
    + elements ()
    + acrossFiles ()
    + lists ()
    + checkCount (liveCells () - before) 0
