module Exceptions

// raise, try/with, try/finally and reraise. A function that can raise returns an error to
// its caller, which gives up what it still owns and passes the error on, until a handler
// takes the exception.
// `run` returns the number of failed checks.

open Helpers

#if FABLE_COMPILER
open Fable.Core

[<Emit("@as(i32, @intCast(fable_rt.live()))")>]
let liveCells () : int = nativeOnly

[<Emit("fable_rt.track")>]
let counting () : bool = nativeOnly
#else
let liveCells () : int = 0
let counting () : bool = false
#endif

let expect (expected: int) (actual: int) : int =
    if actual = expected then
        0
    else
        1

type Tree =
    | Leaf
    | Node of left: Tree * value: int * right: Tree

exception ParseError of pos: int * code: int
exception Fatal of items: IntList
exception Plain

let rec treeSize (t: Tree) : int =
    match t with
    | Leaf -> 0
    | Node(l, _, r) -> treeSize l + 1 + treeSize r

// 1. raise deep in a recursion, caught several frames up
let rec sumBelow (xs: IntList) (limit: int) : int =
    match xs with
    | Nil -> 0
    | Cons(h, t) ->
        if h > limit then
            raise (ParseError(h, 1))

        h + sumBelow t limit

let caughtDeep () : int =
    let xs = rangeFrom 1 10

    let ok =
        try
            sumBelow xs 100
        with ParseError(pos, _) ->
            0 - pos

    let bad =
        try
            sumBelow xs 6
        with ParseError(pos, code) ->
            0 - pos * 10 - code

    ok + bad

// 2. every frame on the way out owns a list that has to be freed
let rec buildAndCheck (n: int) (limit: int) : int =
    let mine = rangeFrom 1 n

    if n = 0 then
        raise (ParseError(limit, 2))

    let below = buildAndCheck (n - 1) limit
    below + sumList mine

let framesDropWhatTheyOwn () : int =
    try
        buildAndCheck 5 77
    with ParseError(p, c) ->
        p + c

// 3. a handler takes one case; the others go on
let classify (k: int) : int =
    if k = 1 then
        raise (ParseError(k, 0))
    elif k = 2 then
        raise (Fatal(rangeFrom 1 3))
    elif k = 3 then
        raise Plain
    else
        k

let inner (k: int) : int =
    try
        classify k
    with ParseError(pos, _) ->
        100 + pos

let outer (k: int) : int =
    try
        inner k
    with
    | Fatal items -> 200 + sumList items
    | Plain -> 300

let handlerSelection () : int = outer 1 + outer 2 + outer 3 + outer 4

// 4. reraise, and a handler that raises something else
let relabel (k: int) : int =
    try
        classify k
    with
    | Plain -> reraise ()
    | Fatal items -> raise (ParseError(sumList items, 9))

let reraises () : int =
    let a =
        try
            relabel 3
        with
        | Plain -> 1
        | _ -> 0

    let b =
        try
            relabel 2
        with
        | ParseError(p, c) -> p * 10 + c
        | _ -> 0

    a + b

// 5. try/finally runs on both exits
let withFinally (k: int) : int =
    let mutable trace = 0

    let result =
        try
            try
                trace <- trace * 10 + 3
                classify k
            finally
                trace <- trace * 10 + 4
        with Plain ->
            7

    trace * 10 + result

let finallyRuns () : int = withFinally 5 + withFinally 3

// 6. a raise while a structure is half built
let rec grow (d: int) (bad: int) : Tree =
    if d = 0 then
        Leaf
    elif d = bad then
        raise (ParseError(d, 5))
    else
        Node(grow (d - 1) 0, d, grow (d - 1) bad)

let raiseWhileBuilding () : int =
    let failed =
        try
            treeSize (grow 4 2)
        with ParseError(p, c) ->
            p * 10 + c

    failed + treeSize (grow 3 0)

// 7. nested try: the inner handler raises, the outer one catches
let nested (k: int) : int =
    try
        try
            classify k
        with ParseError(pos, _) ->
            raise (Fatal(rangeFrom 1 pos))
    with
    | Fatal items -> sumList items + 40
    | Plain -> 50

let nestedHandlers () : int = nested 1 + nested 3 + nested 7

// 8. a value used in the body, in the handler and after the try
let keepAcross (k: int) : int =
    let xs = rangeFrom 1 4

    let r =
        try
            classify k + sumList xs
        with ParseError _ ->
            sumList xs * 2

    r + sumList xs

let keptForHandler () : int = keepAcross 1 + keepAcross 9

// 9. an argument moved into a function that raises with it as the payload
let failWith (xs: IntList) : int = raise (Fatal xs)

let payloadMoves () : int =
    try
        failWith (rangeFrom 1 5)
    with
    | Fatal items -> sumList items
    | _ -> -1

// 10. an exception raised in a function value, while the caller is building a list in a loop
let rec mapList (f: int -> int) (xs: IntList) : IntList =
    match xs with
    | Nil -> Nil
    | Cons(h, t) -> Cons(f h, mapList f t)

let raisedInLambda () : int =
    let limit = 3

    let checkedDouble x =
        if x > limit then
            raise (ParseError(x, 4))
        else
            x * 2

    let ok = sumList (mapList checkedDouble (rangeFrom 1 3))

    let bad =
        try
            sumList (mapList checkedDouble (rangeFrom 1 8))
        with ParseError(p, c) ->
            p * 100 + c

    ok + bad

// 11. an exception of another file, raised there and handled here; and one that passes
//     through a function of this file that has nothing to do with it
let passesThrough (limit: int) (xs: IntList) : int =
    let copy = mapList (fun x -> x) xs
    sumChecked limit copy + 1

let acrossFiles () : int =
    let fine = passesThrough 100 (rangeFrom 1 5)

    let tooBig =
        try
            passesThrough 9 (rangeFrom 1 5)
        with TooBig(limit, value) ->
            limit * 100 + value

    let direct =
        try
            addChecked 5 3 4
        with
        | ParseError _ -> -1
        | TooBig(_, value) -> value

    fine + tooBig + direct

// 12. an exception as a value: built, passed around, examined and raised later
let describe (e: exn) : int =
    match e with
    | ParseError(p, c) -> p * 10 + c
    | Fatal items -> sumList items
    | _ -> -1

let asValue () : int =
    let e = ParseError(4, 2)
    let f = Fatal(rangeFrom 1 4)

    let again =
        try
            raise e
        with x ->
            describe x

    describe e + describe f + describe Plain + again

// 13. raising in a loop, with a value the loop still owns
let firstAbove (limit: int) (xs: IntList) : int =
    let mutable rest = xs
    let mutable seen = 0

    while not (rest = Nil) do
        match rest with
        | Cons(h, t) ->
            if h > limit then
                raise (ParseError(h, seen))

            seen <- seen + 1
            rest <- t
        | Nil -> ()

    -1

let raisedInLoop () : int =
    let none = firstAbove 10 (rangeFrom 1 5)

    let found =
        try
            firstAbove 3 (rangeFrom 1 5)
        with ParseError(p, c) ->
            p * 10 + c

    none + found

// 14. a generic function that raises
let rec nth (n: int) (xs: 'T list) : 'T =
    match xs with
    | [] -> raise (ParseError(n, 6))
    | h :: t ->
        if n = 0 then
            h
        else
            nth (n - 1) t

let genericRaises () : int =
    let a = nth 1 [ 10; 20; 30 ]

    let b =
        try
            sumList (nth 5 [ rangeFrom 1 2; rangeFrom 1 3 ])
        with ParseError(p, c) ->
            p * 10 + c

    a + b

let run () : int =
    let before = liveCells ()

    let failed =
        expect -16 (caughtDeep ())
        + expect 79 (framesDropWhatTheyOwn ())
        + expect 611 (handlerSelection ())
        + expect 70 (reraises ())
        + expect 692 (finallyRuns ())
        + expect 32 (raiseWhileBuilding ())
        + expect 98 (nestedHandlers ())
        + expect 59 (keptForHandler ())
        + expect 15 (payloadMoves ())
        + expect 416 (raisedInLambda ())
        + expect 935 (acrossFiles ())
        + expect 93 (asValue ())
        + expect 42 (raisedInLoop ())
        + expect 56 (genericRaises ())

    failed
    + (if counting () then
           expect 0 (liveCells () - before)
       else
           0)
