module Functions

// Function values, lambdas and functions declared inside functions.
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

// ---- functions declared inside functions ----

/// (a helper that uses a variable of its surroundings)
let scaleAndShift (k: int) (a: int) (b: int) : int =
    let scale x = x * k
    scale a + scale b + 1

/// (a recursive one: a loop, with no environment)
let sumDigits (n: int) : int =
    let rec loop acc rest =
        if rest = 0 then
            acc
        else
            loop (acc + rest % 10) (rest / 10)

    loop 0 n

/// (two that call each other)
let isEvenSlowly (n: int) : bool =
    let rec even k =
        if k = 0 then
            true
        else
            odd (k - 1)

    and odd k =
        if k = 0 then
            false
        else
            even (k - 1)

    even n

/// (one that walks a list its surroundings own, and one inside another)
let countAbove (limit: int) (xs: IntList) : int =
    let rec go count rest =
        match rest with
        | Nil -> count
        | Cons(h, t) ->
            let above x = x > limit

            if above h then
                go (count + 1) t
            else
                go count t

    go 0 xs

// ---- functions that take functions ----

let rec mapList (f: int -> int) (xs: IntList) : IntList =
    match xs with
    | Nil -> Nil
    | Cons(h, t) -> Cons(f h, mapList f t)

let rec foldList (f: int -> int -> int) (acc: int) (xs: IntList) : int =
    match xs with
    | Nil -> acc
    | Cons(h, t) -> foldList f (f acc h) t

let rec countIf (p: int -> bool) (xs: IntList) : int =
    match xs with
    | Nil -> 0
    | Cons(h, t) ->
        (if p h then
             1
         else
             0)
        + countIf p t

let applyTwice (f: int -> int) (x: int) : int = f (f x)

let apply2 (f: int -> int -> int) (a: int) (b: int) : int = f a b

let double (x: int) : int = x * 2

let add (a: int) (b: int) : int = a + b

// ---- functions that return functions ----

let adder (n: int) : int -> int = fun x -> x + n

let compose (f: int -> int) (g: int -> int) : int -> int = fun x -> g (f x)

/// (the function that is returned owns the list)
let sumWith (xs: IntList) : int -> int =
    let total = sumList xs
    fun extra -> total + extra + sumList xs

let curriedAdd3 (a: int) : int -> int -> int = fun b -> fun c -> a + b + c

// ---- function values in data ----

type Handler =
    {
        Id: int
        Run: int -> int
    }

type Step =
    | Apply of (int -> int)
    | Skip

let runStep (s: Step) (x: int) : int =
    match s with
    | Apply f -> f x
    | Skip -> x

let sumOf (f: IntList -> int) (xs: IntList) : int = f xs

/// (functions that call each other last run in constant stack; .NET in Debug does not, so
/// it gets a smaller number)
let rec isEvenDeep (n: int) : bool =
    if n = 0 then
        true
    else
        isOddDeep (n - 1)

and isOddDeep (n: int) : bool =
    if n = 0 then
        false
    else
        isEvenDeep (n - 1)

let collatzSteps (start: int) : int =
    let rec whenEven (n: int) (steps: int) : int =
        if n = 1 then
            steps
        elif n % 2 = 0 then
            whenEven (n / 2) (steps + 1)
        else
            whenOdd n steps

    and whenOdd (n: int) (steps: int) : int = whenEven (3 * n + 1) (steps + 1)

    whenEven start 0

/// (function values in reference-counted cells)
type Pipeline =
    | Done
    | Then of (int -> int) * Pipeline

let rec runPipeline (p: Pipeline) (x: int) : int =
    match p with
    | Done -> x
    | Then(f, rest) -> runPipeline rest (f x)

let force (f: unit -> int) : int = f ()

let pickOp (which: int) : (int -> int) option =
    if which = 0 then
        None
    elif which = 1 then
        Some double
    else
        Some(fun x -> x + which)

let applyOr (f: (int -> int) option) (x: int) : int =
    match f with
    | Some g -> g x
    | None -> x

/// (a function declared inside that uses a list of its surroundings, called by name and
/// passed as a value)
let addToEach (xs: IntList) (ys: IntList) : int =
    let plusTotal y = y + sumList xs
    sumList (mapList plusTotal ys) + plusTotal 0

/// (a function that passes itself on)
let rec sumMapped (f: int -> int) (n: int) : int =
    if n = 0 then
        0
    else
        f n + sumMapped f (n - 1)

let moreFunctions () : int =
    let before = liveCells ()
    let offset = 100
    let pipeline = Then(double, Then((fun x -> x + offset), Then(adder 1, Done)))
    let shared = rangeFrom 1 3
    let thunk = fun () -> sumList shared + offset

    let rec triangle n =
        if n = 0 then
            0
        else
            n + sumMapped triangle (n - 1)

    let deep =
        if counting () then
            3000001
        else
            2001

    check (isOddDeep deep && not (isEvenDeep deep) && collatzSteps 27 = 111)
    + check (
        runPipeline pipeline 5 = 111
        && runPipeline pipeline 0 = 101
        && runPipeline Done 9 = 9
    )
    + check (force thunk = 106 && force (fun () -> 7) = 7)
    + check (
        applyOr (pickOp 0) 5 = 5
        && applyOr (pickOp 1) 5 = 10
        && applyOr (pickOp 4) 5 = 9
    )
    + check (addToEach (rangeFrom 1 4) (rangeFrom 1 3) = 46)
    + check (sumMapped double 4 = 20 && sumMapped (fun x -> x * offset) 2 = 300)
    + check (triangle 3 = 7)
    + check (sumList shared = 6)
    // (everything above was freed after its last use)
    + checkCount (liveCells () - before) 0

let run () : int =
    let before = liveCells ()
    let xs = rangeFrom 1 5

    // a lambda that captures nothing needs no environment
    let a0 = allocs ()
    let doubled = mapList (fun x -> x * 2) (rangeFrom 1 5)
    let noEnvironment = allocs () - a0 - 5
    // one that captures a number has one, for as long as it is in use
    let k = 10
    let shifted = mapList (fun x -> x + k) (rangeFrom 1 5)
    let add5 = add 5
    let inc = adder 1
    let incTwice = compose inc inc
    let plusList = sumWith (rangeFrom 1 4)

    let handler =
        {
            Id = 7
            Run = adder 100
        }

    let localAsValue =
        let triple x = x * 3
        sumList (mapList triple xs) + triple 2

    let rec fact n =
        if n <= 1 then
            1
        else
            n * fact (n - 1)

    check (scaleAndShift 3 1 2 = 10)
    + check (sumDigits 12345 = 15)
    + check (isEvenSlowly 10 && not (isEvenSlowly 7))
    + check (countAbove 2 xs = 3)
    + check (sumList doubled = 30)
    + checkCount noEnvironment 0
    + check (sumList shifted = 65)
    + check (sumList (mapList double xs) = 30)
    + check (foldList (fun acc x -> acc + x) 0 xs = 15 && foldList add 100 xs = 115)
    + check (countIf isEven xs = 2 && countIf (fun x -> x > k) xs = 0)
    + check (applyTwice double 3 = 12 && applyTwice (fun x -> x - k) 0 = -20)
    + check (apply2 add 3 4 = 7 && apply2 (fun a b -> a * b) 3 4 = 12)
    + check (add5 10 = 15 && inc 1 = 2 && incTwice 1 = 3)
    + check (plusList 1 = 21 && plusList 2 = 22)
    + check (curriedAdd3 1 2 3 = 6)
    + check (handler.Run handler.Id = 107)
    + check (
        runStep (Apply double) 4 = 8
        && runStep Skip 4 = 4
        && runStep (Apply(adder k)) 4 = 14
    )
    + check (sumOf sumList xs = 15)
    + check (localAsValue = 51)
    + check (fact 5 = 120 && applyTwice fact 3 = 720)
    + check ((xs |> mapList double |> sumList) = 30 && (double >> inc) 4 = 9)
    + moreFunctions ()
    + checkCount (liveCells () - before) 0
