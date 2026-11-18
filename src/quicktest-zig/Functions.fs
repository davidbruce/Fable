module Functions

// Function values, lambdas and functions declared inside functions.
// `run` returns the number of failed checks.

open Helpers

open Fable.Core.Zig

let liveCells () : int = Counters.liveCells ()
let allocs () : int = Counters.allocations ()
let counted () : int = Counters.sharedCounts ()
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

// ---- Tier 1 callK: large intra-file HOFs (not inlined by specializeHofs) ----

type StrList =
    | SNil
    | SCons of string * StrList

let rec private mkStrList (n: int) : StrList =
    if n <= 0 then
        SNil
    else
        SCons("item-" + string n, mkStrList (n - 1))

/// Deliberately > 250 IR nodes so `specializeHofs` skips cloning it and `callK` handles it.
let rec largeStrAny (p: string -> bool) (xs: StrList) : bool =
    match xs with
    | SNil -> false
    | SCons(h, t) ->
        let ok =
            if h = "__never_0__" then
                p h
            elif h = "__never_1__" then
                p h
            elif h = "__never_2__" then
                p h
            elif h = "__never_3__" then
                p h
            elif h = "__never_4__" then
                p h
            elif h = "__never_5__" then
                p h
            elif h = "__never_6__" then
                p h
            elif h = "__never_7__" then
                p h
            elif h = "__never_8__" then
                p h
            elif h = "__never_9__" then
                p h
            elif h = "__never_10__" then
                p h
            elif h = "__never_11__" then
                p h
            elif h = "__never_12__" then
                p h
            elif h = "__never_13__" then
                p h
            elif h = "__never_14__" then
                p h
            elif h = "__never_15__" then
                p h
            else
                p h

        ok || largeStrAny p t

let rec largeIntFold (f: int -> int -> int) (acc: int) (xs: IntList) : int =
    match xs with
    | Nil -> acc
    | Cons(h, t) ->
        let next =
            if h = -99990 then
                f acc h
            elif h = -99991 then
                f acc h
            elif h = -99992 then
                f acc h
            elif h = -99993 then
                f acc h
            elif h = -99994 then
                f acc h
            elif h = -99995 then
                f acc h
            elif h = -99996 then
                f acc h
            elif h = -99997 then
                f acc h
            elif h = -99998 then
                f acc h
            elif h = -99999 then
                f acc h
            elif h = -99980 then
                f acc h
            elif h = -99981 then
                f acc h
            elif h = -99982 then
                f acc h
            elif h = -99983 then
                f acc h
            elif h = -99984 then
                f acc h
            elif h = -99985 then
                f acc h
            else
                f acc h

        largeIntFold f next t

let rec largeReuseMap (f: int -> int) (xs: IntList) : IntList =
    match xs with
    | Nil -> Nil
    | Cons(h, t) ->
        let y =
            if h = -99990 then
                f h
            elif h = -99991 then
                f h
            elif h = -99992 then
                f h
            elif h = -99993 then
                f h
            elif h = -99994 then
                f h
            elif h = -99995 then
                f h
            elif h = -99996 then
                f h
            elif h = -99997 then
                f h
            elif h = -99998 then
                f h
            elif h = -99999 then
                f h
            elif h = -99980 then
                f h
            elif h = -99981 then
                f h
            elif h = -99982 then
                f h
            elif h = -99983 then
                f h
            elif h = -99984 then
                f h
            elif h = -99985 then
                f h
            else
                f h

        Cons(y, largeReuseMap f t)

let rec bigStrAny (p: string -> bool) (xs: StrList) : bool =
    match xs with
    | SNil -> false
    | SCons(h, t) ->
        let hit =
            if h = "__never_0__" then
                p h
            elif h = "__never_1__" then
                p h
            elif h = "__never_2__" then
                p h
            elif h = "__never_3__" then
                p h
            elif h = "__never_4__" then
                p h
            elif h = "__never_5__" then
                p h
            elif h = "__never_6__" then
                p h
            elif h = "__never_7__" then
                p h
            elif h = "__never_8__" then
                p h
            elif h = "__never_9__" then
                p h
            elif h = "__never_10__" then
                p h
            elif h = "__never_11__" then
                p h
            elif h = "__never_12__" then
                p h
            elif h = "__never_13__" then
                p h
            elif h = "__never_14__" then
                p h
            elif h = "__never_15__" then
                p h
            elif h = "__never_16__" then
                p h
            elif h = "__never_17__" then
                p h
            elif h = "__never_18__" then
                p h
            elif h = "__never_19__" then
                p h
            elif h = "__never_20__" then
                p h
            elif h = "__never_21__" then
                p h
            elif h = "__never_22__" then
                p h
            elif h = "__never_23__" then
                p h
            elif h = "__never_24__" then
                p h
            elif h = "__never_25__" then
                p h
            elif h = "__never_26__" then
                p h
            elif h = "__never_27__" then
                p h
            elif h = "__never_28__" then
                p h
            elif h = "__never_29__" then
                p h
            elif h = "__never_30__" then
                p h
            elif h = "__never_31__" then
                p h
            elif h = "__never_32__" then
                p h
            elif h = "__never_33__" then
                p h
            elif h = "__never_34__" then
                p h
            elif h = "__never_35__" then
                p h
            else
                p h

        if hit then
            true
        else
            bigStrAny p t

let rec bigIntFold (f: int -> int -> int) (acc: int) (xs: IntList) : int =
    match xs with
    | Nil -> acc
    | Cons(h, t) ->
        let next =
            if h = -90000 then
                f acc h
            elif h = -90001 then
                f acc h
            elif h = -90002 then
                f acc h
            elif h = -90003 then
                f acc h
            elif h = -90004 then
                f acc h
            elif h = -90005 then
                f acc h
            elif h = -90006 then
                f acc h
            elif h = -90007 then
                f acc h
            elif h = -90008 then
                f acc h
            elif h = -90009 then
                f acc h
            elif h = -90010 then
                f acc h
            elif h = -90011 then
                f acc h
            elif h = -90012 then
                f acc h
            elif h = -90013 then
                f acc h
            elif h = -90014 then
                f acc h
            elif h = -90015 then
                f acc h
            elif h = -90016 then
                f acc h
            elif h = -90017 then
                f acc h
            elif h = -90018 then
                f acc h
            elif h = -90019 then
                f acc h
            elif h = -90020 then
                f acc h
            elif h = -90021 then
                f acc h
            elif h = -90022 then
                f acc h
            elif h = -90023 then
                f acc h
            elif h = -90024 then
                f acc h
            elif h = -90025 then
                f acc h
            elif h = -90026 then
                f acc h
            elif h = -90027 then
                f acc h
            elif h = -90028 then
                f acc h
            elif h = -90029 then
                f acc h
            elif h = -90030 then
                f acc h
            elif h = -90031 then
                f acc h
            elif h = -90032 then
                f acc h
            elif h = -90033 then
                f acc h
            elif h = -90034 then
                f acc h
            elif h = -90035 then
                f acc h
            else
                f acc h

        bigIntFold f next t

let rec bigReuseMap (f: int -> int) (xs: IntList) : IntList =
    match xs with
    | Nil -> Nil
    | Cons(h, t) ->
        let y =
            if h = -90000 then
                f h
            elif h = -90001 then
                f h
            elif h = -90002 then
                f h
            elif h = -90003 then
                f h
            elif h = -90004 then
                f h
            elif h = -90005 then
                f h
            elif h = -90006 then
                f h
            elif h = -90007 then
                f h
            elif h = -90008 then
                f h
            elif h = -90009 then
                f h
            elif h = -90010 then
                f h
            elif h = -90011 then
                f h
            elif h = -90012 then
                f h
            elif h = -90013 then
                f h
            elif h = -90014 then
                f h
            elif h = -90015 then
                f h
            elif h = -90016 then
                f h
            elif h = -90017 then
                f h
            elif h = -90018 then
                f h
            elif h = -90019 then
                f h
            elif h = -90020 then
                f h
            elif h = -90021 then
                f h
            elif h = -90022 then
                f h
            elif h = -90023 then
                f h
            elif h = -90024 then
                f h
            elif h = -90025 then
                f h
            elif h = -90026 then
                f h
            elif h = -90027 then
                f h
            elif h = -90028 then
                f h
            elif h = -90029 then
                f h
            elif h = -90030 then
                f h
            elif h = -90031 then
                f h
            elif h = -90032 then
                f h
            elif h = -90033 then
                f h
            elif h = -90034 then
                f h
            elif h = -90035 then
                f h
            else
                f h

        Cons(y, bigReuseMap f t)

let callKTests () : int =
    let before = liveCells ()
    let sxs = mkStrList 20
    let targetPrefix = "item-" + string 12
    let missingPrefix = targetPrefix + "x"
    // Borrowing lambda with capture passed to large callK HOF: 0 Env allocs and 0 string dups
    let a0 = allocs ()
    let c0 = counted ()
    let found = bigStrAny (fun s -> s = targetPrefix) sxs
    let missing = bigStrAny (fun s -> s = missingPrefix) sxs
    let envAndDupAllocs = allocs () - a0
    let strShared = counted () - c0

    // Capturing fold (with Curried2 -> call2) and non-Curried2 curried lambda (else fallback in invokeK)
    let nums = rangeFrom 1 6
    let bias = 10
    let a1 = allocs ()
    let fold1 = bigIntFold (fun acc x -> acc + x + bias) 0 nums
    let fold1Allocs = allocs () - a1

    let fold2 =
        bigIntFold
            (fun acc ->
                let baseAcc = acc + bias

                if baseAcc >= 0 then
                    fun x -> baseAcc + x
                else
                    fun x -> baseAcc - x
            )
            0
            nums

    // Capture-plus-move hazard: `nums` is captured AND passed to `bigReuseMap` (which consumes its list)
    let haz = bigReuseMap (fun x -> x + sumList nums) nums

    // Raising lambda inside large callK HOF
    let caught =
        try
            bigStrAny
                (fun s ->
                    if s = "item-3" then
                        failwith "hit-3"
                    else
                        false
                )
                sxs
            |> ignore

            false
        with _ ->
            true

    // Cross-file callK via List / Array library HOFs over string list / array
    let fcl = [ "aa"; "bbb"; "c"; "dd"; "eee" ]
    let missKey = "missing-" + string 99
    let sep = ":" + string 1
    let tagOff = 10

    // `takeWhile` when predicate fails on first element -> 0 heap allocs (0 Cons and 0 closure Env)
    let ta0 = allocs ()
    let twEmpty = List.takeWhile (fun s -> s = missKey) fcl
    let twAllocs = allocs () - ta0

    // `skipWhile` over borrowed list & borrowed string capture -> 0 heap allocs and 0 RC dups
    let sa0 = allocs ()
    let sc0 = counted ()
    let swAll = List.skipWhile (fun s -> s <> missKey) fcl
    let swAllocs = allocs () - sa0
    let swShared = counted () - sc0

    // `takeWhile` matching prefix
    let twHit = List.takeWhile (fun (s: string) -> s.Length >= 2) fcl

    // `collect`, `reduce`, `distinctBy`, `groupBy`, `sortBy`, `partition` over strings
    let collected = List.collect (fun s -> [ s + sep; s ]) [ "x"; "yy" ]
    let reduced = List.reduce (fun a b -> a + sep + b) [ "p"; "q"; "r" ]
    let dist = List.distinctBy (fun (s: string) -> s.Length + tagOff) fcl
    let grouped = List.groupBy (fun (s: string) -> s.Length + tagOff) fcl
    let sorted = List.sortBy (fun (s: string) -> -(s.Length + tagOff)) fcl

    let partT, partF =
        List.partition (fun (s: string) -> s.Length = 2 + (tagOff - 10)) fcl

    // Array `choose`, `collect`, `partition`
    let arrIn = [| "a"; "bb"; "ccc" |]

    let arrCh =
        Array.choose
            (fun (s: string) ->
                if s.Length >= 2 then
                    Some(s + sep)
                else
                    None
            )
            arrIn

    let arrCol = Array.collect (fun (s: string) -> [| s + sep; s |]) [| "u" |]

    let arrT, arrF =
        Array.partition (fun (s: string) -> s.Length > 1 + (tagOff - 10)) arrIn

    check found
    + check (not missing)
    + checkCount envAndDupAllocs 0
    + checkCount strShared 0
    + check (fold1 = 81 && fold2 = 81)
    + checkCount fold1Allocs 0
    + check (sumList haz = 21 + 6 * 21)
    + check caught
    + check (List.isEmpty twEmpty)
    + checkCount twAllocs 0
    + check (List.isEmpty swAll)
    + checkCount swAllocs 0
    + checkCount swShared 0
    + check (List.length twHit = 2)
    + check (collected = [ "x:1"; "x"; "yy:1"; "yy" ])
    + check (reduced = "p:1q:1r")
    + check (List.length dist = 3)
    + check (List.length grouped = 3)
    + check (List.head sorted = "bbb" || List.head sorted = "eee")
    + check (List.length partT = 2 && List.length partF = 3)
    + check (arrCh = [| "bb:1"; "ccc:1" |])
    + check (arrCol = [| "u:1"; "u" |])
    + check (arrT.Length = 2 && arrF.Length = 1)
    + checkCount (liveCells () - before) 0

// ---- Part 1: cross-file Modes, RetFrom (acrossAssumed), and raise-edge borrowed drop ----

let rec private forwardStrBorrowLoop (n: int) (xs: string list) (acc: int) : int =
    if n <= 0 then
        acc
    else
        forwardStrBorrowLoop (n - 1) xs (acc + sumStrLengths xs)

let rec private forwardGenericBorrowLoop (n: int) (xs: 'T list) (acc: int) : int =
    if n <= 0 then
        acc
    else
        forwardGenericBorrowLoop (n - 1) xs (acc + countAny xs)

let private directNonOwnerFirst (p: StrPair) : string = firstStr p

let private elidedCrossTry (a: int) (b: int) : int =
    try
        Helpers.pureAddInts a b
    with _ ->
        -1

let private readStructAAcrossSetB (s: byref<Helpers.MutPairStruct>) (nextB: string) : int =
    let a = s.A
    Helpers.setStructB &s nextB
    a.Length

let factsTests () : int =
    let before = liveCells ()
    let sxs = [ "alpha-" + string 1; "beta-" + string 2; "gamma-" + string 3 ]

    // Cross-file borrow forwarding in loops (concrete + generic 'T list): 0 allocs and 0 RC dups
    let la0 = allocs ()
    let lc0 = counted ()
    let strSum = forwardStrBorrowLoop 10 sxs 0
    let genSum = forwardGenericBorrowLoop 10 sxs 0
    let fwdAllocs = allocs () - la0
    let fwdShared = counted () - lc0

    // Let-bound owner case (`callAssumedM`): 0 allocs and 0 RC dups on borrowed field return
    let p: StrPair =
        {
            First = "first-" + string 42
            Second = "second-" + string 99
        }

    let pa0 = allocs ()
    let pc0 = counted ()
    let h = firstStr p
    let hLen = h.Length
    let hOk = h = "first-42"
    let assumedAllocs = allocs () - pa0
    let assumedShared = counted () - pc0

    // Non-owner direct tail return keeps ordinary `callM` (dups borrowed result cleanly)
    let hDirect = directNonOwnerFirst p

    // Borrowed last-use argument passed to a cross-file raising function (raise edge drops `tmp`)
    let tmp = [ "raise-" + string 7; "edge-" + string 8 ]

    let raiseCaught =
        try
            borrowAndFail tmp |> ignore
            false
        with Helpers.TooBig(0, total) ->
            total = 13

    let mutable st: Helpers.MutPairStruct =
        {
            A = "alpha-" + string 1
            B = "beta-" + string 2
        }

    let nextB = "gamma-" + string 3
    let stBeforeAllocs = allocs ()
    let stBeforeShared = counted ()
    let aLen = readStructAAcrossSetB &st nextB
    let stReadAllocs = allocs () - stBeforeAllocs
    let stReadShared = counted () - stBeforeShared

    check (strSum = 200 && genSum = 30)
    + checkCount fwdAllocs 0
    + checkCount fwdShared 0
    + check (hOk && hLen = 8 && hDirect = "first-42")
    + checkCount assumedAllocs 0
    + checkCount assumedShared 0
    + check raiseCaught
    + check (elidedCrossTry 17 25 = 42)
    + check (aLen = 7 && st.B = "gamma-3")
    + checkCount stReadAllocs 0
    + checkCount stReadShared 0
    + checkCount (liveCells () - before) 0

let private tier2Tests () : int =
    let before = liveCells ()
    let ints = rangeFrom 1 4
    // Captures a runtime value (not constant-folded) and reuses `ints` cells with 0 closure Env allocs.
    let delta =
        10
        + (if counting () then
               0
           else
               0)

    let aInt0 = allocs ()
    let mappedInts = Helpers.mapIntListTier2 (fun x -> x * 2 + delta) ints
    let intAllocs = allocs () - aInt0
    let intSum = sumList mappedInts

    let rec mkCustom n =
        if n <= 0 then
            Helpers.CustomNil
        else
            Helpers.CustomCons("aa" + string n, mkCustom (n - 1))

    let prefix = "p-" + string 7
    let strs = mkCustom 2
    let aStr0 = allocs ()
    let mappedStrs = Helpers.mapCustomWithLoop (fun s -> prefix + ":" + s) strs
    // Two new strings allocated, both CustomCons cells reused via Tier 2 specialization, 0 closure Env allocs.
    let strAllocs = allocs () - aStr0

    let rec countLens acc cur =
        match cur with
        | Helpers.CustomNil -> acc
        | Helpers.CustomCons(h, t) -> countLens (acc + h.Length) t

    let totalLen = countLens 0 mappedStrs

    check (intSum = 60 && totalLen = 14)
    + checkCount intAllocs 0
    + checkCount strAllocs 2
    + checkCount (liveCells () - before) 0

// ---- Step 7: generalized TRMC Plug (`nullOf(R)`) behind `comptime hasNull(R)` ----

type PlugTree =
    | PLeaf of string
    | PNode of PlugTree * PlugTree

let rec buildPlugTree (failAt: int) (n: int) : PlugTree =
    if n = failAt then
        failwith "plug-boom"
    elif n <= 0 then
        PLeaf("leaf-" + string n)
    else
        PNode(PLeaf("node-" + string n), buildPlugTree failAt (n - 1))

let countPlugTree (t: PlugTree) : int =
    let rec loop acc cur =
        match cur with
        | PLeaf _ -> acc + 1
        | PNode(_, right) -> loop (acc + 1) right

    loop 0 t

type IfaceChain =
    | IEnd of Helpers.IGreeter
    | INext of Helpers.IGreeter * IfaceChain

let rec buildIfaceChain (failAt: int) (n: int) : IfaceChain =
    if n = failAt then
        failwith "iface-boom"
    elif n <= 0 then
        IEnd(Helpers.Greeter("end") :> Helpers.IGreeter)
    else
        let g = Helpers.Greeter("step-" + string n) :> Helpers.IGreeter
        INext(g, buildIfaceChain failAt (n - 1))

let countIfaceChain (c: IfaceChain) : int =
    let rec loop acc cur =
        match cur with
        | IEnd g -> acc + g.Greet("x").Length
        | INext(g, rest) -> loop (acc + g.Greet("x").Length) rest

    loop 0 c

// Recursive union holding a 4-parameter uncurried function: `fable_rt.hasNull` is false,
// forcing the `else` fallback branch of `if (comptime fable_rt.hasNull(R))`.
type WideFnChain =
    | WFEnd of (int -> int -> int -> int -> int)
    | WFNext of (int -> int -> int -> int -> int) * WideFnChain

let rec buildWideFnChain (failAt: int) (n: int) : WideFnChain =
    if n = failAt then
        failwith "widefn-boom"
    elif n <= 0 then
        WFEnd(fun a b c d -> a + b + c + d)
    else
        let bias = n
        WFNext((fun a b c d -> a + b + c + d + bias), buildWideFnChain failAt (n - 1))

let sumWideFnChain (c: WideFnChain) : int =
    let rec loop acc cur =
        match cur with
        | WFEnd f -> acc + f 1 2 3 4
        | WFNext(f, rest) -> loop (acc + f 1 2 3 4) rest

    loop 0 c

let private step7Tests () : int =
    let before = liveCells ()
#if FABLE_COMPILER
    let deep = 50000
    let raiseAt = 25000
#else
    let deep = 500
    let raiseAt = 250
#endif
    let okTree = buildPlugTree -1 deep
    let okCount = countPlugTree okTree

    let caughtTree =
        try
            buildPlugTree raiseAt deep |> ignore
            false
        with _ ->
            true

    let okIface = buildIfaceChain -1 5
    let ifaceScore = countIfaceChain okIface

    let caughtIface =
        try
            buildIfaceChain 2 5 |> ignore
            false
        with _ ->
            true

    let okWide = buildWideFnChain -1 5
    let wideSum = sumWideFnChain okWide

    let caughtWide =
        try
            buildWideFnChain 2 5 |> ignore
            false
        with _ ->
            true

    check (
        okCount = deep + 1
        && caughtTree
        && ifaceScore > 0
        && caughtIface
        && wideSum = 75
        && caughtWide
    )
    + checkCount (liveCells () - before) 0

// ---- Step 8: TRMC inside fused mutual recursion (`emitScc`) ----

let rec evenBuild (n: int) : Helpers.CustomStrList =
    if n <= 0 then
        Helpers.CustomNil
    else
        Helpers.CustomCons("e" + string n, oddBuild (n - 1))

and oddBuild (n: int) : Helpers.CustomStrList =
    if n <= 0 then
        Helpers.CustomCons("end", Helpers.CustomNil)
    else
        Helpers.CustomCons("o" + string n, evenBuild (n - 1))

let rec skipEvenBuild (n: int) (result: string) : Helpers.CustomStrList =
    if n <= 0 then
        Helpers.CustomCons(result, Helpers.CustomNil)
    else
        consOddBuild (n - 1) result

and consOddBuild (n: int) (result: string) : Helpers.CustomStrList =
    if n <= 0 then
        Helpers.CustomNil
    else
        Helpers.CustomCons(result + "-" + string n, skipEvenBuild (n - 1) result)

let countCustomStrList (xs: Helpers.CustomStrList) : int * string =
    let rec loop n last cur =
        match cur with
        | Helpers.CustomNil -> n, last
        | Helpers.CustomCons(s, rest) -> loop (n + 1) s rest

    loop 0 "" xs

let rec evenPlugTree (failAt: int) (n: int) : PlugTree =
    if n = failAt then
        failwith "even-plug-boom"
    elif n <= 0 then
        PLeaf("even-end")
    else
        PNode(PLeaf("e-" + string n), oddPlugTree failAt (n - 1))

and oddPlugTree (failAt: int) (n: int) : PlugTree =
    if n = failAt then
        failwith "odd-plug-boom"
    elif n <= 0 then
        PLeaf("odd-end")
    else
        PNode(PLeaf("o-" + string n), evenPlugTree failAt (n - 1))

let private step8Tests () : int =
    let before = liveCells ()
#if FABLE_COMPILER
    let deep = 200000
    let raiseAt = 100000
#else
    let deep = 500
    let raiseAt = 250
#endif
    let built = evenBuild deep
    let builtLen, builtLast = countCustomStrList built

    let mixed = skipEvenBuild 10 ("tag-" + string 1)
    let mixedLen, mixedLast = countCustomStrList mixed

    let okTree = evenPlugTree -1 deep
    let okCount = countPlugTree okTree

    let caughtPlug =
        try
            evenPlugTree raiseAt deep |> ignore
            false
        with _ ->
            true

    check (
        builtLen = deep
        && builtLast = "o1"
        && mixedLen = 6
        && mixedLast = "tag-1"
        && okCount = deep + 1
        && caughtPlug
    )
    + checkCount (liveCells () - before) 0

// ---- Step 9: Uniform `$tc` entries for file functions & lambdas ----

#if FABLE_COMPILER
[<Fable.Core.Emit("@import(\"builtin\").zig_backend == .stage2_llvm")>]
let private isLlvm () : bool = false
#else
let private isLlvm () : bool = false
#endif

type private CpsExpr =
    | CNum of int
    | CAdd of CpsExpr * CpsExpr
    | CTag of string * CpsExpr
    | CFail of string

let rec private evalK (e: CpsExpr) (k: int -> int) : int =
    match e with
    | CNum n -> k n
    | CFail msg -> failwith msg
    | CTag(tag, inner) ->
        let bonus = tag.Length % 2
        evalK inner (fun v -> k (v + bonus))
    | CAdd(l, r) -> evalK l (fun lv -> evalK r (fun rv -> k (lv + rv)))

let rec private foldk (f: 'Acc -> 'T -> ('Acc -> 'R) -> 'R) (acc: 'Acc) (xs: 'T list) (k: 'Acc -> 'R) : 'R =
    match xs with
    | [] -> k acc
    | x :: rest -> f acc x (fun acc2 -> foldk f acc2 rest k)

let rec private flipA (n: int) (a: 'A list) (b: 'B list) : int =
    if n <= 0 then
        a.Length + b.Length
    else
        flipB (n - 1) b a

and private flipB (n: int) (b: 'B list) (a: 'A list) : int =
    if n <= 0 then
        a.Length + b.Length + 1
    else
        flipA (n - 1) a b

[<Struct>]
type private BigArgs =
    {
        F0: int64
        F1: int64
        F2: int64
        F3: int64
        F4: int64
        F5: int64
        F6: int64
        F7: int64
        F8: int64
        F9: int64
        F10: int64
        F11: int64
        F12: int64
        F13: int64
        F14: int64
        F15: int64
        F16: int64
    }

type private BigBox = { mutable Acc: int64 }

let private makeBigArgs (v: int64) : BigArgs =
    {
        F0 = v
        F1 = v + 1L
        F2 = v + 2L
        F3 = v + 3L
        F4 = v + 4L
        F5 = v + 5L
        F6 = v + 6L
        F7 = v + 7L
        F8 = v + 8L
        F9 = v + 9L
        F10 = v + 10L
        F11 = v + 11L
        F12 = v + 12L
        F13 = v + 13L
        F14 = v + 14L
        F15 = v + 15L
        F16 = v + 16L
    }

let private sumBigArgs (b: BigArgs) : int64 =
    b.F0
    + b.F1
    + b.F2
    + b.F3
    + b.F4
    + b.F5
    + b.F6
    + b.F7
    + b.F8
    + b.F9
    + b.F10
    + b.F11
    + b.F12
    + b.F13
    + b.F14
    + b.F15
    + b.F16

let private tailBigValue (f: string -> BigArgs -> int64) (tag: string) (b: BigArgs) : int64 = f tag b

let private tailBigUnit (f: string -> BigArgs -> unit) (tag: string) (b: BigArgs) : unit = f tag b

let private step9Tests () : int =
    let before = liveCells ()

    let deep =
        if isLlvm () then
            200000
        else
            500

    let raiseAt =
        if isLlvm () then
            100000
        else
            250

    // 1. Deep CPS evalK + mid-raise cleanup
    let mutable cpsTree = CNum 1
    let mutable cpsExpected = 1
    let mutable i = 1

    while i <= deep do
        let tag = "t" + string i
        cpsExpected <- cpsExpected + 1 + (tag.Length % 2)
        cpsTree <- CAdd(CTag(tag, CNum 1), cpsTree)
        i <- i + 1

    let cpsRes = evalK cpsTree id

    let mutable cpsBadTree = CNum 1
    let mutable j = 1

    while j <= deep do
        if j = deep - raiseAt then
            cpsBadTree <- CAdd(CFail("cps-boom-" + string j), cpsBadTree)
        else
            cpsBadTree <- CAdd(CTag("u" + string j, CNum 1), cpsBadTree)

        j <- j + 1

    let caughtCps =
        try
            evalK cpsBadTree id |> ignore
            false
        with _ ->
            true

    // 2. Deep CPS foldk over string list + mid-raise cleanup
    let mutable strList: string list = []
    let mutable expectedStrLen = 0
    let mutable k = deep

    while k >= 1 do
        let s = "s" + string k
        expectedStrLen <- expectedStrLen + s.Length
        strList <- s :: strList
        k <- k - 1

    let foldSum = foldk (fun acc (s: string) cont -> cont (acc + s.Length)) 0 strList id

    let caughtFoldk =
        try
            foldk
                (fun acc (s: string) cont ->
                    if acc = raiseAt then
                        failwith ("foldk-boom:" + s)
                    else
                        cont (acc + 1)
                )
                0
                strList
                id
            |> ignore

            false
        with _ ->
            true

    // 3. Unfused generic intra-file cycle at 200k depth
    let flipEven = flipA deep [ "a" + string 1; "b" + string 2 ] [ 10; 20; 30 ]
    let flipOdd = flipA (deep + 1) [ "x" + string 1 ] [ 1; 2 ]

    // 4. >128B struct fallback through value-returning & unit-returning $tc/closure tail calls
    let big = makeBigArgs 10L
    let box = { Acc = 0L }
    let salt = "big-" + string 7

    let bigVal =
        tailBigValue (fun (s: string) b -> sumBigArgs b + int64 s.Length) salt big

    tailBigUnit (fun (s: string) b -> box.Acc <- sumBigArgs b + int64 s.Length) ("u-" + string 9) big
    let bigExpected = sumBigArgs big + int64 salt.Length
    let boxExpected = sumBigArgs big + int64 ("u-" + string 9).Length

    check (
        cpsRes = cpsExpected
        && caughtCps
        && foldSum = expectedStrLen
        && caughtFoldk
        && flipEven = 5
        && flipOdd = 4
        && bigVal = bigExpected
        && box.Acc = boxExpected
    )
    + checkCount (liveCells () - before) 0

// Step 10 helpers and tests ($tc across files, class vtable, and fat-pointer interfaces)
let rec private crossPing (n: int) (raiseAt: int) (tag: string) : int =
    if n = raiseAt then
        raise (Helpers.TooBig(raiseAt, tag.Length + n))
    elif n <= 0 then
        tag.Length + n
    else
        Helpers.crossPong crossPing (n - 1) raiseAt tag

let private crossTailLeaf (n: int) (tag: string) : int = Helpers.crossLeaf n tag

let rec private crossGenPing (n: int) (xs: string list) : int =
    if n <= 0 then
        xs.Length
    else
        Helpers.crossPongGen crossGenPing (n - 1) xs

type private LocalCrossSub(label: string) =
    inherit Helpers.CrossBase(label)

    override this.Step(other, n, raiseAt, tag) =
        if n = raiseAt then
            raise (Helpers.TooBig(raiseAt, this.Label.Length + tag.Length))
        elif n <= 0 then
            this.Label.Length + tag.Length + n
        else
            other.Step(this, n - 1, raiseAt, tag)

type private SubIfaceImpl(prefix: string) =
    interface Helpers.ICrossSubPing with
        member _.Bonus = 7

        member this.Ping(other, n, raiseAt, tag) =
            if n = raiseAt then
                raise (Helpers.TooBig(raiseAt, prefix.Length + tag.Length))
            elif n <= 0 then
                prefix.Length + tag.Length + n
            else
                other.Ping(this, n - 1, raiseAt, tag)

type private BoxRecordPing =
    {
        TagSalt: string
    }

    interface Helpers.ICrossPing with
        member this.Ping(other, n, raiseAt, tag) =
            if n = raiseAt then
                raise (Helpers.TooBig(raiseAt, this.TagSalt.Length + tag.Length))
            elif n <= 0 then
                this.TagSalt.Length + tag.Length + n
            else
                other.Ping(this, n - 1, raiseAt, tag)

[<Struct>]
type private ValuePingStruct =
    {
        Salt: string
    }

    interface Helpers.ICrossPing with
        member this.Ping(other, n, raiseAt, tag) =
            if n = raiseAt then
                raise (Helpers.TooBig(raiseAt, this.Salt.Length + tag.Length))
            elif n <= 0 then
                this.Salt.Length + tag.Length + n
            else
                let selfCopy: ValuePingStruct = { Salt = this.Salt }
                other.Ping(selfCopy, n - 1, raiseAt, tag)

type private IMutBox =
    abstract Inc: int -> int

[<Struct>]
type private MutBoxStruct =
    val mutable Count: int
    new(c) = { Count = c }

    interface IMutBox with
        member this.Inc(d) =
            this.Count <- this.Count + d
            this.Count

let private tailCallMutBox (b: IMutBox) (d: int) : int = b.Inc d

let private tailCallIface
    (p: Helpers.ICrossPing)
    (other: Helpers.ICrossPing)
    (n: int)
    (raiseAt: int)
    (tag: string)
    : int
    =
    p.Ping(other, n, raiseAt, tag)

let private step10Tests () : int =
    let before = liveCells ()

    let deep =
        if isLlvm () then
            200000
        else
            500

    let raiseAt =
        if isLlvm () then
            100000
        else
            250

    let sTag = "tag-" + string 10

    // (a) Cross-file $tc ping-pong, generic $tc, non-chain cross fallback, and mid-raise
    let crossRes = crossPing deep -1 sTag
    let crossLeafRes = crossTailLeaf 10 sTag
    let genRes = crossGenPing deep [ "x" + string 1; "y" + string 2 ]

    let caughtCross =
        try
            crossPing deep raiseAt sTag |> ignore
            false
        with :? Helpers.TooBig as _ ->
            true

    // (b) Virtual class + subclass + object-expression @raw: thunk ping-pong
    let vtA: Helpers.CrossBase = LocalCrossSub("vA") :> Helpers.CrossBase
    let vtB: Helpers.CrossBase = Helpers.CrossSubInHelpers("vB-") :> Helpers.CrossBase
    let oePrefix = "oe-" + string 42

    let vtObjExpr: Helpers.CrossBase =
        { new Helpers.CrossBase("oeBase") with
            override this.Step(other, n, rAt, tag) =
                if n = rAt then
                    raise (Helpers.TooBig(rAt, oePrefix.Length + tag.Length))
                elif n <= 0 then
                    oePrefix.Length + tag.Length + n
                else
                    other.Step(this, n - 1, rAt, tag)
        }

    let vtRes1 = vtA.Step(vtB, deep, -1, sTag)
    let vtRes2 = vtObjExpr.Step(vtB, deep, -1, sTag)

    let caughtVt =
        try
            vtObjExpr.Step(vtA, deep, raiseAt, sTag) |> ignore
            false
        with :? Helpers.TooBig as _ ->
            true

    // (c) Fat-pointer interface ping-pong (IVtObj, IVtUpcast, IVtCaptures, IVtBox value & ptr)
    let ifHelpers = Helpers.HelpersObjPing("hi-") :> Helpers.ICrossPing
    let ifUpcast = (SubIfaceImpl("sub") :> Helpers.ICrossSubPing) :> Helpers.ICrossPing
    let capSalt = "cap-" + string 99

    let ifCaps =
        { new Helpers.ICrossPing with
            member this.Ping(other, n, rAt, tag) =
                if n = rAt then
                    raise (Helpers.TooBig(rAt, capSalt.Length + tag.Length))
                elif n <= 0 then
                    capSalt.Length + tag.Length + n
                else
                    other.Ping(this, n - 1, rAt, tag)
        }

    let ifRecordBox = ({ TagSalt = "rec-" + string 7 } :> Helpers.ICrossPing)
    let ifStructBox = ({ Salt = "box-" + string 7 } :> Helpers.ICrossPing)

    let resObjUp = tailCallIface ifHelpers ifUpcast deep -1 sTag
    let resCapObj = tailCallIface ifCaps ifHelpers deep -1 sTag
    let resRecBoxCap = tailCallIface ifRecordBox ifCaps deep -1 sTag
    let resStructBoxCap = tailCallIface ifStructBox ifCaps 50 -1 sTag

    let caughtIface =
        try
            tailCallIface ifUpcast ifCaps deep raiseAt sTag |> ignore
            false
        with :? Helpers.TooBig as _ ->
            true

    let caughtRecBox =
        try
            tailCallIface ifRecordBox ifCaps deep raiseAt sTag |> ignore
            false
        with :? Helpers.TooBig as _ ->
            true

    let caughtStructBox =
        try
            tailCallIface ifStructBox ifCaps 50 25 sTag |> ignore
            false
        with :? Helpers.TooBig as _ ->
            true

    let mutBox = (MutBoxStruct(10) :> IMutBox)
    let mutRes1 = tailCallMutBox mutBox 5
    let mutRes2 = tailCallMutBox mutBox 7

    check (
        crossRes = sTag.Length
        && crossLeafRes = 10 + sTag.Length
        && genRes = 2
        && caughtCross
        && vtRes1 =
            (if deep % 2 = 0 then
                 2
             else
                 3)
            + sTag.Length
        && vtRes2 =
            (if deep % 2 = 0 then
                 oePrefix.Length
             else
                 3)
            + sTag.Length
        && caughtVt
        && resObjUp = 3 + sTag.Length
        && resCapObj =
            (if deep % 2 = 0 then
                 capSalt.Length
             else
                 3)
            + sTag.Length
        && resRecBoxCap =
            (if deep % 2 = 0 then
                 5
             else
                 capSalt.Length)
            + sTag.Length
        && resStructBoxCap = 5 + sTag.Length
        && caughtIface
        && caughtRecBox
        && caughtStructBox
        && mutRes1 = 15
        && mutRes2 = 22
    )
    + checkCount (liveCells () - before) 0

// Step 11 tests: TRMC into unknown callees (`next_ret`) over KHeapUnion and KValueUnion
let private goTrmc (next: int -> int -> string list) (n: int) (raiseAt: int) : string list =
    if n = raiseAt then
        raise (Helpers.TooBig(raiseAt, n))
    elif n <= 0 then
        []
    else
        ("item-" + string n) :: next (n - 1) raiseAt

let rec private goTie (n: int) (raiseAt: int) : string list =
    if n % 2 = 0 then
        goTrmc goTie n raiseAt
    else
        Helpers.trmcCrossCons goTie n raiseAt

type private ITrmcList =
    abstract Build: ITrmcList * int * int -> string list

type private ValWrap =
    | WrapItems of label: string * items: string list
    | WrapEmpty

let private buildWrap (next: int -> int -> string list) (n: int) (raiseAt: int) : ValWrap =
    if n <= 0 then
        WrapEmpty
    else
        WrapItems("hdr-" + string n, next n raiseAt)

let private wrapViaMaker
    (maker: (int -> int -> string list) -> int -> int -> ValWrap)
    (next: int -> int -> string list)
    (n: int)
    (raiseAt: int)
    : ValWrap
    =
    maker next n raiseAt

let private step11Tests () : int =
    let before = liveCells ()

    let deep =
        if isLlvm () then
            200000
        else
            500

    let raiseAt =
        if isLlvm () then
            100000
        else
            250

    let countAndEnds (xs: string list) =
        let mutable len = 0
        let mutable first = ""
        let mutable last = ""
        let mutable cur = xs

        while not (List.isEmpty cur) do
            if len = 0 then
                first <- cur.Head

            last <- cur.Head
            len <- len + 1
            cur <- cur.Tail

        len, first, last

    // 1. KHeapUnion TRMC through alternating local/cross-file unknown closures + mid-raise
    let len1, first1, last1 = countAndEnds (goTie deep -1)

    let caughtHeapTrmc =
        try
            goTie deep raiseAt |> ignore
            false
        with :? Helpers.TooBig as _ ->
            true

    // 2. Interface TRMC with captured heap string + mid-raise
    let ifPrefix = "if-" + string 3

    let ifBuilder =
        { new ITrmcList with
            member this.Build(other, n, rAt) =
                if n = rAt then
                    raise (Helpers.TooBig(rAt, n))
                elif n <= 0 then
                    []
                else
                    (ifPrefix + "-" + string n) :: other.Build(this, n - 1, rAt)
        }

    let tailBuild (a: ITrmcList) (b: ITrmcList) (n: int) (rAt: int) = a.Build(b, n, rAt)
    let len2, first2, last2 = countAndEnds (tailBuild ifBuilder ifBuilder deep -1)

    let caughtIfaceTrmc =
        try
            tailBuild ifBuilder ifBuilder deep raiseAt |> ignore
            false
        with :? Helpers.TooBig as _ ->
            true

    // 3. KValueUnion TRMC at DReturn (direct) and DTcRet (via maker closure) + mid-raise
    let directWrapOk =
        match buildWrap goTie deep -1 with
        | WrapItems(lbl, items) ->
            let n, f, l = countAndEnds items

            lbl = ("hdr-" + string deep)
            && n = deep
            && f = ("item-" + string deep)
            && l = "h-1"
        | WrapEmpty -> false

    let tcWrapOk =
        match wrapViaMaker buildWrap goTie deep -1 with
        | WrapItems(lbl, items) ->
            let n, f, l = countAndEnds items

            lbl = ("hdr-" + string deep)
            && n = deep
            && f = ("item-" + string deep)
            && l = "h-1"
        | WrapEmpty -> false

    let wrapEmptyOk =
        match wrapViaMaker buildWrap goTie 0 -1 with
        | WrapEmpty -> true
        | WrapItems _ -> false

    let caughtValWrap =
        try
            wrapViaMaker buildWrap goTie deep raiseAt |> ignore
            false
        with :? Helpers.TooBig as _ ->
            true

    check (
        len1 = deep
        && first1 = ("item-" + string deep)
        && last1 = "h-1"
        && caughtHeapTrmc
        && len2 = deep
        && first2 = (ifPrefix + "-" + string deep)
        && last2 = (ifPrefix + "-1")
        && caughtIfaceTrmc
        && directWrapOk
        && tcWrapOk
        && wrapEmptyOk
        && caughtValWrap
    )
    + checkCount (liveCells () - before) 0

type private NonNullFuncStream =
    | NFStep of System.Func<int, int, int, int, int> * NonNullFuncStream
    | NFEnd

let private evalPadWeight (n: int) : int =
    if n = 1 then
        10
    elif n = 2 then
        20
    elif n = 3 then
        30
    elif n = 4 then
        40
    elif n = 5 then
        50
    elif n = 6 then
        60
    elif n = 7 then
        70
    elif n = 8 then
        80
    elif n = 9 then
        90
    elif n = 10 then
        100
    elif n = 11 then
        110
    elif n = 12 then
        120
    elif n = 13 then
        130
    elif n = 14 then
        140
    elif n = 15 then
        150
    elif n = 16 then
        160
    elif n = 17 then
        170
    elif n = 18 then
        180
    elif n = 19 then
        190
    elif n = 20 then
        200
    elif n = 21 then
        210
    elif n = 22 then
        220
    elif n = 23 then
        230
    elif n = 24 then
        240
    elif n = 25 then
        250
    elif n = 26 then
        260
    elif n = 27 then
        270
    elif n = 28 then
        280
    elif n = 29 then
        290
    elif n = 30 then
        300
    else
        0

let private evalBigTouch (n: int) =
    if n = 1 then
        1
    elif n = 2 then
        2
    elif n = 3 then
        3
    elif n = 4 then
        4
    elif n = 5 then
        5
    elif n = 6 then
        6
    elif n = 7 then
        7
    elif n = 8 then
        8
    elif n = 9 then
        9
    elif n = 10 then
        10
    elif n = 11 then
        11
    elif n = 12 then
        12
    elif n = 13 then
        13
    elif n = 14 then
        14
    elif n = 15 then
        15
    elif n = 16 then
        16
    elif n = 17 then
        17
    elif n = 18 then
        18
    elif n = 19 then
        19
    elif n = 20 then
        20
    elif n = 21 then
        21
    elif n = 22 then
        22
    elif n = 23 then
        23
    elif n = 24 then
        24
    elif n = 25 then
        25
    elif n = 26 then
        26
    elif n = 27 then
        27
    elif n = 28 then
        28
    elif n = 29 then
        29
    elif n = 30 then
        30
    elif n = 31 then
        31
    elif n = 32 then
        32
    else
        0

let rec private evenSwap<'A, 'B> (f: int -> int) (n: int) (a: 'A) (b: 'B) : int =
    let w =
        if n = -9 then
            evalBigTouch 1
        elif n = -8 then
            evalBigTouch 2
        elif n = -7 then
            evalBigTouch 3
        elif n = -6 then
            evalBigTouch 4
        elif n = -5 then
            evalBigTouch 5
        elif n = -4 then
            evalBigTouch 6
        elif n = -3 then
            evalBigTouch 7
        elif n = -2 then
            evalBigTouch 8
        elif n = -11 then
            evalBigTouch 9
        elif n = -12 then
            evalBigTouch 10
        elif n = -13 then
            evalBigTouch 11
        elif n = -14 then
            evalBigTouch 12
        elif n = -15 then
            evalBigTouch 13
        elif n = -16 then
            evalBigTouch 14
        elif n = -17 then
            evalBigTouch 15
        elif n = -18 then
            evalBigTouch 16
        elif n = -19 then
            evalBigTouch 17
        elif n = -20 then
            evalBigTouch 18
        else
            0

    if n <= 0 then
        f (1 + w)
    else
        oddSwap<'B, 'A> f (n - 1) b a

and private oddSwap<'A, 'B> (f: int -> int) (n: int) (a: 'A) (b: 'B) : int =
    let w =
        if n = -9 then
            evalBigTouch 1
        elif n = -8 then
            evalBigTouch 2
        elif n = -7 then
            evalBigTouch 3
        elif n = -6 then
            evalBigTouch 4
        elif n = -5 then
            evalBigTouch 5
        elif n = -4 then
            evalBigTouch 6
        elif n = -3 then
            evalBigTouch 7
        elif n = -2 then
            evalBigTouch 8
        elif n = -11 then
            evalBigTouch 9
        elif n = -12 then
            evalBigTouch 10
        elif n = -13 then
            evalBigTouch 11
        elif n = -14 then
            evalBigTouch 12
        elif n = -15 then
            evalBigTouch 13
        elif n = -16 then
            evalBigTouch 14
        elif n = -17 then
            evalBigTouch 15
        elif n = -18 then
            evalBigTouch 16
        elif n = -19 then
            evalBigTouch 17
        elif n = -20 then
            evalBigTouch 18
        else
            0

    if n <= 0 then
        f (2 + w)
    else
        evenSwap<'B, 'A> f (n - 1) b a

let rec private selfSwap<'A, 'B> (f: int -> int) (n: int) (a: 'A) (b: 'B) : int =
    let _ =
        evalPadWeight (
            if n < 0 then
                1
            else
                0
        )

    if n <= 0 then
        f 3
    else
        selfSwap<'B, 'A> f (n - 1) b a

let rec private evenHofH2 (f: int -> int) (n: int) (acc: int) : int =
    let w =
        if n = -9 then
            evalBigTouch 1
        elif n = -8 then
            evalBigTouch 2
        elif n = -7 then
            evalBigTouch 3
        elif n = -6 then
            evalBigTouch 4
        elif n = -5 then
            evalBigTouch 5
        elif n = -4 then
            evalBigTouch 6
        elif n = -3 then
            evalBigTouch 7
        elif n = -2 then
            evalBigTouch 8
        elif n = -11 then
            evalBigTouch 9
        elif n = -12 then
            evalBigTouch 10
        elif n = -13 then
            evalBigTouch 11
        elif n = -14 then
            evalBigTouch 12
        elif n = -15 then
            evalBigTouch 13
        elif n = -16 then
            evalBigTouch 14
        elif n = -17 then
            evalBigTouch 15
        elif n = -18 then
            evalBigTouch 16
        elif n = -19 then
            evalBigTouch 17
        elif n = -20 then
            evalBigTouch 18
        else
            0

    if n <= 0 then
        acc + w
    else
        oddHofH2 f (n - 1) (acc + f 1)

and private oddHofH2 (f: int -> int) (n: int) (acc: int) : int =
    let w =
        if n = -9 then
            evalBigTouch 1
        elif n = -8 then
            evalBigTouch 2
        elif n = -7 then
            evalBigTouch 3
        elif n = -6 then
            evalBigTouch 4
        elif n = -5 then
            evalBigTouch 5
        elif n = -4 then
            evalBigTouch 6
        elif n = -3 then
            evalBigTouch 7
        elif n = -2 then
            evalBigTouch 8
        elif n = -11 then
            evalBigTouch 9
        elif n = -12 then
            evalBigTouch 10
        elif n = -13 then
            evalBigTouch 11
        elif n = -14 then
            evalBigTouch 12
        elif n = -15 then
            evalBigTouch 13
        elif n = -16 then
            evalBigTouch 14
        elif n = -17 then
            evalBigTouch 15
        elif n = -18 then
            evalBigTouch 16
        elif n = -19 then
            evalBigTouch 17
        elif n = -20 then
            evalBigTouch 18
        else
            0

    if n <= 0 then
        acc + w
    else
        evenHofH2 f (n - 1) (acc + f 2)

let rec private raiseGenH1<'T> (f: int -> 'T) (n: int) : 'T =
    if n <= 0 then
        invalidOp "boom_h1"
    else
        f n

let rec private buildNonNullVia (next: int -> NonNullFuncStream) (n: int) : NonNullFuncStream =
    if n < 0 then
        NFEnd
    else
        let fn4 = System.Func<int, int, int, int, int>(fun a b c d -> a + b + c + d)
        NFStep(fn4, raiseGenH1 next (n - 1))

let rec private driveNonNull (n: int) : NonNullFuncStream = buildNonNullVia driveNonNull n

let private applyThenTail (f: int -> int) (k: int -> int) (x: int) : int = k (f x)

let rec private chainTailStep (k: int -> int) (n: int) (acc: int) : int =
    if n <= 0 then
        acc
    else
        applyThenTail (fun v -> v + 1) (fun v -> chainTailStep k (n - 1) (k v)) acc

let private forwardKToAssumed (pred: string -> bool) (s: string) : int =
    let b1 = Helpers.findBorrowedOrFallback pred s 3
    let b2 = Helpers.findBorrowedOrFallbackGen pred s s 4
    b1.Length + b2.Length

let private evalRegressionTests () : int =
    let before = liveCells ()

    let deep =
        if isLlvm () then
            200000
        else
            500

    let cpsDropDepth = 150000

    // Bug C1: KParam / EKnown forwarding into assumed-borrowed cross-file HOFs
    let pfx = "pre-" + string 9
    let ownedStr = pfx + "-owned"
    let c1Direct = Helpers.findBorrowedOrFallback (fun x -> x.StartsWith pfx) ownedStr 5
    let c1KParam = forwardKToAssumed (fun x -> x.StartsWith pfx) ownedStr

    // Bug C2: 150k linear CPS closure chain where recursive c0 precedes tail_field c1
    let bonus = 7
    let post = fun (x: int) -> x + bonus
    let mutable cpsK: int -> int = fun x -> x + 1

    for _ = 1 to cpsDropDepth do
        let prev = cpsK

        cpsK <-
            fun x ->
                if x >= 0 then
                    prev (x + 1)
                else
                    post x

    let c2Res = cpsK (-1)
    cpsK <- fun x -> x

    // Bug C3: Type-swapping & polymorphic recursive HOFs + non-KParam tail inside callK
    let cap = 10
    let swapRes = evenSwap<int, string> (fun x -> x + cap) deep 1 "a"
    let selfSwapRes = selfSwap<int, string> (fun x -> x + cap) deep 1 "a"
    let callKChainRes = chainTailStep (fun v -> v + 1) deep 0

    // Bug H1: generic $tc raise into fieldless non-hasNull union
    let caughtH1 =
        try
            driveNonNull 12 |> ignore
            false
        with :? System.InvalidOperationException as ex ->
            ex.Message = "boom_h1"

    // Bug H2: same-signature mutually recursive HOFs fused in O(1) stack on Zig
    let h2Depth =
#if FABLE_COMPILER
        200000
#else
        500
#endif
    let h2Res = evenHofH2 (fun x -> x + cap) h2Depth 0

    // Tier 2 pub VGlobal qualification
    Helpers.tier2GlobalMut <- 10
    let factor = 2
    let t2g1 = Helpers.applyWithGlobals (fun v -> v * factor) 5
    let t2g2 = Helpers.applyWithGlobals (fun v -> v * factor) 5

    // Rewritten List/Array maxBy, minBy, groupBy, countBy with capturing lambdas & single-item projection eval
    let scale = 3
    let mutable listHits = 0

    let oneMax =
        [ 7 ]
        |> List.maxBy (fun x ->
            listHits <- listHits + 1
            x * scale
        )

    let oneMin =
        [| 9 |]
        |> Array.minBy (fun x ->
            listHits <- listHits + 1
            x * scale
        )

    let lMax = [ 1; 4; 2 ] |> List.maxBy (fun x -> x * scale)
    let lMin = [ 3; 1; 4 ] |> List.minBy (fun x -> x * scale)
    let aMax = [| 2; 8; 5 |] |> Array.maxBy (fun x -> x * scale)
    let aMin = [| 6; 1; 5 |] |> Array.minBy (fun x -> x * scale)
    let groups = [ 1; 2; 3; 4 ] |> List.groupBy (fun x -> x % scale)
    let counts = [ 1; 2; 3; 4 ] |> List.countBy (fun x -> x % scale)

    check (
        c1Direct.Length = ownedStr.Length
        && c1KParam = ownedStr.Length * 2
        && c2Res = 6
        && swapRes =
            (if deep % 2 = 0 then
                 1 + cap
             else
                 2 + cap)
        && selfSwapRes = 3 + cap
        && callKChainRes = deep * 2
        && caughtH1
        && h2Res = (h2Depth / 2) * (1 + cap + 2 + cap)
        && t2g1 = ((5 + 42 + 5) * 2) + 11
        && t2g2 = ((5 + 42 + 5) * 2) + 12
        && oneMax = 7
        && oneMin = 9
        && listHits = 2
        && lMax = 4
        && lMin = 1
        && aMax = 8
        && aMin = 1
        && groups.Length = 3
        && counts.Length = 3
    )
    + checkCount (liveCells () - before) 0

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
    + callKTests ()
    + factsTests ()
    + tier2Tests ()
    + step7Tests ()
    + step8Tests ()
    + step9Tests ()
    + step10Tests ()
    + step11Tests ()
    + evalRegressionTests ()
    + checkCount (liveCells () - before) 0
