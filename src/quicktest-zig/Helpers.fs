module Helpers

/// (a second file, so that the quicktest also covers a call across files)
let clamp (lo: int) (hi: int) (x: int) : int =
    if x < lo then
        lo
    elif x > hi then
        hi
    else
        x

let isEven (x: int) : bool = x % 2 = 0

/// (types declared here and used from QuickTest.fs)
type Point =
    {
        X: int
        Y: int
    }

type Shape =
    | Circle of radius: float
    | Rect of width: float * height: float
    | Dot

let origin () : Point =
    {
        X = 0
        Y = 0
    }

let area (s: Shape) : float =
    match s with
    | Circle r -> 3.0 * r * r
    | Rect(w, h) -> w * h
    | Dot -> 0.0

/// (a recursive union: its values live in reference-counted cells; the functions below are
/// called from another file with such values)
type IntList =
    | Nil
    | Cons of head: int * tail: IntList

let rec rangeFrom (lo: int) (hi: int) : IntList =
    if lo > hi then
        Nil
    else
        Cons(lo, rangeFrom (lo + 1) hi)

let rec sumList (xs: IntList) : int =
    match xs with
    | Nil -> 0
    | Cons(h, t) -> h + sumList t

let tailOf (xs: IntList) : IntList =
    match xs with
    | Nil -> Nil
    | Cons(_, t) -> t

let rec incAll (xs: IntList) : IntList =
    match xs with
    | Nil -> Nil
    | Cons(h, t) -> Cons(h + 1, incAll t)

/// (a generic type and generic functions that another file uses)
type Box<'T> =
    {
        Value: 'T
        Tag: int
    }

let boxOf (tag: int) (value: 'T) : Box<'T> =
    {
        Value = value
        Tag = tag
    }

let mapBox (f: 'T -> 'U) (b: Box<'T>) : Box<'U> =
    {
        Value = f b.Value
        Tag = b.Tag
    }

/// (an exception that another file handles, and functions that raise it)
exception TooBig of limit: int * value: int

let addChecked (limit: int) (a: int) (b: int) : int =
    if a + b > limit then
        raise (TooBig(limit, a + b))
    else
        a + b

let rec sumChecked (limit: int) (xs: IntList) : int =
    match xs with
    | Nil -> 0
    | Cons(h, t) -> addChecked limit h (sumChecked limit t)

/// (a type with members that another file uses)
type Money =
    {
        Units: int
        Cents: int
    }

    member m.Total = m.Units * 100 + m.Cents
    member m.Add(other: Money) = Money.OfCents(m.Total + other.Total)

    static member OfCents(cents: int) =
        {
            Units = cents / 100
            Cents = cents % 100
        }

    static member (+)(a: Money, b: Money) = a.Add b

    override m.ToString() =
        string m.Units + "." + (string m.Cents).PadLeft(2, '0')

/// (a generic type with members that another file uses)
type Tagged<'T> =
    {
        Mark: string
        Item: 'T
    }

    member t.With(item: 'U) =
        {
            Mark = t.Mark
            Item = item
        }

    static member Of(item: 'T) =
        {
            Mark = "of"
            Item = item
        }

/// (module-level values that another file reads and assigns)
let primes = [ 2; 3; 5; 7; 11 ]
let banner = "helpers " + string (sumList (rangeFrom 1 4))
let mutable hits = 0
let mutable lastSeen = "nothing"

let visit (who: string) : int =
    hits <- hits + 1
    lastSeen <- who + "#" + string hits
    hits

/// (an interface and a class that another file uses)
type IGreeter =
    abstract Greet: string -> string
    abstract Count: int

type Greeter(prefix: string) =
    let mutable count = 0

    member _.Prefix = prefix

    interface IGreeter with
        member _.Greet(name: string) =
            count <- count + 1
            prefix + ", " + name

        member _.Count = count

/// Cross-file ownership facts test helpers (Part 1: Modes, RetFrom, borrow-raise edge)
type StrPair =
    {
        First: string
        Second: string
    }

let firstStr (p: StrPair) : string = p.First

let rec countAny (xs: 'T list) : int =
    match xs with
    | [] -> 0
    | _ :: t -> 1 + countAny t

let rec sumStrLengths (xs: string list) : int =
    match xs with
    | [] -> 0
    | s :: t -> s.Length + sumStrLengths t

let borrowAndFail (xs: string list) : int =
    let n = sumStrLengths xs

    if n >= 0 then
        raise (TooBig(0, n))
    else
        0

/// Cross-file Raises and field-sensitive Stores test helpers (Part 1, Step 5)
let pureAddInts (a: int) (b: int) : int = a + b

[<Struct>]
type MutPairStruct =
    {
        mutable A: string
        mutable B: string
    }

let setStructB (s: byref<MutPairStruct>) (v: string) : unit = s.B <- v

/// Cross-file Tier 2 HOF cloning test helpers (Part 2, Step 6)
type CustomStrList =
    | CustomNil
    | CustomCons of item: string * rest: CustomStrList

let mapCustomWithLoop (f: string -> string) (xs: CustomStrList) : CustomStrList =
    let rec loop cur =
        match cur with
        | CustomNil -> CustomNil
        | CustomCons(h, t) -> CustomCons(f h, loop t)

    loop xs

let mapIntListTier2 (f: int -> int) (xs: IntList) : IntList =
    let rec loop cur =
        match cur with
        | Nil -> Nil
        | Cons(h, t) -> Cons(f h, loop t)

    loop xs

/// Cross-file $tc, virtual class, and fat-pointer interface helpers (Part 3, Step 10)
let crossPong (cb: int -> int -> string -> int) (n: int) (raiseAt: int) (tag: string) : int =
    if n = raiseAt then
        raise (TooBig(raiseAt, tag.Length + n))
    elif n <= 0 then
        tag.Length + n
    else
        cb (n - 1) raiseAt tag

let crossLeaf (n: int) (tag: string) : int = n + tag.Length

let crossPongGen (cb: int -> 'T -> int) (n: int) (v: 'T) : int =
    if n <= 0 then
        1
    else
        cb (n - 1) v

[<AbstractClass>]
type CrossBase(label: string) =
    member _.Label = label
    abstract Step: CrossBase * int * int * string -> int

type CrossSubInHelpers(prefix: string) =
    inherit CrossBase(prefix)

    override this.Step(other, n, raiseAt, tag) =
        if n = raiseAt then
            raise (TooBig(raiseAt, this.Label.Length + tag.Length))
        elif n <= 0 then
            this.Label.Length + tag.Length + n
        else
            other.Step(this, n - 1, raiseAt, tag)

type ICrossPing =
    abstract Ping: ICrossPing * int * int * string -> int

type ICrossSubPing =
    inherit ICrossPing
    abstract Bonus: int

type HelpersObjPing(prefix: string) =
    interface ICrossPing with
        member this.Ping(other, n, raiseAt, tag) =
            if n = raiseAt then
                raise (TooBig(raiseAt, prefix.Length + tag.Length))
            elif n <= 0 then
                prefix.Length + tag.Length + n
            else
                other.Ping(this, n - 1, raiseAt, tag)

/// Step 11 cross-file TRMC into unknown callee helper
let trmcCrossCons (next: int -> int -> string list) (n: int) (raiseAt: int) : string list =
    if n = raiseAt then
        raise (TooBig(raiseAt, n))
    elif n <= 0 then
        []
    else
        ("h-" + string n) :: next (n - 1) raiseAt

/// Non-Tier-2 cross-file borrowed-return HOF helper (size > 250 prevents Tier 2 body cloning)
let c1PadWeight (n: int) : int =
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
    elif n = 31 then
        310
    elif n = 32 then
        320
    elif n = 33 then
        330
    elif n = 34 then
        340
    elif n = 35 then
        350
    else
        0

let findBorrowedOrFallback (pred: string -> bool) (fallback: string) (tag: int) : string =
    let w =
        if tag = 1 then
            c1PadWeight 1
        elif tag = 2 then
            c1PadWeight 2
        elif tag = 3 then
            c1PadWeight 3
        elif tag = 4 then
            c1PadWeight 4
        elif tag = 5 then
            c1PadWeight 5
        elif tag = 6 then
            c1PadWeight 6
        elif tag = 7 then
            c1PadWeight 7
        elif tag = 8 then
            c1PadWeight 8
        elif tag = 9 then
            c1PadWeight 9
        elif tag = 10 then
            c1PadWeight 10
        elif tag = 11 then
            c1PadWeight 11
        elif tag = 12 then
            c1PadWeight 12
        elif tag = 13 then
            c1PadWeight 13
        elif tag = 14 then
            c1PadWeight 14
        elif tag = 15 then
            c1PadWeight 15
        elif tag = 16 then
            c1PadWeight 16
        elif tag = 17 then
            c1PadWeight 17
        elif tag = 18 then
            c1PadWeight 18
        elif tag = 19 then
            c1PadWeight 19
        elif tag = 20 then
            c1PadWeight 20
        elif tag = 21 then
            c1PadWeight 21
        elif tag = 22 then
            c1PadWeight 22
        elif tag = 23 then
            c1PadWeight 23
        elif tag = 24 then
            c1PadWeight 24
        else
            c1PadWeight tag

    if w >= 0 && pred fallback then
        fallback
    else
        fallback

let findBorrowedOrFallbackGen<'T> (pred: 'T -> bool) (fallback: string) (item: 'T) (tag: int) : string =
    let w =
        if tag = 1 then
            c1PadWeight 1
        elif tag = 2 then
            c1PadWeight 2
        elif tag = 3 then
            c1PadWeight 3
        elif tag = 4 then
            c1PadWeight 4
        elif tag = 5 then
            c1PadWeight 5
        elif tag = 6 then
            c1PadWeight 6
        elif tag = 7 then
            c1PadWeight 7
        elif tag = 8 then
            c1PadWeight 8
        elif tag = 9 then
            c1PadWeight 9
        elif tag = 10 then
            c1PadWeight 10
        elif tag = 11 then
            c1PadWeight 11
        elif tag = 12 then
            c1PadWeight 12
        elif tag = 13 then
            c1PadWeight 13
        elif tag = 14 then
            c1PadWeight 14
        elif tag = 15 then
            c1PadWeight 15
        elif tag = 16 then
            c1PadWeight 16
        elif tag = 17 then
            c1PadWeight 17
        elif tag = 18 then
            c1PadWeight 18
        elif tag = 19 then
            c1PadWeight 19
        elif tag = 20 then
            c1PadWeight 20
        elif tag = 21 then
            c1PadWeight 21
        elif tag = 22 then
            c1PadWeight 22
        elif tag = 23 then
            c1PadWeight 23
        elif tag = 24 then
            c1PadWeight 24
        else
            c1PadWeight tag

    if w >= 0 && pred item then
        fallback
    else
        fallback

/// Tier 2 `pub` VGlobal qualification helpers (small size <= 250)
let tier2GlobalConst = 42
let tier2GlobalStr = "glb-" + string 7
let mutable tier2GlobalMut = 10

let applyWithGlobals (f: int -> int) (x: int) : int =
    tier2GlobalMut <- tier2GlobalMut + 1
    f (x + tier2GlobalConst + tier2GlobalStr.Length) + tier2GlobalMut
