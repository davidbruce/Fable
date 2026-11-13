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
