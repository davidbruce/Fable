module Members

// Members on records and unions: properties, methods, static members, operators a type
// declares for itself, and a `ToString` of its own. A member is a function whose first
// argument is the object. `run` returns the number of failed checks.

open Fable.Core.Zig

let liveCells () : int = Counters.liveCells ()
let counting () : bool = Counters.isCounting ()

let check (ok: bool) : int =
    if ok then
        0
    else
        1

let same (expected: string) (actual: string) : int =
    if actual = expected then
        0
    else
        1

type Vec =
    {
        X: int
        Y: int
    }

    member v.Length2 = v.X * v.X + v.Y * v.Y

    member v.Scale(k: int) =
        {
            X = v.X * k
            Y = v.Y * k
        }

    member v.Add(o: Vec, k: int) =
        {
            X = v.X + o.X + k
            Y = v.Y + o.Y
        }

    member v.Curried (a: int) (b: int) = v.X * a + v.Y * b

    static member Zero =
        {
            X = 0
            Y = 0
        }

    static member Make (x: int) (y: int) =
        {
            X = x
            Y = y
        }

    static member (+)(a: Vec, b: Vec) =
        {
            X = a.X + b.X
            Y = a.Y + b.Y
        }

    static member (*)(a: Vec, k: int) = a.Scale k
    static member (~-)(a: Vec) = a.Scale -1
    override v.ToString() = $"<{v.X}, {v.Y}>"

type Shape =
    | Circle of int
    | Square of int
    | Named of string * Shape

    member s.Area =
        match s with
        | Circle r -> 3 * r * r
        | Square a -> a * a
        | Named(_, inner) -> inner.Area

    member s.Describe(prefix: string) =
        match s with
        | Named(name, _) -> prefix + name
        | _ -> prefix + string s.Area

    static member Unit = Square 1

type Counter =
    {
        mutable Count: int
        Label: string
    }

    member c.Bump() = c.Count <- c.Count + 1

    member c.BumpBy(n: int) =
        c.Count <- c.Count + n
        c.Count

    member c.Text = c.Label + "=" + string c.Count

type Pair<'T> =
    {
        First: 'T
        Second: 'T
    }

    member p.Swap =
        {
            First = p.Second
            Second = p.First
        }

    member p.Map(f: 'T -> 'U) =
        {
            First = f p.First
            Second = f p.Second
        }

    static member Twice(x: 'T) =
        {
            First = x
            Second = x
        }

type Temp =
    | Celsius of float

    override t.ToString() =
        match t with
        | Celsius c -> sprintf "%.1f C" c

let run () : int =
    let before = liveCells ()

    let v =
        {
            X = 3
            Y = 4
        }

    let w = Vec.Make 1 2

    let counter =
        {
            Count = 0
            Label = "n" + string 1
        }

    counter.Bump()
    counter.Bump()
    let after = counter.BumpBy 5

    let words =
        {
            First = "a" + "b"
            Second = "c"
        }

    let price = Helpers.Money.OfCents 1999 + Helpers.Money.OfCents 251
    let scale = v.Scale
    let dot = v.Curried 2

    let failed =
        check (
            v.Length2 = 25
            && (v.Scale 2).X = 6
            && (v.Add(w, 10)).X = 14
            && v.Curried 2 3 = 18
        )
        + check (
            Vec.Zero =
                {
                    X = 0
                    Y = 0
                }
            && v + w =
                {
                    X = 4
                    Y = 6
                }
            && v * 2 = v.Scale 2
            && -v = v.Scale -1
        )
        + check ((scale 3).Y = 12 && dot 1 = 10)
        + same "<3, 4>|<3, 4>|<4, 6>|<3, 4>" (v.ToString() + "|" + string v + "|" + $"{v + w}" + "|" + sprintf "%O" v)
        + same "{ X = 3\n  Y = 4 }" (sprintf "%A" v)
        + check ((Circle 2).Area = 12 && (Named("big", Square 3)).Area = 9 && Shape.Unit.Area = 1)
        + same "it is big|it is 12" ((Named("big", Square 3)).Describe "it is " + "|" + (Circle 2).Describe "it is ")
        + check (after = 7 && counter.Count = 7)
        + same "n1=7" counter.Text
        + check (
            words.Swap.First = "c"
            && (words.Map String.length).First = 2
            && (Pair<int>.Twice 4).Second = 4
        )
        + same "36.5 C|36.5 C" (string (Celsius 36.5) + "|" + $"{Celsius 36.5}")
        + check (price.Total = 2250 && price.Units = 22)
        + same "22.50|22.50" (price.ToString() + "|" + string price)
        + check (
            ((Helpers.Tagged<int>.Of 5).With "five").Item = "five"
            && (Helpers.Tagged<string>.Of "x").Mark = "of"
        )

    printfn "members: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
