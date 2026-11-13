module Inheritance

// Classes that derive from classes (also of another file), abstract classes, virtual members,
// `base` calls, type tests and casts, and objects that refer to each other.
// `run` returns the number of failed checks.

open Fable.Core.Zig
open Shapes

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

type Circle(r: float) =
    inherit Shape("circle")
    let mutable radius = r
    member _.Radius = radius
    override _.Area() = 3.0 * radius * radius
    override _.Scale(factor) = radius <- radius * factor

type Rect(w: float, h: float) =
    inherit Shape("rect")
    member val Width = w with get, set
    member val Height = h with get, set
    override this.Area() = this.Width * this.Height

    override this.Scale(factor) =
        this.Width <- this.Width * factor
        this.Height <- this.Height * factor

    override _.Corners = 4

type Square(side: float) =
    inherit Rect(side, side)
    override this.Describe() = "square! " + base.Describe()

/// A node of a tree of shapes whose children point back at it.
type Node(shape: Shape) =
    let mutable parent: Node option = None
    let mutable children: Node list = []
    member _.Shape = shape
    member _.Parent = parent

    member this.Add(child: Node) =
        child.SetParent this
        children <- child :: children

    member _.SetParent(p: Node) = parent <- Some p
    member _.Children = children

type Ticker() =
    inherit Counter()

    member this.Twice() =
        this.Bump()
        this.Bump()

type IArea =
    abstract Size: unit -> float

type Named(name: string) =
    member _.Name = name
    override _.ToString() = "named " + name

    interface IArea with
        member _.Size() = float name.Length

type Labelled(name: string, label: string) =
    inherit Named(name)
    member _.Label = label

let size (a: IArea) = a.Size()

type IBase =
    abstract A: unit -> int

type IDerived =
    inherit IBase
    abstract B: unit -> int

type Both() =
    interface IDerived with
        member _.A() = 1
        member _.B() = 2

let viaDerived (x: IDerived) = x.A() + x.B()
let viaBase (x: IBase) = x.A()

let both =
    { new IDerived with
        member _.A() = 10
        member _.B() = 20
    }

let total (shapes: Shape list) =
    shapes |> List.sumBy (fun s -> s.Area())

let kind (s: Shape) =
    match s with
    | :? Square -> "square"
    | :? Rect as r -> sprintf "rect %gx%g" r.Width r.Height
    | :? Circle as c -> sprintf "circle %g" c.Radius
    | _ -> "other"

let run () : int =
    let before = liveCells ()

    let shapes: Shape list = [ Circle 1.0; Rect(2.0, 3.0); Square 2.0 ]
    let described = shapes |> List.map (fun s -> s.Describe()) |> String.concat "|"
    let corners = shapes |> List.map (fun s -> s.Corners)
    let areaBefore = total shapes

    for s in shapes do
        s.Scale 2.0

    let areaAfter = total shapes
    let kinds = shapes |> List.map kind |> String.concat "|"

    let cast =
        try
            let s: Shape = Circle 1.0
            (s :?> Rect).Width |> string
        with :? System.InvalidCastException as e ->
            e.Message

    let tree =
        let root = Node(Circle 1.0)
        let a = Node(Square 1.0)
        let b = Node(Rect(1.0, 2.0))
        root.Add a
        root.Add b
        a.Add(Node(Circle 2.0))

        (root.Children |> List.sumBy (fun n -> n.Shape.Area()))
        + (a.Children
           |> List.sumBy (fun n ->
               match n.Parent with
               | Some p -> p.Shape.Area()
               | None -> 0.0
           ))

    let t = Ticker()
    t.Twice()
    t.Bump()

    let failed =
        same "circle with area 3.00|rect with area 6.00|square! rect with area 4.00" described
        + check (corners = [ 0; 4; 4 ])
        + check (areaBefore = 13.0 && areaAfter = 52.0)
        + same "circle 2|rect 4x6|square" kinds
        + same "Unable to cast object of type 'Circle' to type 'Rect'." cast
        + check (tree = 4.0)
        + check (t.Count = 3)
        + same "Inheritance+Circle" (string (Circle 1.0))
        + check (
            viaDerived (Both()) = 3
            && viaBase (Both()) = 1
            && viaBase (Both() :> IDerived) = 1
            && viaDerived both + viaBase both = 40
        )
        + same
            "named abc|named xy|3|2"
            (string (Named "abc")
             + "|"
             + string (Labelled("xy", "l"))
             + "|"
             + string (size (Named "abc"))
             + "|"
             + string (size (Labelled("xy", "l"))))

    printfn "inheritance: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
