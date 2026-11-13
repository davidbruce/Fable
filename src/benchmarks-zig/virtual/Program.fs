module Program

// Classes: virtual calls through an abstract class, and objects made and given up.

[<AbstractClass>]
type Shape() =
    abstract Area: unit -> float

type Circle(r: float) =
    inherit Shape()
    override _.Area() = 3.0 * r * r

type Rect(w: float, h: float) =
    inherit Shape()
    override _.Area() = w * h

[<EntryPoint>]
let main _ =
    let shapes: Shape[] =
        Array.init
            1000
            (fun i ->
                if i % 2 = 0 then
                    Circle(float i) :> Shape
                else
                    Rect(float i, 2.0)
            )

    let mutable total = 0.0

    for _ in 1..20000 do
        for s in shapes do
            total <- total + s.Area()

    let mutable made = 0.0

    for i in 1..2000000 do
        let s: Shape =
            if i % 2 = 0 then
                Circle 1.0
            else
                Rect(1.0, 2.0)

        made <- made + s.Area()

    printfn "%.1f %.1f" total made
    0
