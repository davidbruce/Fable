module Shapes

// Base classes for Inheritance.fs, which derives from them in another file.

[<AbstractClass>]
type Shape(name: string) =
    member _.Name = name
    abstract Area: unit -> float
    abstract Scale: factor: float -> unit
    abstract Describe: unit -> string

    default this.Describe() =
        sprintf "%s with area %.2f" this.Name (this.Area())

    abstract Corners: int
    default _.Corners = 0

/// A class with no virtual member that another file derives from.
type Counter() =
    let mutable count = 0
    member _.Count = count
    member _.Bump() = count <- count + 1
