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
