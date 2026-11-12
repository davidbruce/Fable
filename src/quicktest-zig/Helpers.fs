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
