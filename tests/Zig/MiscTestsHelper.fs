module Fable.Tests.MiscTestsHelper

let counter =
    let mutable i = 0
    fun () ->
        i <- i + 1
        i

type Type = {
    a : int
    b : int
    c : int
    d : int
    e : int
}
  with
    static member New(n) = {
        a = n
        b = n * 2
        c = n * 3
        d = n * 4
        e = counter()  // <== should only be called twice
      }

    member        this.Method  (v:bool) = { this with a = this.a * if v then 2 else 3 }
    member inline this.MethodI (v:bool) = { this with a = this.a * if v then 2 else 3 }
    member        this.Method  ()       = { this with a = this.a * 10 }
    member inline this.MethodI ()       = { this with a = this.a * 10 }

type Vector2<[<Measure>] 'u> = Vector2 of x: float<'u> * y: float<'u> with

  static member inline ( + ) (Vector2(ax, ay), Vector2(bx, by)) = Vector2(ax + bx, ay + by)
  static member inline ( * ) (scalar, Vector2(x, y)) = Vector2(scalar * x, scalar * y)

// Issue4634: an [<AttachMembers>] union with static members, defined in a separate
// module/file so use sites reference it across modules (an Import, not a same-file
// identifier). This exercises the cross-file path of the static-member-on-union fix.
[<Fable.Core.AttachMembers>]
type CrossModuleDemo =
    | A of string
    | B

    static member propDefault = A "prop"
    static member methDefault() = A "meth"

let mutable trackedCalls = 0

let track x =
    trackedCalls <- trackedCalls + 1
    x

let mutable forLoopCrossFileArray = [| 1; 2; 3 |]

let mutable forLoopCrossFileCalls = 0

let forLoopCrossFileMakeArray () =
    forLoopCrossFileCalls <- forLoopCrossFileCalls + 1
    [| 1; 2; 3 |]

// Step 10 cross-file tail-call / virtual / interface test helpers
exception TcCrossBoom of atDepth: int * size: int

let tcCrossPong (cb: int -> int -> string -> int) (n: int) (raiseAt: int) (tag: string) : int =
    if n = raiseAt then raise (TcCrossBoom(raiseAt, tag.Length + n))
    elif n <= 0 then tag.Length + n
    else cb (n - 1) raiseAt tag

let tcCrossLeaf (n: int) (tag: string) : int = n + tag.Length

let tcCrossPongGen (cb: int -> 'T -> int) (n: int) (v: 'T) : int =
    if n <= 0 then 1 else cb (n - 1) v

[<AbstractClass>]
type TcCrossBase(label: string) =
    member _.Label = label
    abstract Step: TcCrossBase * int * int * string -> int

type TcCrossHelperSub(prefix: string) =
    inherit TcCrossBase(prefix)

    override this.Step(other, n, raiseAt, tag) =
        if n = raiseAt then raise (TcCrossBoom(raiseAt, this.Label.Length + tag.Length))
        elif n <= 0 then this.Label.Length + tag.Length + n
        else other.Step(this, n - 1, raiseAt, tag)

type ITcCrossPing =
    abstract Ping: ITcCrossPing * int * int * string -> int

type ITcCrossSubPing =
    inherit ITcCrossPing
    abstract Bonus: int

type TcHelperObjPing(prefix: string) =
    interface ITcCrossPing with
        member this.Ping(other, n, raiseAt, tag) =
            if n = raiseAt then raise (TcCrossBoom(raiseAt, prefix.Length + tag.Length))
            elif n <= 0 then prefix.Length + tag.Length + n
            else other.Ping(this, n - 1, raiseAt, tag)

// Step 11 cross-file TRMC helper
let tcTrmcCrossCons (next: int -> int -> string list) (n: int) (raiseAt: int) : string list =
    if n = raiseAt then raise (TcCrossBoom(raiseAt, n))
    elif n <= 0 then []
    else ("h-" + string n) :: next (n - 1) raiseAt

// Non-Tier-2 cross-file borrowed-return HOF helpers (size > 250)
let tcC1PadWeight (n: int) : int =
    if n = 1 then 10 elif n = 2 then 20 elif n = 3 then 30 elif n = 4 then 40
    elif n = 5 then 50 elif n = 6 then 60 elif n = 7 then 70 elif n = 8 then 80
    elif n = 9 then 90 elif n = 10 then 100 elif n = 11 then 110 elif n = 12 then 120
    elif n = 13 then 130 elif n = 14 then 140 elif n = 15 then 150 elif n = 16 then 160
    elif n = 17 then 170 elif n = 18 then 180 elif n = 19 then 190 elif n = 20 then 200
    elif n = 21 then 210 elif n = 22 then 220 elif n = 23 then 230 elif n = 24 then 240
    elif n = 25 then 250 elif n = 26 then 260 elif n = 27 then 270 elif n = 28 then 280
    elif n = 29 then 290 elif n = 30 then 300 elif n = 31 then 310 elif n = 32 then 320
    elif n = 33 then 330 elif n = 34 then 340 elif n = 35 then 350 else 0

let tcFindBorrowedOrFallback (pred: string -> bool) (fallback: string) (tag: int) : string =
    let w =
        if tag = 1 then tcC1PadWeight 1 elif tag = 2 then tcC1PadWeight 2 elif tag = 3 then tcC1PadWeight 3
        elif tag = 4 then tcC1PadWeight 4 elif tag = 5 then tcC1PadWeight 5 elif tag = 6 then tcC1PadWeight 6
        elif tag = 7 then tcC1PadWeight 7 elif tag = 8 then tcC1PadWeight 8 elif tag = 9 then tcC1PadWeight 9
        elif tag = 10 then tcC1PadWeight 10 elif tag = 11 then tcC1PadWeight 11 elif tag = 12 then tcC1PadWeight 12
        elif tag = 13 then tcC1PadWeight 13 elif tag = 14 then tcC1PadWeight 14 elif tag = 15 then tcC1PadWeight 15
        elif tag = 16 then tcC1PadWeight 16 elif tag = 17 then tcC1PadWeight 17 elif tag = 18 then tcC1PadWeight 18
        elif tag = 19 then tcC1PadWeight 19 elif tag = 20 then tcC1PadWeight 20 elif tag = 21 then tcC1PadWeight 21
        elif tag = 22 then tcC1PadWeight 22 elif tag = 23 then tcC1PadWeight 23 elif tag = 24 then tcC1PadWeight 24
        else tcC1PadWeight tag

    if w >= 0 && pred fallback then fallback else fallback

let tcFindBorrowedOrFallbackGen<'T> (pred: 'T -> bool) (fallback: string) (item: 'T) (tag: int) : string =
    let w =
        if tag = 1 then tcC1PadWeight 1 elif tag = 2 then tcC1PadWeight 2 elif tag = 3 then tcC1PadWeight 3
        elif tag = 4 then tcC1PadWeight 4 elif tag = 5 then tcC1PadWeight 5 elif tag = 6 then tcC1PadWeight 6
        elif tag = 7 then tcC1PadWeight 7 elif tag = 8 then tcC1PadWeight 8 elif tag = 9 then tcC1PadWeight 9
        elif tag = 10 then tcC1PadWeight 10 elif tag = 11 then tcC1PadWeight 11 elif tag = 12 then tcC1PadWeight 12
        elif tag = 13 then tcC1PadWeight 13 elif tag = 14 then tcC1PadWeight 14 elif tag = 15 then tcC1PadWeight 15
        elif tag = 16 then tcC1PadWeight 16 elif tag = 17 then tcC1PadWeight 17 elif tag = 18 then tcC1PadWeight 18
        elif tag = 19 then tcC1PadWeight 19 elif tag = 20 then tcC1PadWeight 20 elif tag = 21 then tcC1PadWeight 21
        elif tag = 22 then tcC1PadWeight 22 elif tag = 23 then tcC1PadWeight 23 elif tag = 24 then tcC1PadWeight 24
        else tcC1PadWeight tag

    if w >= 0 && pred item then fallback else fallback

// Tier 2 pub VGlobal qualification helpers
let tcTier2GlobalConst = 42
let tcTier2GlobalStr = "glb-" + string 7
let mutable tcTier2GlobalMut = 10

let tcApplyWithGlobals (f: int -> int) (x: int) : int =
    tcTier2GlobalMut <- tcTier2GlobalMut + 1
    f (x + tcTier2GlobalConst + tcTier2GlobalStr.Length) + tcTier2GlobalMut
