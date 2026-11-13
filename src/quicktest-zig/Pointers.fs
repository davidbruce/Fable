module Pointers

// Byrefs and spans: `byref`/`inref`/`outref` are pointers, `&x` takes the address of a
// variable, and `Span`/`ReadOnlySpan` are slices of the array they view (which stays alive
// while they are in use). `run` returns the number of failed checks.

open System
open Fable.Core.Zig

let liveCells () : int = Counters.liveCells ()
let counting () : bool = Counters.isCounting ()

let check (ok: bool) : int =
    if ok then
        0
    else
        1

[<Struct>]
type Descriptor =
    {
        mutable Addr: int
        mutable Length: int
        mutable Flags: int
    }

[<Struct>]
type Header =
    {
        DmaAddr: int
        PayloadLen: int
    }

let submit (desc: byref<Descriptor>) (hdr: inref<Header>) : unit =
    desc.Addr <- hdr.DmaAddr
    desc.Length <- hdr.PayloadLen
    desc.Flags <- 1

let bump (x: byref<int>) : unit = x <- x + 1

let swap (a: byref<int>) (b: byref<int>) : unit =
    let t = a
    a <- b
    b <- t

let sumSpan (s: ReadOnlySpan<int>) : int =
    let mutable acc = 0

    for i in 0 .. s.Length - 1 do
        acc <- acc + s.[i]

    acc

let fillRamp (dst: Span<int>) (start: int) : unit =
    for i in 0 .. dst.Length - 1 do
        dst.[i] <- start + i

let scaleInPlace (dst: Span<int>) (k: int) : unit =
    for i in 0 .. dst.Length - 1 do
        dst.[i] <- dst.[i] * k

type Tagged =
    {
        Tag: string
        Id: int
    }

let overwriteByref (slot: byref<string>) (value: string) : unit = slot <- value

let joinChars (sp: ReadOnlySpan<char>) : string = String(sp.ToArray())

let checkManagedSpans () : int =
    let before = liveCells ()

    let mutable innerFailed = 0

    let runInner () =
        let words = [| "one" + "!"; "two" + "!"; "three" + "!"; "four" + "!" |]
        let sp = Span<string>(words)
        overwriteByref &sp.[0] ("zero" + "!")
        sp.Slice(1, 2).Fill("mid" + "!")
        let tail = sp.Slice(2).ToArray()
        let ok1 = sp.[0] = "zero!" && sp.[1] = "mid!" && sp.[2] = "mid!" && sp.[3] = "four!"
        let ok2 = tail.Length = 2 && tail.[0] = "mid!" && tail.[1] = "four!"

        // Overlapping CopyTo: shift [0..2] -> [1..3]
        sp.Slice(0, 3).CopyTo(sp.Slice(1, 3))

        let ok3 =
            words.[0] = "zero!"
            && words.[1] = "zero!"
            && words.[2] = "mid!"
            && words.[3] = "mid!"

        let dstTooShort = [| "x" |]
        let tryShort = sp.TryCopyTo(Span<string>(dstTooShort))

        let mutable copyEx = false

        try
            sp.CopyTo(Span<string>(dstTooShort))
        with :? ArgumentException ->
            copyEx <- true

        sp.Slice(1, 2).Clear()
        let okClear = isNull words.[1] && isNull words.[2] && words.[3] = "mid!"

        let recs =
            [|
                {
                    Tag = "a" + "1"
                    Id = 1
                }
                {
                    Tag = "b" + "2"
                    Id = 2
                }
                {
                    Tag = "c" + "3"
                    Id = 3
                }
            |]

        let rsp = Span<Tagged>(recs)
        let r0 = rsp.[0]
        rsp.[0] <- rsp.[2]
        rsp.[2] <- r0
        let ro = ReadOnlySpan<Tagged>(recs)
        let cloned = ro.Slice(0, 2).ToArray()
        let okRec = recs.[0].Id = 3 && cloned.Length = 2 && cloned.[1].Tag = "b2"

        let text = "hello " + "world"
        let roChars = ReadOnlySpan<char>(text.ToCharArray()).Slice(6, 5)

        let okChars =
            roChars.Length = 5
            && joinChars roChars = "world"
            && not roChars.IsEmpty
            && Span<int>.Empty.IsEmpty
            && (Span<string>()).IsEmpty

        innerFailed <-
            check ok1
            + check ok2
            + check ok3
            + check (not tryShort)
            + check copyEx
            + check okClear
            + check okRec
            + check okChars

    runInner ()

    innerFailed
    + (if counting () then
           check (liveCells () = before)
       else
           0)

let run () : int =
    let before = liveCells ()

    let mutable desc =
        {
            Addr = 0
            Length = 0
            Flags = 0
        }

    let hdr =
        {
            DmaAddr = 4096
            PayloadLen = 512
        }

    submit &desc &hdr
    let mutable n = 41
    bump &n
    let mutable p = 1
    let mutable q = 2
    swap &p &q
    let buf = Array.zeroCreate<int> 8
    let all = Span<int>(buf)
    fillRamp all 10
    let window = all.Slice(2, 4)
    scaleInPlace window 2
    let whole = sumSpan (ReadOnlySpan<int>(buf))
    let part = sumSpan (Span<int>.op_Implicit window)

    let outside =
        try
            let s = Span<int>(buf)
            string s.[8]
        with :? IndexOutOfRangeException ->
            "outside"

    let failed =
        check (desc.Addr = 4096 && desc.Length = 512 && desc.Flags = 1)
        + check (n = 42 && p = 2 && q = 1)
        + check (whole = 162 && part = 108 && buf.[3] = 26)
        + check (outside = "outside")
        + checkManagedSpans ()

    printfn "pointers: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
