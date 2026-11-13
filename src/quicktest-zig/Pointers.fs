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

    printfn "pointers: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
