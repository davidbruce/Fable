module Resources

// Resources and stack arenas, for code that runs where there is hardware and no heap.
// A type that implements IResource<'T> is destroyed right after its last use (its Destroy
// runs) and is move-only; an ISharedResource<'T> is shared by its copies (Dup runs at each).
// The hooks never run on .NET, so they may not change what the program computes: this test
// watches them through the runtime's counters. A [<StackArena(bytes)>] function allocates
// from a buffer on its stack. `run` returns the number of failed checks.

#nowarn "3535" // interfaces with static abstract members

open Fable.Core
open Fable.Core.Zig

let counting () : bool = Counters.isCounting ()
let liveCells () : int = Counters.liveCells ()

let check (ok: bool) : int =
    if ok then
        0
    else
        1

type IResource<'T when 'T :> IResource<'T>> =
    static abstract Destroy: 'T -> unit

type ISharedResource<'T when 'T :> ISharedResource<'T>> =
    inherit IResource<'T>
    static abstract Dup: 'T -> 'T

/// (what the hardware would do: nothing the program sees)
[<Emit("_ = $0")>]
let hwRelease (handle: int) : unit = ()

/// A move-only resource: a buffer of the hardware.
type DmaBuffer =
    {
        Handle: int
        Size: int
    }

    interface IResource<DmaBuffer> with
        static member Destroy(b) = hwRelease b.Handle

/// Holding a move-only value makes a type move-only too.
type Frame =
    {
        Id: int
        Buffer: DmaBuffer
    }

type Queue =
    | Empty
    | Queued of Frame * Queue

let size (f: Frame) : int = f.Id + f.Buffer.Size
let enqueue (f: Frame) (q: Queue) : Queue = Queued(f, q)

let route (urgent: bool) (f: Frame) (q: Queue) : Queue =
    if urgent then
        Queued(f, q)
    else
        q

let rec total (q: Queue) : int =
    match q with
    | Empty -> 0
    | Queued(f, rest) -> size f + total rest

/// A shared resource: copies share one page.
type Page =
    {
        Page: int
    }

    interface ISharedResource<Page> with
        static member Dup(p) = p
        static member Destroy(p) = hwRelease p.Page

type Fanout =
    {
        Tx: Page
        Log: Page
    }

let fanOut (p: Page) : Fanout =
    {
        Tx = p
        Log = p
    }

let rec range (lo: int) (hi: int) : int list =
    if lo > hi then
        []
    else
        lo :: range (lo + 1) hi

let rec sum (xs: int list) : int =
    match xs with
    | [] -> 0
    | x :: rest -> x + sum rest

/// 64 cells, rebuilt 1000 times in a 4 KiB arena: every round reuses them in place.
[<StackArena(4096)>]
let kernelWork () : int =
    let mutable xs = range 1 64

    for round in 1..1000 do
        xs <- List.map (fun x -> x + round) xs

    sum xs

/// An arena inside an arena: the inner one's cells come from its own buffer, and the outer
/// one's list stays alive in its buffer across the call.
[<StackArena(2048)>]
let innerArena (n: int) : int = sum (range 1 n)

[<StackArena(4096)>]
let outerArena () : int =
    let xs = range 1 10
    let inner = innerArena 20
    inner + sum xs

let run () : int =
    let before = liveCells ()
    let destroyed0 = Counters.resourceDestroys ()
    let copies0 = Counters.resourceCopies ()

    let f =
        {
            Id = 1
            Buffer =
                {
                    Handle = 7
                    Size = 10
                }
        }

    let a = size f
    let b = size f // (read twice: borrowed, no copy)
    let q = enqueue f Empty

    let q2 =
        route
            true
            {
                Id = 2
                Buffer =
                    {
                        Handle = 8
                        Size = 20
                    }
            }
            q

    let q3 =
        route
            false
            {
                Id = 3
                Buffer =
                    {
                        Handle = 9
                        Size = 30
                    }
            }
            q2

    let t = total q3
    let fan = fanOut { Page = 5 }
    let shared = fan.Tx.Page + fan.Log.Page
    let arena = kernelWork ()
    let nested = outerArena ()

    let failed =
        check (a = 11 && b = 11 && t = 33 && shared = 10)
        + check (arena = 32034080)
        + check (nested = 210 + 55)
        + (if counting () then
               // three buffers destroyed once each; the page was copied once, and each of its
               // two copies is destroyed once
               check (
                   Counters.resourceDestroys () - destroyed0 = 5
                   && Counters.resourceCopies () - copies0 = 1
               )
           else
               0)

    printfn "resources: %d" failed

    failed
    + (if counting () then
           check (liveCells () = before)
       else
           0)
