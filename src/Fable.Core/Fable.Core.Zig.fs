/// The Zig target's runtime, from F#. Under .NET every function here does nothing and every
/// counter is zero, so a program that calls them still runs on both.
module Fable.Core.Zig

open Fable.Core

/// The cycle collector. A structure that reaches itself is freed when the last reference to
/// it from outside goes; nothing here is needed for that. These functions are for programs
/// that want to say when the collector's other work is done: the checks of structures that
/// are still referenced (a dead cycle can sit inside one), and the freeing of big dead
/// structures in small steps. Each thread has a collector of its own.
[<RequireQualifiedAccess>]
module Collector =
    /// Free every cycle that is dead now. Returns the number of cells freed.
    [<Emit("fable_rt.collect()")>]
    let collect () : int = 0

    /// Do at most `budget` cells of work. True while more is waiting. The collector only works
    /// of its own accord when a cell that can be part of a cycle is allocated; a program that
    /// has idle time calls this there.
    [<Emit("fable_rt.collectStep($0)")>]
    let step (budget: int) : bool = false

    /// No collector work until `resume`, for code that must not be delayed.
    [<Emit("fable_rt.collectorPause()")>]
    let pause () : unit = ()

    [<Emit("fable_rt.collectorResume()")>]
    let resume () : unit = ()

    /// false: checks of structures that are still referenced are only started by `collect`
    /// and `step`.
    [<Emit("fable_rt.collectorSet(.automatic, @intFromBool($0))")>]
    let setAutomatic (on: bool) : unit = ()

    /// The cells of a check that are looked at per allocation (0: a check runs to its end at
    /// once). The smaller, the shorter the longest pause.
    [<Emit("fable_rt.collectorSet(.pace, $0)")>]
    let setPace (cells: int) : unit = ()

    /// The cells of a dead structure that are freed per allocation (0: all at once, inside
    /// the release that killed it).
    [<Emit("fable_rt.collectorSet(.free_budget, $0)")>]
    let setFreeBudget (cells: int) : unit = ()

    /// With a free budget: the cells that one drop frees at once before the rest is queued.
    [<Emit("fable_rt.collectorSet(.free_now, $0)")>]
    let setFreeNow (cells: int) : unit = ()

    /// A structure that lost a reference is checked when it has grown by 1/`divisor` since
    /// (and by at least `setCheckMinimum` cells).
    [<Emit("fable_rt.collectorSet(.check_growth, $0)")>]
    let setCheckGrowth (divisor: int) : unit = ()

    [<Emit("fable_rt.collectorSet(.check_min, $0)")>]
    let setCheckMinimum (cells: int) : unit = ()

    /// ... or once max(`allocations`, `setCheckFactor` times its cells) allocations have
    /// passed, for a structure that only shrinks.
    [<Emit("fable_rt.collectorSet(.check_wait, $0)")>]
    let setCheckWait (allocations: int) : unit = ()

    [<Emit("fable_rt.collectorSet(.check_factor, $0)")>]
    let setCheckFactor (times: int) : unit = ()

/// Are `a` and `b` the same cell: one object of a reference type, a list's first cell, a
/// function's environment? Immutable records and unions are values in the Zig target, where
/// `obj.ReferenceEquals` of them is refused: for one of them this is false. A shortcut before
/// structural equality (`sameCell a b || a = b`), as `obj.ReferenceEquals` is under .NET.
[<Emit("fable_rt.sameCell($0, $1)")>]
let sameCell (a: 'T) (b: 'T) : bool = obj.ReferenceEquals(a, b)

/// What the runtime did, for programs and tests that want to see it. The runtime counts in
/// Debug and ReleaseSafe builds only.
[<RequireQualifiedAccess>]
module Counters =
    /// Does this build count? (false under .NET)
    [<Emit("fable_rt.track")>]
    let isCounting () : bool = false

    /// Reference-counted cells of this thread that are allocated now.
    [<Emit("fable_rt.liveCells()")>]
    let liveCells () : int = 0

    /// Cells allocated so far.
    [<Emit("fable_rt.counted(.allocs)")>]
    let allocations () : int = 0

    /// Cells that were not freed but built in again by a constructor.
    [<Emit("fable_rt.counted(.reuses)")>]
    let reuses () : int = 0

    /// References added to, or taken off, cells that stayed shared.
    [<Emit("fable_rt.counted(.shared)")>]
    let sharedCounts () : int = 0

    /// The times a resource was destroyed (its `Destroy` ran).
    [<Emit("fable_rt.counted(.destroys)")>]
    let resourceDestroys () : int = 0

    /// The times a shared resource was copied (its `Dup` ran).
    [<Emit("fable_rt.counted(.copies)")>]
    let resourceCopies () : int = 0

/// Run the heap allocations of this function out of a buffer of `bytes` bytes on the stack
/// (for kernel and interrupt code, where there is no heap). The function may neither take nor
/// give values that live on the heap: they would outlive the buffer. Under .NET it does
/// nothing.
[<System.AttributeUsage(System.AttributeTargets.Method)>]
type StackArenaAttribute(bytes: int) =
    inherit System.Attribute()
    member _.Bytes = bytes
