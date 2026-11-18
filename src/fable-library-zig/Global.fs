/// The part of the Zig runtime library that is written in F#.
/// (Collections and the rest of FSharp.Core arrive here as the target learns to compile them.)
module Fable.Library.Zig.Global

/// Marks a module or function whose recursion is already trampolined (e.g. `Async.bounce`),
/// opting it out of `$tc` / `tcode` generation.
[<Fable.Core.Erase; System.AttributeUsage(System.AttributeTargets.Class ||| System.AttributeTargets.Method)>]
type NoTailCallsAttribute() =
    inherit System.Attribute()

/// Version of the runtime library's interface, checked by generated code.
let libraryVersion () : int = 1
