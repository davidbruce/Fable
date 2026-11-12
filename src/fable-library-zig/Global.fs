/// The part of the Zig runtime library that is written in F#.
/// (Collections and the rest of FSharp.Core arrive here as the target learns to compile them.)
module Fable.Library.Zig.Global

/// Version of the runtime library's interface, checked by generated code.
let libraryVersion () : int = 1
