# Fable Library for Zig

The runtime library of [Fable](https://fable.io/)'s Zig target, which compiles F# to Zig source
without a garbage collector. `fable_rt.zig` (cells, counts, strings, formatting, exceptions,
collections), `fable_sgc.zig` (the cycle collector) and `fable_unicode.zig` are written in Zig;
the `.fs` files (List, Array, Seq, Map, Set, Option, Result, Async, Task) are F# that the target
compiles itself. The design is described in `src/Fable.Transforms/Zig/FABLE-ZIG.md`.

## Using it

You need .NET (to run Fable) and Zig 0.17.1 or later.

```sh
dotnet fable path/to/App.fsproj --lang zig --extension .zig
cd path/to
zig run Program.zig                    # the file with [<EntryPoint>]
zig build-exe -O ReleaseFast Program.zig
```

Fable writes one `.zig` file next to each `.fs` file and puts this library in
`fable_modules/fable-library-zig`. The file with the `[<EntryPoint>]` has Zig's `main`: its
exit code is the one `main` returns, and an exception that nothing handles ends the program
with code 134, as on .NET. Any file can also be imported from Zig code of your own.

## Memory

There is no garbage collector. Records, unions, lists, strings, closures and objects are
reference-counted cells, and the compiler inserts the counting (Perceus): a value is freed at
its last use, a cell that is given up and made again in the same shape is reused in place, and
a function that only reads its argument borrows it at no cost. Data without assignable fields
cannot form a cycle; for the types that can, a cycle collector frees dead cycles without
stopping the program. From F#:

- `Fable.Core.Zig.Collector`: `collect ()`, `step budget`, `pause ()`/`resume ()`, tuning.
- `Fable.Core.Zig.Counters`: what the runtime did (cells made, freed, live).
- `WeakReference<'T>`: handles that are cleared when the target is freed, also for values
  shared between threads (to break the back edges of a cyclic shared structure).
- `Fable.Core.Zig.sameCell a b`: whether two values are the same cell, a shortcut before
  structural equality (`obj.ReferenceEquals` under .NET).
- `[<StackArena(bytes)>]` on a function: what it allocates comes from its stack.
- `IResource<'T>` / `ISharedResource<'T>`: values whose `Destroy` (and `Dup`) the runtime calls,
  for handles of things outside the program.

Under .NET these do nothing (or what .NET does), so the same program runs on both.

Threads are real threads: `Thread`, `Async.Parallel`, `Async.StartChild`, `MailboxProcessor`,
`Task.Run` and the like. A value is marked shared when it reaches another thread, and from then
on its count changes atomically; the rest of the program pays one test of a bit. A message a
MailboxProcessor's receiver alone holds is its own again when it takes it (plain counts, changed
in place). To move a value without ever marking it, `Fable.Core.Zig.Iso.pack value` (the value
given up, nothing else referring to a part of it) and `Iso.unpack` on the other side: each hop
moves one pointer.

## Calling Zig

```fsharp
[<Import("add", "./native.zig")>]           // a declaration of a Zig file of yours
let add: int -> int -> int = nativeOnly

[<ImportMember("./native.zig")>]            // the same, named after the F# function
let greet (name: string) : string = nativeOnly

[<Import("math.maxInt(i32)", "std")>]       // a package, and a Zig expression of it
let maxInt: int = nativeOnly

type System.String with
    [<Emit("@as(i32, @intCast(fable_rt.unitsOf($0).len))")>]   // `$0` is the object
    member s.Units : int = nativeOnly
```

A call is direct. Its arguments are borrowed for the call (Zig code that keeps one calls
`fable_rt.dup` on it) and what it returns belongs to the caller. F#'s `int`, `float`, `bool` and
the like are Zig's `i32`, `f64`, `bool`; a `string` is `fable_rt.String` (UTF-16, as on .NET:
`fable_rt.unitsOf`, `fable_rt.str`). A `.zig` file next to your `.fs` files is copied to the
output with them, as Zig imports only files under the root of the program.

A Zig struct is used through an interface that stands for it, with no wrapper:

```fsharp
[<Erase; Import("*Counter", "./counter.zig")>]   // `*`: a pointer to one
type ICounter =
    abstract add: x: int -> int                   // `c.add(x)`
    abstract n: int with get, set                 // `c.n`, `c.n = v`
```

The program does not count such values: what Zig allocates, Zig frees. A record that implements
an `IResource<'T>` of the program's (`static abstract Destroy: 'T -> unit`) and holds one frees
it right after its own last use.

From Zig, an F# function is called with `fable_rt.callFSharp(@import("App.zig"), "name",
.{ args })`: the arguments stay the caller's, what it gives is the caller's, and it is an error
union (`error.Raised`) whether or not the function can raise.

C functions are called the .NET way, and work on both:

```fsharp
[<DllImport("libc", EntryPoint = "strlen")>]
extern unativeint cStrlen(string s)          // a string is given as UTF-8 ended by a zero

[<Struct>]
type Vector2 = { x: float32; y: float32 }   // a struct of numbers and bools: C's layout

[<DllImport("raylib")>]
extern Vector2 Vector2Add(Vector2 v1, Vector2 v2)   // given and given back by value

[<UnmanagedCallersOnly(EntryPoint = "app_twice")>]
let twice (x: int) : int = x * 2             // exported to C under that name
```

What a C function takes and gives, as .NET marshals it: numbers; `bool` as a 4-byte `BOOL`, or
C's 1-byte `bool` under `[<MarshalAs(UnmanagedType.I1)>]`; strings as UTF-8, or UTF-16 under
`[<MarshalAs(UnmanagedType.LPWStr)>]` or `CharSet = CharSet.Unicode` (one given back is copied,
C keeps it); arrays (a pointer to the items); structs of numbers, bools and such structs, by
value; `out`/`ref` (`int&`, `Vector2&`, `[<Out>] bool&`); and delegates, as C callbacks:

```fsharp
type Compare = delegate of byref<int> * byref<int> -> int

[<DllImport("libc")>]
extern void qsort(int[] items, unativeint count, unativeint size, Compare compare)
```

A callback that C keeps to call later needs its delegate kept alive meanwhile, as on .NET; an
exception that leaves a callback ends the program, as on .NET.

A C header becomes a module the build translates (Zig has no `@cImport`), imported with
`c:`, whose calls are given C's values as `extern` ones are:
`[<Import("sqlite3_open", "c:sqlite")>]`. `fable_build.zig` wires that up for `zig build`:

```zig
const fable = @import("fable_modules/fable-library-zig/fable_build.zig");

pub fn build(b: *std.Build) void {
    const exe = fable.addExecutable(b, .{
        .name = "app",
        .target = b.standardTargetOptions(.{}),
        .optimize = b.standardOptimizeOption(.{}),
        .system_libraries = &.{"sqlite3"},
        .c_headers = &.{.{ .name = "sqlite", .header = "sqlite.h" }}, // `#include <sqlite3.h>`
    });
    b.installArtifact(exe);
}
```

## What differs from .NET

Programs print and compute what they do on .NET; where the target cannot do that yet it refuses
to compile, rather than doing something else. The known exceptions:

- Immutable records, unions and tuples are values, not objects: `obj.ReferenceEquals` and
  `PhysicalEquality` of them are refused (`[<ReferenceEquality>]` gives a type's values an
  identity; `sameCell` is false for them).
- A weak reference sees its target gone at the target's last use, not at a later collection.
- A cycle through values shared between threads is not collected (as in Koka): break it with a
  weak reference.
- A loop over a `Dictionary` walks a snapshot of it.
- The current culture is the invariant culture.
- `Length` of a null array is 0, and a field of a null record is the field's null, where .NET
  raises NullReferenceException.
- An exception thrown by a type's own `Equals`, `GetHashCode` or `CompareTo` while `=`, `hash`
  or `compare` runs it stops the program.

## Developing

```sh
./build.sh fable-library --zig     # compile the .fs files into temp/fable-library-zig
./build.sh quicktest zig           # compile and run src/quicktest-zig
./build.sh test zig                # the library's own tests, then the quicktest in Debug and
                                   # ReleaseSafe and on .NET
src/benchmarks-zig/run.sh          # time five programs against .NET
```
