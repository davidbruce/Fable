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
- `WeakReference<'T>`: handles that are cleared when the target is freed.
- `[<StackArena(bytes)>]` on a function: what it allocates comes from its stack.
- `IResource<'T>` / `ISharedResource<'T>`: values whose `Destroy` (and `Dup`) the runtime calls,
  for handles of things outside the program.

Under .NET these do nothing (or what .NET does), so the same program runs on both.

## What differs from .NET

Programs print and compute what they do on .NET; where the target cannot do that yet it refuses
to compile, rather than doing something else. The known exceptions:

- One thread: values cannot be shared between threads yet. `async` and `task` run on the
  calling thread; `Async.Sleep` and `Task.Delay` do not wait, `Async.Parallel` runs in turn.
- A weak reference sees its target gone at the target's last use, not at a later collection.
- A loop over a `Dictionary` walks a snapshot of it.
- `%A` of a type that contains a `voption`, a struct tuple or a function is refused.
- Comparison by a culture (`String.Compare` without `StringComparison.Ordinal`) is refused;
  `StackTrace` is not supported.
- Immutable records, unions and tuples are values, not objects: `obj.ReferenceEquals` and
  `PhysicalEquality` of them are refused (`[<ReferenceEquality>]` gives a type's values an
  identity). An exception thrown by a type's own `Equals`, `GetHashCode` or `CompareTo` while
  `=`, `hash` or `compare` runs it stops the program.
- `Array.zeroCreate` of a reference record gives records of default fields, where .NET gives
  nulls.
- Not yet supported: reflection, generic classes in class hierarchies, arrays of more than two
  dimensions, `Regex`, dates and times.

## Developing

```sh
./build.sh fable-library --zig     # compile the .fs files into temp/fable-library-zig
./build.sh quicktest zig           # compile and run src/quicktest-zig
./build.sh test zig                # the library's own tests, then the quicktest in Debug and
                                   # ReleaseSafe and on .NET
src/benchmarks-zig/run.sh          # time five programs against .NET
```
