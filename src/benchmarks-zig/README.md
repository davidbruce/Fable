# Benchmarks of the Zig target

Each folder is an F# program that prints what it computed. `run.sh` compiles it to Zig
(`ReleaseFast`) and to .NET (`Release`), checks that both print the same, and prints the best of
three runs of each in milliseconds (.NET's time includes the start of the runtime, about 60 ms).

    ./build.sh quicktest zig        # compiles the runtime library into temp/fable-library-zig
    src/benchmarks-zig/run.sh       # or: run.sh nbody maps

- `nbody`: the n-body simulation, floats in arrays
- `lists`: building, mapping, filtering, folding and sorting F# lists
- `maps`: F#'s `Map` and `Set`
- `strings`: `StringBuilder`, `Split`, `String.Join`, `Contains`, and `+` in a loop
- `virtual`: virtual calls through an abstract class, and objects made and given up
- `messages`: four threads post batches (a ResizeArray, a list) to a MailboxProcessor, which
  changes and sums them; the total comes back with PostAndReply

On an Apple M-series machine (Zig 0.18, .NET 10), 2026-11-13:

| benchmark | Zig ms | .NET ms |
|-----------|-------:|--------:|
| nbody     |    260 |     271 |
| lists     |    392 |     762 |
| maps      |    173 |     306 |
| strings   |     19 |     628 |
| virtual   |     90 |      93 |
