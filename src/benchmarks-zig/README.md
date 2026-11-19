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

Toolchain baseline: **Zig 0.17.1 stable** and **.NET 10.0.111** (measured 2026-11-19 with `src/benchmarks-zig/run.sh`, `-OReleaseFast`):

| benchmark | Zig ms | .NET ms | output summary           | ReleaseFast B (`__TEXT`) | ReleaseSmall B (`__TEXT`) |
|-----------|-------:|--------:|--------------------------|-------------------------:|--------------------------:|
| nbody     |    259 |     239 | `-0.169075164`           |        423,480 (309,248) |         183,872 (108,920) |
| lists     |    452 |     758 | `84617894480`            |        423,048 (306,352) |         184,304 (107,856) |
| maps      |    242 |     315 | `19999900000 100000 ...` |        469,912 (343,112) |         223,376 (136,400) |
| strings   |     25 |    1153 | `1988895 1988895 ...`    |        423,000 (309,480) |         184,256 (108,416) |
| virtual   |     65 |      76 | `9980020000000.0 ...`    |        424,168 (309,656) |         183,968 (108,544) |
| messages  |    250 |     394 | `508240000`              |        848,712 (600,728) |         342,960 (244,760) |
