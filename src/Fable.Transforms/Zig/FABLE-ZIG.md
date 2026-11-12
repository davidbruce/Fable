# Fable → Zig

An experimental target that compiles F# to Zig source without a garbage collector: values are
reference counted with Perceus-style dup/drop insertion, borrow inference and in-place reuse,
and reference cycles are reclaimed by a per-structure-count collector in the runtime library.

The design was developed as a stand-alone prototype on the F# compiler's typed tree and is
being moved here stage by stage.

## Pipeline

```text
Fable AST ─► lower ─► ownership IR ─► borrow inference ─► dup/drop insertion ─► emit ─► Zig text
            (Fable2Zig.Lower.fs)      (not ported yet)    (not ported yet)    (Fable2Zig.Emit.fs)
```

- `Zig.IR.fs`: the ownership IR. Flat expressions have no control flow; anything a statement
  needs is let-bound first, so every later pass looks at one use at a time.
- `Fable2Zig.Lower.fs`: Fable AST → IR.
- `Fable2Zig.Emit.fs`: IR → Zig text. Integer arithmetic wraps, as on .NET.
- `Fable2Zig.fs`, `ZigPrinter.fs`: the target's entry point and the file writer.

There is no separate Zig AST: the IR is the last structured form, and the emitter writes text.

## What compiles today

Module-level functions (also recursive, also across files), literal module-level values,
numbers, booleans and chars, `let`, `let mutable`, `if`, `while`, `for .. to`, arithmetic,
comparison, bitwise and boolean operators, conversions between numbers (`int`, `byte`,
`float`, ... with .NET's results), pattern matching, and an `[<EntryPoint>]` whose result
becomes the process exit code.

Types that are plain values, also when another file declares them:

| F# | Zig |
| --- | --- |
| record without mutable fields | `struct` |
| union | `union(enum)`, one payload struct per case |
| tuple, struct tuple | `@Tuple(&.{ ... })` |
| `option`, `voption` | `?T` |

with construction, copy-and-update, field access, pattern matching and structural equality
(`std.meta.eql`). Not yet: recursive types and records with mutable fields (they are heap
cells and come with the runtime), generic types, members on types, ordering comparison.

Everything else is reported as a compile error at the F# source location
("the Zig target does not support … yet").

`./build.sh quicktest zig` compiles `src/quicktest-zig` and runs it with `zig run`.

## What is next, in order

1. ~~Records and unions (value types first), tuples, options~~ (done).
2. Heap values: recursive unions as reference-counted cells, the runtime library
   (`src/fable-library-zig`), borrow inference and dup/drop insertion (Perceus), reuse.
3. Per-function summaries across files (borrow modes, borrowed returns, raising, allocator
   needs). F# has no recursion across files, so a file only needs the finished summaries of
   the files before it. Fable already shares inline functions between file compilations
   this way (`InlineExprLazy` in `State.fs`).
4. Closures and function values, generics, exceptions, byrefs and spans.
5. Mutable reference records and the cycle collector.
6. Strings, collections and the rest of FSharp.Core through `Replacements.fs` and the library.
7. The test suite (`tests/Zig`), starting from the tests the other targets share.

## Notes for the shared code

- Nothing goes through another target's replacements. `Zig/Replacements.fs` handles every
  entry point of `Replacements.Api`: operators on numbers, booleans and chars become plain
  operation nodes, and every other call into .NET or FSharp.Core is kept as it is, as a call
  to an import named after the declaring type (`dotnet:System.Math`, `Sqrt`). The lowering
  resolves those by their .NET names (`dotnetCall` in `Fable2Zig.Lower.fs`) or rejects them
  by name ("the Zig target does not support System.Math.Sqrt yet"). So far it knows
  structural equality, `ignore`, `id`, `fst`, `snd` and the conversions between numbers.
- Generated files import the hand-written runtime (`fable_rt.zig`, copied into
  `fable_modules/fable-library-zig`) only when they use it. It has its own Zig tests
  (`zig test src/fable-library-zig/fable_rt.zig`).
- Two places in `FSharp2Fable.fs` drop information this target needs and will need a
  Zig-specific branch: the address of anything but a variable or field is discarded, and a
  store through a byref that is not a plain variable is rejected.
- The target is not part of the stand-alone (JavaScript-hosted) compiler.
