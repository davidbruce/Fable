# Fable → Zig

An experimental target that compiles F# to Zig source without a garbage collector: values are
reference counted with Perceus-style dup/drop insertion, borrow inference and in-place reuse,
and reference cycles are reclaimed by a per-structure-count collector in the runtime library.

The design was developed as a stand-alone prototype on the F# compiler's typed tree and is
being moved here stage by stage.

## Pipeline

```text
Fable AST ─► lower ─► ownership IR ─► borrow inference ─► dup/drop insertion ─► emit ─► Zig text
            (Fable2Zig.Lower.fs)      (Fable2Zig.Perceus.fs, both passes)     (Fable2Zig.Emit.fs)
```

- `Zig.IR.fs`: the ownership IR. Flat expressions have no control flow; anything a statement
  needs is let-bound first, so every later pass looks at one use at a time.
- `Fable2Zig.Lower.fs`: Fable AST → IR.
- `Fable2Zig.Perceus.fs`: the ownership passes (see "Ownership" below).
- `Fable2Zig.Emit.fs`: IR → Zig text. Integer arithmetic wraps, as on .NET. Self tail calls
  become loops, also when the call is the last field of a new cell (the list is then built
  top-down through a destination pointer).
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
| union that does not contain itself | `union(enum)`, one payload struct per case |
| union that contains itself | `union(enum)` whose cases point to reference-counted cells |
| tuple, struct tuple | `@Tuple(&.{ ... })` |
| `option`, `voption` | `?T` |

with construction, copy-and-update, field access, pattern matching and structural equality.
A record, union, tuple or option that holds a recursive union is still a plain value; the
references inside it are counted. Not yet: recursive records and records with mutable fields,
generic types, members on types, ordering comparison, module-level values that are not
literals.

`[<Emit("...")>]` is supported for Zig text, with `$0`, `$1`, ... standing for the arguments.

## Ownership

A recursive union is a handle to reference-counted cells:

```zig
pub const IntList = union(enum) {
    Nil,
    Cons: *struct { @"$rc": u32 = 1, head: i32, tail: IntList },
};
```

The passes in `Fable2Zig.Perceus.fs` decide who owns each value, so that most code does no
reference counting at all:

1. **Naming field reads.** Fable inlines a binding that is used once, so
   `Cons(h, t) -> Cons(h + 1, f t)` arrives as `Cons(xs.Cons.head + 1, f xs.Cons.tail)`, where
   `xs` is read after the call. Every field read of a managed value is named once, at the
   start of the branch that reads it. A read moves up past statements but never out of its
   branch, so it only happens where the program would have done it anyway.
2. **Borrow inference.** A parameter is borrowed unless the function returns it, stores it,
   passes it to an owning parameter, or takes it apart while building the same type. A result
   is borrowed when every value the function returns is part of a borrowed parameter.
3. **Perceus.** Each owned variable is consumed exactly once: its last use in an owning
   position is a move, earlier ones are dups, and a drop is inserted where it dies unused. A
   dead value whose case is known is unpacked instead: its fields move out, and if its cell
   was not shared the cell is freed or kept as a token and built in again by the next
   constructor of the same shape. `map`, `insert` into a tree and the like therefore update
   a structure in place when nobody else holds it, and copy the path when somebody does.

A variable that can be assigned is treated conservatively: nothing is remembered about what
it holds, and a name for one of its fields gets its own reference.

The runtime (`src/fable-library-zig/fable_rt.zig`) has no per-type code: `dup`, `drop` and
`eql` are generic over the type and find the cells through `@typeInfo`. Dropping a list (or
the right spine of a tree) is a loop, not recursion. Cells come from `fable_rt.allocator`,
one global that a program may set before it allocates; the allocator is not passed from
function to function. In Debug and ReleaseSafe builds the runtime counts cells, and a program
whose entry point returns with cells still allocated says so and exits with code 70.

### Calls between files

Fable compiles files one at a time and in parallel, so a file cannot see what a function of
another file was inferred to borrow; and what it borrows depends on its body, so a cached
answer would go stale whenever the body changes without the signature changing. The question
is therefore left to the Zig compiler, which sees every file:

```zig
// Helpers.zig: next to each function that takes or returns a managed value
pub const @"sumList$sig" = .{ .borrows = .{ true }, .result_borrowed = false };

// Heap.zig: the caller says what it does with each argument
fable_rt.across(m_Helpers.sumList, m_Helpers.@"sumList$sig", .{ .keep }, .{ xs })
```

`.keep` means the caller uses the value again, `.give` that this was its last use. `across`
is resolved at compile time: a value the caller keeps and the callee borrows is passed as it
is; one the caller gives and the callee borrows is dropped after the call; a borrowed result
is made owned. The call costs what it would cost inside one file, except that a borrowed
result is always dup'ed (inside a file it can stay a borrow).

`./build.sh quicktest zig` compiles `src/quicktest-zig` and runs it with `zig run`.

## What is next, in order

1. ~~Records and unions (value types first), tuples, options~~ (done).
2. ~~Heap values: recursive unions as reference-counted cells, the runtime library
   (`src/fable-library-zig`), borrow inference and dup/drop insertion (Perceus), reuse~~
   (done).
3. ~~What functions of other files borrow~~ (done, at Zig compile time: see "Calls between
   files"). Whether a function of another file can raise will be stated the same way.
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
  (`zig test src/fable-library-zig/fable_rt.zig`). Its type introspection uses the
  `field_names` / `field_types` form of `@typeInfo` (Zig 0.17 and later).
- Two places in `FSharp2Fable.fs` drop information this target needs and will need a
  Zig-specific branch: the address of anything but a variable or field is discarded, and a
  store through a byref that is not a plain variable is rejected.
- The target is not part of the stand-alone (JavaScript-hosted) compiler.
