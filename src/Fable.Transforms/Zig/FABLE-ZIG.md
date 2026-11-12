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

Module-level functions (also recursive, also across files), functions declared inside
functions, lambdas and function values (see "Function values"), pipes and composition,
literal module-level values,
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
| `list` | `fable_rt.List(T)`, a recursive union of the runtime library |
| generic record or union | a Zig function from its type arguments to the type |
| `unit` | `void`; a unit argument is passed, it has no size |

with construction, copy-and-update, field access, pattern matching and structural equality.
A record, union, tuple or option that holds a recursive union is still a plain value; the
references inside it are counted. Not yet: recursive records and records with mutable fields,
members on types, ordering comparison, module-level values that are not literals, and the
functions of the `List` module (literals, `::`, patterns, `IsEmpty`, `Head` and `Tail` work).

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
is made owned. The call costs what it would cost inside one file, with two exceptions: a
borrowed result is always dup'ed (inside a file it can stay a borrow), and a parameter that
a function passes on to a function of another file is inferred as owned, because inference
has to assume the other function consumes it (assuming the opposite would cost in-place
reuse, which is worth more). So the callers of such a forwarding function pay a dup and a
drop where code in one file would pay nothing.

## Generics

A generic function is compiled once, for any type, and Zig makes the instances:

```zig
pub fn map(comptime @"'T": type, comptime @"'U": type) type {
    return struct {
        pub fn call(f: fable_rt.Func(*const fn (?*fable_rt.Env, @"'T") @"'U"), xs: Chain(@"'T")) Chain(@"'U") { ... }
    };
}

map(i32, bool).call(f, xs)
```

(a function from types to a namespace, so that `map(i32, bool).call` is an ordinary function
that can be passed on, also to `fable_rt.across`). This needs nothing shared between file
compilations either: a generic function of another file is instantiated by Zig like any
other.

The ownership passes run on the generic code. A value whose type is a type parameter counts
as managed; its dups and drops are calls of the runtime's generic `dup` and `drop`, which
compile to nothing when the function is used with `int`. Borrowing is inferred once and
holds for every instance. Reuse is decided as far as it can be: a dead cell and a new one
that are the same case of one generic type are paired, and the runtime builds in the dead
cell only if the two turn out to have the same layout in that instance (`map` over an
unshared `Chain<int>` to `Chain<int>` allocates nothing; to `Chain<int64>` it allocates).

The type arguments of a call are the ones Fable records; where it records none (a generic
function used as a value), they are inferred from the types of the arguments and the result.

A function declared inside another one may be generic itself (`let pair x = (x, x)` used at
two types): the lifted function has the surrounding function's type parameters and then its
own.

## Function values

Every lambda, and every function declared inside another function, is compiled as a function
of the file that takes the variables it uses from its surroundings as extra, leading
parameters (lambda lifting). Calling such a function by name is therefore a plain call: no
environment is allocated, its parameters can be borrowed, and a `let rec loop` that calls
itself last is a loop.

Only where a function is used as a *value* is there a function value:

```zig
fable_rt.Func(*const fn (?*fable_rt.Env, i32) i32)   // F#: int -> int
```

a pointer to code and a pointer to a reference-counted environment that owns the captured
values (no environment when nothing is captured, so passing `double` or `fun x -> x * 2`
allocates nothing). The code is a small adapter generated per function: it reads the
captures from the environment and calls the lifted function. A function value owns its
arguments and its result; the adapter is where that convention meets whatever the function
itself was inferred to borrow.

`int -> int -> int` as a value is the uncurried form wherever Fable can uncurry it (a
two-argument function value); where it cannot, it is a function that returns a function.
Functions cannot capture `let mutable` variables (F# does not allow it either).

Not yet: a higher-order function is not specialised for the lambda it is given, so each call
through a function value is an indirect call.

## Exceptions

`raise`, `try ... with`, `try ... finally` and `reraise ()`, for exceptions declared with F#'s
`exception`.

A function that can raise returns a Zig error union, `fable_rt.Raised!T`; every other function
keeps its plain result type and pays nothing. `raise` moves the exception into a slot of the
runtime and returns `error.Raised`. A call that may raise has an error edge:

```zig
const below: i32 = (buildAndCheck(n - 1, limit) catch { fable_rt.drop(mine); return error.Raised; });
```

What the edge drops is the set the ownership pass tracks anyway: what the function owns and
has not consumed at that point. So there are no unwinding tables and no cleanup stack, and
an exception frees exactly what a normal return would have. A `try` is a labelled block: the
error edges inside its body break to the handler, which takes the exception out of the slot
and owns it. Values that the handler, or the code after the `try`, still needs are not moved
or dropped inside the body.

An exception is a reference-counted cell that starts with a header naming its type
(`fable_rt.ExnOf("ParseError", struct { pos: i32, code: i32 })`), so a file can declare
exception types that no other file knows of; `exn` is a pointer to that header.

Who can raise:

- A function with a `raise` that no `try` of its own handles, or that calls such a function.
- A function value, always: its code returns an error union whatever is behind it, so that
  it has one shape. Hence a function that calls a function value can raise.
- A function of another file: this file cannot know, so the call is written both ways and
  Zig picks (`if (comptime fable_rt.isRaised(@TypeOf(raw))) ...`), and the result type of the
  calling function is `fable_rt.MayRaise(T, .{ m_Other.f, ... })`, which Zig resolves to
  `T` or `Raised!T`. Like borrowing, this needs nothing shared between file compilations.

A loop that builds a list top-down (`map`) stays a loop when it can raise: on the error edge
the hole is filled with the type's case without fields (`Nil`) and what was built is dropped.
A type that has no such case makes the function recurse instead.

Not yet: .NET's own exception classes and `failwith` (they carry a message, which needs
strings), structural equality of exceptions, a `while` condition that can raise, and the
exceptions .NET raises for a division by zero or a failed pattern match (those are still Zig
panics). An exception that reaches the entry point is printed by name and the program exits
with 134, as on .NET on Unix.

## Tail calls

A function that calls itself last is a loop (also when the call is the last field of a new
cell). A call of *another* function of the file that ends a function is a jump
(`@call(fable_rt.tail_call, f, .{ ... })`) when both functions have the same parameter and
result types, all of them are numbers, booleans or chars, and neither can raise; `even`/`odd` and state machines
over numbers then run in constant stack, as on .NET. Other signatures stay calls: Zig passes
and returns records and unions through pointers into the caller's frame, which a jump would
leave dangling (and LLVM rejects the jump when the result is returned that way). So mutual
recursion over lists or trees still uses stack in proportion to its depth. The jump is only
forced on the LLVM backend; elsewhere it is an ordinary call.

`./build.sh quicktest zig` compiles `src/quicktest-zig` and runs it with `zig run`.

## What is next, in order

1. ~~Records and unions (value types first), tuples, options~~ (done).
2. ~~Heap values: recursive unions as reference-counted cells, the runtime library
   (`src/fable-library-zig`), borrow inference and dup/drop insertion (Perceus), reuse~~
   (done).
3. ~~What functions of other files borrow~~ (done, at Zig compile time: see "Calls between
   files"). Whether a function of another file can raise will be stated the same way.
4. ~~Closures and function values~~ (done), ~~generics~~ (done), ~~exceptions~~ (done for
   F# `exception` declarations), byrefs and spans.
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
