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
numbers, booleans, chars and strings (see "Strings"), `let`, `let mutable`, `if`, `while`, `for .. to`, arithmetic,
comparison, bitwise and boolean operators, conversions between numbers (`int`, `byte`,
`float`, ... with .NET's results), pattern matching, and an `[<EntryPoint>]` whose result
becomes the process exit code.

Types that are plain values, also when another file declares them:

| F# | Zig |
| --- | --- |
| record without mutable fields | `struct` |
| union that does not contain itself | `union(enum)`, one payload struct per case |
| union that contains itself | `union(enum)` whose cases point to reference-counted cells |
| record with mutable fields (not a struct), record that contains itself | a pointer to a reference-counted cell |
| `ref` cell | `fable_rt.Ref(T)`, such a record of the runtime library |
| tuple, struct tuple | `@Tuple(&.{ ... })` |
| `option`, `voption` | `?T` |
| `list` | `fable_rt.List(T)`, a recursive union of the runtime library |
| array | `fable_rt.Array(T)`, a counted cell that holds the items |
| `string` | `fable_rt.String`, a pointer to counted UTF-16 text or null; a literal is static data |
| generic record or union | a Zig function from its type arguments to the type |
| `unit` | `void`; a unit argument is passed, it has no size |

with construction, copy-and-update, field access, pattern matching and structural equality.
A record, union, tuple or option that holds a recursive union is still a plain value; the
references inside it are counted. `compare`, `<`, `max`, `min` and `hash` work on every
value as F# defines them: records and tuples field by field, unions by case then field,
`None` first, lists item by item, arrays by length then item; `fable_rt.compare` and
`fable_rt.hash` walk the Zig types. `Result` is a union of the runtime library.

Members on records and unions are functions whose first argument is the object: properties,
methods (also curried, also used as function values), static members, the operators a type
declares for itself (`static member (+)`), and members of generic types, in the file that
declares the type or in another. A `ToString` that a type overrides is called where .NET
calls it: by `x.ToString()`, `string x`, `{x}` and `%O` (`%A` does not use it, as on .NET).
Not yet: other overrides and interface implementations, classes, object expressions.

## Classes, interfaces, object expressions

A class is a counted cell of its fields (all of which can be assigned, so a class can close a
cycle). Its constructor is a function that computes the fields in order, as locals, and makes
the cell of them at the end; `this` cannot be used in a constructor yet. Members are functions
whose first argument is the object, as for records.

An interface value is a struct of function values, one per member (a property is a function of
unit). A value of a class given where an interface is expected becomes that struct: each member
is a function value that holds the object and calls the class's implementation
(`Counter__Probe_IShape_Area`). An object expression is the same struct made of the lambdas of
its members. A call of an interface member is a call of a function value. So interfaces reuse
what function values already do: ownership, raising, cycles; the cost is a function value per
member when a value is made an interface. `use` works with a class that implements
`IDisposable` (the test and the call are settled from the class's type).

Not yet: inheritance and abstract classes, `this` in a constructor or an object expression,
interfaces that inherit interfaces, generic interface members, type tests against interfaces at
run time, and overrides other than `ToString`.

A module-level value that is not a literal is computed when the program starts: every file
has an `$init` that first runs those of the files it uses and then fills its own values in
their order, and `main` calls the one of its file before the entry point (an exception there
ends the program as an unhandled one). A value has a place of its own for the whole run and
is given up when the program ends, before the check for cells left behind. A `let mutable`
at module level can be assigned, from its own file or another; a read of it is a reference
of its own, because the value may be replaced while the reader still uses it.

A `let mutable` inside a function that a function declared there reads or assigns is a ref
cell that both share, which is what F# makes of it on .NET.

Active patterns (also partial, parameterised and with several cases, which give F#'s `Choice`,
a union of the runtime library), enums, struct records and unions, and units of measure work
as they do on .NET. An anonymous record is a struct of the runtime library, one type per shape
(`fable_rt.Anon2(.{ "Age", "Name" }).of(i32, String)`, declared at the top of each file that
uses it), so two files that make the same shape have the same type. `lazy` is a cell that
holds the code, then the value, or the exception the code raised, which every later `Force`
raises again, as on .NET.

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

## Records that can be assigned

A record with mutable fields is a reference on .NET: two names for it see each other's
assignments. So it is a pointer to a counted cell here, and so are a record that contains
itself and a `ref` cell. Its equality is still structural, as in F#.

- `r.F <- v` is `fable_rt.store(&r.F, v)`: the field takes ownership of the new value and
  the old one is given up once the new one is in place.
- A value read from a field that can be assigned is a borrow only while nothing can assign a
  field: if anything in the rest of the scope may (an assignment, a call of a function that
  assigns, of a function of another file or of a function value, which this file cannot see
  into), the read gets a reference of its own, because the field could be given another value
  while the read one is still in use. A function that only walks a mutable structure
  therefore does no reference counting at all.
- Nothing is remembered about what such a field holds, and such reads are not moved to the
  start of their branch: they happen where the program does them.

## Numbers

`abs`, `sign`, `pown`, `**`, `round` (a tie to the even number, as .NET), `sqrt`, `exp`, `log`,
the trigonometric functions, `floor`, `ceil`, `truncate`, and of `System.Math` also `Round`
with digits, `Log` with a base, `Clamp`, `Max`, `Min`, `PI`, `E`. `abs` of the smallest
whole number raises `OverflowException`, `sign nan` raises `ArithmeticException`, as on .NET.

Text to numbers: F#'s `int s`, `float s`, `byte s`, ... read white space, a sign, and `0x`,
`0o`, `0b` and `_` as F# does; the types of 32 bits and less are read as 32 bits and then
converted with a check, so the messages are F#'s. `Int32.Parse` and the other `Parse`s read
what .NET reads, and `TryParse` in its F# form (`match Int32.TryParse s with | true, v ->`).
`List.sum`, `sumBy`, `average`, `averageBy`, `Array.sum` and `Array.average` add with the
item type's `+` (wrapping for whole numbers).

Not yet: `decimal`, `bigint`, `Checked` arithmetic, sums of types with an `+` of their own,
culture-specific parsing.

## The library

The runtime library has two parts. `fable_rt.zig` (with `fable_sgc.zig` and
`fable_unicode.zig`) is written by hand: cells, counts, the collector, strings, formatting,
arrays. The rest is F#, in `src/fable-library-zig/*.fs`, compiled by this target like any
program (`./build.sh fable-library --zig`) and copied next to the hand-written part. `List.fs`
is F#'s `List` module: `map` is three lines of F#, becomes a loop through tail calls modulo
cons, borrows its list, and raises what FSharp.Core raises because it says `invalidArg` where
FSharp.Core does.

A call of `List.map` in a program is kept under its .NET name by `Replacements.fs`, and the
lowering sends it to `m_List.map` (`libraryFunction` in `Fable2Zig.Lower.fs` lists what the
library has). It is then a call between files like any other: what the function borrows and
whether it raises is settled when the Zig is compiled. The type arguments are found by name
from the signature of the FSharp.Core function and given in the order of the names, so a
library function declares its type parameters, with FSharp.Core's names, in that order
(`fold<'State, 'T>`). A library function is named as FSharp.Core compiles it, with a small
first letter (`mapIndexed` for `List.mapi`).

`Seq.fs` is F#'s `seq`: a sequence is a record around a function that starts a walk, and a
walk is a record around the function that gives the next item or `None`. Nothing is computed
before it is asked for: `Seq.take 2` of a sequence with side effects runs them twice, and
infinite sequences work. `seq { }`, list and array comprehensions and ranges (`1 .. 10`,
`0 .. 2 .. 10`, `'a' .. 'z'`, of `int`, `int64`, `float` and `char`) are what F# makes of them:
calls of `Seq.delay`, `Seq.collect`, `Seq.append`, ... A list, an array or a collection given
where a sequence is expected is walked as one; a sequence given to a function that takes a list
is the list of what it gives. `for x in s` over a sequence asks it for each item in turn.
`%A` walks a sequence for its first four items (`seq [1; 2; 3; 4; ...]`), as .NET does.

`Async.fs` is F#'s `async`: a computation is a function given a record of what to do with its
result and with an exception (continuations). There is one thread and nothing waits:
`Async.Sleep` returns at once and `Async.Parallel` runs the computations one after the other,
in order; what a computation gives and raises, and the order of its effects, are .NET's. The
builder (`async`) has no state; its members, `RunSynchronously`, `StartImmediate`, `Start`,
`Catch`, `Ignore` and `Parallel` are the library's. A builder of the program's own is a class
like any other. Not yet: cancellation, `Async.FromContinuations`, `use!`.

`Task.fs` is F#'s `task`. With one thread a task runs to its end where it is made (it starts
there on .NET too), so a task is what it ended with: its result or its exception. `let!` of a
faulted task raises the exception again; `.Result` and `.Wait()` of one raise
`AggregateException` ("One or more errors occurred. (boom)"), as on .NET. Fable gives the
builder's intermediate calls no usable type (they are F#'s resumable code); a pass before the
lowering gives each the type its arguments say. `Task.FromResult`, `Task.Delay` (which does not
wait), `Task.WhenAll`, `IsCompleted` and `IsFaulted` work.

`open Checked`: `+`, `-`, `*`, unary `-` of whole numbers and the conversions raise
`OverflowException` where the result does not fit, as on .NET.

So far: `List.fs` (the `List` module, sorting included: a merge sort, stable as F#'s),
`Option.fs`, `Result.fs`, `Map.fs` and `Set.fs`. `Map` and `Set` are balanced trees ordered
by `compare`, as in FSharp.Core; a program's `Map<'K, 'V>` is the library's `MapTree_2`, and
the members of a map (`m.[k]`, `m.Add`, `m.Count`, ...) are library functions that take the
map first. Their trees carry `fable_collection`, so that the runtime compares, hashes and
writes them by what they hold (`map [(1, "a")]`, nine entries then `...`, as F#), not by the
shape of the tree. `Map.keys` and `Map.values` give lists. An empty value whose item type F# left open (`Option.isNone
None`, where .NET has `obj`) is given `unit`.

## Arrays

An array is a counted cell that holds its items, with an identity as on .NET: two names for
one array see each other's assignments, and `=` compares the items. An index outside the
array raises `IndexOutOfRangeException`. `a.[i]` gives a reference of its own to the item;
`a.[i] <- x` gives up the item that was there and tells the collector, because an array is
where a cycle can be closed like a record with an assignable field (the cycle analysis takes
what an array, a ref cell or any generic cell with assignable fields holds as assignable).

`[| ... |]`, indexing, slices (`a.[1..3]`, lenient at both ends as in F#), `for x in a`,
`.Length`, and of the `Array` module: `length`, `isEmpty`, `empty`, `get`, `set`,
`zeroCreate`, `create`, `init`, `copy`, `append`, `rev`, `sub`, `fill`, `ofList`, `toList`,
`contains`, `map`, `mapi`, `iter`, `iteri`, `fold`, `filter`, `exists`, `forall` in the
runtime, and the rest of the module (sorting, `sortInPlace`, `max`, `groupBy`, `zip`, `take`,
`chunkBySize`, `blit`, ...) in F# in the library (`Array.fs`).

Not yet: `Array.zeroCreate n` for items that have no null here (records, unions, functions:
only the empty array can be made that way; use `Array.create` or `Array.init`), arrays of
more than one dimension, the rest of the `Array` module, and reading an item without a
reference of its own where the array is only looked at.

## .NET's collections, and loops over collections

`ResizeArray`, `Dictionary` and `HashSet` are cells of the runtime library, equal only to
themselves as on .NET. A dictionary and a hash set are .NET's own design (buckets that chain
into an array of entries, and a list of freed entries that the next ones reuse), so they hold
their entries in the order .NET does: a loop over a dictionary and `%A` of it (`seq [[1, a];
...]`, four entries then `...`) give what .NET gives. Keys are hashed with `fable_rt.hash`
and compared with `=`. What they raise, and the messages, are .NET's. Like an array, each
can close a cycle, and tells the collector what it holds.

`for x in s do` is a loop of the source's own: down a list, along a string by index; a set,
a map (its entries are pairs: `kv.Key`, `kv.Value`), a ResizeArray, a dictionary and a hash
set are walked as the list of what they hold when the loop starts. (On .NET changing a .NET
collection inside a loop over it raises; here the loop goes on over what it started with.)

Not yet: `dict`, `Stack`, `Queue`, `SortedDictionary`, LINQ, and the rarer members.

## Resources and stack arenas

For code that drives hardware, as in the prototype. A record or union that implements
`IResource<'T>` (an interface of the program with `static abstract Destroy: 'T -> unit`) is a
resource: its `Destroy` runs right after the last use of a value, and the type is move-only. A
copy of it, or of anything that holds one, is a compile error ("a value of the move-only type
Buf is needed again after it was given away"); reading it, borrowing it and moving it are
fine. An `ISharedResource<'T>` (`inherit IResource<'T>`, `static abstract Dup: 'T -> 'T`) can
be copied: each copy runs `Dup` and is destroyed once. The type's Zig declaration carries
`fable_destroy` and `fable_dup`, which the runtime calls where it gives a value up and copies
one. The hooks never run on .NET, so they may not change what the program computes: they may
read the value and call `[<Emit>]` code (the hardware), and an assignment in one is a compile
error. `Counters.resourceDestroys` and `resourceCopies` count them.

`[<StackArena(bytes)>]` (Fable.Core.Zig) on a function runs its allocations out of a buffer of
that size on its stack: the allocator is swapped on entry and back on exit, the collector's and
the weak table's bookkeeping stay where they were, and running out of the buffer is a panic.
The function may neither take nor give values that live on the heap; a cell made in it that is
still alive when it ends is a panic in builds that count.

Not yet: generic resources, `IResource` on classes, hooks that raise (what they raise is
given up), and a stack arena shared between threads.

## Byrefs and spans

A `byref`, `inref` or `outref` is a pointer (`*T`, `*const T` for an `inref`); `&x` is the
address of a variable (a `let mutable` whose address is taken is a Zig `var`), a byref passed
on is the pointer it is, and where F# gives a value for an `inref` its address is taken.
Reading a byref reads what it points at; assigning to it, or to a field through it, assigns
there.

`Span<'T>` and `ReadOnlySpan<'T>` are slices (`[]T`, `[]const T`) of the array they view, and
the array stays alive while a span made of it is in use (the ownership pass takes the span for
an alias of it). `s.[i]` is the item's place, with .NET's `IndexOutOfRangeException` outside;
`Slice`, `Length`, `Fill` and the conversion to `ReadOnlySpan` work. Spans of values that are
counted are not supported yet (an assignment through one could not tell the collector), nor
`stackalloc`, `Span.ToArray` and spans of strings.

(A fix in the shared `FableTransforms.fs`: `let t = r`, where `r` is a byref, copies the value
it points at, so Fable no longer inlines `t`; that was wrong for every target.)

## Weak references

`WeakReference<'T>` of a reference type (a class, a record with mutable fields, an array, ...)
points at a cell without keeping it alive. Every weak reference to one cell shares a handle,
found through a table of the thread; when the cell is freed (its last reference went, or the
cycle collector found it dead) the handle is cleared and `TryGetTarget` gives false from then
on. While no weak reference exists the table is empty and freeing a cell costs one compare.
`match w.TryGetTarget() with | true, x -> ...` and `match d.TryGetValue k with ...` of a value
whose type has no default here (null on .NET) are read as an option.

A cell is freed at the last use of its last reference, so a weak reference sees it gone at
once, where on .NET it stays until the garbage collector runs; `GC.Collect()` runs the cycle
collector. Not yet: the non-generic `WeakReference`, weak references to strings and to
function values.

## Cycles

Reference counting alone never frees a structure that reaches itself. The cycle collector
(`fable_sgc.zig`, the per-structure-count collector of the prototype) does.

**Which types.** A cell that is never assigned after it was made can only point at cells that
were there before it, so data without assignable fields cannot form a cycle however recursive
its type is. A type can be part of a cycle only if, in the graph of which cell type can point
at which, it is in a strongly connected component that contains an assignable field. Only the
cells of those types carry the collector's header (36 bytes, next to the count); every other
type is plain reference counting and the collector never sees it. Three refinements:

- A function value and an exception can hold anything, and their type does not say what. But
  a cycle through one of them still needs an assignable field to close it: one that can
  hold a function value or an exception, directly or through other data. So they, and the
  types that can reach them, count as cycle-capable only in a program that makes a record
  with such a field somewhere. Every file states what its own code does (`$cycles`), the
  statements are joined along the imports, and the runtime reads the result from the
  program's root file (`fable_rt.functions_in_cycles`). In a program without such a record
  a cell of `(int -> int) list` is 40 bytes and no environment has a header; in one with,
  the cell is 72 bytes. (A program whose root file is not generated by this target gets
  the careful answer.)
- For a generic type the question is answered for its declaration; whether an instance is
  cyclic because of its type arguments is decided when the Zig is compiled
  (`fable_rt.holdsCyclic`): the cells of `Folder list` have a header, those of `int list` do
  not.
- The answer depends only on type declarations, so every file gives the same one.

**How.** Every connected group of such cells that an assignment has joined keeps one count:
the references to its cells that are not held in a field of one of them. When that count
reaches zero the whole group is dead, cycles included, and is freed at once; nothing is
scanned. A dead cycle inside a group that is still referenced is found by a check of that one
group, in bounded steps, at later allocations of such cells. A cell of such a type that is
never assigned to is in no group and costs one test per retain and release.

**Where the collector is told.** All in the runtime: a cell is made, retained, released, taken
apart, and a field of a reference record is assigned (`fable_rt.storeIn`). Generated code
never calls the collector, and it has no per-type code either: what a cell refers to is found
through `@typeInfo`.

Checks: `pub const fable_verify_cycles = true;` in a program's root file compares every
group's count with the cells before every allocation of such a cell (slow; for tests). In
every build, a group whose count says it is dead is checked against its cells' counts before
any of them is freed, so a wrong report is a panic with a message, not freed memory in use.

**From F#.** `Fable.Core.Zig.Collector` has `collect`, `step` (a bounded amount of work, for
idle time), `pause`/`resume` and the tuning (`setPace`, `setFreeBudget`, ...);
`Fable.Core.Zig.Counters` shows what the runtime did. Under .NET they do nothing and return
zero, so a program that calls them still runs on both.

**Threads.** Reference counts are not atomic: a value belongs to the thread that made it.
Each thread therefore has a collector, counters and an exception slot of its own
(thread-local; plain globals where there is one thread or no thread-local storage, or when
the root file says `pub const fable_one_thread = true;`). Values shared between threads need
a design of their own and are not supported.

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

`failwith`, `failwithf`, `invalidArg`, `invalidOp` and `nullArg` raise what they raise on
.NET, with the same message (`invalidArg "n" "too big"` says "too big (Parameter 'n')"). The
runtime library declares `System.Exception` and the classes a program most often raises or
handles by name, each under the class it derives from on .NET:

```text
System.Exception
├─ System.SystemException
│  ├─ ArgumentException ─ ArgumentNullException, ArgumentOutOfRangeException
│  ├─ ArithmeticException ─ DivideByZeroException, OverflowException
│  ├─ InvalidOperationException, NotSupportedException, NotImplementedException
│  ├─ IndexOutOfRangeException, NullReferenceException, FormatException
│  └─ KeyNotFoundException
└─ Microsoft.FSharp.Core.MatchFailureException
```

They can be made with a message (`raise (System.ArgumentException "...")`), matched
(`Failure msg`, `:? System.ArgumentException as e`) and asked for their message
(`e.Message`). A handler for a class catches the classes under it: a type test walks the
few links from the exception's class upwards. `Failure` is exactly `System.Exception`, as on
.NET, and an F# `exception` is a class of its own that nothing derives from, so its test is
one comparison. The message of an F# exception is the exception as `%A` writes it
(`Broken (1, "a")`), which is what .NET gives.

What .NET raises without a `raise` in the program is raised here too, with the same class and
message, and can be handled:

- A whole number divided by zero (`/` and `%`): `DivideByZeroException`. The smallest `int`
  or `int64` divided by -1: `OverflowException`. A divisor that is written out and is neither
  0 nor -1 needs no test and gets none.
- A match that no case covers: `MatchFailureException`.
- A character of a string outside of it: `IndexOutOfRangeException`. A member of a null
  string: `NullReferenceException`. An argument of a string method out of range:
  `ArgumentOutOfRangeException` or `ArgumentNullException`.

These are calls into the runtime library that return an error union (`ERt` in the IR), so a
function that divides by a variable can raise, and its callers have an error edge. A `while`
condition may raise, and may have `&&` and `||` in it: it is then tested inside the loop.

Not yet: `e.StackTrace` and inner exceptions, the file and line of a `MatchFailureException`,
structural equality of exceptions, arithmetic that is `Checked`, and other .NET classes than
those above. An exception that reaches the entry point is printed with its name and message,
and the program exits with 134, as on .NET on Unix.

## Strings

A `string` is what it is on .NET: immutable UTF-16, or null. `s.Length` and `s.[i]` count and
give code units, so an emoji has length 2 here as there, and nothing a program computes from
a string differs. In memory it is a pointer to a header (count and length, 8 bytes) that the
units follow. A literal is static data of the program: its count is a fixed mark, so that
making, copying and dropping one costs nothing and it is never freed.

```zig
pub fn greet(name: fable_rt.String) fable_rt.String {
    return fable_rt.format(.{ "hello, ", name, "!" });
}
```

A string is counted like a cell, by the same ownership pass: a parameter that is only read
is borrowed, the last use moves. It can hold no reference, so the cycle collector never
looks at one. `a + b + c` makes one string whatever the number of parts.

Null is a value like on .NET: `isNull`, `match s with null -> ...`, `s = null`; `+`, the
`String` module and formatting take it for an empty string; a member of it (`s.Length`,
`s.[0]`, `s.Trim()`) raises `NullReferenceException`. The length of a string that cannot be
null (a literal, the result of `+`, of `sprintf`, of the `String` module) is read without a
test.

Of `System.String`: `Length`, indexing, `Substring`, `IndexOf`, `LastIndexOf`, `Contains`,
`StartsWith`, `EndsWith` (each for a string and for a char), `ToUpper`, `ToLower` and their
`Invariant` forms, `Trim`, `TrimStart`, `TrimEnd` (white space or one char), `Replace`,
`Insert`, `Remove`, `PadLeft`, `PadRight`, `Equals`, `String(c, n)`, `String.IsNullOrEmpty`,
`IsNullOrWhiteSpace`, `Concat`, `CompareOrdinal`. Of the `String` module: `length`, `concat`
(of a list), `replicate`, `init`, `map`, `mapi`, `iter`, `iteri`, `forall`, `exists`,
`filter`, `collect`. Of `System.Char`: `ToUpper`, `ToLower`, `IsWhiteSpace`. What they
return, and what they raise for which argument with which message, is .NET's.

There is no current culture: everything is done as .NET does it in the invariant culture.
Searching and comparing are by code unit (`IndexOf "x"` is what `IndexOf("x",
StringComparison.Ordinal)` is on .NET). Upper and lower case map each code unit as
`Char.ToUpperInvariant` does; the table (`fable_unicode.zig`) was written out from .NET, and
a test compares all 65536 code units with a sum computed there.

### Text from values

`sprintf`, `$"..."` and `string x` all become one call of `fable_rt.format` with the parts of
the format, taken apart at compile time, so that no format string is read while the program
runs and a value of a type that cannot be formatted is a compile error. `printf`, `printfn`,
`eprintf` and `eprintfn` write such text as UTF-8 through `fable_rt.write_out` and
`fable_rt.write_err`, which a program without an operating system sets to its own functions.
A printf that is not given all its values (`List.iter (printfn "%d") xs`, `let show = sprintf
"<%d>"`) is the function that takes the rest.

The text is .NET's, character for character; the runtime library's tests hold what .NET 10
prints for each case:

- `%d %i %u %x %X %o %b %c %s %f %F %e %E %g %G %O %A` with width, precision and the flags
  `0`, `-`, `+` and space; `{x}` and `%d{x}` in an interpolated string.
- `%f` and `%e` round the exact value of the number, a tie to the even digit (`%.2f` of 2.675
  is "2.67", of 0.125 "0.12"), from the number's exact decimal digits. `%e` writes three
  exponent digits, `%g` at least two.
- `string x` and `{x}` are the shortest text that reads back as the same number: in digits
  from 10^-4 up to 10^17 (10^9 for a `float32`), as `1E+17` or `1E-05` outside of that.
  `string 1.0` is "1".
- `{x:N2}`, `{n:D5}`, `{n:X}`, `{x:E2}`, `{x:G3}`: .NET's standard numeric formats (D, X, B,
  N, F, E, G, R, P, C with an optional precision), and `{x,8}` and `{x,-8:F1}` for alignment.
- `compare` on strings is by code unit and gives the number `String.CompareOrdinal` gives
  (`compare "a" "A"` is 32); on a float, not-a-number comes first.

`%A` writes a value as F# code: `{ Name = "Ann"` with every further field on its own line,
`Some (1, "a")`, `[1; 2; 3]`, `Node (Leaf, 1, Leaf)`. It is FSharp.Core's printer rule for
rule: the value becomes a layout of text and joints, the joints are broken from the
outside in until every line fits in 80 columns, a list shows 100 items, and a record that
contains itself is cut with `...` where it comes round again. `string x` and `{x}` of a
record or a union are its `%A`, and so is the message of an F# exception. The printer reads
the Zig types: field and case names are the F# ones, so nothing is generated per type.

Also: `Split` (by chars, a string or strings, with `StringSplitOptions`), `String.Join` and
`String.concat` of any collection or sequence, `ToCharArray`, `String(chars)`,
`StringBuilder` (`Append` of any value, `AppendLine`, `Clear`, `Length`, `ToString`),
`String.Format` with a literal format (taken apart at compile time like an interpolated
string: `{0,5:N2}`), and the classes of characters (`Char.IsDigit`, `IsLetter`, `IsUpper`,
`IsPunctuation`, ...: .NET's Unicode categories, a table written out from .NET).
`string x`, `{x}` and `Append x` of an option, a tuple, a list, a map or a set are .NET's
ToString: `Some(1)`, `(1, a)`, `[1; 2; 3; ... ]`. Comparisons that say how compare
`Ordinal` or `OrdinalIgnoreCase` (each code unit by its upper case).

Not yet, each of them a compile error and not a different text:

- `%A` of a type that mentions a `uint16`, a `voption`, a struct tuple or a function. (The
  first three are the same Zig type as `char`, `option` and a tuple. In the message of an F#
  exception, where nothing can be refused, they are written as those.)
- A width or flags on `%A`; a custom .NET format (`{x:0.00}`); `String.Format` of a format that is not a literal.
- Comparison by a culture: `CompareTo`, `String.Compare` without `Ordinal`, and the
  `CurrentCulture` and `InvariantCulture` kinds of `StringComparison`.

Appending to a string in a loop copies it each time, as on .NET. A program that declares an
F# exception links the `%A` printer, because any exception may be asked for its message.

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
5. ~~Mutable reference records and the cycle collector~~ (done).
6. ~~Strings, formatting and printing, `%A`, the `String` module, exceptions with messages
   and classes~~ (done); arrays and the other collections, and the rest of FSharp.Core
   through `Replacements.fs` and the library.
7. The test suite (`tests/Zig`), starting from the tests the other targets share.

## Notes for the shared code

- Nothing goes through another target's replacements. `Zig/Replacements.fs` handles every
  entry point of `Replacements.Api`: operators on numbers, booleans and chars become plain
  operation nodes, and every other call into .NET or FSharp.Core is kept as it is, as a call
  to an import named after the declaring type (`dotnet:System.Math`, `Sqrt`). The lowering
  resolves those by their .NET names (`dotnetCall` in `Fable2Zig.Lower.fs`) or rejects them
  by name ("the Zig target does not support System.Math.Sqrt yet"). So far it knows
  structural equality, `compare`, `ignore`, `id`, `fst`, `snd`, the conversions between
  numbers, strings and `printf`, the ref cell operators and the functions that raise.
- Generated files import the hand-written runtime (`fable_rt.zig`, copied into
  `fable_modules/fable-library-zig`) only when they use it. It has its own Zig tests
  (`zig test src/fable-library-zig/fable_rt.zig`). Its type introspection uses the
  `field_names` / `field_types` form of `@typeInfo` (Zig 0.17 and later).
- Two places in `FSharp2Fable.fs` drop information this target needs and will need a
  Zig-specific branch: the address of anything but a variable or field is discarded, and a
  store through a byref that is not a plain variable is rejected.
- `src/Fable.Core/Fable.Core.Zig.fs` is the target's F# API (the collector and the runtime's
  counters). Its functions have `Emit` attributes and ordinary bodies, which is what makes
  them usable under .NET too.
- The target is not part of the stand-alone (JavaScript-hosted) compiler.
