# Fable → Zig: planned enhancements

Status: implemented (Parts 1, 2, and 3). Revised after two reviews checked it against the code. Three
parts:

- **Part 1:** borrow inference across files.
- **Part 2:** specialization of higher-order functions for known lambdas.
- **Part 3:** tail calls that run in constant stack wherever .NET's do. That covers calls of
  function values, of functions of other files, and of virtual and interface methods, plus
  tail recursion modulo cons inside fused mutual recursion.

Parts 1 and 2 address two limits named in `FABLE-ZIG.md`:

1. **Borrowing across files.** A file cannot see what another file's functions were inferred to
   borrow. `fable_rt.across` reconciles each call at Zig compile time, but two costs remain
   (FABLE-ZIG.md, "Calls between files"):
   - a parameter that a function forwards to another file's function is inferred as owned,
     so its callers pay a dup and a drop;
   - a borrowed result from another file is always dup'ed.
2. **Higher-order functions are not specialized for the lambda they are given**, except:
   - inside one file (`specializeHofs`, `Fable2Zig.Perceus.fs:2260`);
   - for a fixed list of library functions, through hand-written IR templates
     (`trySpecListHof` / `trySpecArrayHof`, `Fable2Zig.Lower.fs:7445-8880`, about 1,400
     lines). They cover `init`, `map`, `mapi`, `filter`, `choose`, `fold`, `iter`, `iteri`,
     `exists`, `forall`, `tryFind`, `sumBy` and the `Array` equivalents.

   Every other call of a function value is an indirect call through `fable_rt.Func`. That
   includes any HOF of another file of the program and any library function without a
   template. If the lambda captures anything, a reference-counted `Env` is allocated.

Neither fix needs whole-program compilation. Both follow Koka, Lean and GHC: each module
exports a summary of facts, and the modules that import it read the summary. The F# file
order makes this easier than in most languages: **files cannot depend on each other in a
cycle**, so the facts of every file a file calls can be computed before that file.

---

## Part 1: borrow facts in file order

### What exists

- `Fable2Zig.fs`, `transformFileHere`, runs `Lower.lowerFile`, then `NonNull.run`, then
  `Perceus.run`, then `Emit.emitFile`. It runs on a worker thread with a 256 MB stack, which
  `transformFile` starts and then `Join()`s. `Pipeline.Zig.compileFile` calls it
  synchronously, so a pool thread is held for the whole file.
- `Perceus.run` (`Fable2Zig.Perceus.fs:2723`) works on one file:
  1. `cleanup` and `specializeHofs`;
  2. `inferRaises`, then `elideDeadTry`;
  3. `inferStores`;
  4. normalisation: `hoistRaising`, `hoistMutableReads`, `nameProjections`, `splitPathsIn`;
  5. `inferBorrows`, a fixed point over the file's functions;
  6. `pc`, which inserts dups and drops using the inferred modes.
- **Calls to another file's functions:**
    - `modesOf` (`:917`) assumes every managed argument is owned, and `isBorrowedRet`
    (`:930`) assumes the result is owned.
    - The emitter writes `fable_rt.across` or one of its compact forms (`callM`, `callG`,
    `xcallM`, `xcallG`, through `acrossCompact` with `err_drops`). Zig reconciles each call
    with the callee's real `$sig` at compile time (`fable_rt.zig:7649`).
- **How the emitter decides `.keep` / `.give`.** It doesn't track liveness: `formatCrossCall`
  (`Fable2Zig.Emit.fs:289-299`) reads it off the shape of the IR. An argument wrapped in
  `EDup` becomes `'k'` and anything else `'g'`. This only works because every argument to
  another file is assumed owned, so Perceus wraps each argument that stays live in an
  `EDup`. Part 1 has to change this first (see "Recording uses explicitly").
- **A borrowed result stays a borrow only when it is let-bound.** The owner mechanism in
  `pcLet` (`Perceus.fs:2027-2038`) keeps a borrowed result as a borrow only if three
  things hold: the result is let-bound, it is not mutable, and every argument it comes from
  is a stable path. In every other owning position, `pc` wraps the call in `EDup`
  (`:1644`).
- **Scheduling.** Fable starts compiling a file in the thread pool as soon as the F#
  compiler has checked it (`Fable.Cli/Main.fs`, `FSharpFileTypeChecked` → `fableCompile`).
  `FSharpCompilationFinished` computes the dependents of files whose *F# signature* changed.
  That is decided when *type checking* finishes, which does not wait for Fable's compiles of
  the batch.

### The change

Split each file's Zig transform in two, with a facts table for the whole project between
the halves:

```text
lower ─► NonNull.run ─► cleanup ─► specializeHofs (same file)
      ─► [wait for the facts of the files it calls]
      ─► Tier 2 clones (Part 2) ─► inferRaises ─► elideDeadTry ─► inferStores
      ─► hoistRaising ─► hoistMutableReads ─► nameProjections ─► splitPathsIn
      ─► inferBorrows ─► no-escape inference (Part 2) ─► publish facts ─► pc ─► emit
```

Every pass that consults other files' facts comes after the wait. That includes the
normalisation passes, which have to follow the inferences they read: `elideDeadTry` and
`hoistRaising` read `inferRaises`, and `hoistMutableReads` reads `inferStores`. Before the
wait is only purely local work. A file waits only for the files it calls.

How much parallelism this costs depends on how a file's time splits between lowering and
the rest. Measure it with `FABLE_ZIG_TIME` before and after.

**The two halves run as two hops of an `async`, so a waiting file holds no thread:**

```fsharp
// Pipeline.Zig.compileFile
async {
    let lowered = Compiler.lowerOnBigStack com file           // 256 MB thread, Join
    let! facts = Facts.awaitImports com lowered |> Async.AwaitTask
    let zig = Compiler.inferAndEmitOnBigStack com lowered facts   // 256 MB thread, Join
    ...
}
```

Each hop still joins its own big-stack thread, but none waits on another file while
holding a pool thread. Today's single `transformFile` holds one for the whole file, and a
pool thread blocked on a wait would stall large projects, because .NET adds pool threads
slowly.

#### The facts of a function

```fsharp
type FnFacts =
    { Modes: Mode list              // per parameter: MBorrowed | MOwned | MPlain
      RetFrom: int list option      // the result is a borrow of these parameters
      Raises: Raises                // with names qualified by file (see below)
      StoredFields: string list     // field keys (entity full name | field) it may assign
      CallsCallback: bool           //   (the same precision as inferStores inside a file,
      CallsExtStore: bool           //   rather than one Stores flag)
      FnParamsNoEscape: bool list   // used by Part 2
      NeedsChain: bool }            // used by Part 3 (full or thin $tc)

type FileFacts =
    { Version: int                  // the format and the compiler's version; a mismatch
                                    // means "no facts"
      File: string                  // normalized full path of the .fs file
      Hash: string                  // over Fns and the bodies exported for Tier 2 (Part 2)
      Fns: Map<string, FnFacts> }   // only the pub functions (IsLocal = false)
```

- **One entry per generic function.** Borrowing is inferred once, on the generic code
  (FABLE-ZIG.md, "Generics"), so the facts are the same for every instance and the table
  is keyed by name.
- **Names in `Raises.RDepends` are qualified.** Inside a file it holds local names and `Ty`
  values. When published, the names are qualified with the file and the types made
  portable, so they mean the same in the importing file and in a sidecar.

#### Recording uses explicitly

**This is a prerequisite. Without it, correct facts would cause double frees.** Once facts
say a parameter is borrowed, Perceus passes a live argument with no `EDup`. The emitter
then writes `'g'`, `across` drops the argument after the call, and the caller drops it
again.

So Perceus records the use of each argument of a call into another file explicitly, and
the emitter stops inferring it:

- an argument in a position the facts call **borrowed** is always `'k'`. If it is the
  argument's last use, Perceus inserts the drop after the call itself;
- an argument in an **owned** position is `'k'` if it stays live (Perceus would have wrapped
  it in `EDup`), and `'g'` on its last use.

In the IR this is a marker node (`EUse(kind, arg)`) or a list of flags on the cross-file
`ECall`; the emitter reads the marker and never looks at `EDup` to decide. The same applies
to the compact forms.

**The raise edge needs the same drops.** Today, when the callee raises, `across` drops the
`'g'` arguments. An argument in a borrowed position whose last use is the call is now `'k'`,
and Perceus drops it after the call. That drop must also be on the call's raise edge (the
`err_drops` of the compact forms, `EOnRaise` in the IR), or the argument leaks when the
callee raises.

This encoding stays correct when facts are stale:

- `'k'` to a parameter that has since become owned: `across` dups the argument.
- `'g'` to a parameter that has since become borrowed: `across` drops the argument after
  the call.

#### Using the facts

In step 3 of the order of work, **only `Modes` and `RetFrom` are used**. `across` provides a
backstop for those two, and nothing does yet for the rest (see "Stores and Raises").

- `modesOf`: for a function of another file whose facts are known, use its `Modes`.
- `isBorrowedRet`: likewise with `RetFrom`, **in the let-bound owner case only** (next
  section).
- `inferBorrows` then treats calls into another file like calls inside the file. A
  forwarded parameter stays borrowed when the function it is forwarded to borrows it.
- **`borrowSources` and `tailSources` (`Perceus.fs:1022-1070`) don't use `Ext` in step 3.**
  They read a callee's `RetFrom` to infer the caller's *own* `RetFrom`. Take
  `let g xs = Helpers.first xs`: the call is returned directly, not let-bound, so it is
  emitted in the form where `across` dups the result. If `tailSources` trusted the fact, `g`
  would claim to return a borrow while returning an owned value, which would leak at every
  caller of `g`. Later they may use `Ext` only for calls in the owner case. For example, a
  call in return position could be let-bound first, so that it takes the owner form, but
  that only after measuring that it pays.

#### Borrowed results: two forms of the call

`across` drops `.give` arguments as soon as the callee returns. That is why today it dups a
borrowed result before the drop. So Part 1 uses two forms:

1. **The owner case.** The result is let-bound, not mutable, and its source arguments are
   stable paths (the condition at `Perceus.fs:2027`).
   - Perceus records the result as owned by its sources, and each source argument
     is `'k'`. Its drop comes after the result's last use, as for a call inside the file.
   - The call is `acrossAssumed`, which does not dup the result. At Zig compile time it
     asserts that `sig.result_from` matches the assumption, and that `uses[j] == 'k'` for
     every `j` in it. If either fails, it stops with a `@compileError` naming the file to
     recompile.
2. **Every other position.** Keep today's form: `across` dups the borrowed result inside
   the call, before dropping the `.give` arguments. Perceus does **not** add an `EDup` of
   its own: for these calls `isBorrowedRet` stays false.

`$sig` gains `result_from` (the indices) next to `result_borrowed`. `acrossAssumed` gets
compact forms to match `callM` / `callG` / `xcallM` / `xcallG`.

#### Soundness when facts are missing or stale

| Fact relied on | Callee changed since | Outcome |
| --- | --- | --- |
| parameter `i` borrowed (`'k'`) | `i` is now owned | `across` dups. Correct, slightly slower. |
| parameter `i` owned (`'g'` on last use) | `i` is now borrowed | `across` drops after the call. Correct. |
| result borrowed from `j` (owner case) | the result is now owned | `acrossAssumed` stops with a `@compileError` asking for a recompile. |
| `Raises`, `Stores` | anything | No backstop: these two aren't used until one exists (below). |

Where no facts are known (a hand-written Zig file, a sidecar from another version, a file
that failed to compile), keep today's assumptions: owned parameters, an owned result, and
`across` sorting it out.

#### Stores and Raises

A stale "does not store" would let `hoistMutableReads` move a read across the call. A stale
`RNever` would let `elideDeadTry` remove a `try ... with`. Both give silently wrong results,
and `across` does not catch either. So they are used only with a backstop of their own:

- **Raises:**
    - Today the Zig type already says whether a call can raise (`MayRaise`, a `Raised!`
    result).
    - When the caller relies on `RNever`, it emits a compile-time assertion that the callee's
    return type cannot raise (`!fable_rt.isRaised(...)`). A mismatch stops the Zig build and
    asks for a recompile.
- **Stores:** each function gets a `$stores` constant with its field keys and its two flags,
  and the caller asserts what it relied on in the same way.

They come after step 4 (the CLI hooks), which keeps such assertions unreachable in practice.

#### Where the table lives, and how a file waits

There are three sources of facts, tried in this order:

1. **This batch.** A `TaskCompletionSource<FileFacts option>` per file of the batch, in a
   table for the project. A file publishes its facts as soon as no-escape inference
   finishes. A file that needs them awaits them asynchronously (the hop described above).
2. **An earlier batch of the same process** (watch mode): the last published `FileFacts`.
3. **A sidecar file**, written next to each output: `Helpers.zig` + `Helpers.facts.json`.
   - It covers a cold start where Fable skips files whose output is up to date
     (`areCompiledFilesUpToDate`).
   - It also covers **the library**: `BuildFableLibraryZig` copies the `*.facts.json`
     files into `fable_modules/fable-library-zig/`, the way Koka ships `.kki` files next to
     its compiled modules.
   - A sidecar whose `Version` does not match is ignored.

**Every pending task is completed, whatever happens.** Otherwise a wait could hang forever:

- **A file whose compile fails** (`ZigError`, or an internal error, where
  `transformFileHere` returns `""`) publishes `None` in a `finally`. Its importers fall
  back to today's assumptions.
- **A file the F# compiler never reports.** An earlier file with type errors may never get
  `FSharpFileTypeChecked`, so it is never dispatched and never publishes. When
  `FSharpCompilationFinished` arrives, every file of the batch that has not been dispatched
  never will be, so its task is completed with `None` then.

  This has to happen **after** that handler's own dispatch: with `NoParallelTypeCheck`,
  files are dispatched *inside* `FSharpCompilationFinished` (`Main.fs:758-774`). Completing
  first would answer every file `None`.

  This cannot wait for the end of the batch: waiting files are themselves compiles of the
  batch, so the batch would never end.
- **Ordering.** The F# file order rules out cycles of waits. Together with the two rules
  above, no wait can last past the end of type checking plus the compiles it waits for.

#### Changes to Fable's shared code (Fable.Cli only)

The changes are guarded by `Language = Zig`. They follow the precedent of Rust's
`DelayedLastFile` in the same loop (`Main.fs`, `FSharpFileTypeChecked`).

1. **Start of every batch.** Call `Zig.Facts.beginBatch files` wherever `Main.fs` sets
   `FilesToCompile`:
   - in `StartCompilation`;
   - where `FSharpCompilationFinished` schedules F# signature dependents;
   - where hook 3 schedules a facts batch.

   This creates a pending task for each implementation file of the batch (`.fs`, `.fsx`;
   none for `.fsi`), which replaces its facts from the previous batch. Any file outside the
   batch is answered from source 2 or 3.
2. **End of type checking.** In `FSharpCompilationFinished`, after its own dispatch,
   complete with `None` the tasks of the files of the batch that were never dispatched (see
   above).
3. **Facts changed → a facts batch.**
   - **When.** This trigger has to wait for the last `FableFileCompiled` of the batch, after
     `FSharpCompilationFinished`. The F# signature path can't be used for it: it decides at
     the end of type checking, which usually comes *before* most of Fable's compiles have
     published.
   - **What.** At that point, compare each compiled file's `Hash` with its previous one. For
     each file whose facts changed, take the files that import it directly. These come from
     a reverse map built from each file's `state.Imports`, recorded in the facts table when
     the file publishes. That is exact, unlike `GetSignatureDependents`, and it includes
     imports that exist only on the Zig side. Exclude only
     those that were **in the same batch** as the changed file, because only they waited
     for its new facts. Start a new batch with the rest.

     Excluding everything compiled anywhere in the cycle (`FilesCompiledInCycle`) would be
     wrong. Say batch 1 is `{A, C}` and C imports B, which is not in the batch, so C reads
     B's facts from before. A's facts change, so B is rebuilt in a facts batch, and B's facts
     change too. C was compiled in this cycle, but against B's *old* facts, so it must be
     rebuilt.

     Direct importers are enough. A file only reads the facts of the files it imports, and
     if the facts of a file in between change, that file's own batch takes the change on.
   - **No new type check.** A facts batch skips `typeCheck`, because the F# of those files
     has not changed. It calls `fableCompile` directly with the `FableProj` already in the
     state.
   - **Finishing.** `CheckIfCompilationIsFinished` must not report the compilation finished
     while a facts batch is running. The loop ends once a batch changes no facts.

     It always ends. Within a cycle the sources don't change, so a file's facts depend only
     on the facts of the files it imports, all of which come earlier in the F# order. The
     first file's facts are final after its first compile. Once the facts of every file
     before file *i* are final, file *i*'s facts are final after one more batch. So the
     number of batches is at most the length of the longest chain of imports.

A body edit that leaves the facts unchanged recompiles nothing downstream. That answers the
"a cached answer would go stale" concern in FABLE-ZIG.md. `Pipeline.fs` (already
Zig-specific) writes the sidecar. Nothing in `Fable.AST`, `FSharp2Fable` or
`FableTransforms` changes.

#### Changes to the Zig target

- `Fable2Zig.fs`: `transformFile` becomes `lowerOnBigStack` and `inferAndEmitOnBigStack`,
  with publishing (and the `finally` that publishes `None`) in the second.
- `Perceus.fs`:
    - `run` is split at the wait.
    - `P` gains `Ext: string -> FnFacts option`. It resolves an `ECall` name such as
    `m_Helpers.sumList` through `state.Imports` (alias → file path), then looks the name up
    in the table.
    - `modesOf` and `isBorrowedRet` consult `Ext` (and so do `callRaises` and `scanFnStores`,
    once their backstops exist).
    - `pc` records uses explicitly.
- `Emit.fs`:
    - `formatCrossCall` reads the recorded uses.
    - It emits `acrossAssumed` (or a compact form) in the owner case, and the `$raises` /
    `$stores` assertions when those facts are used.
    - It keeps emitting `$sig` as today, so hand-written Zig code and older callers keep
    working.

#### What it does not cover

- Calls through `ECallVt`, `ECallIface` or `ECallClo` (virtual calls, interfaces, function
  values) are still treated as owning, because the callee is not known statically. Part 2
  handles the function-value case where the lambda is known.
- Recursion between files is impossible in F#, so no fixed point ever has to cross a file
  boundary.

---

## Part 2: specialization for known lambdas

There are two tiers:

- **Tier 1** handles every HOF, the library included. It needs no facts from the F# side,
  so it can ship before Part 1.
- **Tier 2** adds what only cloning the body can give, and needs Part 1's table.

### Tier 1: Zig instantiates a HOF for each lambda type (`callK`)

Zig already makes the instances of generic functions (`map(i32, bool).call`). The same
mechanism can make an instance per lambda: a second entry point whose function parameter has
a type Zig knows at compile time.

```zig
pub fn map(comptime @"'T": type, comptime @"'U": type) type {
    return struct {
        pub const sig = @"map$sig";
        // today: an indirect call through a Func per element
        pub fn call(mapping: fable_rt.Func(*const fn (?*fable_rt.Env, @"'T") fable_rt.Raised!@"'U"), list_in: fable_rt.List(@"'T")) ... { ... }
        // new: `mapping` is any callable whose type Zig knows; one instance per lambda
        pub fn callK(mapping: anytype, list_in: fable_rt.List(@"'T")) ... { ... }
    };
}
```

The caller passes a **known lambda**: a struct, built in place, that holds the captured
values. Its type names the lifted function as a declaration.

```zig
// F#: xs |> List.map (fun x -> x * k)
const K1 = fable_rt.Known(main_lambda_1, .{ i32 }, 1);     // code, capture types, arity
m_List.map(i32, i32).callK(K1{ .caps = .{ k } }, xs)
```

Inside `callK`, a call of `mapping` is `fable_rt.invokeK(mapping, uses, .{ x })`. At Zig
compile time it becomes a direct call of the lifted function, which LLVM can inline. When
the argument is an ordinary `Func` (a lambda that isn't known at the call site), `invokeK`
makes the indirect call, so `callK` also accepts what `call` accepts.

What this gains:

- **A direct call** per element instead of an indirect one, so LLVM can inline the lambda.
- **No `Env` allocation.** The captures live in the struct, on the caller's stack. This is
  sound only if the HOF never lets `mapping` outlive the call, which is what the no-escape
  rule below guarantees.

#### What `invokeK` does

- **Arity, and curried lambdas.**
    - **A lambda whose type is not curried** (`TFn([a; b], r)`, the uncurried form Fable gives
    wherever it can): `Known` names the lifted function, its arity is the number of
    parameters once the captures are removed, and `invokeK` passes exactly that many.
    - **A curried lambda** (`TFn([S], TFn([T], S))`, the type of `fold`'s `folder`).
    `folder state x` is *one* `ECallClo` with two arguments, which the emitter turns into
    `fable_rt.apply2` (`Emit.fs:488-496`). `apply2` uses `code2` when there is one, and
    otherwise applies twice. The two-argument lifted function exists only through
    `state.Curried2`, and only for some lambdas (`Emit.fs:545-571`), so `Known` follows the
    same scheme:
        - `Known` gets a `call` for the first stage, which returns a `Func`. When the caller's
      `state.Curried2` has an entry for the lambda (the caller made the lambda, so it
      knows), `Known` also gets a `call2` for the two-argument form.
        - `invokeK` with two arguments on a curried type uses `call2` when it exists. Otherwise
      it calls `call` with the first argument and applies the returned `Func` to the second,
      as `apply2` does without `code2`. A lambda such as
      `fun acc -> let y = ... in fun x -> ...` has no `Curried2` form and takes this path.
      It is still a direct call for the first stage, and it is never a compile error.

    This is what makes `fold`, `reduce` and the other curried HOFs usable with `callK` from
    every caller. `Known` copies `code2`'s idea (`call2`); it doesn't need `Env.stage`.
    - **Three or more arguments.** Lowering (`applyValue`, `Lower.fs:5262-5294`) applies at
    most two arguments at a time from a curried value and nests the rest. `folder state x y`
    in `fold2` is `ECallClo(ECallClo(folder, [state; x]), [y])`.
        - **Such a chain counts as one full application** when its arguments together match the
      curried type's depth and the inner results are used for nothing else. `invokeK`
      applies it in stages: `call2` (or `call`), then the returned `Func`.
        - **This can't lead to `Known(Known(...))`,** because the intermediate result is an
      ordinary `Func`.

    This covers `fold2`, `foldBack2`, `mapIndexed2` and `map3` (`List.fs:584, 753, 874`).
    - **A HOF that applies its parameter in stages and keeps the intermediate function**
    (`let g = f acc in ...`, or the inner result used anywhere other than as the next callee
    of the chain) is partially applying it. That is an escape, so it gets no `callK`.
- **Arguments.** `uses` and the lifted function's `$sig` decide which arguments are dup'ed,
  as in `across`. See "Ownership inside `callK`".
- **Result.** If the lifted function's result is borrowed (`RetFrom`), `invokeK` dups it,
  as `across` does, since the HOF expects an owned result from a function value.

#### Who owns the captures of a known lambda

The struct is a *view* of the caller's captured values, not an owner of them. An `EClosure`
moves its captures into the `Env` it makes; a `Known` struct does not:

- **The caller treats each capture as borrowed for the whole call.** Each capture is a use
  in a borrowed position, live until `callK` returns, and the caller drops it after its own
  last use, as with any borrowed argument. Nothing moves into the struct, so there is
  nothing to drop on the `callK` path, and nothing is counted twice on the fallback path.
- **The lambda receives its captures as borrowed.** The struct is called once per element,
  so the lambda can't consume them:
    - The adapter (`Known(...).call`) passes them as `*const Caps` when they are larger than
    two words, and by value otherwise.
    - It reconciles them with the lifted function's inferred modes the way `across` does:
    a capture that the lifted function takes as owned is dup'ed for each call.
- **The lambda's body never sees the struct.** It receives capture *values*, so a closure
  it builds (`fun a -> let y = f a in fun b -> y + b + cap`) dups `cap` into its own heap
  `Env`, as `EClosure` does today. Nothing can alias `&mapping.caps` on the caller's stack.

#### The rule that guards it: function parameters that do not escape

A parameter of function type *does not escape* when every use of it in the body is one of:

- the callee of an `ECallClo` that passes the lambda's full arity (above);
- passed **unchanged** to a not-escaping parameter of a function of this file that has a
  `callK` (a fixed point, like `inferBorrows`). This includes the lifted local
  `let rec go` / `loop` helpers that idiomatic HOFs use, since lambda lifting passes the
  parameter to them unchanged;
- passed **unchanged** to a not-escaping parameter of another file's function that has a
  `callK`, according to its facts (Part 1), or to its `$noescape` constant when there are
  no facts.

Everything else is an escape:

- storing it in a field or a cell;
- capturing it in an `EClosure` (`Seq.map`'s lazy sequence, or a HOF that wraps the lambda
  before passing it on, such as `fun x -> mapping (f x)`);
- returning it;
- passing it to an owning position, a virtual call or an interface;
- passing it to a function that only takes a `Func`;
- applying it with fewer arguments than its arity, other than as the start of a chain that
  supplies them all (above).

The rule is strict on purpose:

- **Recursive calls cannot build ever-bigger types.** A recursive call passes `mapping` on
  unchanged, so it is the same instance. A HOF that wrapped the lambda on each recursive
  call would make Zig instantiate `callK` with `Known(Known(...))` without end. Under the
  rule, that parameter escapes, so it has no `callK`.
- **`callK` never has to turn its struct into a `Func`.** A `Func` made from the caller's
  stack would need per-capture dup and `Env` drop glue in `Known`. Nothing inside `callK`
  ever needs one.

No-escape inference uses other files' facts, so it runs after the wait (Part 1's diagram).
Before Part 1 exists, other files are covered by `$noescape` at Zig compile time.

`callK` is emitted **only for HOFs where at least one function parameter does not escape**,
and only those parameters become `anytype`. The answer is published as `FnParamsNoEscape`,
and in Zig as `pub const map$noescape = .{ true }`, so that a caller can choose at Zig
compile time:

```zig
fable_rt.callHof(m_List.map(i32, i32), K1{ .caps = .{ k } }, .{ xs })
// → .callK(...) when @hasDecl(M, "callK") and the parameter does not escape;
//   otherwise an ordinary closure is made and .call(...) is used
```

**`toFunc` exists only for that fallback, in the caller.** It does what the `EClosure` the
caller would otherwise have built does: a heap `Env` with each capture dup'ed into it (the
caller's own stay borrowed for the call), dropped after the call. Inside `callK` it is
never emitted.

#### How much of the library this reaches

This is what decides Tier 1's value. Several library HOFs wrap their parameter in a closure,
so under the rule they get **no** `callK`:

- `partition`: `filter (fun x -> not (predicate x))`, `List.fs:341`;
- `sortBy`: `sortWith (fun a b -> compare (projection a) (projection b))`, `:402`;
- `groupBy`, `countBy`, `maxBy` and `minBy` (folds with a wrapping lambda).

These recurse directly, or through a lifted `go`, and qualify: `map`, `filter`, `choose`,
`collect`, `exists`, `tryFind`, `takeWhile`, `fold`, `reduce` (which forwards to `fold`
unchanged) and `distinctBy` (through its `go`). `fold` and `reduce` take a curried
`folder`, so they go through `call2`, or the first stage plus `apply`, as described above.
Most of those already have templates. The ones that don't, and are therefore the real
measure of Tier 1, are `collect`, `takeWhile`, `reduce` and `distinctBy`.

For the wrapping ones there are two options, to choose after step 2's measurements:

- rewrite them in `List.fs` so they forward the parameter unchanged, for example
  `partition` as one pass with a `go` that calls `predicate`. That is a library change,
  with no change to the rule;
- relax the rule so that a wrapping closure which itself doesn't escape counts as not
  escaping. That is a compiler change, and it needs the `Known(Known(...))` question
  answered first.

#### Ownership inside `callK`

Today a function value owns its arguments and its result (FABLE-ZIG.md, "Function values").
So Perceus treats every argument of an `ECallClo` as owned, and dups it when the HOF still
needs it. For `List.exists` over a list of strings, that is a dup per element, followed by
a drop inside the lambda.

`callK` is a **second Perceus run on a clone of the HOF**, made before `pc`. In it, an
`ECallClo` of a not-escaping parameter is treated like a call into another file, with uses
recorded explicitly (Part 1, "Recording uses explicitly"). `invokeK` reads the lifted
function's `$sig` and dups only for an owned parameter, as `across` does.

This way the lambda's borrowing reaches through a HOF of another file, or of the library,
without that HOF's body leaving its file. Only HOFs that have a `callK` pay for the clone
and the second run.

#### Effect on the existing special cases

- **The templates** (`trySpecListHof` / `trySpecArrayHof`) become optional. Remove one only
  when the `lists` benchmark, and a new one per removed family, stays within the 5% gate. A
  template still wins where it fuses a pipeline or knows a length, so expect some to remain.
- **`specializeHofs`** (inside one file) stays. It also gives in-place reuse and borrow
  inference over the specialized body, which `callK` doesn't.

#### Costs and interactions

- **Zig compile time and code size:** one instance per (HOF, lambda type). `callK` is only
  instantiated where a known lambda is passed. Track `FABLE_ZIG_TIME` and the size of the
  benchmark binaries.
- **Recursion and forwarding:** one instance per chain. TRMC and loops are kept, since they
  come from the same Perceus output.
- **Tail calls (Part 3):** an `invokeK` of a `Known` lambda in tail position is a direct
  call to a known target. It doesn't take Part 3's path for unknown callees. If the lambda
  itself ends in a call of an unknown continuation, the lambda's own body makes that tail
  call.

### Tier 2: cloning HOF bodies from other files of the project

This is what `specializeHofs` already does inside a file, extended across files with Part
1's table.

#### What is exported

When a file publishes its facts, it also publishes a **unit** for each pub HOF that has a
not-escaping function parameter.

- **The unit holds** the HOF and every function its body reaches through `ECall` or
  `EClosure` that is `IsLocal`: its `let rec loop` helpers and its lifted lambdas.
  Idiomatic F# writes HOFs around an inner `loop`, so a rule of "pub declarations only"
  would turn most of them down. The reachable functions are found by the same walk as the
  dead-function pruning at the end of `specializeHofs`.
- **Snapshot:** the IR after `NonNull.run` and `cleanup`, and before `specializeHofs`. The
  exported body is the generic one, not one already specialized for the callee file's own
  lambdas.
- **Size:** `exprSize ≤ 250` for the whole unit, the limit used today.

The unit is exported only if everything it refers to can be named from another file. **It
is not exported if it refers to any of these:**

- an entity type (`TEnt`) that isn't pub;
- a `VGlobal` that isn't pub;
- an `EEmit` whose text names a symbol of the file (text that only names `fable_rt` is
  fine);
- an `EIface` (an object expression). Its slots point at the file's own vtables, which
  the walk would also have to follow (`Perceus.fs:2706-2708`) and clone. Leave this out
  until it is needed;
- a function with a stack arena (`state.Arenas`), or a resource hook.

Entries of `state.Curried2` for functions of the unit go with it.

#### What the caller does

A caller that passes a known lambda to such a HOF clones the unit into its own file after
the wait, with `cloneSpecializedFn`:

- every `Var` gets a fresh id from the caller's `state.NewVar`;
- the functions of the unit get fresh names;
- calls to the callee file's pub functions and references to its pub types are qualified
  with the import's alias (`ECall "go"` → `ECall "m_Helpers.go"`);
- calls between functions of the unit point at their clones;
- the imports the unit needs are added to the caller's `state.Imports`.

A folding round then runs on the clones: `foldKnownClosures` (`Perceus.fs:2180`),
`dropDeadClosures` and `cleanup`. These are private to the `Perceus` module, which is where
the cloning code should live too; then nothing needs exposing. They go
through borrow inference, reuse and TRMC as functions of the caller, which `callK` can't
provide.

The exported units are part of `FileFacts.Hash`, so an edit that only changes a body
(`+ 1` to `+ 2`) still recompiles the files that cloned it. The units are shared in memory
only; they are not written to sidecars. Tier 1 covers the library.

---

## Part 3: tail calls

### What exists

| Kind of call in tail position | Today | Where |
| --- | --- | --- |
| a function calling itself | a loop | `emitTailJump`, `Fable2Zig.Emit.fs` |
| a function calling itself as the one field of a new cell (`let r = self args in Case(..., r, ...)`) | a loop that builds the result top-down through `hole` (tail recursion modulo cons, TRMC) | `trmcSite`, `Emit.fs:866` |
| a group of functions of one file that call each other last, with the same result type, type parameters and raising | one loop with a `switch` on which function is running | `Emit.fs:2650-2740` (eligibility at about `:2729`) |
| functions of one file with the same signature of numbers, bools and chars, that cannot raise | `@call(fable_rt.tail_call, ...)` | `fable_rt.zig:6490` |
| a **function value** (continuation-passing style, `cont { }`, parser combinators) | an ordinary call | |
| a function of **another file** | an ordinary call | |
| a **virtual or interface method** | an ordinary call | |
| a TRMC function inside a mutually recursive group | an ordinary call: the eligibility check excludes the whole group (`(trmcSite fn.Name fn.Body).IsNone`) | `Emit.fs` |

The last four rows are what this part fixes. On .NET, F# emits `tail.` in Release builds
(`--tailcalls+`), so all four run in constant stack there. Code that relies on it, such as
CPS parsers or interpreters written with continuations, overflows the stack on the Zig
target today.

**A raise in the middle of TRMC is already safe.** `Plug` and `leaveText`
(`Emit.fs:1501-1510`, `:786-797`) emit `hole.* = plug; fable_rt.drop(result); return
error.Raised;` on a raise, so the partly built result is complete and gets dropped. The plug
is a case of the result type that has no fields. TRMC is turned off for a function that can
raise and whose result type has no such case (`fn.Raises = RNever || plug.IsSome`).

### Why the existing mechanism can't be stretched

`@call(.always_tail)` becomes LLVM's `musttail`. That needs the caller and the callee to have
the same parameter and result types, and it cannot be used when the result is returned
through a pointer into the caller's frame, which Zig does for records and unions
(FABLE-ZIG.md, "Tail calls"). For an unknown callee, the signatures are whatever they happen
to be.

The usual way out is a trampoline: the call returns a "call this next" request to a driver
loop. It allocates on every call and turns every return into a branch. That is what makes
tail calls slow on the JVM and in JavaScript.

### The design: a uniform tail-call entry

Give a function a second entry point whose signature is **the same for every function in the
program**, so `musttail` from any such entry to any other is always valid:

```zig
// fable_rt
pub const TailCtx = struct {
    self: ?*anyopaque,                     // a closure's Env, or a method's receiver; owned
    args: [tail_args_cap]u8 align(tail_args_align),   // the arguments of the call being made
};
pub const TailStatus = enum(u8) { ok, raised };
pub const TailFn = *const fn (ctx: *TailCtx, ret: *anyopaque) TailStatus;
```

#### How a jump carries what it needs

- **`ret` is a destination.** The callee writes its result to `*ret`. The destination lives
  in the frame of the *boundary*: the first caller that is not itself part of the chain. So
  it stays valid however many jumps follow. This is destination-passing style, the idea
  TRMC's `hole` already uses.
- **Each boundary has its own `TailCtx`, in its frame.** It passes `&ctx` down the chain.
  Every `$tc` takes `ctx` as a parameter and hands it on.

  A single buffer per thread would not be safe. After a `$tc` stores the next arguments,
  its defers still run (reuse-token frees, drops). A drop can run an `Env`'s `destroy` or a
  resource's `Destroy` hook, which is F# code. If that code enters a chain of its own, it
  overwrites the buffer before the jump. With one `ctx` per boundary, a nested chain always
  has its own.

  Each boundary frame grows by `tail_args_cap` bytes. Keep the cap small (128 bytes:
  sixteen words). Arguments that don't fit fall back to an ordinary call.
- **`ctx.self` carries the closure's environment or the method's receiver**, and the jump
  *moves* it in:
    - the caller dups it first if it keeps `k`, or gives up its own reference on its last use;
    - the caller can't drop `k` before the jump, because the callee reads `k.env`;
    - it can't drop it after the jump either, because its frame is gone.

  So the callee's `$tc` owns `self`: a closure's `$tc` takes or dups the captures it needs,
  then drops the `Env`. Virtual and interface adapters borrow the receiver today
  (`BorrowFirst`), so the `$tc` slots need adapters of their own that take it owned.
- **The result is a plain status, not an error union.** Zig's error-return traces (on in
  Debug and ReleaseSafe) add bookkeeping around functions that return `!T`, which doesn't
  sit well with a forced tail call. That is also why today's `fable_rt.tail_call` sites
  can't raise.

  A raise sets the exception the way it does now, makes `*ret` droppable (see "Raises in a
  chain"), and returns `.raised`, which every `$tc` passes back unchanged. Only the boundary
  turns it into Zig's error again.

#### The layout of the arguments

Zig doesn't promise the same field order for an anonymous tuple and a named struct, so the
caller and the callee get the buffer's type from one function of the parameter types:

```zig
pub fn TailArgs(comptime Params: []const type) type   // extern struct, fields a0, a1, ...
```

`tailStore(ctx, TailArgs(&.{ Expr, K }), .{ ... })` and
`tailLoad(ctx, TailArgs(&.{ Expr, K }))` use that one type. At Zig compile time,
`@sizeOf(Args) <= tail_args_cap` and `@alignOf(Args) <= tail_args_align` are both checked. If
either fails (a big struct, an over-aligned SIMD vector), the function gets no `$tc` and
calls to it stay ordinary.

#### Thin and full `$tc` entries

Every function `f` keeps its normal entry, unchanged, so ordinary calls cost what they cost
now. It also gets `f$tc`, in one of two forms.

**Which form.** A function `f` *needs a chain* if, following its tail calls (not counting
self calls and its fused group, which are loops), it can reach either:

- **an unknown callee**: a function value, or a virtual or interface method;
- **a function of another file that needs a chain** (decided in Zig; see below);
- **a cycle**: functions of the file that tail-call each other and could not be fused (for
  example different signatures, or `even`/`odd` over lists).

This is a fixed point over the file's graph of tail calls. **Full** entries are for the
functions that need a chain; every other function gets a **thin** one. A thin entry's
tail calls reach only a finite, acyclic set of known functions, so calling them as ordinary
calls adds a bounded number of frames, and constant stack still holds wherever it matters.
Most lambdas and methods, such as `fun x -> foo x y` with a known `foo`, or one that ends
in `List.map`, stay thin.

**Calls into other files are decided in Zig, from the callee's `f$chain` constant.** Every
function publishes whether it needs a chain as a Zig constant, `pub const f$chain`. For a
tail call into another file, the F# side doesn't guess; it emits both choices and lets Zig
pick:

- **The caller's normal body** makes the call a boundary only if the callee says so:

  ```zig
  if (comptime @hasDecl(M, "f$chain") and M.@"f$chain") <boundary> else <ordinary call>
  ```

  A callee without the constant (hand-written Zig, a library built before step 10) gets an
  ordinary call.
- **The caller's own `$chain` and `$tc`.** For a function whose only possible reason to
  need a chain is a tail call into another file, the F# side emits its `$chain` as an
  expression over its callees' constants. It then emits both forms, and an alias that picks
  one:

  ```zig
  pub const @"g$chain" = (@hasDecl(m_List, "map$chain") and m_List.@"map$chain") or @"h$chain";
  pub const @"g$tc" = if (@"g$chain") @"g$tcfull" else @"g$tcthin";
  ```

    - **Cost.** Fable pays for the second Perceus run of the full form; Zig compiles only the
    form that is chosen.
    - **No dependency loops.** A function in a cycle of the file needs a chain whatever its
    other callees are, so its constant is the literal `true`. The other constants refer
    only to functions further along an acyclic graph, either later in the file's tail-call
    graph or in earlier files, so Zig never sees a dependency loop between them.
- **Before step 10**, no function has an `f$chain` constant, so every call into another
  file is an ordinary call and every caller whose only reason would be such a call is thin.
  Part 3 therefore stays independent of Part 1.
- **With Part 1.** The facts carry the same answer (`NeedsChain`). When they are known, the
  F# side can emit just the right form instead of both.

A stale answer is harmless either way:

- a caller compiled as thin whose callee now needs a chain only costs stack;
- one compiled as full when it no longer needs to only costs speed;
- every function has a `$tc`, so a jump always has a target.

**Thin**: adapts the convention around the normal entry:

```zig
pub fn @"f$tc"(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {
    const a = fable_rt.tailLoad(ctx, TailArgs(&.{ A, B }));
    // a lambda: its captures come from the Env in ctx.self (taken or dup'ed), then the Env
    // is dropped; a method: ctx.self is the receiver, owned
    const env = fable_rt.takeSelf(ctx);
    // (through fable_rt.lift, as formatCrossCall does: when f cannot raise, its result is
    // not an error union, and `catch` on it would not compile)
    const r = fable_rt.lift(@"f"(env.caps..., a.a0, a.a1)) catch {
        // the same drops as below, on the raise edge
        plugRet(R, ret);
        return .raised;
    };
    // everything arrived owned: drop what the normal entry only borrowed (arguments, the
    // receiver, the Env); dup the result if the normal entry returns it borrowed
    ...
    @as(*R, @ptrCast(@alignCast(ret))).* = r;
    return .ok;
}
```

A thin entry needs no second Perceus run and no copy of the body. That matters because once
`Func.tcode` and the vtable slots exist, **every lambda's and every method's `$tc` is
referenced**, so all of them are compiled. Zig's lazy compilation only skips the `$tc`s of
module functions that nothing jumps to.

**Full**: split in two, so that the body is ordinary Zig, where `try`, `defer` and
`errdefer` work as they do anywhere else:

```zig
// the body: an ordinary function. It either writes the result to `ret` and returns null,
// or stores the next call's arguments in `ctx` and returns where to jump.
fn @"eval$tcbody"(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.Raised!?fable_rt.TailFn {
    const a = fable_rt.tailLoad(ctx, TailArgs(&.{ Expr, K }));    // copied out first
    ... body, with its usual try / defer / errdefer ...
    // `k v` in tail position, k a function value:
    const v = try ...;
    fable_rt.tailStore(ctx, TailArgs(&.{ V }), .{ v });
    ctx.self = k.env;                                         // moved, not dropped
    return k.tcode;
}   // ← its defers (reuse tokens, drops) run here; ctx belongs to the boundary, so a
    //   chain that one of them enters uses its own

// the entry: nothing to clean up, so the jump is always a real tail call
pub fn @"eval$tc"(ctx: *fable_rt.TailCtx, ret: *anyopaque) fable_rt.TailStatus {
    const next = @"eval$tcbody"(ctx, ret) catch { plugRet(R, ret); return .raised; };
    if (next) |f| return @call(fable_rt.tail_call, f, .{ ctx, ret });
    return .ok;
}
```

The body's frame has been popped by the time the entry jumps, so the stack stays constant.
LLVM will usually inline the body into the entry, and the `musttail` stays the entry's last
instruction. Error-return traces stay on the body, which is an ordinary call.

The body of a full entry is **a second Perceus run on a clone of the function**, with every
mode forced to `MOwned` and `RetFrom = None` (see "Ownership"). A function whose inferred
modes are already all owned, with an owned result, reuses its own Perceus output.

**For a generic function**, `$tc` is a member of the namespace it returns (`eval(T).tc`).

#### Which tail calls jump

In a full `$tc` body, every call in tail position goes to the callee's `$tc`:

| Callee | Jumps to |
| --- | --- |
| a function value | its `tcode` (see "Where `tcode` lives") |
| a function of another file | `m_Other.@"f$tc"` |
| a virtual method | `vt.@"m$tc"` (a second slot, with an owned receiver) |
| an interface method | the `$tc` slot of the interface's table |
| a function of this file | its `$tc` |

A function calling itself, or a fused group, still becomes a loop, which is cheaper than any
jump.

In a **normal** body, a tail call is a **boundary** when the callee may need a chain: an
unknown callee, or a known function that needs a chain (including a function in an
unfused cycle). Without this, mutually recursive known functions that can't be fused would
grow the stack whenever a normal body enters them, while .NET runs them in constant stack.
A tail call to a known function that needs no chain stays an ordinary call. The boundary
calls the callee's `$tc` as an ordinary call:

```zig
var ctx: fable_rt.TailCtx = undefined;
var result: R = undefined;
fable_rt.tailStore(&ctx, TailArgs(&.{ V }), .{ v });
ctx.self = k.env;
if (k.tcode(&ctx, &result) == .raised) {
    if (comptime fable_rt.hasNull(R)) fable_rt.drop(result);   // made droppable by the chain
    return error.Raised;                                      // back to Zig's error
}
return result;
```

The boundary adds **one frame**, and the chain behind it runs in constant stack. The depth
of the stack is therefore bounded by how many times the program *enters* a chain, not by how
long the chain is. .NET behaves the same way where a call is not a tail call.

A `Known` lambda's call in a normal `callK` body never goes through a boundary (Part 2).

#### Raises in a chain

**The invariant: a `$tc` that returns `.raised` leaves `*ret` safe to drop.** This is how
`Plug` works today, extended to chains, and it costs nothing on the path without a raise:

- **Who plugs:** the raising `$tc` writes the plug into `*ret` (`plugRet` above), whatever
  `ret` is:
    - the boundary's `result`, if nothing was written yet;
    - or the hole of a cell built earlier in the chain (TRMC into unknown callees, below).
- **The plug** is the field-less case where there is one, as today. Otherwise it is
  `fable_rt.nullOf(R)` (`fable_rt.zig:5549`):
    - for a counted cell, the type's immortal null cell, which `drop` never frees;
    - for a union, its first case with null fields, so `Leaf null` for
    `Tree = Leaf of string | Node of Tree * Tree`.
- **The boundary** drops `result` on `.raised` when `hasNull(R)`. For a type without a null
  (interfaces, identity objects), nothing in a chain writes `*ret` before its last step,
  because TRMC needs a type with cells, so there is nothing to drop and nothing is plugged.

**Generalize today's `Plug` the same way:** `nullOf` when the result type has no field-less
case. That **narrows** the `fn.Raises = RNever || plug.IsSome` restriction rather than
removing it. `nullOf` exists only where `fable_rt.hasNull(T)` holds, which is false for
types that contain an interface or an identity object (`fable_rt.zig:5512-5546`), and the
F# side doesn't compute `hasNull`.

So the emitter puts the TRMC loop behind a Zig compile-time check:

```zig
if (comptime fable_rt.hasNull(R)) {
    // the TRMC loop, plugging with nullOf(R) on a raise
} else {
    // the plain recursive version, as emitted today when TRMC is off
}
```

This is only for functions that can raise and whose result type has no field-less case;
the others keep today's single loop. The two copies are emitted with separate `Em` states:
`canPlainTry` and `leaveText` read `em.Loop` (`Trmc`, `Plug`), which must describe the
copy being emitted. It turns on TRMC for raising functions over types like
`Tree`, at no cost to the hot path. Holes stay `undefined` until the raise path plugs them,
as now.

Mirroring `hasNull` in F# would avoid emitting two versions, but it would have to follow
the runtime's rules exactly (depth limit, the `fable_null_cell` / `fable_identity` /
`fable_object` declarations, the arity limit on functions). The check in Zig can't drift
from the runtime.

TRMC into unknown callees (below) and fused groups with TRMC use the same check.

#### Ownership: a full `$tc` body owns everything

Nothing can run after a tail call. Two of today's conventions would need code after it:

- **A borrowed parameter** of the callee, whose argument the caller was done with, has to be
  dropped after the call (what `across` does with `.give`).
- **A borrowed result** has to be dup'ed after the call.

So a full `$tc` body uses the convention function values already use: **every managed
parameter owned, the result owned** (FABLE-ZIG.md, "Function values"). Before a tail call,
the caller dups what it keeps, and moves what it is done with into the buffer.

Lean does the same: its borrow inference marks a parameter as owned when it is passed on in
a tail call, so the call stays a tail call. `inferBorrows` already does this for mutual tail
groups (`mutualTail.Contains fn.Name then MOwned`, `Perceus.fs:1179`). A thin `$tc` does the
adapting around the normal entry instead.

#### Where `tcode` lives

`Func` is `{ env, code }`, or `{ env, code, code2 }` for curried two-argument functions.
There are two options:

- **A. In `Func`**, as a third or fourth word: `tcode: ?TailFn = null`. This is simple, but
  function values get bigger everywhere.
    - **The default of `null` matters.** Every existing `Func` literal keeps compiling: the
    runtime's (`fable_rt.zig:973, 5552, 7402, 7422`, ...), the emitter's
    `.{ .env = null, .code = ... }`, and the `Dotnet.*` modules'. So do `nullOf(Func)`,
    hand-written Zig and functions crossing threads.
    - A boundary or a full body that finds `tcode == null` makes an ordinary call instead.
    That also allows rolling it out gradually.
    - `isNullOf` and `nullCode` keep working on `env` and `code` alone.
- **B. In `Env`**, next to `stage` and `destroy`. `Func` stays the same size. A lambda
  without captures (`env = null` today) would need a static, immortal `Env`, and dup and
  drop of such a `Func` would then touch a counter where today they skip a null. That is a
  cost on every use, not only on tail calls.

Start with A. Measure the `virtual` and `lists` benchmarks, and the size of the binaries.
Move to B only if A's size shows.

#### What has to be true at a jump

The emitter checks these. Where one fails, the call stays an ordinary call. That is always
correct, just not constant stack.

- **No cleanup after the jump.** The split between body and entry ensures this. A raise
  while an argument is evaluated unwinds through the body's `errdefer`s as it does today.
- **Nothing in the arguments points into the frame:** no byref of a local, no
  `NativePtr.stackalloc`, no stack arena (`state.Arenas`). The IL `tail.` prefix doesn't
  allow these on .NET either.
- **The call isn't inside `try ... with`, `try ... finally` or `use`.** It isn't in tail
  position then, on .NET as well.
- **The arguments fit in `ctx.args`**, by size and alignment, checked at Zig compile time.

#### Tail recursion modulo cons into unknown callees

`ret` is a destination, so TRMC can extend to callees other than the function itself:

```fsharp
let rec go (next: int -> int list) n =
    if n = 0 then [] else n :: next (n - 1)
```

`n :: next (n - 1)` is `Case(..., k args, ...)` with an unknown `k`. In a full `$tc` body, the
cell is built with its field as a hole, written to the destination, and the jump to
`k.tcode` gets `ret = &cell.field`. This is Koka's TRMC for a callee that is not the
function itself. Where the cell and the hole live depends on how the union is represented:

- **A union whose cases are cells** (the recursive unions: `Cons: *struct {...}`):
  write `ret.* = .{ .Cons = cell }`, then jump with `ret = &cell.Tail`. The hole is inside
  the heap cell.
- **A union that is a value** (`KValueUnion`): write the outer union, tag included, into
  `*ret` first with `@unionInit`, then take `&ret.payload.field` as the next `ret`. The next
  destination is then inside the caller's destination, never inside the frame that is about
  to disappear.

If the chain raises, the `$tc` that raises plugs the hole it was given, and the boundary
drops a complete structure.

#### Fused mutual recursion with TRMC

The fused loop already requires every function in the group to have the same result type,
so **one shared `result` / `hole` pair serves the whole group**: `hole` always points where
the current function's result goes.

- **A plain tail call to another member:** set its parameters and the state, then
  `continue`. `hole` is unchanged.
- **`Case(..., member(args), ...)`:** build the cell with the field left as a hole, set
  `hole.* = cell` and `hole = &cell.field`, set the state, then `continue`.
- **A return of a value `v`:** `hole.* = v; return result;`.
- **A raise:** the existing `leaveText` path (`hole.* = plug; fable_rt.drop(result); return
  error.Raised;`), with the generalized plug.

**The code changes:**

- remove `(trmcSite fn.Name fn.Body).IsNone` from the eligibility check;
- generalize `trmcSite` from `f = self` to "a member of the group";
- emit `result` and `hole` for the fused loop when any member has a TRMC site, and set
  `Plug` on the fused loop so `leaveText` uses it.

Functions with a borrowed result (`RetFrom.IsSome`) stay excluded, because a borrowed
result can't be written into a new cell. The fused group then covers state machines that
build lists, such as a lexer that switches states while producing tokens.

#### Costs

- **Function values and method tables get bigger** (see "Where `tcode` lives").
- **A jump goes through memory.** Arguments are stored to the boundary's buffer and loaded
  back, which usually stays in L1 cache. That is far cheaper than a trampoline, which
  allocates, but dearer than passing arguments in registers. Only tail calls to unknown
  callees pay it. Calls to known functions, self calls and fused groups are unchanged.
- **Boundaries on every tail call to an unknown callee in a normal body**, including in code
  that never recurses (`fun x -> g x`). Each pays:
    - a store;
    - a frame;
    - `tail_args_cap` bytes of stack;
    - **a dup of the closure.** In a normal body a function value is usually borrowed, so
    moving `k.env` into `ctx.self` costs an increment at the boundary and a decrement in
    the callee, atomic if the closure is shared.

  The dup could be avoided with a flag in `TailCtx` saying that `self` is only lent, which
  is safe at a boundary because its frame outlives the chain. But the callee would then have
  to dup each capture it keeps instead of taking them from a unique `Env`, so measure before
  choosing.

  If all this shows up in measurements, turn it off per build mode as .NET does:
  `--tailcalls+` is on in Release and off in Debug. Give the Zig target the same switch, on
  by default in the release modes, matching .NET's default as the OOM policy does.
- **Fable's compile time:** a second Perceus run, for full entries only.
- **The split of a full `$tc` into entry and body** costs a call and a return per jump when
  LLVM doesn't inline the body. Check that it does in ReleaseFast.

#### Where it does not apply

- **Zig backends other than LLVM.** `fable_rt.tail_call` falls back to an ordinary call.
  Zig's Debug default on x86_64 is the self-hosted backend, so Debug builds there have no
  guarantee.
- **wasm32**, without the `tail_call` CPU feature.
- **Calls into hand-written Zig or C**, which have no `$tc` entry.
- **`async { }` / `task { }`**: their builders compile to state machines of their own
  (`Fable2Zig.Dotnet.Async.fs`).

**Testing.** The tests run `zig run -O Debug` and `-O ReleaseSafe` without `-fllvm`
(`Fable.Build/Test/Zig.fs:32`), and Debug is the only mode with the leak check. Tests that
recurse to a depth that overflows the stack today must run with `-fllvm`. Otherwise they
would still overflow in Debug. Where `-fllvm` isn't available, they must skip the depth
check when `builtin.zig_backend != .stage2_llvm`.

---

## Order of work

Each step must pass the full test suite (including the leak check: exit code 70 in Debug)
and the 5% benchmark gate.

**Part 2, Tier 1 (needs nothing else):**

- **1. Tier 1 inside one file.** The no-escape analysis, the `callK` emission with its second
    Perceus run, explicit uses for `invokeK`, `fable_rt.Known` / `invokeK` / `callHof`.
    Measure on calls of this file's HOFs that `specializeHofs` turns down (too large, or
    reached after its two rounds).
- **2. Tier 1 for the library and other files**, through `callHof` and `$noescape` (decided at
    Zig compile time; no F# facts). Benchmark the library HOFs that qualify and have no
    template: `collect`, `takeWhile`, `reduce`, `distinctBy`, over a list of strings. Then
    decide between rewriting the wrapping library HOFs (`partition`, `sortBy`, `groupBy`,
    ...) and relaxing the rule, and retire the templates that no longer win.

**Part 1:**

- **3. Facts for `Modes` and `RetFrom` only.**
    - The facts table, the two-hop `async` and the split of `Perceus.run`.
    - Explicit uses in Perceus, read by `formatCrossCall`.
    - The two forms of borrowed results: `acrossAssumed` and its compact forms.
    - The `finally` that publishes `None`, and the sidecars with their `Version`.

    New benchmarks: a function that forwards a list to another file's function in a loop,
    and a cross-file accessor that returns a borrowed field.
- **4. The Fable.Cli hooks:** `beginBatch` for every batch, completion of never-dispatched
    files at `FSharpCompilationFinished`, and facts batches after the last
    `FableFileCompiled` (no new type check).

    Tests in watch mode:
    - edit a callee so a parameter becomes owned; check that only its direct importers
      recompile, and that no `@compileError` is hit;
    - the earlier counter-example: a batch of `{A, C}` where C imports B. Change A so that
      both A's and B's facts change, and check that C is rebuilt;
    - introduce a type error in an early file; check that nothing hangs, with and without
      `NoParallelTypeCheck`.
- **5. `Raises` and `Stores` facts**, with their compile-time assertions.
- **6. Tier 2**, after step 3.

**Part 3 (independent of Parts 1 and 2: calls into other files are decided in Zig, from
`f$chain`; Part 1's `NeedsChain` only saves emitting a second form):**

- **7. Generalize `Plug` to `nullOf`**, behind `comptime hasNull(R)` with the plain version as
    the fallback, which narrows the `RNever || plug.IsSome` restriction. Test: TRMC over a
    `Tree`-like type that raises halfway, under the leak checker, and a type containing an
    interface to check that the fallback compiles.
- **8. TRMC in fused mutual recursion**: the shared `result` / `hole`, `Plug` on the fused
    loop, and the eligibility change. Test: mutually recursive list builders, including one
    that raises halfway, under the leak checker, at a depth that overflows the stack today
    (with `-fllvm`).
- **9. `$tc` entries for functions of the file and for lambdas.**
    - The "needs a chain" fixed point, thin and full entries, a `TailCtx` per boundary,
      `tcode` (option A, defaulting to `null`), jumps for function values in tail position,
      and boundaries into unfused cycles of known functions.
    - Measure how many entries end up full, against the number of lambdas and methods.
    - New benchmark, with `-fllvm`: a CPS evaluator and a continuation-based `fold`, at a
      depth that overflows the stack today. Compare with .NET.
- **10. `$tc` across files, and the vtable and interface slots** with owned-receiver adapters.
    `f$chain` constants, boundaries into other files chosen at Zig compile time, and both
    `$tc` forms with an alias where the choice depends on another file. This doesn't need
    Part 1; with Part 1's `NeedsChain`, the F# side can emit just one form.
- **11. TRMC into unknown callees** (needs 7 and 9). Test: the `go` example above, deep, with a
    raise halfway.
- **12. The switch per build mode**, if the measurements in 9 call for it.

## Open questions

- **How much parallelism is lost.** Measure with `FABLE_ZIG_TIME` before and after step 3.
  If it is noticeable, a file could run `pc` on its functions that call no other file while
  it waits.
- **Can the library's facts be computed from source instead of sidecars?** No:
  `fable-library-zig` is compiled as a separate project. The sidecars (or a single
  `facts.json` for the package) are the interface between projects, as `.kki` files are for
  Koka.
- **Does `callK` need `noinline` control?** LLVM may refuse to inline large lambdas, which is
  fine: the call is still direct. Check that `ReleaseSmall` builds don't grow unreasonably.
- **Interfaces and object expressions** passed to a HOF (`IComparer` to `List.sortWith`)
  would benefit from the same struct-of-a-known-type idea. Out of scope here.
- **`tail_args_cap`**: 128 bytes is a guess. Measure how often real argument lists exceed it,
  against the stack each boundary costs.
