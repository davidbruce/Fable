# Fable2Zig Enhancements — Round 2

Status: proposed (follows [fable2zig-enhancements.md](fable2zig-enhancements.md) Parts 1–3).

---

## Executive Summary & Toolchain Policy

Round 1 ([fable2zig-enhancements.md](fable2zig-enhancements.md), Parts 1–3 / Steps 1–11) landed the core Koka-style Perceus reference-counting, tail-call / call-stack optimizations, and bug fixes (with Step 12 `--tailcalls` intentionally omitted after `[<NoTailCalls>]` on `Async.fs` brought all 6 baseline benchmarks inside the 5% gate).

Round 2 establishes **Zig 0.17.1 stable** as the sole supported target baseline and addresses what remains across four areas:

- **Toolchain Policy — Pin to Zig `0.17.1` Stable**: Drop Zig `0.18`-dev tracking, benchmarks, and workarounds until Zig `0.18` is officially released (at which point the target will be re-evaluated).
- **Part 0 — Cleanup, CI Gaps, Refactoring & Docs**: Close the `-fllvm` CI blind spot in `Zig.fs`, fix remaining `FABLE0114` and `FS0026` compiler warnings, split oversized compiler and runtime files (`Lower.fs` 9,357 lines, `Emit.fs` 6,767 lines, `Perceus.fs` 5,286 lines, `fable_rt.zig` 10,931 lines), clean up `Array.sortBy` / `sortByDescending`, reconcile stale docs, and carry forward deferred Round 1 open questions.
- **Part 1 — Koka-Inspired Enhancements (Perceus, Reuse & FBIP)**: Relax `cellsMatch` for cross-constructor/size-class reuse, add drop specialization and optional inter-procedural reuse tokens (`fip`/FBIP), implement in-place unique array reuse (`arrayMapInPlace` / `arrayFilterInPlace` handling the no-`capacity` layout carefully), add closure `Env` reuse (`closureReuse`), and specialize HOFs taking single-method interfaces/object expressions (e.g., `IComparer`).
- **Part 2 — Verona-Inspired Enhancements (Regions, `Iso`, `Weak` & Cowns)**: Close the `Iso.pack` interface gap via `IfaceMeta.iso_reach`, clear active `fable_sgc` cursor state (`gc.finishCheck()`) before `moveOut`, replace `adoptShared`'s process-wide weak bailout with a per-cell `weak_bit` (`1 << 30`), automate `isoSend` at concurrency boundaries, introduce deadlock-free `Cown<'T>` + `when`, and add bulk-freeable heap `Region` allocators with per-region `IResource` finalizer lists.
- **Part 3 — Nimony-Inspired Enhancements (Move-Only `IResource`, `StackArena`, `[<Lent>]` & Shared-Cycle Boundaries)**: Extend `IResource<'T>` / `ISharedResource<'T>` to generic types and classes (defining class and raising-hook rules), replace `arenaEnter`'s global `@cmpxchgStrong` with zero-overhead `uses_arena` routing + nesting + `SpillToHeap` + static escape diagnostics, add opt-in `[<Lent>]` borrow parameters, and enforce crisp `fable_sgc` shared-cycle boundaries and diagnostics.
- **Part 4 — Phased Implementation Order, Verification Gates & Open Questions**.

---

## Verified Baseline Snapshot (Zig 0.17.1)

Observed directly prior to authoring this specification:

- **CI workflow**: [`.github/workflows/build.yml`](../../../.github/workflows/build.yml#L330-L360) (`build-zig` job on `ubuntu-latest`, lines 344–349) already pins `mlugg/setup-zig@v2` to `version: 0.17.1` and runs `./build.sh test zig`.
- **Direct Zig 0.17.1 test runs**:
    - `zig test src/fable-library-zig/fable_rt.zig -lc` → `All 66 tests passed.`
    - `zig test src/fable-library-zig/fable_rt.zig` → `All 66 tests passed.`
    - `zig test -fllvm tests/Zig/TailCallTests.zig -lc` → `All 99 tests passed.`
- **Working tree scope from prior rounds**: `git diff --stat` shows `27 files changed, 10741 insertions(+), 1500 deletions(-)`, plus untracked `src/Fable.Transforms/Zig/Fable2Zig.Facts.fs` (1,020 lines), `src/Fable.Transforms/Zig/fable2zig-enhancements.md` (1,179 lines), and `scripts/`.

---

## Part 0: Cleanup, CI Gaps, Refactoring & Documentation

### 0.1 Pin Toolchain & Documentation to Zig `0.17.1` Stable

#### Current state

- CI ([`.github/workflows/build.yml`](../../../.github/workflows/build.yml#L344-L349)) already uses Zig `0.17.1`, and all unit/tail-call tests pass on `0.17.1`.
- However, [`src/benchmarks-zig/README.md`](../../../src/benchmarks-zig/README.md#L18) (line 18) and [`Zig_Roadmap.md`](../../../Zig_Roadmap.md#L530) (line 530) still reference `0.18`.

#### Proposed change

- Establish Zig `0.17.1` as the single supported compiler version in docs, benchmark scripts, and CI until `0.18` ships as a stable release.
- Update `src/benchmarks-zig/README.md:18` and `Zig_Roadmap.md:530` to remove active `0.18`-dev tracking and record the re-evaluation trigger (official Zig `0.18.0` release).

---

### 0.2 Close the `-fllvm` CI Coverage Gap in `src/Fable.Build/Test/Zig.fs`

#### Current state

- [`tests/Zig/TailCallTests.fs`](../../../tests/Zig/TailCallTests.fs#L419) gates deep tail-call stress (`200000` iterations vs `500` on the self-hosted backend) using:

  ```fsharp
  [<Fable.Core.Emit("@import(\"builtin\").zig_backend == .stage2_llvm")>]
  ```

  (`isLlvmTc`), because Zig `0.17.1`'s default self-hosted x86_64/aarch64 backend does not guarantee full `200000`-frame tail recursion while the LLVM backend (`-fllvm`) does.
- [`src/Fable.Build/Test/Zig.fs`](../../../src/Fable.Build/Test/Zig.fs#L61-L72) invokes `zig test <name>Tests.zig` (adding `-lc` only for `InteropTests.zig`) **without** `-fllvm`. Consequently, `./build.sh test zig` in CI never runs the `200000`-depth tail-call assertions in `TailCallTests.zig`.

#### Proposed change

- Update `src/Fable.Build/Test/Zig.fs` so CI runs an explicit `-fllvm` pass (at minimum `zig test -fllvm TailCallTests.zig -lc`, or a dedicated LLVM verification step for release/tailcall-sensitive suites) alongside the default backend pass.
- Verify both backends pass in CI (note: test whether `-lc` can remain conditional or uniform under `-fllvm` on macOS and `ubuntu-latest`).

---

### 0.3 Cross-Target Regression Verification (Shared Compiler Files)

#### Current state

- Prior work modified shared files outside `src/Fable.Transforms/Zig/` (part of the 27 changed files in `git diff --stat`, including shared CLI/pipeline touches).

#### Proposed change

- Before landing Round 2 work, audit `git diff` on any non-Zig files and run cross-target suites (`./build.sh test javascript`, `./build.sh test typescript`) alongside `./build.sh test zig` to guarantee zero regressions to existing Fable targets.

---

### 0.4 Compiler Warnings Cleanup

#### Current state

Two known compiler warnings remain in Zig runtime/transform sources:

1. [`src/fable-library-zig/Global.fs`](../../../src/fable-library-zig/Global.fs#L8-L9): `NoTailCallsAttribute` (lines 8–9) emits a `FABLE0114` warning during transpilation.
2. [`src/Fable.Transforms/Zig/Fable2Zig.Dotnet.Collections.fs`](../../../src/Fable.Transforms/Zig/Fable2Zig.Dotnet.Collections.fs#L135): line 135 produces a pre-existing `FS0026` pattern-match warning during F# compilation of `Fable.Transforms`.

#### Proposed change

- Inspect and resolve the `FABLE0114` warning triggered by `NoTailCallsAttribute` in `Global.fs` (e.g., adjusting attribute placement/emission so it is recognized cleanly without emitting a warning).
- Fix the `FS0026` unreachable/overlapping rule at `Fable2Zig.Dotnet.Collections.fs:135`.
- Treat zero compiler warnings in `Fable.Transforms` and `fable-library-zig` builds as a CI merge gate.

---

### 0.5 `Array.fs` Sorting & Projection Cleanup

#### Current state

- [`src/fable-library-zig/Array.fs`](../../../src/fable-library-zig/Array.fs#L267-L281): `sortBy` (line 267) and `sortByDescending` (line 277) currently delegate to `sortWith (fun a b -> ...) array` (recomputing projections on every comparison), whereas `sortInPlaceBy` sits right below `sortInPlaceWith` at line 281.

#### Proposed change

- Align `sortBy` and `sortByDescending` with `sortInPlaceBy` / single-projection-or-copy patterns as needed (checking .NET comparison stability and side-effect count expectations — `.NET`'s `Array.Sort` with projection vs F# `Array.sortBy` semantics).
- Coordinate with Part 1.5 (interface/comparer HOF specialization) so `sortBy` / `sortWith` avoid closure allocation and virtual dispatch overhead in hot loops.

---

### 0.6 Large-File Modularity & Refactoring Plan

#### Current state

Several core compiler and runtime files have grown past maintainable thresholds (observed line counts via `wc -l`):

| File | Current Lines | Pain Points |
| --- | ---: | --- |
| [`src/Fable.Transforms/Zig/Fable2Zig.Lower.fs`](Fable2Zig.Lower.fs) | 9,357 | Still holds ~940 lines of `dotnetCall` ([`Zig_Roadmap.md#L279`](../../../Zig_Roadmap.md#L279)), plus pattern matching, CEs, attributes (`StackArena`), and expression lowering |
| [`src/fable-library-zig/fable_rt.zig`](../../fable-library-zig/fable_rt.zig) | 10,931 | Mixes RC core, `cellReuse`, `adoptShared`, `Iso`/`Region`, `Arena`, `IfaceMeta`, strings/formatting, async/threading, and inline unit tests in one file |
| [`src/Fable.Transforms/Zig/Fable2Zig.Emit.fs`](Fable2Zig.Emit.fs) | 6,767 | Combines top-level decls, type emission, IR statements/expressions, tailcall/trampoline emission, and runtime call synthesis |
| [`src/Fable.Transforms/Zig/Fable2Zig.Perceus.fs`](Fable2Zig.Perceus.fs) | 5,286 | Combines ownership/borrow/alias analysis with IR rewriting (`rewriteFlat`), drop/dup insertion, reuse matching, and move-only resource checks |
| [`src/Fable.Transforms/Zig/Fable2Zig.LowerHelpers.fs`](Fable2Zig.LowerHelpers.fs) | 2,836 | Broad bag of type helpers, member resolution, naming, and IR builders |
| [`src/Fable.Transforms/Zig/Fable2Zig.Dotnet.Misc.fs`](Fable2Zig.Dotnet.Misc.fs) | 2,761 | Catch-all `.NET` BCL lowering module |

**Proposed refactoring split** (pure structural extraction, zero behavioral changes per split PR):

1. **`Fable2Zig.Lower.fs` (9,357 → <2,500 lines/file)**:
   - Migrate the remaining ~940 lines of `dotnetCall` out into dedicated `Fable2Zig.Dotnet.*.fs` modules (`Zig_Roadmap.md:279`).
   - Split into `Fable2Zig.Lower.Patterns.fs`, `Fable2Zig.Lower.Calls.fs`, `Fable2Zig.Lower.Control.fs` (CEs/async/seq/try-with), and `Fable2Zig.Lower.fs` (entry/bindings/modules).
2. **`Fable2Zig.Dotnet.Misc.fs` (2,761 lines)**:
   - Carve out focused domain files (e.g., numerics/math, reflection/diagnostics, threading/atomics, formatting).
3. **`Fable2Zig.Perceus.fs` (5,286 lines)**:
   - Separate analysis (`Fable2Zig.Perceus.Analysis.fs`: liveness, borrow inference, uniqueness, escape/lent facts) from transformation (`Fable2Zig.Perceus.Reuse.fs`: `rewriteFlat`/`cellsMatch`/`EUse`, `Fable2Zig.Perceus.fs`: RC insertion & orchestration).
4. **`Fable2Zig.Emit.fs` (6,767 lines)**:
   - Separate into `Fable2Zig.Emit.Types.fs` (structs, tagged unions, `IfaceMeta`, RTTI), `Fable2Zig.Emit.Exprs.fs`, `Fable2Zig.Emit.TailCalls.fs`, and `Fable2Zig.Emit.fs`.
5. **`fable_rt.zig` (10,931 lines)**:
   - Extract cohesive Zig modules imported cleanly by `fable_rt.zig`: `fable_iso.zig` (`Iso`/`Region`), `fable_arena.zig` (`Arena`), `fable_iface.zig` (`IfaceMeta`), and move bulk unit-test blocks into `fable_rt_tests.zig` (wired via `comptime { _ = @import("fable_rt_tests.zig"); }`) so `zig test fable_rt.zig` stays one command.

---

### 0.7 Documentation Sync & Deferred Round 1 Open Questions

- **Docs out of sync with shipped behavior**:
    - [`src/Fable.Transforms/Zig/FABLE-ZIG.md`](FABLE-ZIG.md) lines `67`, `108–110`, and `434` still contain stale `Not yet:` entries for features that shipped in earlier milestones.
    - [`Zig_Roadmap.md`](../../../Zig_Roadmap.md) needs its `[x]` ledger reconciled with landed Round 1 items and linked forward to this Round 2 specification.
- **Deferred Round 1 open questions** ([`fable2zig-enhancements.md#L1165-L1179`](fable2zig-enhancements.md#L1165-L1179)) — dispositions for Round 2:
    - **Interface / object-expression HOF specialization** (`IComparer`, etc.) → promoted to **Part 1.5**.
    - **`FABLE_ZIG_TIME` phase timing instrumentation**: decide whether to add an environment-gated pass timing dump (`Lower`, `Perceus`, `Emit`, `zig build`) for compiler-speed regression tracking.
    - **Sidecars / incremental emission**: evaluate whether `.fable.zig` or IR sidecar caching is needed to speed up multi-file debug rebuilds under Zig `0.17.1`.
    - **`ReleaseSmall` `callK` binary-size growth**: measure `.text` size delta from CPS `callK` / tail-call transformations under `-OReleaseSmall` and gate aggressive inlining/duplication if size exceeds target budget.
    - **`tail_args_cap` (`128` B)**: benchmark whether `128` bytes remains optimal under Zig `0.17.1` LLVM/self-hosted ABIs on `splay`/`deriv`/`nqueens` or needs adjustment.

---

## Part 1: Koka-Inspired Enhancements (Perceus RC, Reuse & FBIP)

Round 1 delivered intra-constructor/exact-cell Perceus reuse (`EUse`) and RC elision. Round 2 closes the remaining gaps toward Koka-level **Functional But In-Place (FBIP)** optimization.

### 1.1 Cross-Constructor & Size-Class Cell Reuse

#### Current state

- In [`src/Fable.Transforms/Zig/Zig.IR.fs`](Zig.IR.fs#L290-L298) (`cellsMatch`) and [`src/Fable.Transforms/Zig/Fable2Zig.Perceus.fs`](Fable2Zig.Perceus.fs#L1665-L1760) (`rewriteFlat`), reuse token matching is conservative: two cells typically must match tightly, missing cases where a dead cell of type/case `A` could back an allocation of type/case `B` with compatible size and alignment (e.g., transforming AST/IR discriminated union cases of different shapes, or reusing a dead `Cons` node for another 2-field heap record).
- Meanwhile, [`src/fable-library-zig/fable_rt.zig`](../../fable-library-zig/fable_rt.zig#L202-L225) (`cellReuse`) **already** validates `@sizeOf` and `@alignOf` at comptime and re-initializes the `$rc` / GC header when `hasGc(C)` holds!

#### Proposed design

1. Relax `cellsMatch` in `Zig.IR.fs` and `Perceus.fs` into a tiered matcher:
   - **Exact layout match**: identical Zig heap type (fastest path, reuses allocation unconditionally; can skip zeroing untouched constant fields if proven unnecessary).
   - **Compatible size/alignment class match**: different Zig struct/union types `OldT` and `NewT` whose static sizes and alignments satisfy `@sizeOf(NewT) == @sizeOf(OldT)` and `@alignOf(NewT) <= @alignOf(OldT)` (or same allocator size-class bucket when freed via identical allocator protocol and wrapped by `cellReuse`).
2. Emit `cellReuse(NewT, OldT, old_ptr)` whenever `OldT != NewT`, ensuring:
   - Child fields of `OldT` are dropped before `NewT` header re-init (`hasGc` metadata updated accurately so `fable_sgc` never traces stale `OldT` pointers through `NewT`'s RTTI!).
   - If `OldT` could be `inThreadArena` (`fable_rt.zig:302-386`) or stack-arena allocated (`StackArena`), guard reuse so heap-escaping allocations do not reuse a narrower-lifetime arena cell unless proven to share the same lifetime.
3. Track cross-constructor reuse hits using `Fable.Core.Zig.Counters` ([`Fable.Core.Zig.fs`](../../../src/Fable.Core/Fable.Core.Zig.fs#L1-L120)).

---

### 1.2 Drop Specialization & Optional Inter-Procedural Reuse Tokens (`fip` / FBIP)

#### Current state

- Dropping a possibly-cyclic or nested cell invokes generic drop/decrement paths; recursive transformations split across helper functions cannot pass a dead cell from caller to callee for reuse without returning to the caller.

#### Proposed design

1. **Drop specialization**:
   - Emit fast-path specialized drop helpers when Perceus knows at a drop site that a cell:
     - has zero heap-allocated children (skip child traversal completely); or
     - belongs to an acyclic type (`$cycles` = false, skip `fable_sgc` decrement hooks); or
     - is consumed in a drop-and-reuse pair (`EDrop` matched with `EUse`), avoiding unnecessary refcount writes before `cellReuse`.
2. **Inter-procedural reuse tokens (optional / attributed FBIP)**:
   - Add an internal IR concept of a **reuse token** (`?ReuseToken` or nullable typed slot `?*anyopaque` stripped at emit time if unused) that an annotated or recognized recursive constructor helper can accept.
   - Example: tree balancing / list partition helpers called on a dead node pass the dead cell directly to the helper rather than dropping and immediately reallocating.
   - Explore an opt-in `[<Fip>]` (Functional In-Place) diagnostic attribute: compiler warns or errors if an annotated function allocates fresh heap cells without matching reuse tokens along its non-base paths (giving library authors hard FBIP guarantees).

---

### 1.3 In-Place Unique Array Reuse (`arrayMapInPlace` & `arrayFilterInPlace`)

#### Current state

- [`src/fable-library-zig/fable_array.zig`](../../fable-library-zig/fable_array.zig#L44-L54) defines `Array(T)` with fields `items: []T` and `shape: ?[2]usize = null` — **there is no `capacity` field**.
- Dropping an `Array(T)` calls `allocator.free(a.items)` directly using `a.items.len`.
- Helper builders such as `ArrayBuf` and `arrayFilterFinish` (`fable_array.zig:449-505`, `616-624`) always allocate a new buffer and copy elements.

#### Proposed design

When Perceus establishes that the input array argument to `Array.map` or `Array.filter` is **uniquely owned** at its last use (`isUnique` on both the wrapper if heap-boxed and the array buffer):

1. **`arrayMapInPlace`**:
   - Enabled when `@sizeOf(T_in) == @sizeOf(T_out)` and `@alignOf(T_in) == @alignOf(T_out)` (and same element copy/drop safety; e.g., `int -> int`, `float -> float`, or pointer -> pointer where old elements are dropped before overwriting slot `i`).
   - Mutates elements in place in a single pass with zero allocation! (Careful: if an `out` element throws in `f`, elements `[0..i)` have already been transformed while `[i+1..n)` still hold `T_in` — if `f` can raise and `T_in != T_out`, fall back to non-in-place or unwind cleanly.)
2. **`arrayFilterInPlace`** — **CRITICAL ALLOCATOR SAFETY PITFALL**:
   - Because `Array(T)` in `fable_array.zig:44-54` has **no `capacity` field** and frees `a.items` via `allocator.free(a.items)`, **you MUST NOT simply overwrite `a.items = a.items[0..out_len]`**. Doing so passes `out_len` instead of the original allocated length to `allocator.free(a.items)`, triggering Zig allocator size-mismatch panics / leaks!
   - Choose explicitly between two safe representations during implementation:
     - **Option A (`allocator.resize` + fallback, keeps `Array(T)` layout unchanged)**: Compact surviving elements into `[0..out_len)` (dropping filtered-out managed elements safely), then call `if (!allocator.resize(a.items, out_len))`: copy `[0..out_len)` into a new `out_len` slice and free the full `a.items`; otherwise update `a.items = a.items[0..out_len]`. Keeps `Array(T)` header compact (zero field overhead for all arrays).
     - **Option B (add `capacity: usize` to `Array(T)`)**: Track `capacity` separately from `items.len` so `a.items = a.items[0..out_len]` never reallocates when shrinking and frees `a.items.ptr[0..a.capacity]`. Eliminates copy fallback even if `allocator.resize` returns `false`, at the cost of `+1 usize` per `Array(T)` header.

---

### 1.4 CPS & Closure `Env` Reuse (`closureReuse`)

#### Current state

- Heap closure environments (`Env`) allocated in tight `Async`, `Seq`, CPS-transformed loops, and recursive higher-order chains currently use normal alloc/drop even when an immediately-preceding continuation `Env` becomes uniquely dead right as the next step's `Env` is built.
- `cellReuse` (`fable_rt.zig:202-225`) handles standard structs/unions, while `IfaceMeta` (`fable_rt.zig:7135-7250`) wraps closures via `env_iface_meta`.

#### Proposed design

- Introduce `closureReuse` in `fable_rt.zig` and expose `Env` cell reuse candidates in `Perceus.fs`:
    - When a closure wrapper / `Env` is uniquely owned (`isUnique`), drop captured dead bindings and reuse its allocation for the successor continuation `Env` (same type or compatible size/alignment class).
    - Respect [`Perceus.fs`](Fable2Zig.Perceus.fs#L1665-L1760) `touchesMutable` guards and `env_iface_meta` vtable updates when the reused `Env` implements a different closure interface/fn signature.

---

### 1.5 Interface & Object-Expression HOF Specialization (`IComparer`, etc.)

#### Current state

- Deferred Open Question from [`fable2zig-enhancements.md`](fable2zig-enhancements.md#L1165-L1179): F# higher-order functions that take function values have specialization/inlining, whereas HOFs accepting single-method interfaces or object expressions (`{ new IComparer<'T> with member _.Compare(a, b) = ... }`, `IEqualityComparer<'T>`) still dispatch dynamically through `IfaceMeta` / fat interface pointers inside tight loops (`Array.sortWith`, `Set`/`Map` lookups, collection scans).

#### Proposed design

- Extend HOF specialization in `Lower.fs` / `FableTransforms` (or Zig-local lowering) to recognize concrete object expressions and single-method interface arguments passed to collection/sort HOFs.
- Generate monomorphized callee specializations taking the concrete environment struct (or comptime type parameter in Zig) so `.Compare` / `.Equals` / `.Invoke` devirtualizes and inlines into comparison loops, eliminating `env_iface_meta` boxing allocations as well.

---

## Part 2: Verona-Inspired Enhancements (Regions, `Iso`, `Weak`, Shared Ownership & Cowns)

Zig-Fable already has foundational Verona primitives (`Iso<'T>`, `Region`, `adoptShared`, `fable_weak.zig`, `fable_sgc.zig`). Round 2 completes region reachability across interfaces, removes global weak bailouts, automates ownership transfer, and adds `Cown<'T>` and bulk-freeable `Region` arenas.

### 2.1 Closing the `Iso.pack` Interface Gap (`IfaceMeta.iso_reach`)

#### Current state

- [`src/fable-library-zig/fable_rt.zig`](../../fable-library-zig/fable_rt.zig#L690-L860) implements `Region` graph traversal for `Iso.pack` / `isoTryPack` ([`Fable.Core.Zig.fs`](../../../src/Fable.Core/Fable.Core.Zig.fs#L1-L120)).
- At line `758`, `Region` unconditionally rejects any field or value satisfying `isIface(T)` by setting `r.ok = false`. Consequently, any object graph containing an interface field, F# object expression, or boxed function/closure cannot be packed into an `Iso<'T>`.
- Yet [`fable_rt.zig`](../../fable-library-zig/fable_rt.zig#L7135-L7250) already populates `IfaceMeta` with `{ retain, drop, share, hdr_of, as_obj, find_box }` across `empty_iface_meta`, `obj_iface_meta`, `box_iface_meta`, `env_iface_meta`, and `upcastIfaceMeta`.

#### Proposed design

1. Add an `iso_reach` (or `region_visit`) function pointer to `IfaceMeta` (`fable_rt.zig:7135-7250`).
2. Emit an `iso_reach` implementation per concrete `IfaceMeta` instance (objects, boxed values, closure `Env`s via `as_obj`/`hdr_of`; `empty_iface_meta` as a trivial no-op returning `true`).
3. Inside `Region` (`fable_rt.zig:758`), replace the blanket `if (comptime isIface(T)) { r.ok = false; ... }` rejection with delegation through `iface.meta.iso_reach(iface.ptr, r)`:
   - Traces internal fields of the concrete backing object/closure cleanly.
   - Preserves `r.ok = false` only if the concrete runtime object genuinely violates region isolation (e.g., already shared externally, holds non-isolated captured mutable state, or references a weaker arena/weak cell).
   - Ensure `upcastIfaceMeta` preserves the underlying `iso_reach` pointer.

---

### 2.2 Clear Active `fable_sgc` Check State Before `moveOut` (`gc.finishCheck()`)

#### Current state

- [`src/fable-library-zig/fable_sgc.zig`](../../fable-library-zig/fable_sgc.zig#L738-L778): `canMove` (lines 738–744) rejects moving an object (`moveOut`, lines 759–764; `moveIn`, lines 767–778) whenever `r.dead || gc.check == r`.
- If the incremental structure-count cycle collector currently holds root `r` as its active `gc.check` cursor, `Iso.pack` / `Region` isolation fails non-deterministically depending on prior allocation history rather than true reachability!

#### Proposed design

- Add `gc.finishCheck()` in `fable_sgc.zig` to advance/complete (or cleanly release) an in-progress `gc.check` cycle inspection step before `canMove` / `moveOut` checks `gc.check == r`.
- Invoke `gc.finishCheck()` automatically inside `Region.moveOut` / `Iso.pack` when `gc.check != null`, keeping invariant rules `(A)`/`(B)`/`(C)` (`fable_sgc.zig:1-90`) intact while making `Iso.pack` deterministic.

---

### 2.3 Per-Cell `weak_bit` (`1 << 30`) Eliminating `adoptShared`'s Global Bailout

#### Current state

- [`src/fable-library-zig/fable_rt.zig`](../../fable-library-zig/fable_rt.zig#L317-L320): `adoptShared` checks `weak_refs.shared_count.load(.acquire) != 0` ([`fable_weak.zig`](../../fable-library-zig/fable_weak.zig#L55)) and **bails out process-wide** if *any* shared weak reference exists anywhere in the process.
- This creates a cliff: creating one long-lived `WeakReference` to an unrelated object disables `adoptShared` across all threads for the lifetime of that weak reference.

#### Proposed design

- Reserve `weak_bit = 1 << 30` alongside `shared_bit = 1 << 31` in each managed object's `$rc` word (`fable_weak.zig:30-81`).
- Set `weak_bit` on the target cell inside `shareWeakHandle` (and when creating a weak handle on a local cell before sharing).
- Update `adoptShared` (`fable_rt.zig:302-386`) and `Region` to remove the global `weak_refs.shared_count != 0` check and instead inspect only whether **this cell** (or a cell in the packed region) has `weak_bit` set (using a per-cell slow path or rejecting/upgrading only weak-targeted cells).
- **CRITICAL `$rc` BIT-MASKING & REFCOUNT OVERFLOW PITFALL**:
    - Reserving `weak_bit = 1 << 30` leaves **30 bits** for the reference count (`max_rc = (1 << 30) - 1`, ~1.07 billion) alongside the two flag bits (`shared_bit | weak_bit = 0xC000_0000`).
    - Every single helper inspecting or modifying `$rc` across `fable_rt.zig` and `fable_sgc.zig` — including `isUnique`, `countedOnce`, `releaseIsLast`, `decs`, atomic CAS loops, and `rc` extractors — **must** mask out `flag_mask = shared_bit | weak_bit` (`rc & ~flag_mask`) and preserve both flag bits when incrementing/decrementing counts!
    - Guard against 30-bit refcount saturation cleanly (saturate or trap in debug/checked mode rather than rolling into `weak_bit`!).
    - **Bonus optimization**: In `free` / `drop`, skip calling `sharedWeakGone` (`fable_weak.zig:63-70`) unless `(rc & weak_bit) != 0` — making weak-ref cleanup zero-cost for the 99.9% of cells never targeted by a `WeakReference`.

---

### 2.4 Automatic `isoSend` at Concurrency Boundaries

#### Current state

- [`fable_rt.zig`](../../fable-library-zig/fable_rt.zig#L576-L625) implements `isoSend` / `transferOrShare`, and `Fable.Core.Zig.fs:1-120` exposes manual `Iso<'T>`, `Iso.pack`, `Iso.unpack`, and `Iso.tryPack`.
- However, normal thread/task spawns (`System.Threading.Thread`, `Task.Run`, `Async.Parallel`) share captured environment values through `adoptShared`, incurring atomic refcount conversion (`shared_bit`) even when a captured object/subgraph is uniquely owned at the spawn site.

#### Proposed design

- Analyze captured bindings at `Thread` / `Task.Run` / `Async.Parallel` spawn points in `Lower.fs` / `Perceus.fs`:
    - If a captured value has static type `Iso<'T>`, move it directly across the spawn boundary via `isoSend` without converting to atomic refcounting.
    - If a captured value is non-`Iso` but statically proven **uniquely owned** (`isUnique`, no surviving local alias after spawn) and safe under `Region` rules (e.g., acyclic or isolated via `moveOut`), emit a zero-overhead `moveOut`/`transferOrShare` (or fast-path `isoTryPack` -> `isoSend` falling back to `adoptShared` only if dynamic sharing prevents isolation).

---

### 2.5 Behavior-Oriented Concurrency: `Cown<'T>` & Deadlock-Free `when`

#### Current state

- Concurrent state sharing currently relies on locks/mutexes + atomic shared RC (`adoptShared`), exposing user code to lock-order deadlocks and manual lock management.

#### Proposed design (Verona `cown<T>` + `when` model)

1. **Type & API**:
   - Introduce `Cown<'T>` encapsulating a thread-safe MPSC queue (intrusive / lock-free or compact mutex-guarded FIFO depending on contention benchmarks) plus exclusive ownership of an `Iso<'T>` (or region-isolated value).
   - Provide `Cown.create (iso: Iso<'T>) : Cown<'T>` and `Cown.when1` / `when2` / `when3` / `whenN` scheduling a behavior closure once all requested cowns become exclusively available.
2. **Deadlock freedom**:
   - Multi-cown `when (c1, c2, ...) (fun (v1, v2, ...) -> ...)` sorts cown pointers by **canonical memory address** before chaining/acquiring permits, guaranteeing global cycle-free acquisition across arbitrary sets of cowns.
   - Each cown runs at most one behavior at a time; intra-cown mutations require zero locks because the cown holds exclusive temporary access (`Region` / thread-local RC inside the behavior, re-isolating on behavior completion before handing off to the next queued behavior).
3. **NuGet Semver Placement (`AGENTS.md` constraint)**:
   - Because `src/Fable.Core/` ships on NuGet and forbids breaking changes within a major version, keep any additions to [`Fable.Core.Zig.fs`](../../../src/Fable.Core/Fable.Core.Zig.fs#L1-L120) strictly additive (`[<Experimental>]` / new module), or place higher-level `Cown` / `Region` F# wrappers in an optional companion library package under `src/` linked by Zig projects.

---

### 2.6 Bulk-Freeable Heap `Region` Allocators

#### Current state

- `Region` in [`fable_rt.zig`](../../fable-library-zig/fable_rt.zig#L690-L860) currently checks graph isolation and moves pointers into/out of `Iso<'T>`, while every object inside still lives on the general allocator with per-object frees.

#### Proposed design

- Add an optional **bulk-freeable heap Region** (bump-slab allocator + explicit disposal) for short-lived, possibly cyclic object graphs whose members never escape the region:
    - Tag cells allocated inside a bulk region with a dedicated header marker (`region_bit`, or thread/region allocator pointer in allocator router / `canMove` check).
    - Retaining or dropping a `region_bit` cell intra-region becomes a **no-op** (eliminating both `$rc` updates and `fable_sgc` work for region-local cycles).
    - Track any `IResource<'T>` values allocated or moved into the region on a per-region intrusive/chunked **finalizer list**; `Region.dispose()` invokes every registered `IResource` destructor deterministically in LIFO order before freeing all region slabs in **O(slabs)** time.
    - Strictly forbid escaping pointers from a bulk `Region` (`[<Lent>]` or static escape check, and runtime trap in debug if a `region_bit` pointer crosses out without cloning/moving via an approved boundary).
    - Coordinate with `inThreadArena` (`fable_rt.zig:302-386`) and `StackArena` (Part 3.2) so allocator routing shares one clean abstraction.

---

## Part 3: Nimony-Inspired Enhancements (`IResource`, `StackArena`, `[<Lent>]`, Diagnostics)

Round 1 introduced `IResource<'T>`, `ISharedResource<'T>`, and `[<StackArena(bytes)>]`. Round 2 generalizes resource ownership to generics and classes, eliminates global `Arena` overhead/hazards, adds `[<Lent>]` borrows, and formalizes shared-cycle diagnostics.

### 3.1 `IResource<'T>` & `ISharedResource<'T>` on Generic Types and Classes

#### Current state

- [`src/Fable.Transforms/Zig/Fable2Zig.LowerTypes.fs`](Fable2Zig.LowerTypes.fs#L470-L530) currently:
    - Rejects **generic** `IResource` / `ISharedResource` definitions at line `500`;
    - Rejects `KHeapUnion` and `KRefRecord` types implementing resources at line `494`;
    - Populates `e.Hooks` and `e.Copyable` (`lines 516–525`) while [`Fable2Zig.Perceus.fs`](Fable2Zig.Perceus.fs#L1465-L1473) enforces move-only errors on `IResource`.

#### Proposed design

1. **Generic `IResource<'T>` / `ISharedResource<'T>`**:
   - Allow generic structs and records (e.g., `type OwnedBuffer<'T> = ... interface IResource<...>`) by resolving `e.Hooks` (`close`/`drop` specialized per monomorphized instantiation `T`) and propagating `e.Copyable = false` through generic substitution in `LowerTypes.fs` and `Perceus.fs`.
   - Ensure containers (options, tuples, records, unions) containing a non-copyable generic `IResource` inherit move-only / deterministic-drop semantics automatically!
2. **Class types (`KRef` / heap-allocated classes)**:
   - Decide and enforce clean semantics for heap classes (`KRefRecord` / F# `type Foo(...) = ...`):
     - **`ISharedResource<'T>` on classes**: Permitted! Because classes are shared-reference types (not affine linear values), copying/sharing a class handle increments `$rc` and executes the `ISharedResource` destructor deterministically when the final reference drops (including via `IfaceMeta` if cast to an interface!).
     - **`IResource<'T>` (move-only) on classes**: Either emit a clear compile-time error directing authors to `ISharedResource<'T>` or F# `struct` (since heap classes naturally alias), **or** support move-only unique classes only when explicitly affine. Recommended: permit `ISharedResource<'T>` on heap classes and require value `struct` / unique records for move-only `IResource<'T>`.
3. **Raising cleanup-hook policy**:
   - Specify how F# `Dispose()` / `IResource` close hooks that might throw exceptions lower to Zig `drop`/`defer`: Perceus destructors cannot propagate exceptions cleanly out of arbitrary scope exits. Either diagnose non-`nothrow` / throwing cleanup implementations at compile time, or wrap cleanup calls in an explicit catch/log/abort policy (documented consistently with `.NET` `IDisposable` destructors in finalizers).

---

### 3.2 Zero-Overhead `[<StackArena>]` Routing, Nesting, `SpillToHeap` & Escape Checks

#### Current state

- [`src/fable-library-zig/fable_rt.zig`](../../fable-library-zig/fable_rt.zig#L3585-L3660): `Arena` (`3588–3592`) uses `arena_router` (`3600–3605`), `arenaOwning` (`3608–3612`), and **`arenaEnter` (`3645–3653`), which executes a `@cmpxchgStrong` overwriting the global `allocator`**; `arenaLeave` (`3657–3660`) **panics if `frame.live != 0`**.
- Overwriting the global `allocator` creates severe thread-safety races (two threads entering arenas corrupt each other's `allocator`!) and prevents zero-cost nesting.
- [`src/Fable.Transforms/Zig/Fable2Zig.Lower.fs`](Fable2Zig.Lower.fs#L9239-L9258) parses `[<StackArena(bytes)>]` and only checks managed parameter/return types — leaving closures, mutable refs, globals, and raised exceptions unchecked until `arenaLeave` panics at runtime.

#### Proposed design

1. **Thread-local stack of active arenas + zero global `@cmpxchgStrong`**:
   - Replace the global `allocator` `@cmpxchgStrong` swap in `arenaEnter` with a `threadlocal` pointer/stack (`active_arena: ?*Arena = null`, with `prev` pointer in `Arena` enabling arbitrary nesting!).
   - Eliminate all atomic CAS overhead at `arenaEnter`/`arenaLeave`.
2. **Zero-overhead `uses_arena` routing (mirroring `$cycles`)**:
   - Just as Perceus tracks `$cycles` statically to omit cycle-collector calls on acyclic code, compute a `uses_arena` static/call-graph fact (or compile-time flag on non-arena modules/functions):
     - Functions/paths proven not to execute inside `[<StackArena>]` allocate/free directly through the fast base allocator without querying `active_arena`!
     - Functions reachable from a `[<StackArena>]` frame check an inline thread-local `if (active_arena != null)` fast path (or receive an implicit arena context parameter in optimized internal calls).
3. **`SpillToHeap` overflow mode**:
   - Extend `[<StackArena(bytes)>]` with an optional mode `[<StackArena(bytes, SpillToHeap = true)>]` (or enum policy `Overflow = ArenaOverflow.Panic | ArenaOverflow.SpillToHeap`): when stack bytes saturate, spill excess allocations to a linked heap slab buffer tracked on the `Arena` frame and bulk-freed at `arenaLeave`, preventing unexpected OOM aborts on occasional large inputs.
4. **Static escape diagnostics in `Lower.fs` / `Perceus.fs`**:
   - Extend the checks around `Lower.fs:9239-9258` so escaping an arena allocation via:
     - captured closure `Env` escaping the `[<StackArena>]` scope,
     - writes into external `ref` / mutable fields / arrays / globals, or
     - managed exception payloads thrown out of the `[<StackArena>]` body
     fails cleanly at compile time (or emits a targeted error) instead of deferring to `arenaLeave`'s `if (frame.live != 0) @panic(...)`.

---

### 3.3 Opt-In `[<Lent>]` Verified Borrow Parameters

#### Current state

- Perceus already performs internal borrow inference for generated calls, allowing callers to skip retain/drop pairs when arguments are only read. However, F# authors cannot express or enforce borrow contracts on public/helper signatures — especially important for `[<StackArena>]`-backed data and move-only `IResource<'T>` handles where passing ownership would either fail `StackArena` escape checks or consume the resource!

#### Proposed design

- Add an opt-in `[<Lent>]` parameter attribute (additive in `Fable.Core.Zig.fs`):

  ```fsharp
  let sumFields ([<Lent>] node: Node) : int = ...
  ```

- Compiler enforcement in `Perceus.fs` / `Lower.fs`:
  1. A `[<Lent>]` parameter is strictly read-only wrt ownership: it **cannot** be returned, stored in a mutable/escaping cell, captured into an escaping closure, moved (`IResource`), or passed to a non-`[<Lent>]` parameter that retains ownership.
  2. Callers incur **zero** `EDup`/`EDrop` RC traffic around `[<Lent>]` arguments, and move-only `IResource<'T>` or `[<StackArena>]` / bulk-`Region` values may be passed freely into `[<Lent>]` helpers.

---

### 3.4 Explicit `fable_sgc` Shared-Cycle Boundary & Diagnostics

#### Current state

- As documented in [`Zig_Roadmap.md`](../../../Zig_Roadmap.md#L196-L208), `fable_sgc` (`fable_sgc.zig`) is deliberately **thread-local**: cross-thread cycles on atomic `$rc` (`shared_bit` cells) are not collected automatically by `fable_sgc` (consistent with Verona's principle that shared mutable graphs should be structured via `Iso`/`Cown` or broken manually with `Weak`).
- Today, hitting cyclic or non-isolatable boundaries can fail silently via `adoptShared` slow paths or raise opaque runtime exceptions without actionable remediation hints.

#### Proposed design

1. **Explicit boundary diagnostics**:
   - Emit crisp, actionable `NotSupportedException` / compile-time diagnostics when unsupported patterns cross shared-cycle boundaries (e.g., mutable cyclic F# records/objects marked/used across threads without `Weak` / `Iso` / `Cown`).
   - Print explicit guidance naming `WeakReference`, `Iso.pack`, or `Cown` as the idiomatic resolution.
2. **Singleton-drain & thread-exit leak telemetry**:
   - Under `Fable.Core.Zig.Counters` and Debug builds, report thread-exit `fable_sgc` drain statistics (singleton root sweeps, orphaned cycle counts) cleanly so leaks from uncollected cross-thread cycles are immediately diagnosable during testing rather than silent in production.

---

## Part 4: Phased Implementation Order, Verification Gates & Open Questions

### 4.1 Phased Implementation Order (Steps 1–12)

1. **Step 1 — Toolchain, CI & Warning Baseline (Part 0.1–0.4)**:
   - Align `src/benchmarks-zig/README.md:18` and `Zig_Roadmap.md:530` to Zig `0.17.1`; audit non-Zig diffs and verify JS/TS regression tests; wire `-fllvm` (`TailCallTests.zig -lc`) into `src/Fable.Build/Test/Zig.fs`; fix `FABLE0114` (`Global.fs:8-9`) and `FS0026` (`Fable2Zig.Dotnet.Collections.fs:135`).
2. **Step 2 — Large-File Splitting & Docs Sync (Part 0.5–0.7)**:
   - Split `Fable2Zig.Lower.fs`, `Fable2Zig.Dotnet.Misc.fs`, `Fable2Zig.Perceus.fs`, `Fable2Zig.Emit.fs`, and `fable_rt.zig` (pure refactors tested step-by-step against full Zig test suite); align `FABLE-ZIG.md` and `Zig_Roadmap.md`; decide Round 1 open questions (`FABLE_ZIG_TIME`, `ReleaseSmall` `callK`, `tail_args_cap`).
3. **Step 3 — Koka Cell & Closure Reuse (Part 1.1, 1.2, 1.4)**:
   - Relax `cellsMatch` in `Zig.IR.fs` / `Perceus.fs` with `cellReuse` layout/GC-header verification; add drop specialization and `closureReuse` for CPS/`Env` loops.
4. **Step 4 — In-Place Unique Array Reuse & HOF Interface Specialization (Part 1.3, 1.5, 0.5)**:
   - Implement `arrayMapInPlace` and `arrayFilterInPlace` (`allocator.resize` vs `capacity` — see Open Questions); add `IComparer`/interface HOF specialization and align `Array.sortBy` / `sortByDescending`.
5. **Step 5 — Verona `Iso` Interfaces & `fable_sgc` Cursor Fix (Part 2.1, 2.2)**:
   - Add `IfaceMeta.iso_reach` (closing `fable_rt.zig:758`) and `gc.finishCheck()` in `fable_sgc.zig` before `moveOut`.
6. **Step 6 — Per-Cell `weak_bit` & Weak Optimization (Part 2.3)**:
   - Reserve `weak_bit = 1 << 30` in `$rc`, update all RC helpers to mask `shared_bit | weak_bit`, remove `adoptShared`'s process-wide bailout (`fable_rt.zig:317-320`), and gate `sharedWeakGone` on `weak_bit`.
7. **Step 7 — Automatic `isoSend` & Shared-Cycle Diagnostics (Part 2.4, 3.4)**:
   - Emit zero-copy `isoSend`/`moveOut` at `Thread`/`Task.Run`/`Async.Parallel` spawn points for `Iso<'T>` and unique linear captures; enforce clear `fable_sgc` shared-cycle diagnostics and thread-exit telemetry.
8. **Step 8 — Opt-In `[<Lent>]` Borrow Parameters (Part 3.3)**:
   - Add `[<Lent>]` attribute checks in `Perceus.fs`/`Lower.fs` and integrate with existing borrow inference.
9. **Step 9 — Zero-Overhead `[<StackArena>]` Routing, Nesting & Static Escape Checks (Part 3.2)**:
   - Replace `arenaEnter` global `@cmpxchgStrong` (`fable_rt.zig:3645-3653`) with thread-local stack + `uses_arena` routing, add `SpillToHeap`, and add static closure/ref/exception escape diagnostics (`Lower.fs:9239-9258`).
10. **Step 10 — Generic & Class `IResource` / `ISharedResource` (Part 3.1)**:
    - Lift generic (`LowerTypes.fs:500`) and class restrictions appropriately, preserve move-only checks across generic containers, and document raising-hook behavior.
11. **Step 11 — Bulk-Freeable Heap `Region` Allocators (Part 2.6)**:
    - Implement `region_bit` slab regions with per-region `IResource` finalizer lists and O(slabs) disposal.
12. **Step 12 — Behavior-Oriented `Cown<'T>` & `when` + Optional `[<Fip>]` (Part 2.5, 1.2)**:
    - Implement canonical-order multi-cown `when` scheduler + package placement, plus optional `[<Fip>]` verification mode once intra/inter-procedural reuse lands.

---

### 4.2 Verification Gates (Zig `0.17.1` + `.NET 10`)

Every step must clear the applicable gates before proceeding:

- **Zero-warning compiler & runtime build**: `dotnet build` (`Fable.Transforms` / `Fable.Cli`) and Zig transpilation produce zero `FS0026`, `FABLE0114`, or Zig warnings.
- **Full Zig suite on default backend & LLVM backend**:
    - `./build.sh test zig` (and `.NET` parity comparison against every test project);
    - `zig test -fllvm tests/Zig/TailCallTests.zig -lc` (verifying `200000`-depth LLVM tail calls);
    - `zig test src/fable-library-zig/fable_rt.zig -lc` and `zig test src/fable-library-zig/fable_rt.zig`.
- **Cross-target hygiene**: `./build.sh test javascript` and `./build.sh test typescript` green whenever shared non-Zig files are modified.
- **Concurrency & sanitizer checks**: Zig Debug allocator leak assertions + ThreadSanitizer (`-fsanitize=thread` on Linux/macOS where supported) exercising `weak_bit`, `adoptShared`, nested `StackArena` across concurrent threads, bulk `Region` + `IResource` finalization, and multi-cown `when` stress tests.
- **Paired ReleaseFast benchmarks**: Compare alloc counts (`Fable.Core.Zig.Counters`), binary size (`-OReleaseSmall` vs `-OReleaseFast`), and wall time before/after Parts 1–3 on tree/AST transforms, `Array.map`/`filter`/`sortBy`, `Iso.pack` with closures/interfaces, `StackArena`, and `Cown` workloads.

---

### 4.3 Open Questions (Design Decisions Needed Before Coding)

1. **`Array` shrink representation (`arrayFilterInPlace`)**: Should `Array(T)` keep its 2-field header (`items` + `shape`) and use `allocator.resize(a.items, out_len)` with a copy fallback (Option A), or add a `capacity: usize` field to guarantee zero-realloc shrinking everywhere at `+1 usize` per array (Option B)?
2. **Moving `Fable.Core.Zig` APIs (`Cown<'T>`, `[<Lent>]`, `Region`)**: Because `src/Fable.Core/` forbids breaking changes within a major NuGet version (`AGENTS.md`), are strictly additive types/attributes in `Fable.Core.Zig.fs` preferred, or should experimental Verona/Nimony APIs live in a separate Zig-specific helper package/module until stabilized?
3. **Class `IResource<'T>` semantics**: For heap-allocated F# classes (`KRefRecord`), should move-only `IResource<'T>` be rejected at compile time (guiding authors to `ISharedResource<'T>` or F# `struct`), or permitted via affine unique-class tracking?
4. **Raising destructors on `IResource` / `ISharedResource`**: If an F# cleanup method can throw, should Fable2Zig reject it with a compile-time diagnostic (requiring explicit exception handling inside `Dispose`/`Close`), or emit a catch-and-panic / configurable error hook?
5. **Global `-fllvm` CI matrix vs targeted `TailCallTests.zig`**: Should `src/Fable.Build/Test/Zig.fs` run `-fllvm` only on `TailCallTests.zig` (fast CI), or run the full Zig test suite twice (self-hosted + `-fllvm`) on CI?
6. **Optional `[<Fip>]` attribute & `FABLE_ZIG_TIME` priority**: Should `[<Fip>]` compile-time allocation audits and `FABLE_ZIG_TIME` compiler telemetry land in Round 2 Step 2 / Step 12, or remain deferred to a dedicated tooling pass?
