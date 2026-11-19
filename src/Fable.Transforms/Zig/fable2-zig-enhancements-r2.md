# Fable2Zig Enhancements — Round 2

Status: proposed (follows [fable2zig-enhancements.md](fable2zig-enhancements.md) Parts 1–3).

---

## Executive Summary & Design Principle

Round 1 ([fable2zig-enhancements.md](fable2zig-enhancements.md), Parts 1–3 / Steps 1–11) landed in commit `ef5ad8669` with cross-file facts (`.facts.json`), HOF specialization (`callK`/`EKnown`), Koka-style Perceus reference-counting and reuse, and `$tc` tail calls (with Step 12 `--tailcalls` intentionally omitted after `[<NoTailCalls>]` on `Async.fs` brought all 6 baseline benchmarks inside the 5% gate).

**Core Round 2 Principle — Make Idiomatic Standard F# Faster and Safer (Avoid Zig-Only Dialect Bloat):**
Prioritize automatic compiler/runtime optimizations and real bug fixes that transparently improve ordinary F# code running identically on `.NET` and Zig. Do **not** add custom Zig-only F# language annotations or overlapping region systems when Perceus inference, standard F# (`inref<'T>`, `byref<'T>`, `Span<'T>`, `NativePtr.stackalloc`, `IDisposable`), and existing `Iso<'T>` / `fable_sgc` already cover the need (see [Part 3: Non-Goals & Deferred Ideas](#part-3-explicit-non-goals--deferred-ideas)).

Round 2 establishes **Zig 0.17.1 stable** as the sole supported target baseline and focuses on three concrete areas:

- **Toolchain Policy — Pin to Zig `0.17.1` Stable**: Drop Zig `0.18`-dev tracking, benchmarks, and workarounds until Zig `0.18` is officially released (at which point the target will be re-evaluated).
- **Part 0 — Cleanup, CI Gaps, Refactoring & Docs**: Close the `-fllvm` CI blind spot in `Zig.fs`, fix the `FS0026` unreachable-pattern bug in `Seq.cast` (`Fable2Zig.Dotnet.Collections.fs:135`), resolve `FABLE0114` in `Global.fs`, gate ungated TLS counter writes, split oversized compiler/runtime files (`Lower.fs` 9,355, `Emit.fs` 7,233, `Perceus.fs` 5,330, `fable_rt.zig` 10,931 lines), switch `Array.sortBy` / `sortByDescending` / `sortInPlaceBy` to .NET-matching O(N) key precomputation, reconcile stale docs, audit shared non-Zig edits (`Fable.Cli`, `Fable.AST`), and run deferred Round 1 measurements.
- **Part 1 — Automatic Perceus Reuse & HOF Optimizations (Koka-Inspired)**: Relax `cellsMatch` for cross-constructor exact-layout reuse (fixing latent `cellReuse` `collector_ready` and `weakGone` hazards), add zero-live-field known-case `EUnpack` drop specialization in `settle`, implement in-place unique array reuse (`arrayMapInPlace` / `arrayFilterInPlace` with `MOwned` input, `fable_sgc` safety, and `capacity: usize`), add `$tc` owned-`Env` `closureReuse`, and specialize HOFs taking `IComparer`/`IEqualityComparer`/object expressions.
- **Part 2 — Isolation, Weak Refs, Concurrency & Existing-Primitive Hardening**: Adopt a clean 3-flag `$rc` bit layout (`shared_bit`, `immortal_bit`, `weak_bit`, relocating existing `null_count = 1 << 30`) eliminating `adoptShared`'s process-wide weak bailout and `fable_sgc` masking hazards; close the `Iso.pack` interface gap (`IfaceMeta.iso_reach` + `Region.closed()` partial-mutation fix); invoke `gc.finishCheck()` *before* `region.visit(x)`; automate `isoSend` / `adoptShared` on direct spawn lambdas + `threadStart` move + `Task.Run`/`Async.Parallel` return paths; introduce a persistent worker thread pool powering `Task.Run`/`Async.Parallel`/`Parallel.For`; and land targeted safety fixes for already-shipped `IResource` (`retainAll` `@compileError`, optional generic `IResource<'T>`), `[<StackArena>]` (fix global install race via whole-program `uses_arena`), and `fable_sgc` shared-cycle diagnostics.
- **Part 3 — Explicit Non-Goals & Deferred Ideas** (`[<Lent>]`, `StackArena` `SpillToHeap`/escape analyzer, `IResource` on classes, bulk-freeable `Region` allocators, `Cown<'T>`/`when`, `[<Fip>]`).
- **Part 4 — Focused 7-Step Implementation Order, Verification Gates & Open Questions**.

---

## Verified Baseline Snapshot (Zig 0.17.1)

Observed directly on the `zig` branch (head after `ef5ad8669`):

- **CI workflow**: [`.github/workflows/build.yml`](../../../.github/workflows/build.yml#L330-L360) (`build-zig` job on `ubuntu-latest`, lines 344–349) already pins `mlugg/setup-zig@v2` to `version: 0.17.1` and runs `./build.sh test zig`.
- **Direct Zig 0.17.1 test runs**:
    - `zig test src/fable-library-zig/fable_rt.zig -lc` → `All 66 tests passed.`
    - `zig test src/fable-library-zig/fable_rt.zig` → `All 66 tests passed.`
    - `zig test -fllvm tests/Zig/TailCallTests.zig -lc` → `All 99 tests passed.`
- **Round 1 landed baseline**: Commit `ef5ad8669` (`29 files changed, 14308 insertions(+), 1604 deletions(-)`, including `Fable2Zig.Facts.fs` 1,072 lines and `fable2zig-enhancements.md` 1,184 lines); branch-wide diff against `main` touches 28 shared/non-Zig files (including `src/Fable.Cli/Pipeline.fs` +199, `src/Fable.Cli/Main.fs` +79, `src/Fable.Transforms/FSharp2Fable.fs`, `FableTransforms.fs`, and `Fable.AST/Plugins.fs`).

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
- Verify both backends pass in CI (test whether `-lc` can remain conditional or uniform under `-fllvm` on macOS and `ubuntu-latest`).

---

### 0.3 Cross-Target Regression Verification & Upstreaming Audit

#### Current state

- The `zig` branch modifies 28 shared/non-Zig files (including [`src/Fable.Cli/Pipeline.fs`](../../Fable.Cli/Pipeline.fs) +199 lines, [`src/Fable.Cli/Main.fs`](../../Fable.Cli/Main.fs) +79 lines, [`src/Fable.Transforms/FSharp2Fable.fs`](../FSharp2Fable.fs), [`src/Fable.Transforms/FableTransforms.fs`](../FableTransforms.fs), and `Fable.AST`'s `Language` union).
- As noted in [`Zig_Roadmap.md`](../../../Zig_Roadmap.md#L333-L334) and `AGENTS.md`, adding `| Zig` to `Fable.AST.Language` is a breaking change to `Fable.AST` requiring maintainer sign-off before upstreaming.

#### Proposed change

- Audit `git diff main...HEAD` on all non-Zig files before landing Round 2 changes, ensuring every Zig-specific branch in shared compiler/CLI code is tightly guarded by `Language = Zig`.
- Run cross-target verification (`./build.sh test javascript`, `./build.sh test typescript`, plus quicktest/smoke checks on other targets affected by `Fable.Cli` / `FableTransforms` edits) alongside `./build.sh test zig`.
- Track the `Fable.AST` upstreaming decision separately from Round 2 work.

---

### 0.4 Compiler Warnings, `Seq.cast` Bug & Runtime Counter Hygiene

#### Current state

1. **Active semantic bug (`FS0026`) in [`src/Fable.Transforms/Zig/Fable2Zig.Dotnet.Collections.fs`](Fable2Zig.Dotnet.Collections.fs#L126-L138)**:
   - Line 128 (`| Fable.DeclaredType(_, [ item ]), Fable.DeclaredType(a, []) -> a.FullName = "System.Array" && item <> Fable.Any`) matches *every* non-generic `DeclaredType` without a `when` guard, making line 135 (`System.Collections.IEnumerable`) **unreachable**. Consequently, `Seq.cast<'T>` over a non-generic `System.Collections.IEnumerable` never enters that branch.
2. **`FABLE0114` warning in [`src/fable-library-zig/Global.fs`](../../fable-library-zig/Global.fs#L7-L9)**:
   - `type NoTailCallsAttribute() = inherit System.Attribute()` triggers `WarningCodes.nonPrimaryBaseConstructor` at [`FSharp2Fable.fs:45-46`](../FSharp2Fable.fs#L45-L46) (`not baseCons.IsImplicitConstructor`) because `Global.fs` is compiled as part of `fable-library-zig` (unlike `StackArenaAttribute` in excluded `Fable.Core`).
3. **Ungated counter writes in [`fable_rt.zig`](../../fable-library-zig/fable_rt.zig#L1491-L1532)**:
   - `thread.stats.copies += 1` (line 1493) and `thread.stats.destroys += 1` (line 1531) are not guarded by `if (track)`, mutating TLS counters even in `ReleaseFast`/`ReleaseSmall`.

#### Proposed change

- Fix `Fable2Zig.Dotnet.Collections.fs:128-136` using `when` guards (or combining `a.FullName = "System.Array" || a.FullName = "System.Collections.IEnumerable"`) and add a unit test covering `Seq.cast<'T>` over non-generic `IEnumerable`.
- Resolve `FABLE0114` on `NoTailCallsAttribute` cleanly (e.g., skipping the warning for `[<Erase>]` attribute types inheriting `System.Attribute` or relocating the attribute cleanly).
- Gate `thread.stats.copies += 1` and `thread.stats.destroys += 1` on `if (track)`.
- Treat zero compiler warnings in `Fable.Transforms` and `fable-library-zig` builds as a CI merge gate.

---

### 0.5 `Array.fs` Sorting & Projection Cleanup

#### Current state

- [`src/fable-library-zig/Array.fs`](../../fable-library-zig/Array.fs#L267-L299): `sortBy` (line 267), `sortByDescending` (line 277), and `sortInPlaceBy` (line 298) currently delegate to `sortWith` / `sortInPlaceWith` with `(fun a b -> compare (projection a) (projection b))`.
- This recomputes `projection` **O(N log N)** times (capturing `projection` in an extra closure), whereas .NET's `FSharp.Core` `Array.sortBy` / `sortInPlaceBy` precomputes keys into a `keys[]` array in **O(N)** projections and sorts by key. (By contrast, [`List.fs`](../../fable-library-zig/List.fs#L408-L452) already split out `mergeSortByKey` in Round 1 to avoid capturing `projection` in a wrapper closure.)

#### Proposed change

- Implement O(N) key-projection sorting for `Array.sortBy`, `Array.sortByDescending`, and `Array.sortInPlaceBy` (preserving merge-sort stability for equal keys and matching .NET's projection side-effect count).
- Coordinate with Part 1.3 (unique array reuse) and `callK` specialization so hot array sorts avoid unnecessary closure allocations.

---

### 0.6 Large-File Modularity & Refactoring Plan

#### Current state

Several core compiler and runtime files have grown past maintainable thresholds (verified line counts via `wc -l`):

| File | Current Lines | Pain Points |
| --- | ---: | --- |
| [`src/Fable.Transforms/Zig/Fable2Zig.Lower.fs`](Fable2Zig.Lower.fs) | 9,355 | Still holds ~940 lines of `dotnetCall` ([`Zig_Roadmap.md#L279`](../../../Zig_Roadmap.md#L279)), plus pattern matching, CEs, attributes (`StackArena`), and expression lowering |
| [`src/fable-library-zig/fable_rt.zig`](../../fable-library-zig/fable_rt.zig) | 10,931 | Mixes RC core, `cellReuse`, `adoptShared`, `Iso`/`Region`, `Arena`, `IfaceMeta`, strings/formatting, async/threading, and inline unit tests in one file |
| [`src/Fable.Transforms/Zig/Fable2Zig.Emit.fs`](Fable2Zig.Emit.fs) | 7,233 | Combines top-level decls, type emission, IR statements/expressions, tailcall/trampoline emission, and runtime call synthesis |
| [`src/Fable.Transforms/Zig/Fable2Zig.Perceus.fs`](Fable2Zig.Perceus.fs) | 5,330 | Combines ownership/borrow/alias analysis with IR rewriting (`rewriteFlat`), drop/dup insertion, reuse matching (`EUnpack`/`TTok`), HOF cloning, and move-only resource checks |
| [`src/Fable.Transforms/Zig/Fable2Zig.LowerHelpers.fs`](Fable2Zig.LowerHelpers.fs) | 2,836 | Broad bag of type helpers, member resolution, naming, and IR builders |
| [`src/Fable.Transforms/Zig/Fable2Zig.Dotnet.Misc.fs`](Fable2Zig.Dotnet.Misc.fs) | 2,761 | Catch-all `.NET` BCL lowering module |

**Proposed refactoring split** (pure structural extraction, zero behavioral changes per split PR):

1. **`Fable2Zig.Lower.fs` (9,355 → <2,500 lines/file)**:
   - Migrate the remaining ~940 lines of `dotnetCall` out into dedicated `Fable2Zig.Dotnet.*.fs` modules (`Zig_Roadmap.md:279`).
   - Split into `Fable2Zig.Lower.Patterns.fs`, `Fable2Zig.Lower.Calls.fs`, `Fable2Zig.Lower.Control.fs` (CEs/async/seq/try-with), and `Fable2Zig.Lower.fs` (entry/bindings/modules).
2. **`Fable2Zig.Dotnet.Misc.fs` (2,761 lines)**:
   - Carve out focused domain files (e.g., reflection/diagnostics, threading/atomics, formatting/interop).
3. **`Fable2Zig.Perceus.fs` (5,330 lines)**:
   - Separate analysis (`Fable2Zig.Perceus.Analysis.fs`: liveness, borrow inference, uniqueness), HOF/tail-call specialization (`Fable2Zig.Perceus.Specialize.fs`), and transformation (`Fable2Zig.Perceus.Reuse.fs`: `settle`/`tryUnpack`/`cellsMatch`/`TTok`/`rewriteFlat`, `Fable2Zig.Perceus.fs`: RC insertion & orchestration).
4. **`Fable2Zig.Emit.fs` (7,233 lines)**:
   - Separate into `Fable2Zig.Emit.Types.fs` (structs, tagged unions, `IfaceMeta`, RTTI), `Fable2Zig.Emit.Exprs.fs`, `Fable2Zig.Emit.TailCalls.fs`, and `Fable2Zig.Emit.fs`.
5. **`fable_rt.zig` (10,931 lines)**:
   - Extract cohesive Zig modules imported cleanly by `fable_rt.zig`: `fable_iso.zig` (`Iso`/`Region`), `fable_arena.zig` (`Arena`), `fable_iface.zig` (`IfaceMeta`), `fable_thread.zig` (threads/locks/pool), and move bulk unit-test blocks into `fable_rt_tests.zig` (wired via `comptime { _ = @import("fable_rt_tests.zig"); }`) so `zig test fable_rt.zig` stays one command.

---

### 0.7 Documentation Sync, Round 1 Open Questions & Remaining Backlog

- **Docs out of sync with shipped behavior**:
    - [`src/Fable.Transforms/Zig/FABLE-ZIG.md`](FABLE-ZIG.md) has several stale sections describing pre-shipped architecture: line `67` (`Not yet:`), line `78` (`this` cannot be used in constructors yet), lines `99–110` (still describes interfaces as "a struct of function values, one per member" instead of `{ data, vt }` fat pointers, plus stale `Not yet:` items), line `434` (`Not yet:` for resources/arenas), and lines `448–450` (counted spans and `stackalloc` already shipped).
    - [`Zig_Roadmap.md`](../../../Zig_Roadmap.md) needs its `[x]` ledger reconciled with landed Round 1 items and linked forward to this Round 2 specification.
- **Deferred Round 1 open questions** ([`fable2zig-enhancements.md#L1170-L1184`](fable2zig-enhancements.md#L1170-L1184)) — dispositions for Round 2:
    - **Interface / object-expression HOF specialization** (`IComparer`, `IEqualityComparer`, etc.) → promoted to **Part 1.5**.
    - **2-hop compile-time parallelism loss** (note: `FABLE_ZIG_TIME=1` is already implemented at [`Fable2Zig.fs:95`](Fable2Zig.fs#L95), and `.facts.json` sidecars are already implemented in [`Fable2Zig.Facts.fs:94-95`](Fable2Zig.Facts.fs#L94-L95)): use `FABLE_ZIG_TIME=1` on `tests/Zig` and `fable-library-zig` to measure wait time across the 2-hop facts barrier and decide whether running local `pc` on leaf functions while awaiting imports is worthwhile.
    - **`ReleaseSmall` `callK` binary-size growth**: measure `.text` size delta from `callK` specialization under `-OReleaseSmall` and add `noinline` / size-budget gating if growth is excessive.
    - **`tail_args_cap` (`128` B)**: measure how often real argument lists exceed `128` bytes vs stack cost across the 6 existing benchmarks (`nbody`, `lists`, `maps`, `strings`, `virtual`, `messages`) and `TailCallTests`.
- **Remaining minor F#/.NET backlog tracked in `Zig_Roadmap.md`** (track explicitly rather than silently dropping):
    - Excluded test in [`tests/Zig/ApplicativeTests.fs:744`](../../../tests/Zig/ApplicativeTests.fs#L744) (uncurried multi-arg local function placed in an option) and generic values holding generic functions (`let f_option = Some f`, [`Zig_Roadmap.md#L108-L112`](../../../Zig_Roadmap.md#L108-L112), [`#L571`](../../../Zig_Roadmap.md#L571)).
    - Remaining P/Invoke / Zig interop gaps ([`Zig_Roadmap.md#L505`](../../../Zig_Roadmap.md#L505), [`#L524-L525`](../../../Zig_Roadmap.md#L524-L525)): imported Zig function used as first-class value, `[<MarshalAs>]` on struct fields, `SetLastError`, `StringBuilder` buffers.
    - Remaining OOM raising sites for collection capacities and big strings ([`Zig_Roadmap.md#L296`](../../../Zig_Roadmap.md#L296)).

---

## Part 1: Automatic Perceus Reuse & HOF Optimizations (Koka-Inspired)

Round 1 delivered exact-shape Perceus reuse (`EUnpack` + `TTok` + `ECon(..., Some tok)`) and RC elision. Round 2 expands automatic in-place reuse and devirtualization across ordinary F# code with zero new F# annotations required.

### 1.1 Cross-Constructor & Same-Layout Cell Reuse

#### Current state

- In [`src/Fable.Transforms/Zig/Zig.IR.fs`](Zig.IR.fs#L290-L299) (`cellsMatch`) and [`src/Fable.Transforms/Zig/Fable2Zig.Perceus.fs`](Fable2Zig.Perceus.fs#L1542-L1557) (`tryUnpack` / `rewriteFlat`), reuse token matching requires identical field type keys (`tyKey`) or the same case of the same generic entity. This misses cases where a dead cell of case/type `A` could back an allocation of a different case/type `B` with identical layout (e.g., transforming AST/IR discriminated union cases with different field types of equal size/alignment, or reusing a dead `Cons` cell for another 2-word record).
- [`src/fable-library-zig/fable_rt.zig`](../../fable-library-zig/fable_rt.zig#L202-L225) (`cellReuse`) **already** validates `@sizeOf` and `@alignOf` equality at comptime and re-initializes `$gc` when `hasGc(C)` holds.
- **Two latent safety bugs in `cellReuse` today** that become critical once cross-constructor/cross-type reuse is enabled:
    1. **Uninitialized `thread.collector` UB**: At `fable_rt.zig:215-218`, if `OldT` has `!hasGc(OldT)` and `NewT` has `hasGc(NewT)`, `cellReuse` increments `thread.collector.allocs += 1` without calling `gcTick()` / checking `thread.collector_ready` — writing to `undefined` `thread.collector` if `NewT` is the thread's first cyclic cell.
    2. **Weak-reference type confusion**: `cellReuse` clears `thread.stamps` (line 214) but **never calls `weakGone`**. If a `WeakReference` points to a dead `OldT` cell that is reused in place as `NewT`, `TryGetTarget` resurrects a `NewT` cell as `OldT`.

#### Proposed design

1. **Relax `cellsMatch` while strictly honoring Zig's `std.mem.Allocator` contract**:
   - **Exact layout match (fast path)**: identical Zig heap type.
   - **Cross-constructor / cross-type exact size & alignment match**: allow different heap cases/types `OldT` and `NewT` to pair in `Perceus.fs` (letting `cellReuse` verify comptime layout at Zig compile time) **STRICTLY requiring `@sizeOf(NewT) == @sizeOf(OldT)` AND `@alignOf(NewT) == @alignOf(OldT)`**.
   - **CRITICAL ALLOCATOR CONTRACT**: Because `fable_rt.free` (`fable_rt.zig:1387`) calls `allocator.destroy(c)`, passing `@sizeOf(NewT)` and `@alignOf(NewT)` to `rawFree`, Zig's `std.mem.Allocator` forbids freeing a pointer with a smaller alignment (`@alignOf(NewT) < @alignOf(OldT)`) or different size (`smp_allocator`, `DebugAllocator`, and `FixedBufferAllocator` assert or corrupt freelists). Do **not** attempt size-class bucket reuse across differing sizes/alignments without a dedicated size-classed cell pool allocator.
2. **Harden `cellReuse` (`fable_rt.zig:202-225`)**:
   - Guard `hasGc(C)` with `if (!thread.collector_ready) collectorSetup();` (or `gcTick()`) before touching `thread.collector`.
   - Keep `isUnique(c)` as unmasked `rc == 1` (coordinated with Part 2.1's `weak_bit` and `immortal_bit`), so cells targeted by a `WeakReference` or null cells are never reused in place; also retain `weakGone` defense-in-depth if ever needed.
   - Keep `emitUnpack`'s `fable_rt.forget(cell)` call whenever `OldT` may be cyclic ([`Emit.fs:1278-1279`](Fable2Zig.Emit.fs#L1278-L1279)).
3. Track cross-constructor reuse hits using `Fable.Core.Zig.Counters` ([`Fable.Core.Zig.fs`](../../../src/Fable.Core/Fable.Core.Zig.fs#L116-L143)).

---

### 1.2 Known-Case Zero-Live-Field Drop Specialization

#### Current state

- Zig comptime **already** eliminates unmanaged child drops (`if (comptime !isManaged(T)) return;` in [`fable_rt.zig:1508-1611`](../../fable-library-zig/fable_rt.zig#L1508-L1611)), acyclic GC checks (`gcOf(c)` returns `comptime null`), and redundant RC decrements on unique reuse (`emitUnpack` at [`Emit.fs:1274-1290`](Fable2Zig.Emit.fs#L1274-L1290)).
- However, [`Fable2Zig.Perceus.fs:1595-1646`](Fable2Zig.Perceus.fs#L1595-L1646) (`settle`) and [`tryUnpack:1512`](Fable2Zig.Perceus.fs#L1512) only invoke `tryUnpack` when `allLive.Contains x` **and** `not direct.IsEmpty` — i.e., **only when at least one field of `x` is kept live** as a borrowed alias.
- When `x` is dead and its constructor case is known in `env.Known` **but none of its fields are live** (e.g., `match x with | Box _ -> Box 42` or `match t with | Node(_, _) -> Leaf 0`), `settle` falls back to generic `EDrop x` — re-dispatching on the union tag in `dropHeap` AND failing to produce a reuse token.

#### Proposed design

- Extend `settle` / `tryUnpack` so that when `x` is dead with `not (allLive.Contains x)` and `env.Known` knows `x`'s exact heap constructor case, Perceus emits `EUnpack` with `Moves = []`:
    - Directly drops `x`'s managed fields under `isUnique(cell)` without re-switching on the union tag;
    - Produces a `TTok` reuse token whenever `hasConOfShape` finds a matching downstream constructor, unlocking cell reuse for field-ignoring matches.

---

### 1.3 In-Place Unique Array Reuse (`arrayMapInPlace` & `arrayFilterInPlace`)

#### Current state

- [`src/fable-library-zig/fable_array.zig`](../../fable-library-zig/fable_array.zig#L44-L54) defines `Array(T)` as a 48-byte heap cell (`@"$rc"`, `@"$gc"`, `items: []T`, `shape: ?[2]usize = null`) with **no `capacity` field**, freeing `a.items` via `allocator.free(a.items)` using `a.items.len`.
- Helper builders `ArrayBuf` and `FilterBuf` ([`fable_array.zig:449-507`](../../fable-library-zig/fable_array.zig#L449-L507), [`Lower.fs:7706-7895`](Fable2Zig.Lower.fs#L7706-L7895)) always allocate a new buffer and copy elements.
- [`trySpecArrayHof`](Fable2Zig.Lower.fs#L7723) generates a specialized loop helper whose input array parameter `aV` is inferred by Perceus as **`MBorrowed`** — meaning the helper does not currently receive ownership of `a` even at `a`'s last use.

#### Proposed design

When a caller's input array argument to `Array.map`, `Array.mapi`, or `Array.filter` is at its last use, lower/specialize to an **owned-input** variant (`aV` with `MOwned`) that checks `fable_rt.isUnique(a)` at runtime:

- Checking `isUnique(a)` at runtime automatically and safely rejects:
    - externally aliased or shared (`shared_bit`) arrays;
    - arrays captured by the mapping/predicate closure itself (e.g., `Array.map (fun x -> x + a.[0]) a`, where `a` has RC ≥ 2);
    - null arrays (`immortal_bit`) and weak-referenced arrays (`weak_bit`).

1. **`arrayMapInPlace`**:
   - Enabled when `@sizeOf(T_in) == @sizeOf(T_out)`, `@alignOf(T_in) == @alignOf(T_out)`, AND **`holdsCyclic(T_in) == holdsCyclic(T_out)`** (so `Array(T_in)` and `Array(T_out)` have identical header size/alignment including `GcHdr`).
   - **Cycle-collector safety**: if `hasGc(Array(T_in))` holds, call `fable_rt.forget(a)` before mutating/reusing slots (so `fable_sgc` `ext` counts are not corrupted) and re-initialize `a.@"$gc"` for `Array(T_out)` on completion.
   - **Exception safety**: because `a` is uniquely owned and unobservable if `f` raises at index `i`, unwind cleanly even when `T_in != T_out`: move `a.items[i]` out before calling `f`, and on `catch |e|` drop `[0..i)` as `T_out`, drop `[i+1..n)` as `T_in`, free `a.items` and `a`, and return `e`.
2. **`arrayFilterInPlace`** — **CRITICAL ALLOCATOR SAFETY PITFALL**:
   - Because `Array(T)` currently has **no `capacity` field** and frees `a.items` via `allocator.free(a.items)`, **you MUST NOT simply overwrite `a.items = a.items[0..out_len]`** — doing so passes `out_len` instead of the allocated length to `allocator.free`, triggering Zig allocator panics / leaks.
   - Compare the two safe representations (see Open Question 1):
     - **Option B (Recommended — add `capacity: usize` to `Array(T)`)**: Track allocated backing length separately from `items.len` and free `a.items.ptr[0..a.capacity]`. Guarantees O(1) zero-realloc shrinking on **every** allocator (`c_allocator`, `smp_allocator`, `DebugAllocator`) and unlocks amortized in-place `Array.Resize` / `Array.append`, adding only `+1 usize` to an already 48-byte heap header.
     - **Option A (`allocator.resize` + fallback)**: Keep `Array(T)` unchanged and call `allocator.resize(a.items, out_len)`, copying on `false`. Caveat: Zig's `c_allocator` and `smp_allocator` return `false` whenever shrinking crosses a size class (the common case for filtering), falling back to allocating and copying anyway.

---

### 1.4 `$tc` Continuation Closure `Env` Reuse (`closureReuse`)

#### Current state

- Normal indirect closure calls (`ECallClo`, [`Perceus.fs:1761`](Fable2Zig.Perceus.fs#L1761)) **borrow** the closure `f` — the caller owns and drops `f` after `f.code(f.env, arg)` returns. Inside `f.code`, `env` is borrowed and cannot be destroyed or reused.
- Outside `f.code`, `f.env` is type-erased to `?*fable_rt.Env` ([`fable_rt.zig:7565-7618`](../../fable-library-zig/fable_rt.zig#L7565-L7618)) without storing `@sizeOf(EnvOf(Captures))` or `@alignOf`, while locally constructed non-escaping closures are already eliminated by `EKnown` / known-closure folding.
- **However**, in Round 1's **`$tc` tail-call entries (`TailCtx`)**, `ctx.self` is **already owned by the callee** ([`fable2zig-enhancements.md#L1069`](fable2zig-enhancements.md#L1069)) AND the closure's exact `EnvOf(Captures)` type is statically known inside its own body.

#### Proposed design

- Introduce `closureReuse` in `fable_rt.zig` targeting **`$tc` continuation bodies** where `env` is owned and its concrete `EnvOf(Captures)` layout is known:
    - When `isUnique(env)` holds at the point where the continuation's captures are dead and a successor continuation closure is constructed, drop dead captured fields, call `forget(env)` if `E.cyclic`, and reuse the `EnvOf` allocation when `@sizeOf(NewE) == @sizeOf(OldE)` and `@alignOf(NewE) == @alignOf(OldE)` (re-initializing `header.destroy`, `header.share`, and `hdr`).
    - Respect `Perceus.fs` `touchesMutable` guards and `env_iface_meta` vtable updates when reusing object-expression `Env`s.
    - Keep the normal non-`$tc` borrowed-closure calling convention unchanged.

---

### 1.5 Interface & Object-Expression HOF Specialization (`IComparer`, `IEqualityComparer`, etc.)

#### Current state

- Deferred Open Question from [`fable2zig-enhancements.md#L1181-L1182`](fable2zig-enhancements.md#L1181-L1182): F# HOFs accepting function values already benefit from Round 1's `EKnown` / `callK` specialization, whereas HOFs and library operations accepting interfaces or concrete object expressions (`{ new IComparer<'T> with member _.Compare(a, b) = ... }`, `IEqualityComparer<'T>`, single-method interfaces) still allocate `env_iface_meta` closures and dispatch indirectly through `{ data, vt }` fat pointers.
- Actual hot paths include `Array.BinarySearch(a, v, comparer)` ([`Array.fs:1127-1181`](../../fable-library-zig/Array.fs#L1127-L1181)), `Dictionary<'K,'V>(comparer)` / `HashSet<'T>(comparer)` ([`fable_rt.zig:2960, 3055`](../../fable-library-zig/fable_rt.zig#L2960)), and user-written generic algorithms taking `IComparer<'T>` / `IEqualityComparer<'T>` / single-method interfaces. (Note: `Array.sortWith` takes an F# function `'T -> 'T -> int`, and `Map.fs`/`Set.fs` use structural `compare`.)

#### Proposed design

- Extend Round 1's `NoEscape` / `EKnown` / `callK` mechanism in `Lower.fs` and `Perceus.fs` to recognize non-escaping concrete object expressions and known interface structs (`EIface`) passed to HOFs.
- Pass a stack-allocated known-interface struct (comptime Zig type parameter) so `.Compare` / `.Equals` / `.GetHashCode` / single-method calls devirtualize and inline cleanly, eliminating both `ifaceClosure` heap allocation and indirect vtable dispatch.

---

## Part 2: Isolation, Weak Refs, Concurrency & Existing-Primitive Hardening

### 2.1 Clean `$rc` Bit Layout & Per-Cell `weak_bit` (Eliminating `adoptShared`'s Global Bailout)

#### Current state

- [`src/fable-library-zig/fable_rt.zig`](../../fable-library-zig/fable_rt.zig#L317-L320): `adoptShared` checks `weak_refs.shared_count.load(.acquire) != 0` ([`fable_weak.zig:55`](../../fable-library-zig/fable_weak.zig#L55)) and **bails out process-wide** if *any* shared weak reference exists anywhere in the process.
- **CRITICAL EXISTING `$rc` COLLISIONS**:
    1. [`fable_array.zig:126`](../../fable-library-zig/fable_array.zig#L126) **already defines `pub const null_count: u32 = 1 << 30`**, and [`fable_rt.zig:5587-5589`](../../fable-library-zig/fable_rt.zig#L5587-L5589) defines `isCellNull(c)` as `(@atomicLoad(u32, &c.@"$rc", .monotonic) & ~shared_bit) >= arrays.null_count / 2` (`>= 1 << 29`). Placing `weak_bit` at `1 << 30` without relocating `null_count` causes **every weak-targeted cell to test true for `isCellNull`**, and every null cell to look weak-targeted with `rc == 0`.
    2. [`fable_sgc.zig`](../../fable-library-zig/fable_sgc.zig) reads raw `rcPtr(h).*` without masking at **5 sites** ([`L1108`](../../fable-library-zig/fable_sgc.zig#L1108), [`L1276`](../../fable-library-zig/fable_sgc.zig#L1276), [`L1403`](../../fable-library-zig/fable_sgc.zig#L1403), [`L1456`](../../fable-library-zig/fable_sgc.zig#L1456), [`L1597-L1603`](../../fable-library-zig/fable_sgc.zig#L1597-L1603)). Setting `weak_bit` on a local cyclic cell without masking `rcPtr` in `fable_sgc` corrupts `r.ext` / `h.u.refs` and breaks `died_pinned`.
    3. [`fable_string.zig:80`](../../fable-library-zig/fable_string.zig#L80) defines `Str.literal = 0xFFFF_FFFF` (all top bits set).

#### Proposed design

1. **Clean 3-flag `$rc: u32` bit layout**:
   - **Bit 31 (`0x8000_0000`) — `shared_bit`**: atomic refcounting across threads.
   - **Bit 30 (`0x4000_0000`) — `immortal_bit`**: `retain` and `drop` are no-ops; cell is never freed by RC. Used for `.NET` null cells (`null_count = immortal_bit`, so `isCellNull(c)` becomes a single bit test `(rc & immortal_bit) != 0` and static null arrays/records stop performing RC writes / cacheline ping-pong across threads!). `Str.literal` stays `0xFFFF_FFFF`.
   - **Bit 29 (`0x2000_0000`) — `weak_bit`**: cell has (or had) a local or shared `WeakReference`.
   - **Low 29 bits (`count_mask = 0x1FFF_FFFF`, ~536M max refcount)**: reference count, with saturation/debug trap before rolling into `weak_bit`.
2. **Fast-path invariants (zero extra branches on hot paths)**:
   - **`isUnique(c)` MUST remain unmasked `@atomicLoad(u32, &c.@"$rc", .monotonic) == 1`**: automatically returns `false` for `shared_bit`, `immortal_bit` (null cells), **and** `weak_bit` — preventing in-place cell/array reuse from causing weak-reference type confusion!
   - **`retain(c)`**: fast path tests `rc < immortal_bit` (`< 1 << 30`, true for normal AND local-weak cells) and executes plain `c.@"$rc" = rc + 1`; slow path handles `shared_bit` (atomic add) and `immortal_bit` (return no-op).
   - **`releaseIsLast(c)`**: fast path handles normal local `rc == 1` or `1 < rc < weak_bit`; slow path handles `shared_bit` (masking `flag_mask` to detect last count `== 1` while preserving `weak_bit`), `immortal_bit` (return `false`), and local `weak_bit` (`(rc & count_mask) == 1`).
   - **`fable_sgc.zig`**: add an inline helper `rcCount(h)` (`rcPtr(h).* & count_mask`) and use it across all 5 `rcPtr` sites (preserving flag bits on `rcPtr(h).* += 1` / `-= 1` and checking `(rc.* & count_mask) == 0` in `died_pinned`).
3. **Per-cell weak tracking & `adoptShared` fix**:
   - Set `weak_bit` on the target cell in `weakHandle`, `sharedHandle` (atomic `fetchOr`), and `shareWeakHandle`. (Leaving `weak_bit` sticky avoids races with `weakLetGo`.)
   - Remove the process-wide `weak_refs.shared_count.load(.acquire) != 0` bailout in `adoptShared` (`fable_rt.zig:318`) and `unshareable` (`fable_rt.zig:313`); inspect only `(rc & weak_bit) != 0` on the specific cell.
   - Update `weakTryGet` (`fable_weak.zig:206`) to check `(rc & count_mask) != 0` in its CAS loop.
   - **Bonus optimization**: in `free` (`fable_rt.zig:1378-1381`), skip **both** `weakGone` and `sharedWeakGone` unless `(rc & weak_bit) != 0`, making weak-ref cleanup zero-cost on the 99.9% fast path.

---

### 2.2 Closing the `Iso.pack` Interface Gap (`IfaceMeta.iso_reach`)

#### Current state

- [`src/fable-library-zig/fable_rt.zig`](../../fable-library-zig/fable_rt.zig#L690-L861) implements `Region` graph traversal for `Iso.pack` / `isoTryPack`.
- At line `758`, `Region.visit` unconditionally rejects any `isIface(T)` value (`r.ok = false`), preventing any graph containing an interface field, object expression, or boxed interface from being packed into an `Iso<'T>`.
- Meanwhile, [`fable_rt.zig:7135-7255`](../../fable-library-zig/fable_rt.zig#L7135-L7255) has **4 shared `IfaceMeta` singletons** (`empty_iface_meta`, `obj_iface_meta`, `box_iface_meta`, `env_iface_meta`) plus `upcastIfaceMeta` (whose `data` is a **wrapper boxed `Obj`** holding `SubIface`, NOT the inner `SubIface.data`). Per-concrete type hooks live on **`ObjType`** (`fable_rt.zig:3839`) and **`Env`** (`fable_rt.zig:7565`), not `IfaceMeta`.
- **Latent partial-mutation bug in [`Region.closed()`](../../fable-library-zig/fable_rt.zig#L852-L859)**: if `share()` fails on a later opaque cell in the loop (e.g., an object inside a `StackArena` or `fable_sgc` structure), earlier opaque cells were already permanently mutated to `shared_bit` even though `Iso.tryPack` returns `Error originalValue`.

#### Proposed design

1. **Fix `Region.closed()` atomicity first**: validate that every opaque cell is shareable (not `inThreadArena`, not in an active `fable_sgc` structure, etc.) *before* mutating any cell to `shared_bit`, so a failed `Iso.tryPack` leaves the input graph untouched.
2. **Add `iso_reach` to `IfaceMeta` (`fable_rt.zig:7135-7255`)** — choosing between two explicit tiers (see Open Question 3):
   - **Tier 1 (Minimal — matches `Obj`/`Env` semantics today, ~20 lines)**:
     - `empty_iface_meta`: trivial no-op (stateless object expressions pack immediately with zero sharing).
     - `obj_iface_meta`, `box_iface_meta`, and `upcastIfaceMeta`: call `r.reachOpaque(Obj, data)` (`upcastIfaceMeta.data` *is* the wrapper `Obj`, so `reachOpaque(Obj, data)` accounts for the wrapper's `$rc` and shares the boxed `SubIface` through `objIfaceShare`).
     - `env_iface_meta`: call `r.reachOpaque(*Env, data)`.
   - **Tier 2 (Full deep tracing)**:
     - Add `iso_visit` hooks on **`ObjType`** and **`Env`** in addition to `IfaceMeta.iso_reach` (with `upcastIfaceMeta` visiting both the wrapper `Obj` and the boxed `SubIface`), so objects/closures/interfaces stay unshared inside `Iso` and internal diamonds like `(x, iface_holding_x)` succeed.

---

### 2.3 Clear Active `fable_sgc` Check State Before `region.visit` (`gc.finishCheck()`)

#### Current state

- [`src/fable-library-zig/fable_sgc.zig`](../../fable-library-zig/fable_sgc.zig#L738-L744): `canMove` rejects moving an object whenever `h.meta.flags & F_STACKED != 0` or `r.dead || gc.check == r`.
- If the incremental structure-count cycle collector currently holds an in-progress check (`gc.phase != .idle`), `Iso.pack` fails non-deterministically depending on prior allocation history rather than true reachability.

#### Proposed design

- Add `gc.finishCheck()` in `fable_sgc.zig` to drive the currently active local check to `.idle` (`gc.work(unlimited)`), clearing `gc.check` **and** unpinning all `F_STACKED` cells while preserving invariants `(A)`/`(B)`/`(C)`.
- **CRITICAL PLACEMENT**: Invoke `gc.finishCheck()` **before `region.visit(x)`** at the top of [`packOrNull`](../../fable-library-zig/fable_rt.zig#L521-L545) whenever `thread.collector_ready and thread.collector.phase != .idle`. (Calling it in `Region.moveOut` is too late because `Region.closed()` already rejected `canMove`; calling it after `region.visit` risks mutating/freeing cells whose pointers are cached in `region.cells`.)
- Respect `Collector.pause()` (`gc.no_collect > 0`): if collection is paused while a check is active, decline to force-finish or complete only the active check without draining unrelated dying queues.

---

### 2.4 Automatic `isoSend` / `adoptShared` at Concurrency Boundaries

#### Current state

- [`fable_rt.zig:576-652`](../../fable-library-zig/fable_rt.zig#L576-L652) implements `isoSend` / `transferOrShare` (used by `MailboxProcessor`).
- However, normal thread/task spawns (`System.Threading.Thread` at [`fable_rt.zig:955`](../../fable-library-zig/fable_rt.zig#L955), `Task.Run` at [`Task.fs:144-164`](../../fable-library-zig/Task.fs#L144-L164), `Async.Parallel`) currently call **`markShared`** on captured values even when a captured subgraph is uniquely owned at the spawn site.
- In addition, [`threadStart`](../../fable-library-zig/fable_rt.zig#L957-L978) keeps a duplicate reference in `t.start` until `threadMain` exits (keeping `f.env` at RC = 2 during execution), and `Task.Run` (`t.fable_task <- Some r`) / `Async.Parallel` store **return values** into shared cells, triggering `markShared` on results as well.

#### Proposed design

1. **Direct-lambda capture transfer (input direction)**:
   - Only for **direct lambda literals** passed to `Thread(fun () -> ...)`, `Task.Run(fun () -> ...)`, or `Async.Parallel` (never arbitrary function values `f` that could be invoked more than once and fail `isoUnpack`):
     - Captures with static type `Iso<'T>` move across without touching inner cells.
     - Uniquely owned non-`Iso` captures (no surviving local alias after spawn) use `isoSend` / `transferOrShare` (falling back to `markShared` for shared/cyclic subgraphs) and unpack once on the worker thread.
2. **Move `t.start` into `threadMain` (`fable_rt.zig:957-978`)**:
   - Transfer `t.start` out of `ThreadOf` (replacing it with `threadRan`) when spawning so `f.env` arrives on the worker thread with RC = 1 rather than RC = 2.
3. **Return-direction adoption (`Task.Run` & `Async.Parallel`)**:
   - Box `Task.Run` and `Async.Parallel` results via `isoSend` (or call `adoptShared` after `Join()` / worker completion barrier) so results return to the caller with plain local RC.

---

### 2.5 Persistent Worker Thread Pool (`Task.Run`, `Async.Parallel`, `Parallel.For`)

#### Current state

- The runtime currently has **no persistent worker thread pool**: `Task.Run` ([`Task.fs:151`](../../fable-library-zig/Task.fs#L151)) spawns a new OS thread per call, and `Parallel.For` / `Async.Parallel` spawn and join up to 8 OS threads on every invocation.

#### Proposed design

- Introduce a lightweight, lazily started worker thread pool in `fable_thread.zig` (defaulting to CPU core count, capped cleanly) with graceful shutdown before process exit / test teardown so every worker runs `collectorDeinit()` and reports to `ended_threads_live` (keeping `testNoLeak` exact).
- Back `Task.Run`, `Async.Parallel`, and `Parallel.For` with this shared pool — immediately accelerating standard F#/.NET concurrency primitives and laying the foundation if `Cown<'T>` / `when` is added in a later round.

---

### 2.6 Targeted Hardening of Existing `IResource`, `[<StackArena>]` & Shared-Cycle Diagnostics

Keep already-shipped `IResource` (~80 lines) and `[<StackArena>]` (~115 lines) small and rock-solid without expanding them into new language dialects:

1. **Mandatory `retainAll` `@compileError` safety backstop for move-only `IResource` (`fable_rt.zig:1491`)**:
   - Currently [`Zig.IR.fs:171-176`](Zig.IR.fs#L171-L176) returns `isCopyable (TGen _) = true`, and [`retainAll`](../../fable-library-zig/fable_rt.zig#L1491-L1503) has **no `@compileError`** when `isResource(T) and !@hasDecl(T, "fable_dup")`. Passing a move-only `IResource` through any copying generic function (`let dup2 x = (x, x)`, `Array.create`, `a.[i]`, `box`) silently shallow-copies and double-destroys the native handle.
   - Add `if (comptime isResource(T) and !@hasDecl(T, "fable_dup")) @compileError("fable: cannot copy move-only IResource " ++ @typeName(T));` in `retainAll`.
   - *(Small optional extension — see Open Question 4)*: lift [`LowerTypes.fs:500`](Fable2Zig.LowerTypes.fs#L500) to support **generic** value-type `IResource<'T>` (e.g., `OwnedSlice<'T>`) by emitting a 1-arg forwarding wrapper `pub fn fable_destroy(x: @This()) ... { return destroy(T, x); }` in [`Emit.fs:5626-5637`](Fable2Zig.Emit.fs#L5626-L5637), and decide whether raising hooks (`fable_rt.zig:1445-1452`) should remain caught or become a compile-time `RNever` error.
2. **Fix `[<StackArena>]` one-time global install data race & permanent router overhead (`fable_rt.zig:3585-3660`)**:
   - `Arena` **already** has per-thread `thread.arena` and `outer: ?*Arena` nesting, and only swaps `allocator` once via `@cmpxchgStrong`. However, lines `3647-3650` perform non-atomic 16-byte writes `arena_base = allocator; allocator = arena_router;` while other threads concurrently read `allocator` without synchronization (and spinning threads read `arena_base == null` non-atomically), permanently installing vtable overhead across all threads and eagerly calling `collectorSetup()`.
   - Replace the global `allocator = arena_router` mutation with a whole-program comptime boolean `uses_arena` in `root.@"$cycles"` (mirroring `oom_catch` at [`fable_rt.zig:68-75`](../../fable-library-zig/fable_rt.zig#L68-L75)): programs without `[<StackArena>]` pay zero checks; programs with `[<StackArena>]` route via `if (comptime uses_arena) if (thread.arena) |a| ... else allocator` (preserving `fable_oom_hook`, user-set `allocator`, and library calls without any data race). Stop calling `collectorSetup()` eagerly in `arenaEnter`.
3. **Actionable `fable_sgc` shared-cycle diagnostics & thread-exit telemetry**:
   - Improve runtime `NotSupportedException` / `InvalidOperationException` messages at shared-cycle and `Iso.pack` boundaries to name the specific failing cause and suggest `WeakReference` or `Iso.pack`.
   - Surface thread-exit `fable_sgc` drain statistics under `Fable.Core.Zig.Counters` / Debug builds so leaks from uncollected cross-thread cycles are immediately diagnosable during testing.

---

## Part 3: Explicit Non-Goals & Deferred Ideas

The following ideas from earlier Round 2 drafts were intentionally **cut or deferred** to keep Fable-Zig lean, avoid Zig-only F# dialect creep, and prevent overlapping mechanisms:

- **`[<Lent>]` parameter attribute (Cut)**: Perceus **already** infers `MBorrowed` automatically across files via `.facts.json` (zero RC traffic without annotations), and standard F# **already** provides `inref<'T>`, `byref<'T>`, `ReadOnlySpan<'T>`, and `Span<'T>` — which map to unmanaged `TPtr`/`TSlice` ([`Zig.IR.fs:76-77, 117-130`](Zig.IR.fs#L76-L77)) and are escape-checked by the F# compiler itself on both `.NET` and Zig.
- **`[<StackArena>]` `SpillToHeap` & custom static escape analyzer (Cut)**: Standard F# `NativePtr.stackalloc` + `Span<'T>` already cover stack buffers cleanly, and adding `SpillToHeap` + custom escape analysis turns a small no-heap/embedded escape hatch into a second heap-arena system. Fix the global install race (Part 2.6) and keep `[<StackArena>]` minimal.
- **`IResource<'T>` / `ISharedResource<'T>` on classes (Cut)**: Classes already have standard `IDisposable` + `use`, **and** [`ObjCell.destroy`](../../fable-library-zig/fable_rt.zig#L4021-L4032) / [`ObjCell.finalize`](../../fable-library-zig/fable_rt.zig#L4111-L4123) already call `drop` on every initialized field — so a class holding a small `IResource` struct field *already* gets deterministic refcount-zero destruction (including through interfaces and cycle collection) by plain composition, with zero new `ObjType` plumbing and no awkward dead `ISharedResource.Dup` method.
- **Bulk-freeable heap `Region` allocators (Deferred)**: Acyclic short-lived F# graphs already pay zero cycle-collector overhead and benefit from borrow elision + Perceus reuse; cyclic graphs already die in O(1) via `fable_sgc` structure counts. Adding `region_bit` + finalizer lists + incoming external heap-RC leak guards is premature unless post-Part 1 benchmarks show allocator churn is an actual bottleneck.
- **`Cown<'T>` & deadlock-free `when` (Deferred to optional follow-up)**: Worth revisiting as a clean companion library / Round 3 once the shared worker thread pool (Part 2.5) is built and battle-tested on `Task.Run` / `Async.Parallel`. (When revisited, specify duplicate-cown rejection, exception handoff, `Cown`-cycle `WeakReference` guidance, and `.NET` parity.)
- **Inter-procedural reuse tokens & `[<Fip>]` compile-time audits (Deferred)**: Measure the real-world impact of intra-procedural cross-constructor reuse and zero-live-field drop specialization (Part 1.1–1.2) before adding inter-procedural reuse token ABIs or new attributes.

---

## Part 4: Focused Implementation Order, Verification Gates & Open Questions

### 4.1 Phased Implementation Order (Steps 1–7)

1. **Step 1 — Toolchain, CI, `Seq.cast` Bug & Warning Baseline (Part 0.1–0.4)**:
   - Align `src/benchmarks-zig/README.md:18` and `Zig_Roadmap.md:530` to Zig `0.17.1`; audit non-Zig diffs and run cross-target regression tests; wire `-fllvm` (`TailCallTests.zig -lc`) into `src/Fable.Build/Test/Zig.fs`; fix the `FS0026` `Seq.cast` unreachable-pattern bug (`Fable2Zig.Dotnet.Collections.fs:135`), `FABLE0114` (`Global.fs:8-9`), and ungated `thread.stats` writes (`fable_rt.zig:1493, 1531`).
2. **Step 2 — Large-File Splitting, Docs Sync & Round 1 Measurements (Part 0.6–0.7)**:
   - Split `Fable2Zig.Lower.fs`, `Fable2Zig.Dotnet.Misc.fs`, `Fable2Zig.Perceus.fs`, `Fable2Zig.Emit.fs`, and `fable_rt.zig` (pure refactors verified step-by-step against the full Zig suite); reconcile `FABLE-ZIG.md` and `Zig_Roadmap.md`; measure 2-hop wait time with `FABLE_ZIG_TIME=1`, `-OReleaseSmall` `callK` size delta, and `tail_args_cap` across the 6 baseline benchmarks.
3. **Step 3 — Clean `$rc` Bit Layout & Per-Cell `weak_bit` (Part 2.1)** *(lands BEFORE cross-constructor reuse so weak-targeted cells are protected)*:
   - Implement the 3-flag `$rc` layout (`shared_bit`, `immortal_bit`, `weak_bit`), relocate `null_count = immortal_bit`, mask all 5 `rcPtr` sites in `fable_sgc.zig`, keep `isUnique` unmasked (`rc == 1`), remove `adoptShared`'s process-wide weak bailout (`fable_rt.zig:318`), and gate `weakGone`/`sharedWeakGone` on `weak_bit`.
4. **Step 4 — Koka Cross-Constructor Cell Reuse, Drop Specialization & `$tc` `closureReuse` (Part 1.1, 1.2, 1.4)**:
   - Relax `cellsMatch` for exact `@sizeOf ==` and `@alignOf ==` cross-constructor reuse; fix `cellReuse`'s `collector_ready` guard; add zero-live-field known-case `EUnpack` drop specialization in `settle`; add `$tc` owned-`Env` `closureReuse`.
5. **Step 5 — Unique Array Reuse, O(N) `Array.sortBy` & Interface HOF Specialization (Part 1.3, 1.5, 0.5)**:
   - Add `capacity: usize` to `Array(T)` (if Option B is chosen) and implement `arrayMapInPlace` / `arrayFilterInPlace` with owned input mode and `fable_sgc` `forget()`; upgrade `Array.sortBy`/`sortByDescending`/`sortInPlaceBy` to O(N) key precomputation; add `IComparer`/`IEqualityComparer`/object-expression HOF specialization.
6. **Step 6 — `Iso` & Existing-Primitive Hardening (Part 2.2, 2.3, 2.6)**:
   - Fix `Region.closed()` partial-mutation bug; add `IfaceMeta.iso_reach` (Tier 1 or Tier 2); invoke `gc.finishCheck()` before `region.visit(x)` in `packOrNull`; add the mandatory `retainAll` `@compileError` for move-only `IResource` (plus optional generic `IResource<'T>`); fix `[<StackArena>]`'s global install race via whole-program `uses_arena`; add actionable shared-cycle diagnostics and thread-exit telemetry.
7. **Step 7 — Persistent Worker Thread Pool & Automatic Concurrency Transfer (Part 2.4, 2.5)**:
   - Build the shared worker thread pool (with `collectorDeinit`/`ended_threads_live` leak-check integration) backing `Task.Run`, `Async.Parallel`, and `Parallel.For`; move `t.start` out of `ThreadOf` on spawn; emit `isoSend`/`transferOrShare` on direct spawn lambdas and `Iso`/`adoptShared` on `Task.Run`/`Async.Parallel` return values.

---

### 4.2 Verification Gates (Zig `0.17.1` + `.NET 10`)

Every step must clear the applicable gates before proceeding:

- **Zero-warning compiler & runtime build**: `dotnet build` (`Fable.Transforms` / `Fable.Cli`) and Zig transpilation produce zero `FS0026`, `FABLE0114`, or Zig warnings.
- **Full Zig suite on default backend & LLVM backend**:
    - `./build.sh test zig` (with `.NET` parity comparison against every test project);
    - `zig test -fllvm tests/Zig/TailCallTests.zig -lc` (verifying `200000`-depth LLVM tail calls);
    - `zig test src/fable-library-zig/fable_rt.zig -lc` and `zig test src/fable-library-zig/fable_rt.zig`.
- **Targeted regression tests**: `Seq.cast` over non-generic `IEnumerable`, `cellReuse` with `WeakReference` and cross-`hasGc` types, `Iso.tryPack` failure non-mutation, move-only `IResource` rejected in copying generic functions, and `Task.Run`/`Async.Parallel` pool teardown under leak checking.
- **Cross-target hygiene**: `./build.sh test javascript` and `./build.sh test typescript` (plus quicktest checks for other targets when `Fable.Cli` / `FableTransforms` change) green whenever shared non-Zig files are modified.
- **Concurrency & sanitizer checks**: Zig Debug leak assertions (`testNoLeak`) + ThreadSanitizer (**`-fsanitize-thread`** in Zig `0.17.1` on Linux/macOS where supported) exercising `weak_bit`, `adoptShared`, concurrent first-entry nested `StackArena`, and worker thread pool stress tests.
- **Paired ReleaseFast benchmarks**: Compare alloc counts (`Fable.Core.Zig.Counters`), binary size (`-OReleaseSmall` vs `-OReleaseFast`), and wall time before/after Parts 1–2 on the 6 baseline benchmarks (`nbody`, `lists`, `maps`, `strings`, `virtual`, `messages`) plus microbenchmarks for AST transforms, `Array.map`/`filter`/`sortBy`, `Iso.pack` with interfaces/closures, and `Task.Run`/`Async.Parallel`.

---

### 4.3 Open Questions (Design Decisions Needed Before Coding)

1. **`Array` shrink representation (`arrayFilterInPlace`, Part 1.3)**: Add `capacity: usize` to `Array(T)` (Option B — recommended because `c_allocator`/`smp_allocator` reject cross-class `resize` shrinks, `Array(T)` is already 48 bytes, and `capacity` accelerates `Array.Resize`), or keep 2 fields with `allocator.resize` fallback (Option A)?
2. **Global `-fllvm` CI matrix vs targeted `TailCallTests.zig` (Part 0.2)**: Run `-fllvm` only on `TailCallTests.zig` (fast CI), or run the full Zig test suite on both self-hosted and `-fllvm`?
3. **`IfaceMeta.iso_reach` depth (Part 2.2)**: Start with Tier 1 (opaque `Obj`/`Env` matching existing `Iso` semantics in ~20 lines) or build Tier 2 (`ObjType.iso_visit` + `Env.iso_visit` deep tracing) directly so objects/closures/interfaces stay unshared inside `Iso` and support internal diamonds?
4. **Generic `IResource<'T>` & raising hook policy (Part 2.6)**: Include the small (~30-line) generic value-type `IResource<'T>` support in Step 6, and should raising hooks (`fable_rt.zig:1445-1452`) stay silently caught or become a compile-time `RNever` diagnostic?
5. **Follow-up `Cown<'T>` placement (Part 3)**: If `Cown<'T>` / `when` is added after Step 7's worker thread pool lands, should it live strictly additively in `Fable.Core.Zig.fs` (`AGENTS.md` NuGet semver constraint) or in a separate optional Zig concurrency package?
