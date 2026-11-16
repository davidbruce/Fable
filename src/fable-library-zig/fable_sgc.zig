//! Cycle reclamation by one count per structure, for a precise reference-counting
//! runtime. Self-contained (std only); fable_rt.zig is its only caller. Its two long
//! operations (freeing a dead structure, checking a live one) are done in bounded steps.
//!
//! THE IDEA
//! --------
//! A cycle-capable cell is on its own or a member of a *structure*. A
//! structure has one number, `ext`: the references to its cells that are NOT
//! held in a field of one of its cells. The hooks keep it up to date. When it
//! reaches zero nothing outside refers to any of the cells, so the whole
//! structure is dead, cycles included, and nobody had to look at the graph.
//!
//! Who is in a structure:
//!   * the two ends of a store (after construction) are put in the same one;
//!   * a cell that joins brings its children that are still on their own,
//!     transitively, and its edges into the structure are counted then;
//!   * a child that already belongs to another structure stays there (the
//!     reference is one of that structure's outside references);
//!   * two kinds of store are ignored, because neither can close a cycle:
//!     (A) into a cell that is in no structure, of a reference to an OLDER
//!         cell: a constructor can only point at older cells, so a cycle
//!         needs a store that makes an older cell point at a newer one;
//!     (B) into a cell that is in no structure, of a reference to a cell
//!         that is in no structure either and has no cycle-capable children
//!         (a leaf: appending a fresh node). The leaf is flagged, and a
//!         later store INTO it is never ignored by (A).
//!     (C) into an unflagged cell that is in no structure, of a reference to
//!         a cell that is in no structure and from which the owner cannot be
//!         reached (an older cell is given something that was built after
//!         it). Everything reachable from the stored cell is flagged, by a
//!         walk if it is not flagged already; flagged cells keep the
//!         property "what I reach outside structures is flagged too", which
//!         is what makes "unflagged owner, flagged child" a proof that the
//!         owner is not reachable.
//!     Every cycle still contains a store that is tracked. Its edges cannot
//!     all be of kind (A) or constructed (those run from newer to older).
//!     Take the ignored edge of kind (B) or (C) that was stored last, from x
//!     into z. At that moment x could not be reached from z, so some edge on
//!     the cycle's way from z back to x was stored later; the first such
//!     edge leaves a cell that z reached already, which is flagged or a
//!     member of a structure, so it was not ignored by (A), and (B) or (C)
//!     would make it later than the last one. It was tracked.
//!     And when that tracked store comes, the cells joined by ignored stores
//!     come in with it: a joining cell brings its children, however their
//!     edges were made. (That is why (B) needs the owner to be on its own: a
//!     member must never point at a cell that is in no structure.)
//!
//! `ext` is never lower than the truth. It can be higher, and a dead cyclic
//! piece can sit inside a structure that is still referenced. In both cases a
//! member lost a reference and survived; that marks the structure dirty, and
//! a dirty structure gets a *local check*: an incremental mark over its ring
//! alone (colour the cells in place, subtract the edges between them, mark
//! from what is left, sweep the rest).
//!
//! BOUNDED STEPS
//! -------------
//!   * A dead structure is queued. Its cells are released and freed
//!     `cfg.free_budget` at a time, by tick() and step().
//!   * A local check is a sequence of one-cell units, `cfg.pace` per tick().
//!     While one runs, retain / release / store / move-out colour the cell
//!     they touch (white -> grey).
//! Every hook is O(1), except a store that makes cells join (one unit per
//! joining cell) and the drop of a member (its number of traced fields).
//!
//! INTERFACE (everything the generated code calls)
//! -----------------------------------------------
//!   gc.init(cfg, ctx, allocator) once; `gc` must not move afterwards. The
//!                                allocator is for structure records only.
//!   gc.hdr(&desc)                value for a new cell's `gc` field (after
//!                                tick(), so that the cell gets its age)
//!   gc.tick()                    before every allocation of a cycle-capable
//!                                cell, after its field values are computed
//!   gc.onRetain(&c.gc)           after rc += 1
//!   gc.onRelease(&c.gc)          after rc -= 1 that left rc > 0
//!   gc.onZero(&c.gc) -> bool     the last reference is gone. true: the
//!                                collector took the cell (its structure died
//!                                with it), do nothing more. false: drop its
//!                                fields and deallocate it now.
//!   gc.onFree(&c.gc)             a unique cell is taken apart / reused
//!                                without onZero. Call it BEFORE dropping or
//!                                moving out the cell's fields.
//!   gc.onStore(&owner.gc, &new.gc)    after a reference was stored into a
//!                                traced field of `owner` AFTER construction.
//!                                At that moment every traced field of
//!                                `owner` must hold a counted reference of
//!                                its own.
//!   gc.onUnstore(&owner.gc, &old.gc)  a reference was taken out of a traced
//!                                field of `owner` (overwritten) and will be
//!                                released by the caller. Before the onStore
//!                                for the value that replaced it.
//!   gc.onMoveOut(&child.gc)      a reference was moved out of a dying unique
//!                                cell's field into a local without a retain
//!   gc.step(budget) -> bool      explicit bounded work; true while more
//!   gc.collectAll() -> usize     everything now; returns cells freed
//!   gc.configure(cfg), gc.noCollectEnter()/Leave(), gc.counters
//!   sgc.isGarbage(&child.gc)     only inside Desc.release_outside
//!
//! Desc says, for one type of cell: where its count is (rc_offset), which
//! cells it refers to (trace), and how to give up what it holds outside a dead
//! set (release_outside), to free it (free), and to do both (finalize).

const std = @import("std");
const builtin = @import("builtin");
const root = @import("root");
const assert = std.debug.assert;

pub const unlimited: usize = std.math.maxInt(usize);

pub const State = enum(u2) {
    /// Not being looked at.
    idle = 0,
    /// In the ring being checked, not (yet) known to be live.
    white,
    /// In the ring being checked and known live; mark has not done it yet.
    grey,
    sentinel,
};

const F_PASSED: u5 = 1; // white with refs == 0 when the mark scan passed it
const F_STACKED: u5 = 2; // on the grey stack, and pinned (one count is the collector's)
const F_RELEASED: u5 = 4; // garbage whose release_outside has run
const F_TARGET: u5 = 8; // some cell was made to point at it while it was a leaf on its own (rule B)
const F_LEAF: u5 = 16; // has had no cycle-capable child so far (set at allocation, cleared by a store)

/// Descriptors are addressed relative to this byte.
const anchor: u8 align(desc_align) = 0;
/// Descriptors are aligned to this, and a header holds its descriptor's
/// distance from `anchor` in these units: 25 bits reach 1 GB either way.
pub const desc_align = 64;

/// Each thread has a collector of its own, for the cells it made: a value
/// never belongs to two threads (reference counts are not atomic). Where
/// there is one thread, or no thread-local storage (a freestanding target, or
/// a program whose root file says `pub const fable_one_thread = true;`), the
/// state below is plain global.
pub const per_thread: bool = !builtin.single_threaded and builtin.os.tag != .freestanding and
    !(@hasDecl(root, "fable_one_thread") and root.fable_one_thread);

const tl = if (per_thread) struct {
    threadlocal var sweeping: bool = false;
    threadlocal var dying_now: ?*Structure = null;
    threadlocal var the_gc: ?*Gc = null;
} else struct {
    /// True only while a check's sweep runs a garbage cell's release_outside.
    var sweeping: bool = false;
    /// The dead structure whose cells are releasing what they hold outside it
    /// (isGarbage counts the references they hold INSIDE it for the check below).
    var dying_now: ?*Structure = null;
    /// The thread's collector (isGarbage has no other way to find the
    /// structure records).
    var the_gc: ?*Gc = null;
};

/// Is the cell shared between threads (the top bit of its count, see fable_rt.zig's
/// `markShared`)? Such a cell is in no structure and the collector leaves it alone.
pub inline fn isShared(h: *const Hdr) bool {
    const addr: usize = @bitCast(@as(isize, @bitCast(@intFromPtr(h))) + h.desc().rc_offset);
    const rc: *const u32 = @ptrFromInt(addr);
    return @atomicLoad(u32, rc, .monotonic) & (1 << 31) != 0;
}

/// Is the cell a member of a structure (then it cannot be shared)?
pub inline fn inStructure(h: *const Hdr) bool {
    return h.st != 0;
}

/// Type descriptor (its distance from `anchor` in units of `desc_align`,
/// +-1 GB), colour and flags.
pub const Meta = packed struct(u32) {
    desc_off: i25,
    state: State,
    flags: u5,
};

/// Embedded in every cycle-capable cell. 36 bytes on 64-bit targets (24 bytes on 32-bit),
/// alignment 4, so that a cell's 32-bit count in front of it stays 4-byte aligned.
pub const Hdr = extern struct {
    prev: *Hdr align(4),
    next: *Hdr align(4),
    u: extern union {
        /// Scratch count, meaningful only while the cell is white.
        refs: u32,
        /// Next cell on the grey stack, while F_STACKED.
        work: ?*Hdr align(4),
    },
    /// Number of the structure record the cell points at (follow `parent`
    /// for the root); 0: the cell is on its own.
    st: u32,
    meta: Meta,
    /// Low 32 bits of the allocation sequence number (see Gc.setBirth/getBirth).
    age: u32,

    pub inline fn desc(h: *const Hdr) *const Desc {
        const addr: usize = @bitCast(@as(isize, @bitCast(@intFromPtr(&anchor))) + @as(isize, h.meta.desc_off) * desc_align);
        return @ptrFromInt(addr);
    }
};

comptime {
    assert(@sizeOf(Hdr) == 3 * @sizeOf(*Hdr) + 12 and @alignOf(Hdr) == 4);
    assert(@alignOf(Desc) == desc_align and @alignOf(@TypeOf(anchor)) == 1);
}

/// Structure records live in chunks that never move; a cell names its record
/// by number.
const chunk_bits = 6;
const chunk_len = 1 << chunk_bits;

pub const Desc = struct {
    /// (the alignment of this field is what aligns every descriptor)
    rc_offset: isize align(desc_align),
    trace: *const fn (cell: *Hdr, v: *Visitor) void,
    release_outside: *const fn (cell: *Hdr, ctx: ?*anyopaque) void,
    free: *const fn (cell: *Hdr, ctx: ?*anyopaque) void,
    finalize: *const fn (cell: *Hdr, ctx: ?*anyopaque) void,
};

/// A set of cells joined by references. Records form a union-find forest;
/// only a root (parent == null) carries counts and a ring.
pub const Structure = struct {
    /// Its number (1-based); survives recycling.
    index: u32 = 0,
    parent: ?*Structure = null,
    ring: Hdr = undefined,
    /// References to members that are not held in a member's field.
    ext: usize = 0,
    members: usize = 0,
    /// Cells whose `st` is this record + records whose parent it is + one
    /// while it is being checked.
    refs: usize = 0,
    /// Cells that joined since it became dirty.
    grow: usize = 0,
    /// Checks in a row that found nothing dead (at most 6). Each one doubles
    /// the growth the next check waits for.
    quiet: std.math.Log2Int(usize) = 0,
    due: u64 = 0,
    dirty: bool = false,
    dead: bool = false,
    /// Dying: 1 = releasing what the cells hold outside, 2 = freeing them.
    pass: u8 = 0,
    /// Dying, first pass: the sum of the cells' counts and the number of
    /// references they hold to each other. The two must be equal, or some
    /// reference to a cell of this structure comes from outside it.
    v_sum: usize = 0,
    v_edges: usize = 0,
    /// The member whose count field must be read as zero (its last
    /// reference went with the release that killed the structure).
    zeroed: ?*const Hdr = null,
    cursor: *Hdr = undefined,
    stamp: u64 = 0,
    all_prev: *Structure = undefined,
    all_next: *Structure = undefined,
    /// Dirty list while alive and dirty, dying queue while dead.
    q_prev: *Structure = undefined,
    q_next: *Structure = undefined,
    free_next: ?*Structure = null,
};

/// Before a dead structure's cells are freed, check that every reference to
/// them came from one of them (see dyingUnit). This is what turns a store,
/// an overwrite or a move that the generated code reported wrongly into a
/// panic with a message instead of freed memory in use. It costs one add per
/// cell and one per reference between them: 6 to 10% where short-lived
/// cycles are all a program does, nothing where no structure dies.
///
/// A build-time switch, because a test at run time costs most of what the
/// check does. On in every build mode unless the program's root file says
/// `pub const sgc_check_deaths = false;`.
pub const check_deaths: bool = if (@hasDecl(root, "sgc_check_deaths")) root.sgc_check_deaths else true;

/// True for a cell that is going away together with the cell whose
/// release_outside is running.
pub fn isGarbage(h: *const Hdr) bool {
    if (tl.sweeping and h.meta.state == .white) return true;
    if (h.st == 0) return false;
    var s = tl.the_gc.?.rec(h.st);
    while (s.parent) |p| s = p;
    if (!s.dead) return false;
    // (a cell the sweep had already taken out is on neither side of the sum)
    if (check_deaths and tl.dying_now == s and h.meta.flags & F_RELEASED == 0) s.v_edges += 1;
    return true;
}

/// True while the collector holds a count of its own on the cell.
pub inline fn isPinned(h: *const Hdr) bool {
    return h.meta.flags & F_STACKED != 0;
}

pub const Visitor = struct {
    gc: *Gc,
    op: enum { close, discover, mark, detach, unlink, count, count_in, count_dead_in, flag },
    x: *Structure = undefined,
    n: usize = 0,
    /// flag: the cell whose reachability is asked about, the work stack.
    target: *const Hdr = undefined,
    top: ?*Hdr = null,

    pub inline fn visit(v: *Visitor, child: *Hdr) void {
        // (a cell shared between threads is outside every thread's collector: never a member,
        // never flagged or counted; a cycle through it is not collected)
        if (isShared(child)) return;
        switch (v.op) {
            .close => v.gc.closeChild(child, v.x),
            .discover => v.gc.discoverChild(child),
            .mark => if (child.meta.state == .white) v.gc.makeGrey(child),
            // a member is leaving on its own: its edges into the structure
            // become outside references (until they are released)
            .detach => if (child.st != 0 and v.gc.root(child) == v.x) {
                v.x.ext += 1;
            },
            // the same for a garbage cell, whose edges to other garbage die
            // silently
            .unlink => if (child.meta.state != .white and child.st != 0 and v.gc.root(child) == v.x) {
                v.x.ext += 1;
            },
            // rule (C): flag what a cell reaches outside structures
            .flag => {
                if (child == v.target) v.n += 1;
                if (child.st == 0 and child.meta.flags & F_TARGET == 0) {
                    child.meta.flags |= F_TARGET;
                    // a cell on its own does not use `next`
                    child.next = if (v.top) |t| t else child;
                    v.top = child;
                    v.gc.counters.flagged_by_walk += 1;
                }
            },
            // how many children / edges into one structure
            .count => v.n += 1,
            // (cells the sweep has taken out of the ring are not counted
            // on either side)
            .count_in => if (child.st != 0 and child.meta.flags & F_RELEASED == 0 and v.gc.root(child) == v.x) {
                v.n += 1;
            },
            // edges of a swept cell that it did NOT release and that still
            // show in a ring cell's count: those to dead cells not swept yet
            .count_dead_in => if (child.st != 0 and child.meta.state == .white and
                child.meta.flags & F_RELEASED == 0 and v.gc.root(child) == v.x)
            {
                v.n += 1;
            },
        }
    }
};

pub const Config = struct {
    /// false: tick() starts no check (step() and collectAll() still work,
    /// and structure counts always do).
    auto: bool = true,
    /// A dirty structure is checked when the cells that joined it since it
    /// became dirty reach 1/check_growth of its size (at least check_min)...
    check_growth: usize = 4,
    check_min: usize = 64,
    /// ... or, as a backstop for a structure that only shrinks, once
    /// max(check_wait, check_factor * its cells) allocations have passed.
    check_wait: usize = 1000,
    check_factor: usize = 8,
    /// A check that finds nothing dead doubles the growth the structure's
    /// next check waits for (up to 64 times); one that finds something
    /// resets it. A structure that keeps changing without ever holding a
    /// dead piece (a queue owned by a cell in a cycle) is then checked ever
    /// more rarely.
    check_backoff: bool = true,
    /// Units of a local check per tick(). `unlimited`: a check runs to
    /// completion.
    pace: usize = 1024,
    /// Cells of dead structures released / freed per tick() or step(), and
    /// queued single cells (below) finalized per tick() or step().
    /// `unlimited`: a dead structure is freed at once, inside the release
    /// that killed it, and a cell whose count reaches zero is dropped
    /// recursively at once.
    free_budget: usize = unlimited,
    /// Only with a finite free_budget, for cells that die on their own (the
    /// count of the cell reached zero, not the count of its structure): how
    /// many cells ONE drop by the mutator frees at once. What is over waits
    /// in a queue, and credit a later drop does not use finalizes cells that
    /// are waiting. 0: every such cell is queued.
    /// A dead structure of at most this many cells is also freed on the
    /// spot instead of being queued.
    free_now: usize = 0,
    /// Never use more structure records than this (64 are built in; more
    /// come from the allocator, 64 at a time). When there is no record to
    /// be had, for this reason or because the allocator has none, cells
    /// that would have started a structure join an existing one.
    max_records: usize = unlimited,
};

pub const Counters = struct {
    /// Local checks completed.
    runs: u64 = 0,
    full_runs: u64 = 0,
    traced: u64 = 0,
    /// Cells freed by local checks.
    freed: u64 = 0,
    /// Cells freed because their structure's count reached zero.
    freed_by_count: u64 = 0,
    units: u64 = 0,
    max_units_per_step: u64 = 0,
    /// Queued single cells finalized, cells a drop freed at once under a
    /// finite free_budget, and queued cells such drops paid for.
    zombies_finalized: u64 = 0,
    freed_now: u64 = 0,
    zombies_paid_by_drops: u64 = 0,
    suppressed: u64 = 0,
    structures: u64 = 0,
    merges: u64 = 0,
    joined: u64 = 0,
    /// Stores ignored by rule (A) / by rule (B) / by rule (C), and cells
    /// flagged by the walks of rule (C).
    stores_ignored: u64 = 0,
    stores_ignored_leaf: u64 = 0,
    stores_ignored_built: u64 = 0,
    flagged_by_walk: u64 = 0,
    /// A structure record could not be allocated and cells joined an
    /// existing structure instead.
    record_fallbacks: u64 = 0,
    ext_corrected: u64 = 0,
    checks_aborted: u64 = 0,
    died_pinned: u64 = 0,
};

pub const Phase = enum { idle, init, discover, mark, sweep, free };

pub const Gc = struct {
    cfg: Config,
    ctx: ?*anyopaque,
    records: std.mem.Allocator,
    counters: Counters = .{},

    /// True from the start of a check until its mark is done.
    barrier_on: bool = false,
    /// A check is active or dead structures are waiting.
    busy: bool = false,
    phase: Phase = .idle,
    no_collect: u32 = 0,
    /// > 0 while the collector itself runs drop code.
    in_collector: u32 = 0,
    /// Finite free_budget only. free_depth > 0: drop code is running under
    /// the collector's control (a mutator drop it is metering, or its own).
    /// free_credit: cells that drop may still free at once; always 0 when
    /// free_depth is 0.
    free_depth: u32 = 0,
    free_credit: usize = 0,
    n_zombies: usize = 0,

    /// Allocations of cycle-capable cells so far: the clock for ages (64
    /// bits, so it does not wrap) and for when checks are due.
    allocs: u64 = 0,
    next_check: u64 = std.math.maxInt(u64),
    n_dirty: usize = 0,
    n_dying: usize = 0,
    /// Live structures, and cells of dead structures not yet freed.
    n_live: usize = 0,
    dying_cells: usize = 0,
    epoch: u64 = 0,

    /// The structure being checked (a root), null when idle or when it died.
    check: ?*Structure = null,
    cursor: *Hdr = undefined,
    grey_top: ?*Hdr = null,
    n_passed: usize = 0,
    run_freed: usize = 0,
    /// Something changed in the checked structure while it was checked.
    mutated: bool = false,
    /// Another structure was merged into the checked one during the check;
    /// its cells were not all looked at, so it is checked again later.
    check_merged: bool = false,
    ext_sum: usize = 0,

    all: Structure = .{},
    dirty: Structure = .{},
    dying: Structure = .{},
    garbage: Hdr = undefined,
    /// Cells with count zero waiting to be finalized (last in, first out).
    zombies: Hdr = undefined,
    free_records: ?*Structure = null,
    /// chunks[i] holds records i * chunk_len + 1 ...; n_records were handed out.
    /// The first chunk and the first table are part of the collector, so the
    /// first 64 structures need no allocation at all.
    chunks: [][*]Structure = &.{},
    n_chunks: usize = 0,
    n_records: u32 = 0,
    table0: [8][*]Structure = undefined,
    chunk0: [chunk_len]Structure = undefined,

    // =====================================================================
    // setup
    // =====================================================================

    pub fn init(gc: *Gc, cfg: Config, ctx: ?*anyopaque, records: std.mem.Allocator) void {
        gc.* = .{ .cfg = cfg, .ctx = ctx, .records = records };
        gc.all.all_prev = &gc.all;
        gc.all.all_next = &gc.all;
        gc.dirty.q_prev = &gc.dirty;
        gc.dirty.q_next = &gc.dirty;
        gc.dying.q_prev = &gc.dying;
        gc.dying.q_next = &gc.dying;
        headInit(&gc.garbage);
        headInit(&gc.zombies);
        gc.cursor = &gc.garbage;
        gc.table0[0] = &gc.chunk0;
        gc.chunks = &gc.table0;
        gc.n_chunks = 1;
        tl.the_gc = gc;
    }

    /// Give the allocated structure records back. Nothing may be live.
    pub fn deinit(gc: *Gc) void {
        for (gc.chunks[1..gc.n_chunks]) |c| gc.records.free(c[0..chunk_len]);
        if (gc.chunks.ptr != &gc.table0) gc.records.free(gc.chunks);
        gc.chunks = &gc.table0;
        gc.n_chunks = 1;
        gc.n_records = 0;
        gc.free_records = null;
    }

    /// A cell on its own that has never been in a structure keeps its full
    /// 64-bit allocation number across `prev` (high 32 bits on 32-bit targets,
    /// or all 64 bits on 64-bit) and `age` (low 32 bits). That is the only
    /// cell whose exact age rule (A) needs: for the other end of the store 32
    /// bits are enough, because taking a cell for younger than it is only
    /// makes the rule ignore less.
    inline fn setBirth(h: *Hdr, seq: u64) void {
        if (@sizeOf(*Hdr) == 8) {
            @as(*align(4) u64, @ptrCast(&h.prev)).* = seq;
        } else {
            @as(*u32, @ptrCast(&h.prev)).* = @intCast(seq >> 32);
        }
    }

    inline fn getBirth(h: *const Hdr) u64 {
        if (@sizeOf(*Hdr) == 8) {
            return @as(*align(4) const u64, @ptrCast(&h.prev)).*;
        } else {
            return (@as(u64, @as(*const u32, @ptrCast(&h.prev)).*) << 32) | h.age;
        }
    }

    /// The record with number `n` (1-based).
    pub inline fn rec(gc: *const Gc, n: u32) *Structure {
        const i = n - 1;
        return &gc.chunks[i >> chunk_bits][i & (chunk_len - 1)];
    }

    pub fn configure(gc: *Gc, cfg: Config) void {
        gc.cfg = cfg;
        gc.recomputeNext();
    }

    pub fn isEmpty(gc: *const Gc) bool {
        return gc.phase == .idle and gc.all.all_next == &gc.all and gc.dying.q_next == &gc.dying and
            gc.garbage.next == &gc.garbage and gc.n_dirty == 0 and gc.n_zombies == 0;
    }

    pub inline fn noCollectEnter(gc: *Gc) void {
        gc.no_collect += 1;
    }
    pub inline fn noCollectLeave(gc: *Gc) void {
        assert(gc.no_collect > 0);
        gc.no_collect -= 1;
    }

    /// Header of a new cell.
    /// `leaf`: the cell is being constructed with no cycle-capable child
    /// (every traced field null). Saying false is always safe.
    pub inline fn hdr(gc: *Gc, d: *const Desc, leaf: bool) Hdr {
        const off = @as(isize, @bitCast(@intFromPtr(d))) - @as(isize, @bitCast(@intFromPtr(&anchor)));
        var h: Hdr = .{
            .prev = undefined,
            .next = undefined,
            .u = .{ .work = null },
            .st = 0,
            .meta = .{ .desc_off = @intCast(@divExact(off, desc_align)), .state = .idle, .flags = if (leaf) F_LEAF else 0 },
            .age = @truncate(gc.allocs),
        };
        setBirth(&h, gc.allocs);
        return h;
    }

    // =====================================================================
    // mutator hooks
    // =====================================================================

    pub inline fn tick(gc: *Gc) void {
        if (gc.tickDue()) gc.tickSlow();
    }
    pub inline fn tickDue(gc: *Gc) bool {
        gc.allocs += 1;
        return gc.busy or gc.allocs >= gc.next_check;
    }
    pub noinline fn tickSlow(gc: *Gc) void {
        if (gc.no_collect > 0) {
            gc.counters.suppressed += 1;
            return;
        }
        gc.pump(gc.cfg.pace);
    }

    pub inline fn onRetain(gc: *Gc, h: *Hdr) void {
        if (h.st != 0) gc.retained(h);
    }
    noinline fn retained(gc: *Gc, h: *Hdr) void {
        gc.root(h).ext += 1;
        if (gc.phase != .idle) gc.mutated = true;
        if (gc.barrier_on) gc.touch(h);
    }

    pub inline fn onRelease(gc: *Gc, h: *Hdr) void {
        if (h.st != 0) gc.released(h);
    }
    noinline fn released(gc: *Gc, h: *Hdr) void {
        const r = gc.root(h);
        r.ext -= 1;
        if (gc.phase != .idle) gc.mutated = true;
        if (r.ext == 0) return gc.die(r);
        // It lost a reference and lives on: a piece may have come loose.
        // (Not when the reference came from a dead piece of the structure
        // that the check in progress is sweeping out: that check has just
        // looked at all of it.)
        if (!r.dirty and !(tl.sweeping and gc.check == r)) gc.makeDirty(r);
        if (gc.barrier_on) gc.touch(h);
    }

    /// The last reference to the cell is gone.
    pub inline fn onZero(gc: *Gc, h: *Hdr) bool {
        if (h.st == 0) {
            if (gc.cfg.free_budget == unlimited) return false;
            // inside a metered drop that still has credit
            if (gc.free_credit != 0) {
                gc.free_credit -= 1;
                return false;
            }
            return gc.meter(h);
        }
        return gc.zeroed(h);
    }
    noinline fn zeroed(gc: *Gc, h: *Hdr) bool {
        const r = gc.root(h);
        r.ext -= 1;
        if (gc.phase != .idle) gc.mutated = true;
        if (r.ext == 0) {
            gc.dieChecked(r, h);
            return true;
        }
        gc.detach(h, r);
        if (gc.cfg.free_budget == unlimited) return false;
        if (gc.free_credit != 0) {
            gc.free_credit -= 1;
            return false;
        }
        return gc.meter(h);
    }

    /// A cell on its own has count zero, the free budget is finite and there
    /// is no credit. If this is the first cell of a drop by the mutator, the
    /// collector runs the drop itself (so that it knows where the drop ends)
    /// with cfg.free_now cells of credit; otherwise the cell waits.
    noinline fn meter(gc: *Gc, h: *Hdr) bool {
        if (gc.free_depth == 0 and gc.cfg.free_now != 0) {
            gc.free_depth = 1;
            gc.free_credit = gc.cfg.free_now - 1;
            h.desc().finalize(h, gc.ctx);
            const left = gc.free_credit;
            gc.free_credit = 0;
            gc.counters.freed_now += gc.cfg.free_now - left;
            if (left != 0 and gc.n_zombies != 0 and gc.no_collect == 0) {
                const before = gc.counters.zombies_finalized;
                gc.finalizeZombies(left);
                gc.counters.zombies_paid_by_drops += gc.counters.zombies_finalized - before;
            }
            gc.free_depth = 0;
            return true;
        }
        // Its fields keep their references until it is finalized. A check in
        // progress may already have taken its edges off the cells it points
        // at: they are in use.
        if (gc.barrier_on) {
            var v: Visitor = .{ .gc = gc, .op = .mark };
            gc.counters.traced += 1;
            h.desc().trace(h, &v);
        }
        h.prev = &gc.zombies;
        h.next = gc.zombies.next;
        gc.zombies.next.prev = h;
        gc.zombies.next = h;
        gc.n_zombies += 1;
        gc.busy = true;
        return true;
    }

    fn finalizeZombies(gc: *Gc, max: usize) void {
        // No credit in here: what a zombie releases to zero queues up, so
        // finalizing never recurses and costs one cell each.
        assert(gc.free_credit == 0);
        gc.free_depth += 1;
        var n: usize = 0;
        while (n < max and gc.zombies.next != &gc.zombies) : (n += 1) {
            const z = gc.zombies.next;
            z.prev.next = z.next;
            z.next.prev = z.prev;
            gc.n_zombies -= 1;
            gc.counters.zombies_finalized += 1;
            z.desc().finalize(z, gc.ctx);
        }
        gc.free_depth -= 1;
        gc.busy = gc.pending();
    }

    inline fn pending(gc: *const Gc) bool {
        return gc.phase != .idle or gc.dying.q_next != &gc.dying or gc.n_zombies != 0;
    }

    /// A unique cell is taken apart without onZero. Its fields still hold
    /// their references.
    pub inline fn onFree(gc: *Gc, h: *Hdr) void {
        if (h.st != 0) gc.unpacked(h);
    }
    noinline fn unpacked(gc: *Gc, h: *Hdr) void {
        assert(h.meta.flags & F_STACKED == 0); // a pinned cell is not unique
        const r = gc.root(h);
        r.refs += 1; // keep the record over the detach
        gc.detach(h, r);
        if (gc.phase != .idle) gc.mutated = true;
        r.ext -= 1; // the one reference the cell itself had
        if (r.ext == 0 and r.members != 0) gc.die(r);
        gc.unref(r);
    }

    // ---- a value moved to another thread whole (`Fable.Core.Zig.Iso`, Verona's region
    // migration). Its cells leave this collector at `pack` and join the receiving thread's at
    // `unpack`. A cell in no structure is flagged as a target: the rule (A) test, which compares
    // births on this thread's clock, is never applied with it as the owner, and what it reaches
    // (cells of the same value, all flagged, or shared ones) keeps "a flagged cell reaches only
    // flagged cells outside structures". A structure moves whole: its members are detached here
    // and joined to a new structure there, whose count of references from outside is worked
    // out from scratch (`outsideRefs`), so it dies when the receiver lets go of the last. ----

    /// Can `h`'s structure move (not being checked, not dying, no member pinned by a walk)?
    pub fn canMove(gc: *Gc, h: *Hdr) bool {
        if (h.meta.flags & F_STACKED != 0) return false;
        if (h.st == 0) return true;
        const r = gc.root(h);
        if (r.dead or gc.check == r) return false;
        return true;
    }

    /// The structure `h` is a member of, as a key, and how many members it has (h.st != 0)
    pub fn structureOf(gc: *Gc, h: *Hdr) struct { key: usize, members: usize } {
        const r = gc.root(h);
        return .{ .key = @intFromPtr(r), .members = r.members };
    }

    /// A cell in no structure, moving: flagged (see above)
    pub fn moveLoose(h: *Hdr) void {
        h.meta.flags |= F_TARGET;
    }

    /// `h`'s structure leaves this collector: each member detached (the record is recycled
    /// with the last one)
    pub fn moveOut(gc: *Gc, h: *Hdr) void {
        const r = gc.root(h);
        r.refs += 1; // (kept over the detaches)
        while (r.ring.next != &r.ring) gc.detach(r.ring.next, r);
        gc.unref(r);
    }

    /// Cells that were one structure join this collector as one, dirty (see above)
    pub fn moveIn(gc: *Gc, members: []const *Hdr) void {
        if (members.len == 0) return;
        const r = gc.newRecord();
        for (members) |h| {
            h.meta.flags = 0;
            h.meta.state = .idle;
            gc.join(h, r);
        }
        // (the references from outside counted exactly: dropping the last one frees the
        // structure at once, as for one built here)
        r.ext = @intCast(gc.outsideRefs(r, null));
    }

    pub inline fn onStore(gc: *Gc, owner: *Hdr, child: *Hdr) void {
        if (isShared(child)) return;
        if (owner.st != 0) return gc.stored(owner, child);
        // The leaf bit only matters while a cell is in no structure.
        const flags = owner.meta.flags;
        if (flags & F_LEAF != 0) owner.meta.flags = flags & ~F_LEAF; // it has a child now
        // (A) A cell in no structure that is made to point at an older cell
        // cannot be closing a cycle (unless something was made to point at
        // it while rule (B) was looking away).
        if (flags & F_TARGET == 0) {
            // The child's allocation number from its low 32 bits: exact if it
            // was allocated within the last 2^32 allocations, too high (too
            // young) otherwise, which only makes this test fail.
            const now: u32 = @truncate(gc.allocs);
            const child_birth = gc.allocs - (now -% child.age);
            if (child_birth < getBirth(owner)) {
                gc.counters.stores_ignored += 1;
                return;
            }
        }
        gc.stored(owner, child);
    }

    pub inline fn onUnstore(gc: *Gc, owner: *Hdr, old: *Hdr) void {
        if (isShared(old)) return;
        if (owner.st == 0 or old.st == 0) return;
        gc.unstored(owner, old);
    }
    noinline fn unstored(gc: *Gc, owner: *Hdr, old: *Hdr) void {
        const r = gc.root(owner);
        if (gc.root(old) == r) {
            r.ext += 1;
            if (gc.phase != .idle) gc.mutated = true;
        }
    }

    pub inline fn onMoveOut(gc: *Gc, child: *Hdr) void {
        if (gc.barrier_on and !isShared(child)) gc.touch(child);
    }

    pub inline fn step(gc: *Gc, budget: usize) bool {
        if (!(gc.busy or gc.allocs >= gc.next_check)) return false;
        return gc.stepSlow(budget);
    }
    noinline fn stepSlow(gc: *Gc, budget: usize) bool {
        if (gc.no_collect > 0) {
            gc.counters.suppressed += 1;
            return false;
        }
        gc.pump(budget);
        return gc.busy;
    }

    /// Start a check by hand: of the first dirty structure, or (full) of the
    /// first structure whatever its state. For tests.
    pub fn startRun(gc: *Gc, full: bool) bool {
        if (gc.phase != .idle or gc.no_collect > 0) return false;
        const s = if (full) gc.all.all_next else gc.dirty.q_next;
        if (s == &gc.all or s == &gc.dirty) return false;
        gc.begin(s);
        return true;
    }

    /// Everything now: finish what is in progress, then check every
    /// structure until a round frees nothing.
    pub fn collectAll(gc: *Gc) usize {
        if (gc.no_collect > 0) {
            gc.counters.suppressed += 1;
            return 0;
        }
        const before = gc.counters.freed + gc.counters.freed_by_count;
        while (true) {
            const round = gc.counters.freed + gc.counters.freed_by_count;
            gc.checkEverything();
            if (gc.counters.freed + gc.counters.freed_by_count == round) break;
        }
        return @intCast(gc.counters.freed + gc.counters.freed_by_count - before);
    }

    /// One round: finish what is in progress, check every structure once.
    pub fn collectOnce(gc: *Gc) usize {
        if (gc.no_collect > 0) {
            gc.counters.suppressed += 1;
            return 0;
        }
        const before = gc.counters.freed + gc.counters.freed_by_count;
        gc.checkEverything();
        return @intCast(gc.counters.freed + gc.counters.freed_by_count - before);
    }

    /// For a caller that wants a full round in bounded steps: startRound(),
    /// then startNextInRound() each time the collector is idle, until it
    /// returns false.
    pub fn startRound(gc: *Gc) void {
        gc.epoch += 1;
    }
    pub fn startNextInRound(gc: *Gc) bool {
        if (gc.phase != .idle or gc.no_collect > 0) return false;
        const s = gc.all.all_next;
        if (s == &gc.all or s.stamp == gc.epoch) return false;
        s.stamp = gc.epoch;
        allUnlink(s);
        gc.allAppend(s);
        gc.begin(s);
        return true;
    }

    /// Everything that is only waiting to be freed.
    fn drain(gc: *Gc) void {
        while (gc.n_zombies != 0 or gc.dying.q_next != &gc.dying) {
            gc.finalizeZombies(unlimited);
            gc.freeDying(unlimited);
        }
    }

    fn checkEverything(gc: *Gc) void {
        gc.work(unlimited);
        gc.drain();
        gc.epoch += 1;
        while (true) {
            const s = gc.all.all_next;
            if (s == &gc.all or s.stamp == gc.epoch) break;
            s.stamp = gc.epoch;
            // to the back, so the head is always one not yet looked at
            allUnlink(s);
            gc.allAppend(s);
            gc.begin(s);
            gc.work(unlimited);
            gc.drain();
        }
    }

    // =====================================================================
    // lists and records
    // =====================================================================

    inline fn headInit(h: *Hdr) void {
        h.* = .{ .prev = h, .next = h, .u = .{ .work = null }, .st = 0, .meta = .{ .desc_off = 0, .state = .sentinel, .flags = 0 }, .age = 0 };
    }

    inline fn append(list: *Hdr, h: *Hdr) void {
        const last = list.prev;
        h.prev = last;
        h.next = list;
        last.next = h;
        list.prev = h;
    }

    /// Take a cell out of the list it is in. The check's cursor and a dying
    /// structure's cursor must never be left on it.
    inline fn unlink(gc: *Gc, h: *Hdr) void {
        if (gc.cursor == h) gc.cursor = h.next;
        h.prev.next = h.next;
        h.next.prev = h.prev;
    }

    /// Move every cell of `from` to the end of `to`. O(1).
    fn splice(from: *Hdr, to: *Hdr) void {
        if (from.next == from) return;
        const first = from.next;
        const last = from.prev;
        first.prev = to.prev;
        to.prev.next = first;
        last.next = to;
        to.prev = last;
        from.prev = from;
        from.next = from;
    }

    inline fn allUnlink(s: *Structure) void {
        s.all_prev.all_next = s.all_next;
        s.all_next.all_prev = s.all_prev;
    }
    inline fn allAppend(gc: *Gc, s: *Structure) void {
        s.all_prev = gc.all.all_prev;
        s.all_next = &gc.all;
        gc.all.all_prev.all_next = s;
        gc.all.all_prev = s;
    }
    inline fn qUnlink(s: *Structure) void {
        s.q_prev.q_next = s.q_next;
        s.q_next.q_prev = s.q_prev;
    }
    inline fn qAppend(head: *Structure, s: *Structure) void {
        s.q_prev = head.q_prev;
        s.q_next = head;
        head.q_prev.q_next = s;
        head.q_prev = s;
    }

    fn newRecord(gc: *Gc) *Structure {
        const s = if (gc.free_records) |f| blk: {
            gc.free_records = f.free_next;
            break :blk f;
        } else blk: {
            if (gc.n_records >= gc.cfg.max_records) return gc.borrowRecord();
            if (gc.n_records == gc.n_chunks * chunk_len and !gc.addChunk()) return gc.borrowRecord();
            gc.n_records += 1;
            const fresh = gc.rec(gc.n_records);
            fresh.index = gc.n_records;
            break :blk fresh;
        };
        const index = s.index;
        s.* = .{};
        s.index = index;
        headInit(&s.ring);
        gc.allAppend(s);
        gc.counters.structures += 1;
        gc.n_live += 1;
        return s;
    }

    /// Room for 64 more records. false: the allocator has none.
    noinline fn addChunk(gc: *Gc) bool {
        if (gc.n_chunks == gc.chunks.len) {
            const bigger = gc.records.alloc([*]Structure, gc.chunks.len * 2) catch return false;
            @memcpy(bigger[0..gc.n_chunks], gc.chunks[0..gc.n_chunks]);
            if (gc.chunks.ptr != &gc.table0) gc.records.free(gc.chunks);
            gc.chunks = bigger;
        }
        const chunk = gc.records.alloc(Structure, chunk_len) catch return false;
        gc.chunks[gc.n_chunks] = chunk.ptr;
        gc.n_chunks += 1;
        return true;
    }

    /// No record can be had. The cells that wanted a structure of their own
    /// join one that exists: putting unrelated cells in one structure is
    /// always sound (its count is the sum, it dies later, and what is dead in
    /// it meanwhile is found by its check). If none is alive, the dead ones
    /// waiting to be freed are freed now, which gives their records back.
    noinline fn borrowRecord(gc: *Gc) *Structure {
        gc.counters.record_fallbacks += 1;
        if (gc.all.all_next != &gc.all) return gc.all.all_next;
        gc.drain();
        if (gc.all.all_next != &gc.all) return gc.all.all_next;
        // Every record was dead and is free now.
        const f = gc.free_records.?;
        gc.free_records = f.free_next;
        const index = f.index;
        f.* = .{};
        f.index = index;
        headInit(&f.ring);
        gc.allAppend(f);
        gc.counters.structures += 1;
        gc.n_live += 1;
        return f;
    }

    /// One reference to the record is gone. A record nothing points at is
    /// recycled, which takes a reference off its parent.
    fn unref(gc: *Gc, s: *Structure) void {
        var cur = s;
        while (true) {
            cur.refs -= 1;
            if (cur.refs != 0) return;
            const parent = cur.parent;
            if (parent == null and !cur.dead) {
                assert(cur.members == 0);
                gc.clean(cur);
                allUnlink(cur);
                gc.n_live -= 1;
            }
            cur.free_next = gc.free_records;
            gc.free_records = cur;
            cur = parent orelse return;
        }
    }

    pub inline fn root(gc: *Gc, h: *Hdr) *Structure {
        const s = gc.rec(h.st);
        if (s.parent == null) return s;
        return gc.rootSlow(h);
    }
    noinline fn rootSlow(gc: *Gc, h: *Hdr) *Structure {
        const old = gc.rec(h.st);
        var r = old;
        while (r.parent) |p| r = p;
        h.st = r.index;
        r.refs += 1;
        gc.unref(old);
        return r;
    }

    inline fn rcPtr(h: *const Hdr) *u32 {
        const addr: usize = @bitCast(@as(isize, @bitCast(@intFromPtr(h))) + h.desc().rc_offset);
        return @ptrFromInt(addr);
    }

    // =====================================================================
    // membership
    // =====================================================================

    inline fn grown(gc: *const Gc, s: *const Structure) bool {
        return s.grow >= gc.cfg.check_min and s.grow *| gc.cfg.check_growth >= s.members << s.quiet;
    }

    fn makeDirty(gc: *Gc, s: *Structure) void {
        s.dirty = true;
        s.grow = 0;
        s.due = gc.allocs +| @as(u64, @max(gc.cfg.check_wait, gc.cfg.check_factor *| s.members));
        qAppend(&gc.dirty, s);
        gc.n_dirty += 1;
        if (gc.cfg.auto and s.due < gc.next_check) gc.next_check = s.due;
    }

    fn clean(gc: *Gc, s: *Structure) void {
        if (!s.dirty) return;
        s.dirty = false;
        qUnlink(s);
        gc.n_dirty -= 1;
    }

    fn recomputeNext(gc: *Gc) void {
        var next: u64 = std.math.maxInt(u64);
        if (gc.cfg.auto) {
            var s = gc.dirty.q_next;
            while (s != &gc.dirty) : (s = s.q_next) {
                next = @min(next, if (gc.grown(s)) gc.allocs else s.due);
            }
        }
        gc.next_check = next;
    }

    fn join(gc: *Gc, h: *Hdr, r: *Structure) void {
        h.st = r.index;
        r.refs += 1;
        r.members += 1;
        r.ext += rcPtr(h).*; // all of them from outside, until its edges are looked at
        append(&r.ring, h);
        gc.counters.joined += 1;
        r.grow += 1;
        if (r.dirty and gc.cfg.auto and gc.grown(r)) gc.next_check = gc.allocs;
    }

    /// Merge two different live roots; returns the survivor.
    fn merge(gc: *Gc, a: *Structure, b: *Structure) *Structure {
        const big = if (a.members >= b.members) a else b;
        const small = if (big == a) b else a;
        // The check's cursor must stay on a cell or on the survivor's head.
        if (gc.cursor == &small.ring) gc.cursor = &big.ring;
        splice(&small.ring, &big.ring);
        small.parent = big;
        big.refs += 1;
        big.members += small.members;
        big.ext += small.ext;
        big.grow += small.grow;
        big.quiet = @min(big.quiet, small.quiet);
        small.members = 0;
        small.ext = 0;
        if (small.dirty) {
            const due = small.due;
            gc.clean(small);
            if (!big.dirty) {
                const g = big.grow;
                gc.makeDirty(big);
                big.grow = g;
            }
            big.due = @min(big.due, due);
            if (gc.cfg.auto and big.due < gc.next_check) gc.next_check = big.due;
        }
        allUnlink(small);
        gc.n_live -= 1;
        if (gc.check == small) {
            // the check goes on, on the merged ring
            big.refs += 1;
            gc.check = big;
            gc.unref(small);
        }
        if (gc.check == big) {
            gc.mutated = true;
            gc.check_merged = true;
        }
        gc.counters.merges += 1;
        return big;
    }

    /// One traced child of a cell that has just joined `r`.
    fn closeChild(gc: *Gc, child: *Hdr, r: *Structure) void {
        if (child.st == 0) {
            gc.join(child, r);
        } else if (gc.root(child) != r) {
            return; // lives in another structure: an outside reference there
        }
        r.ext -= 1;
    }

    /// Flag `from` and every cell it reaches through cells that are in no
    /// structure. True when `target` is one of them. One trace per cell that
    /// was not flagged yet; no recursion (the work stack runs through the
    /// unused `next` links).
    ///
    /// It stops as soon as `target` is found. The walk is then unfinished,
    /// which would break "what a flagged cell reaches is flagged", except
    /// that the caller goes on to track the store: `from` joins a structure
    /// and brings along everything it reaches outside structures, which
    /// includes every cell flagged here.
    fn flagReach(gc: *Gc, from: *Hdr, target: *const Hdr) bool {
        var v: Visitor = .{ .gc = gc, .op = .flag, .target = target };
        from.meta.flags |= F_TARGET;
        from.next = from;
        v.top = from;
        gc.counters.flagged_by_walk += 1;
        while (v.top) |c| {
            v.top = if (c.next == c) null else c.next;
            gc.counters.traced += 1;
            c.desc().trace(c, &v);
            if (v.n != 0) return true;
        }
        return false;
    }

    noinline fn stored(gc: *Gc, owner: *Hdr, child: *Hdr) void {
        // (B) A cell on its own is made to point at a leaf that is on its own
        // too: no path leads from the leaf anywhere, so this closes no cycle.
        // The leaf remembers it.
        if (owner.st == 0 and child.st == 0 and child != owner and child.meta.flags & F_LEAF != 0) {
            child.meta.flags |= F_TARGET;
            gc.counters.stores_ignored_leaf += 1;
            return;
        }
        // (C) An unflagged cell on its own is made to point at a cell on its
        // own that cannot reach it.
        if (owner.st == 0 and child.st == 0 and child != owner and owner.meta.flags & F_TARGET == 0) {
            // Flagged already: all it reaches outside structures is flagged,
            // and the owner is not. Otherwise walk what it reaches, flagging.
            if (child.meta.flags & F_TARGET != 0 or !gc.flagReach(child, owner)) {
                gc.counters.stores_ignored_built += 1;
                return;
            }
        }
        const owner_new = owner.st == 0;
        var first_new: ?*Hdr = null;
        if (owner_new and child.st == 0) {
            const s = gc.newRecord();
            gc.join(owner, s);
            if (child != owner) gc.join(child, s);
            first_new = owner;
        } else if (owner_new) {
            gc.join(owner, gc.root(child));
            first_new = owner;
        } else if (child.st == 0) {
            gc.join(child, gc.root(owner));
            first_new = child;
        } else {
            const a = gc.root(owner);
            const b = gc.root(child);
            if (a != b) _ = gc.merge(a, b);
        }
        const r = gc.root(owner);
        // The new edge. A new owner's edges, this one included, are all
        // counted when it is closed.
        if (!owner_new) r.ext -= 1;
        if (first_new) |f| {
            // new cells are appended to the ring, also while this runs
            var v: Visitor = .{ .gc = gc, .op = .close, .x = r };
            var it = f;
            while (it != &r.ring) : (it = it.next) {
                gc.counters.traced += 1;
                it.desc().trace(it, &v);
            }
        }
        assert(r.ext != 0); // somebody is holding `owner`
        if (gc.phase != .idle) gc.mutated = true;
        if (gc.barrier_on) gc.touch(child);
    }

    /// The member `h` is going away on its own. The references it holds into
    /// its structure are about to be released like any others, or to become
    /// the caller's: either way they are not internal any more.
    fn detach(gc: *Gc, h: *Hdr, r: *Structure) void {
        var v: Visitor = .{ .gc = gc, .op = .detach, .x = r };
        gc.counters.traced += 1;
        h.desc().trace(h, &v);
        if (h.meta.flags & F_PASSED != 0) gc.n_passed -= 1;
        gc.unlink(h);
        r.members -= 1;
        h.meta.flags = 0;
        h.meta.state = .idle;
        const s = gc.rec(h.st);
        h.st = 0;
        if (gc.phase != .idle) gc.mutated = true;
        gc.unref(s);
    }

    /// References to members of `r` that are not held in a field of a member,
    /// worked out from scratch (a pin counts as one). `zeroed`: a member whose
    /// count field must be read as zero (its last reference has just gone;
    /// the caller may not have written the zero).
    fn outsideRefs(gc: *Gc, r: *Structure, zeroed_cell: ?*const Hdr) isize {
        var sum: isize = 0;
        var v: Visitor = .{ .gc = gc, .op = .count_in, .x = r };
        var it = r.ring.next;
        var n: usize = 0;
        while (it != &r.ring) : (it = it.next) {
            n += 1;
            if (it != zeroed_cell) sum += rcPtr(it).*;
            it.desc().trace(it, &v);
        }
        assert(n == r.members);
        var internal = v.n;
        if (gc.check == r) {
            // Cells the sweep of the check in progress has taken out of the
            // ring and not freed yet still hold the references they have to
            // the dead cells that are not swept yet.
            var vd: Visitor = .{ .gc = gc, .op = .count_dead_in, .x = r };
            var g = gc.garbage.next;
            while (g != &gc.garbage) : (g = g.next) g.desc().trace(g, &vd);
            internal += vd.n;
        }
        return sum - @as(isize, @intCast(internal));
    }

    /// Check every live structure's count against the graph. For tests and
    /// for debugging generated code: a count that is LOWER than the truth
    /// means a store or an overwrite was not reported (or reported twice),
    /// and would sooner or later free cells that are in use.
    pub fn verify(gc: *Gc) void {
        var s = gc.all.all_next;
        while (s != &gc.all) : (s = s.all_next) {
            const truth = gc.outsideRefs(s, null);
            if (truth < 0 or s.ext < @as(usize, @intCast(truth))) {
                std.debug.panic("sgc: structure {d} counts {d} outside references but its {d} cells have {d}: a store, an overwrite or a move was reported wrongly", .{ s.index, s.ext, s.members, truth });
            }
        }
    }

    /// Nothing outside refers to any cell of `r`.
    fn die(gc: *Gc, r: *Structure) void {
        gc.dieChecked(r, null);
    }

    fn dieChecked(gc: *Gc, r: *Structure, zeroed_cell: ?*const Hdr) void {
        assert(!r.dead and r.members != 0);
        // The count says zero. Whether that is true is checked while the
        // cells release what they hold outside (dyingUnit), before any of
        // them is freed, in every build.
        r.zeroed = zeroed_cell;
        r.v_sum = 0;
        r.v_edges = 0;
        gc.clean(r);
        allUnlink(r);
        gc.n_live -= 1;
        gc.dying_cells += r.members;
        if (gc.check == r) gc.abandonCheck(r);
        r.refs += 1; // the queue's own reference
        r.dead = true;
        r.pass = 1;
        r.cursor = r.ring.next;
        gc.n_dying += 1;
        gc.busy = true;
        if (gc.in_collector == 0 and gc.cfg.free_budget != unlimited and r.members <= gc.cfg.free_now) {
            // Small enough to go on the spot, like a drop of that many
            // single cells: it jumps the queue and is freed now.
            r.q_next = gc.dying.q_next;
            r.q_prev = &gc.dying;
            gc.dying.q_next.q_prev = r;
            gc.dying.q_next = r;
            gc.freeOne(r);
            return;
        }
        qAppend(&gc.dying, r);
        if (gc.cfg.free_budget == unlimited and gc.in_collector == 0) gc.freeDying(unlimited);
    }

    /// Free the dead structure at the head of the queue completely.
    fn freeOne(gc: *Gc, r: *Structure) void {
        assert(gc.dying.q_next == r);
        gc.in_collector += 1;
        gc.free_depth += 1;
        while (gc.dying.q_next == r) gc.dyingUnit();
        gc.free_depth -= 1;
        gc.in_collector -= 1;
        gc.busy = gc.pending();
    }

    /// Release and free cells of dead structures, at most `budget` units
    /// (one unit: one cell in one of the two passes).
    fn freeDying(gc: *Gc, budget: usize) void {
        var n: usize = 0;
        gc.in_collector += 1;
        gc.free_depth += 1;
        while (n < budget and gc.dying.q_next != &gc.dying) : (n += 1) gc.dyingUnit();
        gc.in_collector -= 1;
        gc.free_depth -= 1;
        gc.counters.units += n;
        if (budget != unlimited and n > gc.counters.max_units_per_step) gc.counters.max_units_per_step = n;
        gc.busy = gc.pending();
    }

    /// One unit of work on the dead structure at the head of the queue.
    fn dyingUnit(gc: *Gc) void {
        const d = gc.dying.q_next;
        const c = d.cursor;
        if (c == &d.ring) {
            if (d.pass == 1) {
                // Nothing was freed so far, so every header could be read.
                // Every reference to a cell of the structure must have come
                // from a cell of the structure: if the counts add up to more
                // than the references the cells hold to each other, the
                // structure's count was wrong, and freeing these cells would
                // leave a reference to freed memory somewhere.
                if (check_deaths and d.v_sum != d.v_edges) {
                    std.debug.panic("sgc: structure {d} was about to be freed, but its cells are referenced {d} times and hold {d} references to each other: a store, an overwrite or a move was reported wrongly", .{ d.index, d.v_sum, d.v_edges });
                }
                d.pass = 2;
                d.cursor = d.ring.next;
                return;
            }
            qUnlink(d);
            gc.n_dying -= 1;
            headInit(&d.ring);
            d.members = 0;
            gc.unref(d); // the queue's own reference
            return;
        }
        d.cursor = c.next;
        if (d.pass == 1) {
            if (c.meta.flags & F_RELEASED == 0) {
                // What the cell holds outside its structure. Nothing this
                // releases can lead back here. (isGarbage counts what it
                // holds inside.)
                if (check_deaths) {
                    if (c != d.zeroed) d.v_sum += rcPtr(c).*;
                    tl.dying_now = d;
                }
                c.desc().release_outside(c, gc.ctx);
                if (check_deaths) tl.dying_now = null;
            } else {
                // Swept by the check that was running when the structure
                // died: it has released everything but its references to the
                // cells that were dying with it. Those to cells not swept
                // yet still show in their counts. (Its own count, and the
                // references to it, are left out: other swept cells that
                // referred to it may be freed already.)
                if (check_deaths) {
                    var v: Visitor = .{ .gc = gc, .op = .count_dead_in, .x = d };
                    c.desc().trace(c, &v);
                    d.v_edges += v.n;
                }
            }
        } else {
            const s = gc.rec(c.st);
            c.st = 0;
            gc.dying_cells -|= 1;
            gc.counters.freed_by_count += 1;
            c.desc().free(c, gc.ctx);
            gc.unref(s);
        }
    }

    // =====================================================================
    // the local check
    // =====================================================================

    noinline fn touch(gc: *Gc, h: *Hdr) void {
        gc.mutated = true;
        if (h.meta.state == .white) gc.makeGrey(h);
    }

    /// A white cell is known to be live. It keeps its place in the ring. If
    /// the mark scan has passed it, it goes on the grey stack, pinned: the
    /// collector holds one reference to it until the stack reaches it.
    fn makeGrey(gc: *Gc, h: *Hdr) void {
        h.meta.state = .grey;
        if (h.meta.flags & F_PASSED != 0) {
            h.meta.flags = (h.meta.flags & ~F_PASSED) | F_STACKED;
            gc.n_passed -= 1;
            rcPtr(h).* += 1;
            gc.root(h).ext += 1;
            h.u.work = gc.grey_top;
            gc.grey_top = h;
        }
    }

    inline fn whiten(h: *Hdr) void {
        h.u.refs = rcPtr(h).*;
        h.meta.state = .white;
    }

    fn discoverChild(gc: *Gc, child: *Hdr) void {
        const r = gc.check.?;
        if (child.st == 0) return; // cannot happen while the invariant holds
        if (gc.root(child) != r) {
            // What a member points at in another structure comes in: a cycle
            // may run through both.
            const other = gc.root(child);
            if (other.dead) return;
            _ = gc.merge(r, other);
        }
        if (child.meta.state == .idle) whiten(child);
        if (child.meta.state == .white and child.u.refs > 0) child.u.refs -= 1;
    }

    fn live(gc: *Gc, c: *Hdr) void {
        var v: Visitor = .{ .gc = gc, .op = .mark };
        gc.counters.traced += 1;
        c.desc().trace(c, &v);
        c.meta.state = .idle;
    }

    fn begin(gc: *Gc, s: *Structure) void {
        assert(gc.phase == .idle and !s.dead and s.parent == null);
        assert(gc.grey_top == null and gc.n_passed == 0 and gc.garbage.next == &gc.garbage);
        gc.clean(s);
        s.grow = 0;
        s.refs += 1;
        gc.check = s;
        gc.cursor = s.ring.next;
        gc.phase = .init;
        gc.barrier_on = true;
        gc.busy = true;
        gc.mutated = false;
        gc.check_merged = false;
        gc.ext_sum = 0;
        gc.run_freed = 0;
    }

    /// The structure being checked died: its cells are all dead whatever
    /// their colour. Cells the sweep has already taken out go back into its
    /// ring, to be freed with it (their flag says they are released).
    fn abandonCheck(gc: *Gc, r: *Structure) void {
        assert(gc.grey_top == null); // a pinned cell keeps ext above zero
        splice(&gc.garbage, &r.ring);
        gc.n_passed = 0;
        gc.barrier_on = false;
        gc.phase = .idle;
        gc.cursor = &gc.garbage;
        gc.check = null;
        gc.counters.checks_aborted += 1;
        gc.unref(r); // the check's reference; the cells still hold theirs
    }

    fn finish(gc: *Gc) void {
        const r = gc.check.?;
        gc.phase = .idle;
        gc.barrier_on = false;
        gc.cursor = &gc.garbage;
        gc.check = null;
        gc.counters.runs += 1;
        gc.counters.full_runs += 1;
        // Nothing changed while it was looked at: what the mark saw is exact.
        if (!gc.mutated and r.members != 0) {
            if (r.ext != gc.ext_sum) gc.counters.ext_corrected += 1;
            r.ext = gc.ext_sum;
        }
        if (gc.cfg.check_backoff) {
            r.quiet = if (gc.run_freed != 0) 0 else @min(r.quiet + 1, 6);
        }
        if (gc.check_merged and r.members != 0 and !r.dirty) gc.makeDirty(r);
        gc.unref(r);
        gc.busy = gc.pending();
    }

    fn pump(gc: *Gc, budget: usize) void {
        if (gc.n_zombies != 0) gc.finalizeZombies(gc.cfg.free_budget);
        if (gc.dying.q_next != &gc.dying) gc.freeDying(gc.cfg.free_budget);
        if (gc.phase == .idle and gc.cfg.auto and gc.allocs >= gc.next_check) {
            var s = gc.dirty.q_next;
            while (s != &gc.dirty and s.due > gc.allocs and !gc.grown(s)) s = s.q_next;
            if (s != &gc.dirty) gc.begin(s) else gc.recomputeNext();
        }
        gc.work(budget);
    }

    fn work(gc: *Gc, budget: usize) void {
        var done: usize = 0;
        while (done < budget and gc.phase != .idle) : (done += 1) gc.unit();
        gc.counters.units += done;
        if (done > gc.counters.max_units_per_step) gc.counters.max_units_per_step = done;
        if (gc.phase == .idle) {
            gc.recomputeNext();
            gc.busy = gc.pending();
        }
    }

    /// Process exactly one cell (phase changes are free and fall through).
    fn unit(gc: *Gc) void {
        while (true) switch (gc.phase) {
            .idle => return,

            .init => {
                const r = gc.check.?;
                const c = gc.cursor;
                if (c == &r.ring) {
                    gc.cursor = r.ring.next;
                    gc.phase = .discover;
                    continue;
                }
                gc.cursor = c.next;
                if (c.meta.state == .idle) whiten(c);
                return;
            },

            .discover => {
                const c = gc.cursor;
                if (c == &gc.check.?.ring) {
                    gc.cursor = gc.check.?.ring.next;
                    gc.phase = .mark;
                    continue;
                }
                // Cells that came in after init (merged in, or joined since)
                // are taken into the check where they stand.
                if (c.meta.state == .idle) whiten(c);
                if (c.meta.state == .white) {
                    var v: Visitor = .{ .gc = gc, .op = .discover };
                    gc.counters.traced += 1;
                    c.desc().trace(c, &v); // may merge: the ring grows behind c
                }
                gc.cursor = c.next;
                return;
            },

            .mark => {
                if (gc.grey_top) |g| {
                    gc.grey_top = g.u.work;
                    g.meta.flags &= ~F_STACKED;
                    const rc = rcPtr(g);
                    rc.* -= 1; // the pin
                    const r = gc.root(g);
                    r.ext -= 1;
                    if (r.ext == 0) {
                        gc.die(r); // the pin was the structure's last outside reference
                    } else if (rc.* == 0) {
                        // the mutator let go of it while it waited
                        gc.counters.died_pinned += 1;
                        gc.detach(g, r);
                        gc.in_collector += 1;
                        gc.free_depth += 1;
                        g.desc().finalize(g, gc.ctx);
                        gc.free_depth -= 1;
                        gc.in_collector -= 1;
                    } else {
                        gc.live(g);
                    }
                    return;
                }
                const r = gc.check.?;
                const c = gc.cursor;
                if (c == &r.ring) {
                    // Every cell of the check has been looked at; what is
                    // still white has no reference from outside the white.
                    gc.barrier_on = false;
                    if (gc.n_passed == 0) {
                        gc.finish();
                        return;
                    }
                    gc.cursor = r.ring.next;
                    gc.phase = .sweep;
                    continue;
                }
                gc.cursor = c.next;
                if (c.meta.state == .white and c.u.refs > 0) {
                    gc.ext_sum += c.u.refs;
                    gc.live(c);
                } else if (c.meta.state == .grey) {
                    // reached from a live cell before the scan got here: its
                    // count is still in place
                    gc.ext_sum += c.u.refs;
                    gc.live(c);
                } else if (c.meta.state == .white) {
                    c.meta.flags |= F_PASSED;
                    gc.n_passed += 1;
                }
                // idle: joined after the check began; live as far as it goes
                return;
            },

            .sweep => {
                const r = gc.check.?;
                const c = gc.cursor;
                if (gc.n_passed == 0 or c == &r.ring) {
                    assert(gc.n_passed == 0);
                    gc.phase = .free;
                    continue;
                }
                if (c.meta.state == .white) {
                    // Its edges to live members stop being internal (they
                    // are released just below); its edges to other garbage
                    // go silently.
                    var v: Visitor = .{ .gc = gc, .op = .unlink, .x = r };
                    gc.counters.traced += 1;
                    c.desc().trace(c, &v);
                    gc.unlink(c); // moves the cursor on
                    append(&gc.garbage, c);
                    c.meta.flags = F_RELEASED;
                    gc.n_passed -= 1;
                    r.members -= 1;
                    gc.in_collector += 1;
                    gc.free_depth += 1;
                    tl.sweeping = true;
                    c.desc().release_outside(c, gc.ctx);
                    tl.sweeping = false;
                    gc.free_depth -= 1;
                    gc.in_collector -= 1;
                } else {
                    gc.cursor = c.next;
                }
                return;
            },

            .free => {
                if (gc.garbage.next == &gc.garbage) {
                    gc.finish();
                    return;
                }
                const g = gc.garbage.next;
                g.prev.next = g.next;
                g.next.prev = g.prev;
                const s = gc.rec(g.st);
                g.st = 0;
                gc.counters.freed += 1;
                gc.run_freed += 1;
                g.desc().free(g, gc.ctx);
                gc.unref(s);
                return;
            },
        };
    }
};
