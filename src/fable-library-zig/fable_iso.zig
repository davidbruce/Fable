//! Region isolation (`Iso<'T>`) and shared-ownership adoption (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const rt = @import("fable_rt.zig");
const Any = rt.Any;
const Env = rt.Env;
const Exn = rt.Exn;
const InvalidOperationException = rt.InvalidOperationException;
const Layout = rt.Layout;
const Obj = rt.Obj;
const Raised = rt.Raised;
const Result = rt.Result;
const Shower = rt.Shower;
const Str = rt.Str;
const String = rt.String;
const across = rt.across;
const bookkeeping = rt.bookkeeping;
const box = rt.box;
const boxed = rt.boxed;
const captured = rt.captured;
const cell = rt.cell;
const collectorSetup = rt.collectorSetup;
const counted = rt.counted;
const drop = rt.drop;
const dup = rt.dup;
const fable_show = rt.fable_show;
const free = rt.free;
const gcOf = rt.gcOf;
const hasGc = rt.hasGc;
const inThreadArena = rt.inThreadArena;
const isCellPtr = rt.isCellPtr;
const isCount = rt.isCount;
const isFunc = rt.isFunc;
const isIface = rt.isIface;
const isManaged = rt.isManaged;
const isShared = rt.isShared;
const isSlice = rt.isSlice;
const markCell = rt.markCell;
const markShared = rt.markShared;
const oom = rt.oom;
const raise = rt.raise;
const sgc = rt.sgc;
const count_mask = rt.count_mask;
const immortal_bit = rt.immortal_bit;
const shareStored = rt.shareStored;
const shared_bit = rt.shared_bit;
const weak_bit = rt.weak_bit;
const str = rt.str;
const take = rt.take;
const thread = rt.thread;
const track = rt.track;
const visit = rt.visit;
const weak_refs = rt.weak_refs;

// ---- Ownership regained on receipt (Verona's regions, Pony's `iso`): a value that was marked
// shared to cross to another thread (a message of a MailboxProcessor) is the receiver's own
// again where only the receiver holds it: the region reached from it through cells and strings
// counted once has its shared bits cleared, so its counts are plain from then on and Perceus may
// change it in place. A cell counted once and reached only through such cells has no other
// holder, so no thread can take a reference to it meanwhile (those that hold one are counted).
// The walk stops, leaving it shared, at anything counted more than once, at what is reached
// through hooks of its own (a function, an object, an exception, an interface), at a weak
// reference and at a cell the collector follows (it left the collector when shared); unshared
// cells then point to shared ones, never the other way. Nothing is taken back while weak
// references to shared values exist (one could take a reference meanwhile). ----

/// Can this cell, counted once, be taken out of sharing (its shared bit cleared)? Never for
/// weak-targeted or immortal cells, regardless of whether other shared weak references exist.
inline fn unshareable(c: anytype) bool {
    return (@atomicLoad(u32, &c.@"$rc", .acquire) & (weak_bit | immortal_bit)) == 0;
}

/// The region of `x` that only the receiver holds made its own again
pub fn adoptShared(x: anytype) void {
    adoptRegion(x);
}

/// (one reference, shared or not; read after the other threads' last releases)
inline fn countedOnce(c: anytype) bool {
    return @atomicLoad(u32, &c.@"$rc", .acquire) & ~shared_bit == 1;
}

fn adoptRegion(x: anytype) void {
    const T = @TypeOf(x);
    if (comptime !isManaged(T)) return;
    if (comptime isFunc(T) or isIface(T) or T == Obj or T == Exn or T == Any) return;
    if (T == String) {
        const p = x orelse return;
        const rc = @atomicLoad(u32, &p.rc, .acquire);
        if (rc != Str.literal and rc & ~shared_bit == 1) p.rc = 1;
        return;
    }
    if (comptime isSlice(T)) {
        for (x) |item| adoptRegion(item);
        return;
    }
    switch (@typeInfo(T)) {
        .pointer => |ptr| {
            const C = ptr.child;
            if (comptime hasGc(C) or @hasDecl(C, "fable_weak") or @hasDecl(C, "fable_object")) return;
            var cur = x;
            while (true) {
                if (!countedOnce(cur)) return;
                cur.@"$rc" = 1;
                if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(cur));
                var next: ?T = null;
                inline for (@typeInfo(C).@"struct".field_names) |name| {
                    if (comptime isCount(name)) continue;
                    const F = @TypeOf(@field(cur, name));
                    if (F == T) next = @field(cur, name) else if (F == ?T) next = @field(cur, name) else adoptRegion(@field(cur, name));
                }
                cur = next orelse return;
            }
        },
        .optional => if (x) |v| adoptRegion(v),
        .@"struct" => |st| inline for (st.field_names) |name| adoptRegion(@field(x, name)),
        .@"union" => {
            var cur = x;
            while (true) {
                var next: ?T = null;
                switch (cur) {
                    inline else => |p| {
                        const P = @TypeOf(p);
                        if (comptime isCellPtr(P)) {
                            const C = @typeInfo(P).pointer.child;
                            if (comptime hasGc(C)) return;
                            if (!countedOnce(p)) return;
                            p.@"$rc" = 1;
                            if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(p));
                            inline for (@typeInfo(C).@"struct".field_names) |name| {
                                if (comptime isCount(name)) continue;
                                if (@TypeOf(@field(p, name)) == T) next = @field(p, name) else adoptRegion(@field(p, name));
                            }
                        } else adoptRegion(p);
                    },
                }
                cur = next orelse return;
            }
        },
        else => {},
    }
}

// ---- `Fable.Core.Zig.Iso<'T>`: a value moved between threads whole (Verona's isolated region,
// Pony's `iso`). `Iso.pack x` takes `x` (the caller gives it up), which must be isolated: each
// cell and string it reaches that is not shared already is counted exactly as often as the value
// refers to it (trees, diamonds and cycles; see `Region`), and what is shared already is left as
// a part of it. A function's environment, an object or an exception not shared yet is counted
// the same way and marked shared once the value is found isolated. A structure of the cycle
// collector it reaches moves whole to the unpacking thread's collector; loose collector cells are
// flagged as targets. Refused: interfaces, what a `[<StackArena>]` made, cells with a weak
// reference of this thread's, a shared cell's bit while shared weak handles exist, a structure
// being checked. The value is kept as bytes the runtime does not walk, so sharing the Iso
// (posting it to a MailboxProcessor, capturing it in a thread) marks only the Iso: the value's
// counts stay plain, and any number of hops cost one pointer each. `Iso.unpack` takes the value
// out once (an atomic swap: one taker), owned by the thread that unpacks it. A MailboxProcessor
// boxes its messages the same way (`isoSend`, `isoHold`). ----

pub fn Iso(comptime T: type) type {
    return *struct {
        const Self = @This();
        pub const fable_identity = {};
        pub const fable_iso = T;
        @"$rc": u32 = 1,
        /// 1 while the value is in it
        full: std.atomic.Value(u8) = .init(1),
        /// the value reaches cells the cycle collector follows (in a structure or not, however
        /// deep): the thread that unpacks it makes its collector if it has none
        has_gc: bool = false,
        /// the value, as bytes nothing walks (see above)
        held: [@sizeOf(T)]u8 align(@alignOf(T)) = undefined,
        /// the structures of the cycle collector the value moved out of the packing thread's
        /// collector with: their members, one group after another, and where each group ends
        moved: []*sgc.Hdr = &.{},
        moved_ends: []usize = &.{},

        fn ptr(c: *Self) *T {
            return @ptrCast(&c.held);
        }

        /// (the moved structures join this thread's collector)
        fn settle(c: *Self) void {
            // (cells the collector follows, in a structure or not, are this thread's now: its
            // collector is made if it was not)
            if (c.has_gc and !thread.collector_ready) collectorSetup();
            var start: usize = 0;
            for (c.moved_ends) |end| {
                thread.collector.moveIn(c.moved[start..end]);
                start = end;
            }
            if (c.moved.len != 0) rt.allocator.free(c.moved);
            if (c.moved_ends.len != 0) rt.allocator.free(c.moved_ends);
            c.moved = &.{};
            c.moved_ends = &.{};
        }

        pub fn fable_free(c: *Self) void {
            if (c.full.load(.acquire) == 1) {
                c.settle();
                drop(c.ptr().*);
            } else c.settle();
        }

        pub fn fable_show(b: *Shower, x: *Self, depth: i32) *Layout {
            _ = x;
            _ = depth;
            return b.word("Fable.Core.Zig.Iso`1");
        }
    };
}

/// Is `x` isolated (see above)? Counts read after the other threads' last releases.
fn isolated(x: anytype) bool {
    const T = @TypeOf(x);
    if (comptime !isManaged(T)) return true;
    if (comptime isFunc(T) or isIface(T) or T == Obj or T == Exn or T == Any) return false;
    if (T == String) {
        const p = x orelse return true;
        const rc = @atomicLoad(u32, &p.rc, .acquire);
        if (rc == Str.literal) return true;
        return rc & ~shared_bit == 1 and !inThreadArena(p);
    }
    if (comptime isSlice(T)) {
        for (x) |item| if (!isolated(item)) return false;
        return true;
    }
    switch (@typeInfo(T)) {
        .pointer => |ptr| {
            const C = ptr.child;
            if (comptime hasGc(C) or @hasDecl(C, "fable_weak") or @hasDecl(C, "fable_object") or @hasDecl(C, "fable_iso")) return false;
            var cur = x;
            while (true) {
                if (!countedOnce(cur) or !unshareable(cur) or inThreadArena(cur)) return false;
                if (thread.weak.count() != 0 and thread.weak.contains(@intFromPtr(cur))) return false;
                var next: ?T = null;
                inline for (@typeInfo(C).@"struct".field_names) |name| {
                    if (comptime isCount(name)) continue;
                    const F = @TypeOf(@field(cur, name));
                    if (F == T) next = @field(cur, name) else if (F == ?T) next = @field(cur, name) else if (!isolated(@field(cur, name))) return false;
                }
                cur = next orelse return true;
            }
        },
        .optional => return if (x) |v| isolated(v) else true,
        .@"struct" => |st| {
            inline for (st.field_names) |name| if (!isolated(@field(x, name))) return false;
            return true;
        },
        .@"union" => {
            var cur = x;
            while (true) {
                var next: ?T = null;
                switch (cur) {
                    inline else => |p| {
                        const P = @TypeOf(p);
                        if (comptime isCellPtr(P)) {
                            const C = @typeInfo(P).pointer.child;
                            if (comptime hasGc(C)) return false;
                            if (!countedOnce(p) or !unshareable(p) or inThreadArena(p)) return false;
                            if (thread.weak.count() != 0 and thread.weak.contains(@intFromPtr(p))) return false;
                            inline for (@typeInfo(C).@"struct".field_names) |name| {
                                if (comptime isCount(name)) continue;
                                if (@TypeOf(@field(p, name)) == T) next = @field(p, name) else if (!isolated(@field(p, name))) return false;
                            }
                        } else if (!isolated(p)) return false;
                    },
                }
                cur = next orelse return true;
            }
        },
        else => return true,
    }
}

const PackFail = enum {
    none,
    external_ref,
    stack_arena,
    weak_ref,
    immortal_or_null,
    nested_iso_or_weak,
    partial_cycle_structure,
    cycle_check_active,
    unshareable_opaque_cycle,
    unshareable_opaque_arena,
    unshareable_opaque,
};

fn packFailString(why: PackFail) String {
    return switch (why) {
        .external_ref => str("Iso.pack: the value is not isolated because another live reference points into part of it."),
        .stack_arena => str("Iso.pack: cannot pack a value allocated inside a [<StackArena>] function (copy it to the heap first)."),
        .weak_ref => str("Iso.pack: cannot pack a value targeted by a thread-local WeakReference."),
        .immortal_or_null => str("Iso.pack: cannot pack an immortal or null runtime cell."),
        .nested_iso_or_weak => str("Iso.pack: cannot pack a value containing a WeakReference, lock-identity System.Object helper, or Iso handle."),
        .partial_cycle_structure => str("Iso.pack: cannot pack only part of a cyclic fable_sgc structure (pack the whole cyclic graph together or break the cycle with WeakReference)."),
        .cycle_check_active => str("Iso.pack: cannot move a fable_sgc cyclic structure while the cycle collector is paused with an active incremental check (call collectorResume before Iso.pack)."),
        .unshareable_opaque_cycle => str("Iso.pack: a captured function environment, object, or interface reaches a cyclic fable_sgc structure that cannot be shared across threads (break the cycle with WeakReference)."),
        .unshareable_opaque_arena => str("Iso.pack: a captured function environment, object, or interface reaches a value allocated inside a [<StackArena>] function."),
        .unshareable_opaque => str("Iso.pack: a captured function environment, object, or interface holds a value that cannot be shared across threads."),
        .none => str("Iso.pack: the value is not isolated (another reference, WeakReference, [<StackArena>] allocation, or active cycle-collector state prevents isolation)."),
    };
}

/// `Iso.pack x` (`x` owned: the caller gives it, or keeps it, which makes it not isolated)
/// `x` in an Iso if it is isolated (see above); null otherwise, `x` left as it was
fn packOrNull(comptime T: type, x: T, fail_out: ?*PackFail) ?Iso(T) {
    const I = @typeInfo(Iso(T)).pointer.child;
    // (a tree of cells counted once, none the collector follows: the quick test)
    if (isolated(x)) {
        adoptRegion(x);
        const c = rt.allocator.create(I) catch oom();
        if (track) thread.stats.allocs += 1;
        c.* = .{};
        c.ptr().* = x;
        return c;
    }
    // Finish any active incremental check before walking so transient F_STACKED / gc.check state
    // does not cause non-deterministic Iso.pack failures.
    if (thread.collector_ready and thread.collector.phase != .idle) thread.collector.finishCheck();
    // (shared parts, cycles, cells the collector follows: each cell counted exactly as often as
    // the value refers to it)
    var region: Region = .{};
    defer region.deinit();
    region.visit(x);
    if (!region.ok or !region.closed()) {
        if (fail_out) |f| f.* = region.fail;
        return null;
    }
    const c = rt.allocator.create(I) catch oom();
    if (track) thread.stats.allocs += 1;
    c.* = .{};
    c.has_gc = region.saw_gc;
    region.moveOut(&c.moved, &c.moved_ends);
    c.ptr().* = x;
    return c;
}

/// `Iso.pack x` (`x` owned: the caller gives it, or keeps it, which makes it not isolated)
pub fn isoPack(comptime T: type) type {
    return struct {
        pub const sig = .{ .borrows = .{false}, .result_borrowed = false };

        pub fn call(x: T) Raised!Iso(T) {
            var reason: PackFail = .none;
            if (packOrNull(T, x, &reason)) |c| return c;
            drop(x);
            return raise(InvalidOperationException, packFailString(reason));
        }
    };
}

/// `Iso.tryPack x`: the Iso, or the value given back (as an F# tuple of two options, which
/// Fable.Core.Zig's inline `tryPack` turns into a Result where it is used)
pub fn isoTryPack(comptime T: type) type {
    return struct {
        pub const sig = .{ .borrows = .{false}, .result_borrowed = false };

        pub fn call(x: T) @Tuple(&.{ ?Iso(T), ?T }) {
            if (packOrNull(T, x, null)) |c| return .{ c, null };
            return .{ null, x };
        }
    };
}

/// A MailboxProcessor's message as it is sent across threads (see Async.fs's MessageQueue): an
/// isolated tree of cells goes in unmarked (its counts stay plain: the receiver gets it as its
/// own); anything else is marked shared, as any value that reaches another thread is
pub fn isoSend(comptime T: type) type {
    return struct {
        pub const sig = .{ .borrows = .{false}, .result_borrowed = false };

        pub fn call(x: T) Iso(T) {
            transferOrShare(x);
            return isoBox(T, x);
        }
    };
}

inline fn shareOrRaise(comptime raise_on_err: bool, v: anytype) (if (raise_on_err) Raised!void else void) {
    if (comptime raise_on_err) return markShared(v) else shareStored(v);
}

fn transferWalk(comptime raise_on_err: bool, x: anytype) (if (raise_on_err) Raised!void else void) {
    const T = @TypeOf(x);
    if (comptime !isManaged(T)) return;
    if (comptime isFunc(T)) {
        if (comptime raise_on_err) {
            const e = x.env orelse return;
            if (!isShared(e) and e.@"$rc" == 1 and !inThreadArena(e)) {
                if (e.gc) |h| {
                    if (h.st != 0) return markShared(x);
                    sgc.Gc.moveLoose(h);
                    thread.transfer_saw_gc = true;
                }
                if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(e));
                thread.transfer_env = true;
                defer thread.transfer_env = false;
                return e.share(e);
            }
        }
        return shareOrRaise(raise_on_err, x);
    }
    if (comptime isIface(T) or T == Obj or T == Exn or T == Any) return shareOrRaise(raise_on_err, x);
    if (T == String) {
        const p = x orelse return;
        const rc = @atomicLoad(u32, &p.rc, .monotonic);
        if (rc == Str.literal or rc & shared_bit != 0) return;
        if (rc == 1 and !inThreadArena(p)) return;
        return shareOrRaise(raise_on_err, x);
    }
    if (comptime isSlice(T)) {
        for (x) |item| {
            if (comptime raise_on_err) try transferWalk(true, item) else transferWalk(false, item);
        }
        return;
    }
    switch (@typeInfo(T)) {
        .pointer => |ptr| {
            const C = ptr.child;
            if (comptime hasGc(C) or @hasDecl(C, "fable_weak") or @hasDecl(C, "fable_object") or @hasDecl(C, "fable_iso")) return shareOrRaise(raise_on_err, x);
            var cur = x;
            while (true) {
                if (isShared(cur)) return;
                if (cur.@"$rc" != 1 or inThreadArena(cur)) return shareOrRaise(raise_on_err, cur);
                if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(cur));
                var next: ?T = null;
                inline for (@typeInfo(C).@"struct".field_names) |name| {
                    if (comptime isCount(name)) continue;
                    const F = @TypeOf(@field(cur, name));
                    if (F == T) next = @field(cur, name) else if (F == ?T) next = @field(cur, name) else {
                        if (comptime raise_on_err) try transferWalk(true, @field(cur, name)) else transferWalk(false, @field(cur, name));
                    }
                }
                cur = next orelse return;
            }
        },
        .optional => if (x) |v| return transferWalk(raise_on_err, v),
        .@"struct" => |st| inline for (st.field_names) |name| {
            if (comptime raise_on_err) try transferWalk(true, @field(x, name)) else transferWalk(false, @field(x, name));
        },
        .@"union" => {
            var cur = x;
            while (true) {
                var next: ?T = null;
                switch (cur) {
                    inline else => |p| {
                        const P = @TypeOf(p);
                        if (comptime isCellPtr(P)) {
                            const C = @typeInfo(P).pointer.child;
                            if (comptime hasGc(C)) return shareOrRaise(raise_on_err, cur);
                            if (isShared(p)) return;
                            if (p.@"$rc" != 1 or inThreadArena(p)) return shareOrRaise(raise_on_err, cur);
                            if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(p));
                            inline for (@typeInfo(C).@"struct".field_names) |name| {
                                if (comptime isCount(name)) continue;
                                if (@TypeOf(@field(p, name)) == T) next = @field(p, name) else {
                                    if (comptime raise_on_err) try transferWalk(true, @field(p, name)) else transferWalk(false, @field(p, name));
                                }
                            }
                        } else if (comptime raise_on_err) try transferWalk(true, p) else transferWalk(false, p);
                    },
                }
                cur = next orelse return;
            }
        },
        else => {},
    }
}

/// What crosses with a message: the cells and strings it alone holds (counted once, not shared,
/// not in a `[<StackArena>]`, no weak reference of this thread's to them, none the collector
/// follows) go as they are, plain; at what is shared already the walk stops (the message's cells
/// may point at it); anything else is marked shared, with all it reaches (shared never points
/// at unshared). A unique envelope around a shared part keeps its plain counts.
fn transferOrShare(x: anytype) void {
    transferWalk(false, x);
}

/// Transfer unique ownership across threads where possible (leaving `rc == 1`, non-arena, non-cyclic
/// subtrees unshared) and mark everything else shared via `markShared`, raising `Raised` instead of
/// panicking when a captured value cannot be shared (e.g. stack arena allocations or cycles).
pub fn transferOrShareOrRaise(x: anytype) Raised!void {
    return transferWalk(true, x);
}

/// After a worker that shared `c` has joined on `c`'s home thread, clear `shared_bit` if
/// `c` has no other live reference, no `weak_bit`, and no `immortal_bit` (`rc == 1 | shared_bit`).
pub fn tryReclaimHomeCell(c: anytype) bool {
    if (@atomicLoad(u32, &c.@"$rc", .acquire) == (1 | shared_bit)) {
        c.@"$rc" = 1;
        return true;
    }
    return false;
}

/// A message boxed by the thread that holds it (a mailbox of one thread, or a message put back)
pub fn isoHold(comptime T: type) type {
    return struct {
        pub const sig = .{ .borrows = .{false}, .result_borrowed = false };

        pub fn call(x: T) Iso(T) {
            return isoBox(T, x);
        }
    };
}

fn isoBox(comptime T: type, x: T) Iso(T) {
    const I = @typeInfo(Iso(T)).pointer.child;
    const c = rt.allocator.create(I) catch oom();
    if (track) thread.stats.allocs += 1;
    c.* = .{};
    c.ptr().* = x;
    return c;
}

/// The value in a box, left in it (a reference of its own)
pub fn isoPeek(iso: anytype) @typeInfo(@TypeOf(iso)).pointer.child.fable_iso {
    return dup(iso.ptr().*);
}

/// `Iso.unpack iso`: the value, once (InvalidOperationException after)
pub fn isoUnpack(iso: anytype) Raised!@typeInfo(@TypeOf(iso)).pointer.child.fable_iso {
    if (iso.full.swap(0, .acq_rel) != 1) return raise(InvalidOperationException, str("Iso.unpack: the value was taken already."));
    iso.settle();
    return iso.ptr().*;
}

/// The cells a value reaches, each with the references to it found inside the value (the value
/// itself is reached once: the caller gave it up). Isolated: each cell's count is that number,
/// nothing is reached through hooks of its own, and every member of a structure of the cycle
/// collector that it reaches is reached (the structure moves whole).
pub const Region = struct {
    /// `share`: a function's environment, an object or an exception, reached through hooks of
    /// its own: counted as a cell, and marked shared once the value is found isolated
    const Reached = struct { rc: *u32, seen: u32, hdr: ?*sgc.Hdr, share: ?*const fn (usize) Raised!void = null };
    cells: std.AutoHashMapUnmanaged(usize, Reached) = .empty,
    ok: bool = true,
    fail: PackFail = .none,
    /// a cell the cycle collector follows was reached
    saw_gc: bool = false,

    fn deinit(r: *Region) void {
        r.cells.deinit(bookkeeping());
    }

    fn reject(r: *Region, why: PackFail) void {
        if (r.fail == .none) r.fail = why;
        r.ok = false;
    }

    /// One reference found to the cell at `addr`: true when it was seen before (not walked again)
    fn reach(r: *Region, addr: usize, rc: *u32, hdr: ?*sgc.Hdr) bool {
        const e = r.cells.getOrPut(bookkeeping(), addr) catch oom();
        if (e.found_existing) {
            e.value_ptr.seen += 1;
            return true;
        }
        if (hdr != null) r.saw_gc = true;
        e.value_ptr.* = .{ .rc = rc, .seen = 1, .hdr = hdr };
        return false;
    }

    /// One reference found to something reached through hooks (see Reached)
    pub fn reachOpaque(r: *Region, comptime P: type, p: P) void {
        if (isShared(p)) return;
        const rc_p = p.@"$rc";
        if (rc_p & immortal_bit != 0) return r.reject(.immortal_or_null);
        if (inThreadArena(p)) return r.reject(.stack_arena);
        if (rc_p & weak_bit != 0 and thread.weak.contains(@intFromPtr(p))) return r.reject(.weak_ref);
        const e = r.cells.getOrPut(bookkeeping(), @intFromPtr(p)) catch oom();
        if (e.found_existing) {
            e.value_ptr.seen += 1;
            return;
        }
        const S = struct {
            fn share(a: usize) Raised!void {
                const q: P = @ptrFromInt(a);
                if (P == *Env) {
                    if (try markCell(q)) try q.share(q);
                } else try markShared(q);
            }
        };
        e.value_ptr.* = .{ .rc = &p.@"$rc", .seen = 1, .hdr = null, .share = S.share };
    }

    /// (what is shared between threads already is left as it is: the value's cells may point at
    /// it, its counts are atomic. A function's environment, an object, an interface, or an
    /// exception, whose parts are reached through hooks, is shared already or counted as an
    /// opaque cell and marked shared once the whole region is verified isolated and shareable.)
    fn visit(r: *Region, x: anytype) void {
        if (!r.ok) return;
        const T = @TypeOf(x);
        if (comptime !isManaged(T)) return;
        if (comptime isFunc(T)) {
            const e = x.env orelse return;
            r.reachOpaque(*Env, e);
            return;
        }
        if (T == Obj or T == Exn) {
            r.reachOpaque(T, x);
            return;
        }
        if (T == Any) {
            const o = x orelse return;
            r.reachOpaque(Obj, o);
            return;
        }
        if (comptime isIface(T)) {
            x.vt.@"$meta".iso_reach(x.data, r);
            return;
        }
        if (T == String) {
            const p = x orelse return;
            const rc = @atomicLoad(u32, &p.rc, .acquire);
            if (rc == Str.literal or rc & shared_bit != 0) return;
            if (inThreadArena(p)) return r.reject(.stack_arena);
            _ = r.reach(@intFromPtr(p), &p.rc, null);
            return;
        }
        if (comptime isSlice(T)) {
            for (x) |item| r.visit(item);
            return;
        }
        switch (@typeInfo(T)) {
            .pointer => |ptr| {
                const C = ptr.child;
                if (comptime @hasDecl(C, "fable_weak") or @hasDecl(C, "fable_object") or @hasDecl(C, "fable_iso")) {
                    return r.reject(.nested_iso_or_weak);
                }
                var cur = x;
                while (r.ok) {
                    if (isShared(cur)) return;
                    const rc_cur = cur.@"$rc";
                    if (rc_cur & immortal_bit != 0) return r.reject(.immortal_or_null);
                    if (inThreadArena(cur)) return r.reject(.stack_arena);
                    if (rc_cur & weak_bit != 0 and thread.weak.contains(@intFromPtr(cur))) return r.reject(.weak_ref);
                    if (r.reach(@intFromPtr(cur), &cur.@"$rc", gcOf(cur))) return;
                    var next: ?T = null;
                    inline for (@typeInfo(C).@"struct".field_names) |name| {
                        if (comptime isCount(name)) continue;
                        const F = @TypeOf(@field(cur, name));
                        if (F == T) next = @field(cur, name) else if (F == ?T) next = @field(cur, name) else r.visit(@field(cur, name));
                    }
                    cur = next orelse return;
                }
            },
            .optional => if (x) |v| r.visit(v),
            .@"struct" => |st| inline for (st.field_names) |name| r.visit(@field(x, name)),
            .@"union" => {
                var cur = x;
                while (r.ok) {
                    var next: ?T = null;
                    switch (cur) {
                        inline else => |p| {
                            const P = @TypeOf(p);
                            if (comptime isCellPtr(P)) {
                                if (isShared(p)) return;
                                const rc_p = p.@"$rc";
                                if (rc_p & immortal_bit != 0) return r.reject(.immortal_or_null);
                                if (inThreadArena(p)) return r.reject(.stack_arena);
                                if (rc_p & weak_bit != 0 and thread.weak.contains(@intFromPtr(p))) return r.reject(.weak_ref);
                                if (r.reach(@intFromPtr(p), &p.@"$rc", gcOf(p))) return;
                                inline for (@typeInfo(@typeInfo(P).pointer.child).@"struct".field_names) |name| {
                                    if (comptime isCount(name)) continue;
                                    if (@TypeOf(@field(p, name)) == T) next = @field(p, name) else r.visit(@field(p, name));
                                }
                            } else r.visit(p);
                        },
                    }
                    cur = next orelse return;
                }
            },
            else => {},
        }
    }

    /// Is every cell counted exactly as often as the value refers to it, every structure of
    /// the collector it reaches reached whole and free to move, and all opaque hooks shareable?
    fn closed(r: *Region) bool {
        const Seen = struct { reached: usize, members: usize };
        var per_structure: std.AutoHashMapUnmanaged(usize, Seen) = .empty;
        defer per_structure.deinit(bookkeeping());
        var has_opaque = false;
        var it = r.cells.iterator();
        while (it.next()) |e| {
            const reached = e.value_ptr.*;
            const rc = @atomicLoad(u32, reached.rc, .acquire);
            if (reached.share != null) has_opaque = true;
            if ((rc & (shared_bit | immortal_bit)) != 0 or (rc & count_mask) != reached.seen) {
                r.fail = if (rc & immortal_bit != 0) .immortal_or_null else .external_ref;
                return false;
            }
            const h = reached.hdr orelse continue;
            if (!thread.collector.canMove(h)) {
                r.fail = .cycle_check_active;
                return false;
            }
            if (h.st == 0) continue;
            const s = thread.collector.structureOf(h);
            const n = per_structure.getOrPut(bookkeeping(), s.key) catch oom();
            if (!n.found_existing) n.value_ptr.* = .{ .reached = 0, .members = s.members };
            n.value_ptr.reached += 1;
        }
        var ps = per_structure.valueIterator();
        while (ps.next()) |n| if (n.reached != n.members) {
            r.fail = .partial_cycle_structure;
            return false;
        };
        if (has_opaque) {
            // Phase 1: dry-run validate every opaque root before mutating any cell to shared_bit
            // so a later failure leaves earlier opaque cells untouched on `Iso.tryPack`.
            var probe: rt.ShareProbe = .{};
            defer probe.deinit();
            thread.share_probe = &probe;
            var ok_probe = true;
            var probe_it = r.cells.iterator();
            while (probe_it.next()) |e| {
                const share = e.value_ptr.share orelse continue;
                share(e.key_ptr.*) catch {
                    drop(take());
                    ok_probe = false;
                    break;
                };
            }
            thread.share_probe = null;
            if (!ok_probe) {
                r.fail = switch (probe.reason) {
                    .cyclic_structure => .unshareable_opaque_cycle,
                    .stack_arena => .unshareable_opaque_arena,
                    .none => .unshareable_opaque,
                };
                return false;
            }
            // Phase 2: commit shared_bit across all validated opaque subgraphs.
            var shares = r.cells.iterator();
            while (shares.next()) |e| {
                const share = e.value_ptr.share orelse continue;
                share(e.key_ptr.*) catch {
                    drop(take());
                    r.fail = .unshareable_opaque;
                    return false;
                };
            }
        }
        return true;
    }

    /// The value's cells made the Iso's: plain counts, no identity stamps of this thread's,
    /// loose collector cells flagged, structures moved out (their members listed for `settle`)
    fn moveOut(r: *Region, moved: *[]*sgc.Hdr, ends: *[]usize) void {
        var groups: std.AutoArrayHashMapUnmanaged(usize, std.ArrayList(*sgc.Hdr)) = .empty;
        defer {
            for (groups.values()) |*g| g.deinit(bookkeeping());
            groups.deinit(bookkeeping());
        }
        var it = r.cells.iterator();
        while (it.next()) |e| {
            const reached = e.value_ptr.*;
            if (reached.share != null) continue;
            reached.rc.* = reached.seen;
            if (thread.stamps.count() != 0) _ = thread.stamps.remove(e.key_ptr.*);
            const h = reached.hdr orelse continue;
            if (h.st == 0) {
                sgc.Gc.moveLoose(h);
                continue;
            }
            const key = thread.collector.structureOf(h).key;
            const g = groups.getOrPut(bookkeeping(), key) catch oom();
            if (!g.found_existing) g.value_ptr.* = .empty;
            g.value_ptr.append(bookkeeping(), h) catch oom();
        }
        if (groups.count() == 0) return;
        var total: usize = 0;
        for (groups.values()) |g| total += g.items.len;
        const all = rt.allocator.alloc(*sgc.Hdr, total) catch oom();
        const group_ends = rt.allocator.alloc(usize, groups.count()) catch oom();
        var at: usize = 0;
        for (groups.values(), 0..) |g, i| {
            // (the structure leaves this collector: one member is enough to name it)
            thread.collector.moveOut(g.items[0]);
            @memcpy(all[at .. at + g.items.len], g.items);
            at += g.items.len;
            group_ends[i] = at;
        }
        moved.* = all;
        ends.* = group_ends;
    }
};
