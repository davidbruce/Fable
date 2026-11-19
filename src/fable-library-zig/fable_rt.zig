//! The hand-written part of the Zig runtime library: reference-counted cells, reuse tokens,
//! the generic dup/drop/equality that generated code calls, and conversions between numbers.
//! The cycle collector will live here too.
const std = @import("std");
const builtin = @import("builtin");
const root = @import("root");
pub const sgc = @import("fable_sgc.zig");
pub const unicode = @import("fable_unicode.zig");
pub const time = @import("fable_time.zig");
pub const io = @import("fable_io.zig");
pub const reflect = @import("fable_reflect.zig");

pub const interface_version: i32 = 12;

// ---------------------------------------------------------------------------------------------
// Cells
//
// A recursive union is a `union(enum)` whose cases with fields point to a cell:
//
//     pub const List = union(enum) {
//         Nil,
//         Cons: *struct { @"$rc": u32 = 1, head: i32, tail: List },
//     };
//
// The count is the first field and has a name no F# field can be given. Counts are not atomic:
// a value belongs to one thread.
// ---------------------------------------------------------------------------------------------

/// Where cells come from. A program may set this before it allocates anything.
pub var allocator: std.mem.Allocator = if (@hasDecl(root, "fable_oom_hook"))
    .{ .ptr = @ptrCast(@constCast(&base_allocator)), .vtable = &OomHooked.vtable }
else
    base_allocator;

// ---------------------------------------------------------------------------------------------
// Out of memory
//
// On .NET an allocation that fails throws OutOfMemoryException; one that nothing catches ends
// the program with "Unhandled exception. System.OutOfMemoryException: ..." (exit code 134 on
// Unix), without running `finally` blocks. Here, by the policy (`fable_oom_policy` in the root
// file, or by the optimization mode):
//
// - `.dotnet` (Debug, ReleaseSafe): the allocations a program can expect to fail (arrays of a
//   length it computes, `Array.Resize`, a collection's capacity) raise OutOfMemoryException, which
//   a handler can catch; an allocation of a cell (a record, a closure, a list cell) ends the
//   program as an exception nothing catches does on .NET. Whether any handler of the program can
//   catch OutOfMemoryException is known when it is compiled (`oom_catch`, joined over its files
//   as `$cycles` is): when none can, every allocation that fails ends the program right there,
//   and no code is spent on raising.
// - `.abort` (ReleaseFast, ReleaseSmall): every allocation that fails ends the program so.
//
// A program may also declare `pub fn fable_oom_hook(bytes: usize) bool`: called when an
// allocation fails, before any of this; when it returns true (it freed memory: caches, say) the
// allocation is tried again.
// ---------------------------------------------------------------------------------------------

pub const OomPolicy = enum { dotnet, abort };

pub const oom_policy: OomPolicy = blk: {
    if (@hasDecl(root, "fable_oom_policy")) break :blk root.fable_oom_policy;
    break :blk switch (builtin.mode) {
        .Debug, .ReleaseSafe => .dotnet,
        .ReleaseFast, .ReleaseSmall => .abort,
    };
};

/// Can a handler of the program catch OutOfMemoryException (so that what can raise it does)?
pub const oom_catchable: bool = blk: {
    if (oom_policy != .dotnet) break :blk false;
    if (builtin.is_test) break :blk true;
    if (!@hasDecl(root, "$cycles")) break :blk true;
    const c = root.@"$cycles";
    if (@hasField(@TypeOf(c), "oom_catch")) break :blk c.oom_catch;
    break :blk true;
};

/// Does any file in the program use `[<StackArena>]`? When false, `alloc()` compiles
/// straight to `allocator` with zero per-allocation thread-local checks.
pub const uses_arena: bool = blk: {
    if (builtin.is_test) break :blk true;
    if (!@hasDecl(root, "$cycles")) break :blk true;
    const c = root.@"$cycles";
    if (@hasField(@TypeOf(c), "uses_arena")) break :blk c.uses_arena;
    break :blk true;
};

/// An allocation failed where it cannot raise: the program ends as .NET ends it when nothing
/// catches OutOfMemoryException (written without allocating)
pub fn oom() noreturn {
    @branchHint(.cold);
    write_err("Unhandled exception. System.OutOfMemoryException: Insufficient memory to continue the execution of the program.\n");
    std.process.abort();
}

/// An allocation failed where it can raise: OutOfMemoryException, when a handler can catch it
pub fn oomRaise() Raised {
    @branchHint(.cold);
    if (comptime !oom_catchable) oom();
    return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
}

/// The allocator a program's `fable_oom_hook` is asked through before an allocation fails
const OomHooked = struct {
    fn hooked_alloc(ctx: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
        const base: *const std.mem.Allocator = @ptrCast(@alignCast(ctx));
        while (true) {
            if (base.rawAlloc(len, alignment, ret_addr)) |p| return p;
            if (!root.fable_oom_hook(len)) return null;
        }
    }
    fn hooked_resize(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
        const base: *const std.mem.Allocator = @ptrCast(@alignCast(ctx));
        return base.rawResize(memory, alignment, new_len, ret_addr);
    }
    fn hooked_remap(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
        const base: *const std.mem.Allocator = @ptrCast(@alignCast(ctx));
        return base.rawRemap(memory, alignment, new_len, ret_addr);
    }
    fn hooked_free(ctx: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
        const base: *const std.mem.Allocator = @ptrCast(@alignCast(ctx));
        base.rawFree(memory, alignment, ret_addr);
    }
    const vtable: std.mem.Allocator.VTable = .{ .alloc = hooked_alloc, .resize = hooked_resize, .remap = hooked_remap, .free = hooked_free };
};

const base_allocator: std.mem.Allocator = if (builtin.link_libc)
    std.heap.c_allocator
else if (builtin.single_threaded)
    std.heap.page_allocator
else
    std.heap.smp_allocator;

/// Counters are kept in Debug and ReleaseSafe builds only.
pub const track = std.debug.runtime_safety;

pub const Stats = struct {
    allocs: i64 = 0,
    frees: i64 = 0,
    reuses: i64 = 0,
    dups: i64 = 0,
    decs: i64 = 0,
    /// the hooks of resources that ran: Destroy, Dup
    destroys: i64 = 0,
    copies: i64 = 0,
};

pub const EnvDropState = struct { depth: u32 = 0, queue: std.ArrayList(*Env) = .empty };

pub const ShareFail = enum { none, stack_arena, cyclic_structure };

pub const ShareProbe = struct {
    seen: std.AutoHashMapUnmanaged(usize, void) = .empty,
    reason: ShareFail = .none,

    pub fn deinit(self: *ShareProbe) void {
        self.seen.deinit(bookkeeping());
    }
};

/// What belongs to one thread: its counters, its cycle collector and the exception it is
/// passing up. A value is owned by the thread that made it (counts are not atomic), so each
/// thread has all of this for itself. (Plain globals where there is one thread or no
/// thread-local storage: see `sgc.per_thread`.)
pub const thread = if (sgc.per_thread) struct {
    pub threadlocal var stats: Stats = .{};
    pub threadlocal var collector: sgc.Gc = undefined;
    pub threadlocal var collector_ready: bool = false;
    pub threadlocal var current: ?Exn = null;
    pub threadlocal var weak: std.AutoHashMapUnmanaged(usize, *WeakHandle) = .empty;
    pub threadlocal var stamps: std.AutoHashMapUnmanaged(usize, u32) = .empty;
    pub threadlocal var book: ?std.mem.Allocator = null;
    pub threadlocal var null_arrays: std.ArrayList(NullArray) = .empty;
    pub threadlocal var async_state: ?*ObjHeader = null;
    pub threadlocal var arena: ?*Arena = null;
    pub threadlocal var env_drop: EnvDropState = .{};
    pub threadlocal var share_probe: ?*ShareProbe = null;
    pub threadlocal var transfer_env: bool = false;
    pub threadlocal var transfer_saw_gc: bool = false;
} else struct {
    pub var stats: Stats = .{};
    pub var collector: sgc.Gc = undefined;
    pub var collector_ready: bool = false;
    pub var current: ?Exn = null;
    pub var weak: std.AutoHashMapUnmanaged(usize, *WeakHandle) = .empty;
    /// the identity hashes given to cells that are not objects (lists, arrays): by address,
    /// until the cell is freed (see `physicalHash`)
    pub var stamps: std.AutoHashMapUnmanaged(usize, u32) = .empty;
    pub var book: ?std.mem.Allocator = null;
    pub var null_arrays: std.ArrayList(NullArray) = .empty;
    pub var async_state: ?*ObjHeader = null;
    pub var arena: ?*Arena = null;
    pub var env_drop: EnvDropState = .{};
    pub var share_probe: ?*ShareProbe = null;
    pub var transfer_env: bool = false;
    pub var transfer_saw_gc: bool = false;
};

/// A null array of a type whose arrays the collector follows, kept until the collector goes
pub const NullArray = struct { cell: *anyopaque, free: *const fn (*anyopaque) void };

/// Where the runtime's own bookkeeping (the collector's, the table of weak references) comes
/// from: `thread.book`, else `allocator` directly (never a stack arena).
pub fn bookkeeping() std.mem.Allocator {
    return thread.book orelse allocator;
}

/// Allocator for F# heap cells and managed buffers: routes into the current thread's
/// `[<StackArena>]` at zero cost when the program uses stack arenas (`uses_arena`),
/// otherwise returns `allocator` directly with no synchronization overhead.
pub inline fn alloc() std.mem.Allocator {
    if (comptime uses_arena) {
        if (thread.arena != null) return arena_mod.arena_router;
    }
    return allocator;
}

/// This thread's counters (all zero in builds that do not count).
pub inline fn counters() *Stats {
    return &thread.stats;
}

/// The cell type of one case of a recursive union.
pub fn Cell(comptime T: type, comptime tag: std.meta.Tag(T)) type {
    return @typeInfo(@FieldType(T, @tagName(tag))).pointer.child;
}

/// A new cell with a count of one.
pub inline fn cell(comptime T: type, comptime tag: std.meta.Tag(T), init: Cell(T, tag)) *Cell(T, tag) {
    const C = Cell(T, tag);
    if (comptime hasGc(C)) gcTick();
    const c = alloc().create(C) catch oom();
    c.* = init;
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

inline fn reuseCellPtr(comptime C: type, tok: anytype, init: C) ?*C {
    const Dead = @typeInfo(@typeInfo(@TypeOf(tok)).pointer.child).optional.child;
    // (In generic code the dead cell and the new one may be different cases or types whose
    // sizes and alignments only match at monomorphization. Only when they match is the dead
    // cell built in; otherwise the token is left alone and its owner frees the cell.)
    if (comptime (@sizeOf(@typeInfo(Dead).pointer.child) == @sizeOf(C) and @alignOf(@typeInfo(Dead).pointer.child) == @alignOf(C))) {
        if (tok.*) |p| {
            tok.* = null;
            std.debug.assert((p.@"$rc" & flag_mask) == 0);
            const c: *C = @ptrCast(@alignCast(p));
            c.* = init;
            // (a new cell: not the identity hash the dead one was given)
            if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(c));
            if (comptime hasGc(C)) {
                // (a cell that is built in again is a new cell: it gets an age of its own)
                if (!thread.collector_ready) collectorSetup();
                thread.collector.allocs += 1;
                c.@"$gc" = gcHeader(C, c);
            }
            if (track) thread.stats.reuses += 1;
            return c;
        }
    }
    return null;
}

/// Reuse: build in the dead cell that `tok` holds, if it holds one; allocate otherwise.
pub inline fn cellReuse(comptime T: type, comptime tag: std.meta.Tag(T), tok: anytype, init: Cell(T, tag)) *Cell(T, tag) {
    return reuseCellPtr(Cell(T, tag), tok, init) orelse cell(T, tag, init);
}

/// (an atomic load: another thread may be changing a shared cell's count, which is then never
/// one; on the targets this is the plain load it was)
pub inline fn isUnique(c: anytype) bool {
    return @atomicLoad(u32, &c.@"$rc", .monotonic) == 1;
}

// ---- values shared between threads (Koka's Perceus) ----
//
// A cell's count is plain while one thread has it. A value made reachable from another thread
// is first marked shared, with everything it reaches (`markShared`): the top bit of the count.
// The count of a shared cell is changed atomically; one test of that bit is what the others
// pay. A shared cell is never unique (`isUnique`), so it is never changed in place. Cells the
// cycle collector follows cannot be shared (the collector belongs to one thread).

pub const shared_bit: u32 = 1 << 31;
pub const immortal_bit: u32 = 1 << 30;
pub const weak_bit: u32 = 1 << 29;
pub const flag_mask: u32 = shared_bit | immortal_bit | weak_bit;
pub const count_mask: u32 = ~flag_mask;

comptime {
    std.debug.assert(sgc.rc_count_mask == count_mask);
}

/// Mark a value shared between threads, with everything it reaches. A cell the cycle collector
/// follows cannot be shared: NotSupportedException.
pub fn markShared(x: anytype) Raised!void {
    const T = @TypeOf(x);
    if (comptime !isManaged(T)) return;
    if (comptime isFunc(T)) {
        const e = x.env orelse return;
        if (!try markCell(e)) return;
        return e.share(e);
    }
    if (comptime isIface(T)) {
        return x.vt.@"$meta".share(x.data);
    }
    if (T == Obj) {
        if (!try markCell(x)) return;
        return x.type.share(x);
    }
    if (T == Exn) {
        if (!try markCell(x)) return;
        return x.type.share(x);
    }
    if (T == String) {
        const p = x orelse return;
        const rc = @atomicLoad(u32, &p.rc, .monotonic);
        if (rc != Str.literal and rc & shared_bit == 0) {
            // (made in a `[<StackArena>]` function: its memory is that function's stack)
            if (inThreadArena(p)) {
                if (thread.share_probe) |pr| pr.reason = .stack_arena;
                return notShareable("a string made in a [<StackArena>] function", " Copy or allocate the string outside the [<StackArena>] function first.");
            }
            if (thread.share_probe == null) p.rc = rc | shared_bit;
        }
        return;
    }
    if (comptime isSlice(T)) {
        for (x) |item| try markShared(item);
        return;
    }
    // (a weak reference: shared with its target and its handle, see fable_on_share in fable_weak.zig)
    switch (@typeInfo(T)) {
        .pointer => try shareCells(T, x),
        .optional => if (x) |v| try markShared(v),
        .@"struct" => |s| inline for (s.field_names) |name| try markShared(@field(x, name)),
        .@"union" => if (comptime isHeapUnion(T)) try shareCells(T, x) else switch (x) {
            inline else => |p| try markShared(p),
        },
        else => comptime unreachable,
    }
}

const iso_mod = @import("fable_iso.zig");
pub const adoptShared = iso_mod.adoptShared;
pub const transferOrShareOrRaise = iso_mod.transferOrShareOrRaise;
pub const tryReclaimHomeCell = iso_mod.tryReclaimHomeCell;
pub const Iso = iso_mod.Iso;
pub const IsoRegion = iso_mod.Region;
pub const isoPack = iso_mod.isoPack;
pub const isoTryPack = iso_mod.isoTryPack;
pub const isoSend = iso_mod.isoSend;
pub const isoHold = iso_mod.isoHold;
pub const isoPeek = iso_mod.isoPeek;
pub const isoUnpack = iso_mod.isoUnpack;

/// `markShared`, or false where the value reaches a cell the cycle collector follows (what was
/// marked before it stays marked: its counts are atomic from then on, which is still right)
pub fn tryMarkShared(x: anytype) bool {
    markShared(x) catch {
        drop(take());
        return false;
    };
    return true;
}

/// A value stored into a shared cell is shared too. (Reading and writing a shared cell's
/// fields from several threads at once needs a `lock`, as on .NET.)
pub fn shareStored(value: anytype) void {
    markShared(value) catch {
        const e = take();
        defer drop(e);
        // (why it cannot be shared: a value the cycle collector follows inside a structure, or one
        // made in a `[<StackArena>]`)
        const msg = exnMessage(e);
        defer drop(msg);
        write_err("fable: a value that cannot be shared between threads reached another thread: ");
        writeText(write_err, msg, true);
        @panic("fable: a value that cannot be shared between threads reached another thread");
    };
}

const thread_mod = @import("fable_thread.zig");
pub const ThreadStart = thread_mod.ThreadStart;
pub const ThreadOf = thread_mod.ThreadOf;
pub const threadNew = thread_mod.threadNew;
pub const threadStart = thread_mod.threadStart;
pub const threadJoin = thread_mod.threadJoin;
pub const threadIsAlive = thread_mod.threadIsAlive;
pub const threadId = thread_mod.threadId;
pub const poolNew = thread_mod.poolNew;
pub const poolStart = thread_mod.poolStart;
pub const poolRunWorkers = thread_mod.poolRunWorkers;
pub const poolShutdown = thread_mod.poolShutdown;
pub const futexWait = thread_mod.futexWait;
pub const futexWake = thread_mod.futexWake;
pub const waitUntilSet = thread_mod.waitUntilSet;
pub const setAndWakeAll = thread_mod.setAndWakeAll;
pub const lockEnter = thread_mod.lockEnter;
pub const lockExit = thread_mod.lockExit;
pub const lockRun = thread_mod.lockRun;
pub const parallelFor = thread_mod.parallelFor;
pub const parallelForRange = thread_mod.parallelForRange;

/// `obj ()`: an object of no class of the program's, to lock on or compare by reference
pub fn objectNew() Obj {
    return objNew(&object_type, PlainObjectChain{ .own = .{} });
}

const PlainObjectChain = struct { own: struct {} };
const object_type: ObjType = objType(PlainObjectChain, "System.Object", null, &.{}, null);

fn notShareable(what: []const u8, hint: []const u8) Raised {
    var b: TextBuilder = .{};
    b.addAscii("The Zig target cannot share ");
    b.addAscii(what);
    b.addAscii(" between threads.");
    b.addAscii(hint);
    return raise(NotSupportedException, b.finish());
}

/// Set the shared bit of a cell: false if it was set already
pub fn markCell(c: anytype) Raised!bool {
    const rc = @atomicLoad(u32, &c.@"$rc", .monotonic);
    // (shared already: other threads may be changing the count; static immortal cells already have shared_bit set,
    // while thread-local immortal null cells need shared_bit set so collectorDeinit leaves them alive)
    if (rc & shared_bit != 0) return false;
    // (made in a `[<StackArena>]` function of this thread: its memory is that function's stack,
    // which another thread would free on the heap)
    if (comptime uses_arena) {
        if (thread.arena != null) {
            const bytes: [*]u8 = @ptrCast(c);
            if (arenaOwning(bytes[0..@sizeOf(@TypeOf(c.*))]) != null) {
                if (thread.share_probe) |pr| pr.reason = .stack_arena;
                return notShareable("a value made in a [<StackArena>] function", " Allocate the value outside the [<StackArena>] function before sharing it.");
            }
        }
    }
    // (a cell the collector follows leaves it when it is shared, unless it is part of a
    // structure of cells already, where its count is the collector's business. The collector
    // does not look at shared cells: a cycle made through them afterwards is not freed, as
    // Koka frees no cycles at all; see Zig_Roadmap.md)
    if (gcOf(c)) |h| {
        if (sgc.inStructure(h)) {
            if (thread.share_probe) |pr| pr.reason = .cyclic_structure;
            return notShareable("a value that is part of a cyclic structure tracked by fable_sgc", " Break the cycle with WeakReference or move the whole isolated graph with Fable.Core.Zig.Iso.pack.");
        }
    }
    // Dry-run validation pass (Region.closed): validate shareability without mutating cells or weak handles.
    if (thread.share_probe) |pr| {
        const e = pr.seen.getOrPut(bookkeeping(), @intFromPtr(c)) catch oom();
        return !e.found_existing;
    }
    // (weak references point at it: their handle moves to the table of shared cells, which a
    // thread that frees it empties)
    if (rc & weak_bit != 0) weak_refs.shareWeakHandle(@intFromPtr(c));
    c.@"$rc" = rc | shared_bit;
    return true;
}

/// A cell (or a list's cells, or a tree's) and what it holds. The field of a cell that has the
/// value's own type is followed in a loop, so a long list does not use stack in proportion.
fn shareCells(comptime T: type, x: T) Raised!void {
    var cur = x;
    while (true) {
        var next: ?T = null;
        switch (@typeInfo(T)) {
            .pointer => {
                if (!try markCell(cur)) return;
                if (comptime @hasDecl(@typeInfo(T).pointer.child, "fable_on_share")) try @typeInfo(T).pointer.child.fable_on_share(cur);
                inline for (@typeInfo(@typeInfo(T).pointer.child).@"struct".field_names) |name| {
                    if (comptime isCount(name)) continue;
                    const F = @TypeOf(@field(cur, name));
                    if (F == T) next = @field(cur, name) else if (F == ?T) next = @field(cur, name) else try markShared(@field(cur, name));
                }
            },
            else => switch (cur) {
                inline else => |p| {
                    const P = @TypeOf(p);
                    if (comptime !isCellPtr(P)) {
                        try markShared(p);
                    } else if (try markCell(p)) {
                        inline for (@typeInfo(@typeInfo(P).pointer.child).@"struct".field_names) |name| {
                            if (comptime isCount(name)) continue;
                            if (@TypeOf(@field(p, name)) == T) next = @field(p, name) else try markShared(@field(p, name));
                        }
                    }
                },
            },
        }
        cur = next orelse return;
    }
}

pub inline fn isShared(c: anytype) bool {
    return @atomicLoad(u32, &c.@"$rc", .monotonic) & shared_bit != 0;
}

pub inline fn retain(c: anytype) void {
    const rc = @atomicLoad(u32, &c.@"$rc", .monotonic);
    if (rc < immortal_bit) {
        std.debug.assert((rc & count_mask) < count_mask);
        c.@"$rc" = rc + 1;
        if (track) thread.stats.dups += 1;
        if (gcOf(c)) |h| thread.collector.onRetain(h);
        return;
    }
    if (rc & immortal_bit != 0) return;
    _ = @atomicRmw(u32, &c.@"$rc", .Add, 1, .monotonic);
}

/// Take one reference off a cell that is known to be shared (or immortal).
pub inline fn release(c: anytype) void {
    const rc = @atomicLoad(u32, &c.@"$rc", .monotonic);
    if (rc < immortal_bit) {
        c.@"$rc" = rc - 1;
        if (track) thread.stats.decs += 1;
        if (gcOf(c)) |h| thread.collector.onRelease(h);
        return;
    }
    if (rc & immortal_bit != 0) return;
    _ = @atomicRmw(u32, &c.@"$rc", .Sub, 1, .release);
}

/// Take one reference off; true when it was the last one, and the caller gives up what the
/// cell holds and frees it. (False also when the cell's whole structure died with this
/// reference: the collector frees all of it, this cell included.)
pub inline fn releaseIsLast(c: anytype) bool {
    const rc = @atomicLoad(u32, &c.@"$rc", .monotonic);
    if (rc < weak_bit) {
        if (rc != 1) {
            c.@"$rc" = rc - 1;
            if (track) thread.stats.decs += 1;
            if (gcOf(c)) |h| thread.collector.onRelease(h);
            return false;
        }
        if (gcOf(c)) |h| return !thread.collector.onZero(h);
        return true;
    }
    if (rc & immortal_bit != 0) return false;
    if (rc & shared_bit != 0) {
        // (the last reference of any thread: what the others wrote is seen before it is freed)
        const prev = @atomicRmw(u32, &c.@"$rc", .Sub, 1, .acq_rel);
        return (prev & count_mask) == 1;
    }
    if ((rc & count_mask) != 1) {
        c.@"$rc" = rc - 1;
        if (track) thread.stats.decs += 1;
        if (gcOf(c)) |h| thread.collector.onRelease(h);
        return false;
    }
    if (gcOf(c)) |h| return !thread.collector.onZero(h);
    return true;
}

/// A cell that is not shared is taken apart without its count going to zero: its fields are
/// about to be moved out or given up.
pub inline fn forget(c: anytype) void {
    if (gcOf(c)) |h| thread.collector.onFree(h);
}

/// A reference left a cell that is being taken apart and went to a variable as it is.
pub inline fn touch(x: anytype) void {
    eachHdr(x, {}, movedOut);
}

pub fn movedOut(_: void, h: *sgc.Hdr) void {
    thread.collector.onMoveOut(h);
}

inline fn rcWeakTarget(c: anytype) ?struct { rc: *const u32, addr: usize } {
    const C = @TypeOf(c.*);
    if (comptime @hasField(C, "$rc")) return .{ .rc = &c.@"$rc", .addr = @intFromPtr(c) };
    if (comptime @hasField(C, "header") and @hasField(@FieldType(C, "header"), "$rc")) return .{ .rc = &c.header.@"$rc", .addr = @intFromPtr(&c.header) };
    if (comptime @hasDecl(C, "fable_rc_header")) return .{ .rc = &@as(*const C.fable_rc_header, @ptrCast(@alignCast(c))).@"$rc", .addr = @intFromPtr(c) };
    return null;
}

pub inline fn free(c: anytype) void {
    if (track) thread.stats.frees += 1;
    // (a cell that weak references point at: they see it is gone. A shared cell's are in the
    // table of all threads)
    if (rcWeakTarget(c)) |info| {
        const rc = @atomicLoad(u32, info.rc, .monotonic);
        if (rc & weak_bit != 0) {
            if (rc & shared_bit != 0) {
                weak_refs.sharedWeakGone(info.addr);
            } else {
                weakGone(info.addr);
            }
        }
    }
    // (a cell whose identity hash was taken: the next cell made here gets a new one)
    if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(c));
    // (the blocks a cell holds besides itself: an array's items, a dictionary's entries)
    if (comptime @hasDecl(@TypeOf(c.*), "fable_array")) {
        if (c.capacity != 0) alloc().free(c.items.ptr[0..c.capacity]);
    }
    if (comptime @hasDecl(@TypeOf(c.*), "fable_free")) @TypeOf(c.*).fable_free(c);
    alloc().destroy(c);
}

/// The items of an array, as a field of its cell.
pub fn isSlice(comptime T: type) bool {
    const info = @typeInfo(T);
    return info == .pointer and info.pointer.size == .slice;
}

/// The count and the collector's header are not part of what a cell holds.
pub fn isCount(comptime field_name: []const u8) bool {
    return std.mem.eql(u8, field_name, "$rc") or std.mem.eql(u8, field_name, "$gc");
}

pub fn isCellPtr(comptime T: type) bool {
    const info = @typeInfo(T);
    if (info != .pointer or info.pointer.size != .one) return false;
    const C = info.pointer.child;
    return @typeInfo(C) == .@"struct" and @hasField(C, "$rc");
}

/// Does a value of this type hold references to cells? (Does not look through a cell.)
pub fn isManaged(comptime T: type) bool {
    if (comptime isKnown(T)) return false;
    if (T == String) return true;
    if (comptime isResource(T)) return true;
    if (isCellPtr(T)) return true;
    if (comptime isFunc(T)) return true;
    if (comptime isIface(T)) return true;
    if (isSlice(T)) return isManaged(@typeInfo(T).pointer.child);
    switch (@typeInfo(T)) {
        .optional => |o| return isManaged(o.child),
        .@"struct" => |s| {
            inline for (s.field_types) |F| {
                if (isManaged(F)) return true;
            }
            return false;
        },
        .@"union" => |u| {
            inline for (u.field_types) |F| {
                if (isManaged(F)) return true;
            }
            return false;
        },
        else => return false,
    }
}

/// A resource (`IResource<'T>`): a value whose hooks the runtime calls.
fn isResource(comptime T: type) bool {
    return switch (@typeInfo(T)) {
        .@"struct", .@"union" => @hasDecl(T, "fable_destroy"),
        else => false,
    };
}

/// Call a hook of a resource; what it raises is given up (a hook runs where nothing can
/// handle it: when a value is given up or copied).
inline fn callHook(hook: anytype, x: anytype) void {
    const r = hook(x);
    if (comptime @typeInfo(@TypeOf(r)) == .error_union) {
        if (r) |v| {
            if (@TypeOf(v) != void) {} // (the copy Dup gives is the value itself: it shares)
        } else |_| drop(take());
    }
}

/// A union whose cases are cells: the handle of a recursive union. (Every case with fields is
/// a cell of its own; an exception is a cell too, so a union that holds one among other
/// values is not one.)
fn isHeapUnion(comptime T: type) bool {
    switch (@typeInfo(T)) {
        .@"union" => |u| {
            var any = false;
            inline for (u.field_types) |F| {
                if (F == void) continue;
                if (!isCellPtr(F) or F == Exn or F == Obj) return false;
                any = true;
            }
            return any;
        },
        else => return false,
    }
}

/// Make a borrowed value an owned one: one more reference to every cell it points to directly.
pub inline fn dup(x: anytype) @TypeOf(x) {
    retainAll(x);
    return x;
}

pub fn retainAll(x: anytype) void {
    const T = @TypeOf(x);
    if (comptime !isManaged(T)) return;
    if (comptime isFunc(T)) {
        if (x.env) |e| retain(e);
        return;
    }
    if (comptime isIface(T)) {
        x.vt.@"$meta".retain(x.data);
        return;
    }
    if (T == String) return strRetain(x);
    // (a resource: shared resources invoke Dup; move-only resources cannot be copied)
    if (comptime isResource(T)) {
        if (comptime !@hasDecl(T, "fable_dup")) {
            @compileError("fable: cannot copy move-only IResource " ++ @typeName(T));
        }
        callHook(T.fable_dup, x);
        if (track) thread.stats.copies += 1;
    }
    switch (@typeInfo(T)) {
        .pointer => retain(x),
        .optional => if (x) |v| retainAll(v),
        .@"struct" => |s| inline for (s.field_names) |name| retainAll(@field(x, name)),
        .@"union" => switch (x) {
            inline else => |p| retainAll(p),
        },
        else => comptime unreachable,
    }
}

/// Give up an owned value: take one reference off every cell it points to directly, and free
/// the cells that were not shared, giving up what they hold.
pub fn drop(x: anytype) void {
    const T = @TypeOf(x);
    if (comptime !isManaged(T)) return;
    if (comptime isFunc(T)) {
        dropEnv(x.env);
        return;
    }
    if (comptime isIface(T)) {
        x.vt.@"$meta".drop(x.data);
        return;
    }
    if (T == Exn or T == Obj) {
        if (releaseIsLast(x)) x.type.destroy(x);
        return;
    }
    if (T == String) return strRelease(x);
    if (comptime isSlice(T)) {
        for (x) |item| drop(item);
        return;
    }
    // (a resource is destroyed, then what it holds is given up)
    if (comptime isResource(T)) {
        callHook(T.fable_destroy, x);
        if (track) thread.stats.destroys += 1;
    }
    switch (@typeInfo(T)) {
        .pointer => dropRecord(T, x),
        .optional => if (x) |v| drop(v),
        .@"struct" => |s| inline for (s.field_names) |name| drop(@field(x, name)),
        .@"union" => if (comptime isHeapUnion(T)) dropHeap(T, x) else switch (x) {
            inline else => |p| drop(p),
        },
        else => comptime unreachable,
    }
}

/// The last field of a cell that has the union's own type is followed in a loop, so giving up
/// a long list (or the right spine of a tree) does not use stack in proportion to its length.
fn dropHeap(comptime T: type, x: T) void {
    var cur = x;
    while (true) {
        switch (cur) {
            inline else => |c| {
                if (@TypeOf(c) == void) {
                    return;
                } else {
                    if (!releaseIsLast(c)) return;
                    const info = @typeInfo(@TypeOf(c.*)).@"struct";
                    const self_field: ?usize = comptime blk: {
                        var found: ?usize = null;
                        for (info.field_types, 0..) |F, i| {
                            if (F == T) found = i;
                        }
                        break :blk found;
                    };
                    inline for (info.field_names, 0..) |name, i| {
                        if (comptime !isCount(name) and (self_field == null or self_field.? != i)) {
                            drop(@field(c, name));
                        }
                    }
                    if (self_field) |i| {
                        const next: T = @field(c, info.field_names[i]);
                        free(c);
                        cur = next;
                    } else {
                        free(c);
                        return;
                    }
                }
            },
        }
    }
}

/// A reference record. Its last field of the record's own type (or an option of it) is
/// followed in a loop, so giving up a long chain of records does not use stack in proportion
/// to its length.
fn dropRecord(comptime P: type, x: P) void {
    const info = @typeInfo(@typeInfo(P).pointer.child).@"struct";
    const self_field: ?usize = comptime blk: {
        var found: ?usize = null;
        for (info.field_types, 0..) |F, i| {
            if (F == P or F == ?P) found = i;
        }
        break :blk found;
    };
    var cur = x;
    while (true) {
        if (!releaseIsLast(cur)) return;
        inline for (info.field_names, 0..) |name, i| {
            if (comptime !isCount(name) and (self_field == null or self_field.? != i)) {
                drop(@field(cur, name));
            }
        }
        if (self_field) |i| {
            const next: ?P = @field(cur, info.field_names[i]);
            free(cur);
            cur = next orelse return;
        } else {
            free(cur);
            return;
        }
    }
}

// ---- `Map` and `Set`: trees (Map.fs, Set.fs) that are compared by what they hold ----

pub fn isCollection(comptime T: type) bool {
    return @typeInfo(T) == .@"union" and @hasDecl(T, "fable_collection");
}

/// The entries of a map or a set, in order: the cells of its tree from left to right.
pub fn TreeWalk(comptime T: type) type {
    const Node = @typeInfo(@typeInfo(T).@"union".field_types[1]).pointer.child;
    return struct {
        stack: [64]*Node = undefined,
        len: usize = 0,

        pub fn init(tree: T) @This() {
            var w: @This() = .{};
            w.pushLeft(tree);
            return w;
        }

        pub fn pushLeft(w: *@This(), tree: T) void {
            var t = tree;
            while (true) {
                switch (t) {
                    inline else => |p| {
                        if (@TypeOf(p) == void) return;
                        w.stack[w.len] = p;
                        w.len += 1;
                        t = p.left;
                    },
                }
            }
        }

        pub fn next(w: *@This()) ?*Node {
            if (w.len == 0) return null;
            w.len -= 1;
            const n = w.stack[w.len];
            w.pushLeft(n.right);
            return n;
        }
    };
}

/// An entry as F# sees it: the item of a set, the `(key, value)` of a map.
fn entryEql(a: anytype, b: @TypeOf(a)) bool {
    if (comptime @hasField(@TypeOf(a.*), "value")) return eql(a.key, b.key) and eql(a.value, b.value);
    return eql(a.key, b.key);
}

pub fn entryCompare(a: anytype, b: @TypeOf(a)) i32 {
    const c = compare(a.key, b.key);
    if (c != 0) return c;
    if (comptime @hasField(@TypeOf(a.*), "value")) return compare(a.value, b.value);
    return 0;
}

pub fn treeEql(a: anytype, b: @TypeOf(a)) bool {
    var x = TreeWalk(@TypeOf(a)).init(a);
    var y = TreeWalk(@TypeOf(a)).init(b);
    while (true) {
        const p = x.next();
        const q = y.next();
        if (p == null or q == null) return p == null and q == null;
        if (!entryEql(p.?, q.?)) return false;
    }
}

pub fn treeCompare(a: anytype, b: @TypeOf(a)) i32 {
    var x = TreeWalk(@TypeOf(a)).init(a);
    var y = TreeWalk(@TypeOf(a)).init(b);
    while (true) {
        const p = x.next() orelse return if (y.next() == null) 0 else -1;
        const q = y.next() orelse return 1;
        const c = entryCompare(p, q);
        if (c != 0) return c;
    }
}

pub fn treeHash(x: anytype) i32 {
    var w = TreeWalk(@TypeOf(x)).init(x);
    var h: i32 = 17;
    while (w.next()) |n| {
        h = hashWith(h, hash(n.key));
        if (comptime @hasField(@TypeOf(n.*), "value")) h = hashWith(h, hash(n.value));
    }
    return h;
}

/// Structural equality, as F#'s `=` on records, unions, tuples and options.
/// A record or union with `[<ReferenceEquality>]` (or `[<NoEquality>]`): its values are cells,
/// equal only to themselves
pub fn byReference(comptime T: type) bool {
    return hookOf(T, "fable_reference_equality");
}

pub fn eql(a: anytype, b: @TypeOf(a)) bool {
    const T = @TypeOf(a);
    if (T == reflect.Type) return reflect.equals(a, b);
    if (comptime byReference(T)) return std.meta.eql(a, b);
    if (comptime hookOf(T, "fable_equals")) return hookType(T).fable_equals.call(.{ a, box(b) });
    if (comptime isCollection(T)) return treeEql(a, b);
    if (comptime isSlice(T)) {
        if (a.len != b.len) return false;
        for (a, b) |x, y| {
            if (!eql(x, y)) return false;
        }
        return true;
    }
    if (comptime isBigInt(T)) return a.value.eql(b.value);
    if (comptime isDecimal(T)) return decCompare(a, b) == 0;
    // (.NET's mutable collections are equal only to themselves)
    if (comptime isCellPtr(T) and @hasDecl(@typeInfo(T).pointer.child, "fable_identity")) return a == b;
    // (an array is equal to another with equal items, as F#'s `=` has it)
    if (comptime isCellPtr(T) and @hasDecl(@typeInfo(T).pointer.child, "fable_array")) return a == b or (!arrayIsNull(a) and !arrayIsNull(b) and eql(a.items, b.items) and std.meta.eql(a.shape, b.shape));
    if (comptime !isManaged(T) and !holdsDecimal(T)) return std.meta.eql(a, b);
    // (a sequence is an object on .NET: equal only to itself, here the same walk and what it holds)
    if (comptime @typeInfo(T) == .@"struct" and @hasField(T, "fable_seq")) return a.fable_seq.env == b.fable_seq.env and a.fable_seq.code == b.fable_seq.code;
    // (F# does not compare function values; what does is an interface value, a struct of them
    // that stands for an object, which .NET compares by identity: the same code and environment)
    if (comptime isFunc(T)) return a.env == b.env and a.code == b.code;
    if (comptime isIface(T)) {
        if (a.data == b.data and a.vt == b.vt) return true;
        if (ifaceToObjBorrow(a)) |oa| {
            if (ifaceToObjBorrow(b)) |ob| return objEql(oa, ob);
        }
        return false;
    }
    if (T == Obj) return objEql(a, b);
    if (T == Exn) return a == b or (a.type == b.type and if (a.type.eql) |f| f(a, b) else false);
    if (T == String) return strEql(a, b);
    switch (@typeInfo(T)) {
        .pointer => |p| {
            if (a == b) return true;
            inline for (@typeInfo(p.child).@"struct".field_names) |name| {
                if (comptime !isCount(name)) {
                    if (!eql(@field(a, name), @field(b, name))) return false;
                }
            }
            return true;
        },
        .optional => {
            if (a) |x| {
                if (b) |y| return eql(x, y);
                return false;
            }
            return b == null;
        },
        .@"struct" => |s| {
            inline for (s.field_names) |name| {
                if (!eql(@field(a, name), @field(b, name))) return false;
            }
            return true;
        },
        .@"union" => {
            // (a recursive union is compared along its last field of its own type in a loop,
            // as `dropHeap` gives it up: a long list does not use the stack)
            var x = a;
            var y = b;
            while (true) {
                if (std.meta.activeTag(x) != std.meta.activeTag(y)) return false;
                switch (x) {
                    inline else => |px, tag| {
                        const py = @field(y, @tagName(tag));
                        const P = @TypeOf(px);
                        const self_field: ?[]const u8 = comptime blk: {
                            if (!isCellPtr(P)) break :blk null;
                            var found: ?[]const u8 = null;
                            const info = @typeInfo(@typeInfo(P).pointer.child).@"struct";
                            for (info.field_types, info.field_names) |F, name| {
                                if (F == T) found = name;
                            }
                            break :blk found;
                        };
                        if (comptime self_field == null) return eql(px, py);
                        if (px == py) return true;
                        inline for (@typeInfo(@typeInfo(P).pointer.child).@"struct".field_names) |name| {
                            if (comptime !isCount(name) and !std.mem.eql(u8, name, self_field.?)) {
                                if (!eql(@field(px, name), @field(py, name))) return false;
                            }
                        }
                        x = @field(px, self_field.?);
                        y = @field(py, self_field.?);
                    },
                }
            }
        },
        else => comptime unreachable,
    }
}

/// A new reference record (a record with mutable fields, or one that contains itself): a
/// pointer to a counted cell that holds the fields.
pub inline fn new(comptime P: type, init: @typeInfo(P).pointer.child) P {
    const C = @typeInfo(P).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = alloc().create(C) catch oom();
    c.* = init;
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

/// Reuse: build a reference record in the dead cell that `tok` holds, if it holds one; allocate otherwise.
pub inline fn newReuse(comptime P: type, tok: anytype, init: @typeInfo(P).pointer.child) P {
    return reuseCellPtr(@typeInfo(P).pointer.child, tok, init) orelse new(P, init);
}

/// Store into a variable or a field of a plain value that owns what it holds: the old value
/// is given up once the new one is in place.
pub inline fn store(place: anytype, value: @TypeOf(place.*)) void {
    const old = place.*;
    place.* = value;
    drop(old);
}

/// Store into a field of a reference record. The collector is told what the record no longer
/// points at and what it points at now: this is where a cycle can be closed.
pub inline fn storeIn(owner: anytype, comptime field: []const u8, value: @FieldType(@TypeOf(owner.*), field)) void {
    if (isShared(owner)) {
        // (Koka's protocol: the value is shared before another thread can read it, and swapped
        // in under the field's lock, so no reader holds the old one uncounted when it goes)
        shareStored(value);
        const l = fieldLock(owner);
        lockField(l);
        const prev = @field(owner, field);
        @field(owner, field) = value;
        unlockField(l);
        drop(prev);
        return;
    }
    const old = @field(owner, field);
    @field(owner, field) = value;
    if (gcOf(owner)) |h| {
        eachHdr(old, h, unstored);
        storeValue(h, value);
    } else {
        touch(value);
    }
    drop(old);
}

// ---- reading and writing the assignable fields of shared values (Koka's protocol) ----
//
// A field that can be assigned is read with its own reference (`loadIn`, `objLoad`): where the
// value it belongs to is shared between threads, the read and its count are made under the
// field's lock, which a store takes to swap the value in; the old value is given up after.
// Without it a thread could read a value another thread has just replaced and freed. The
// locks are a table of their own, never held while waiting for anything else, so they cannot
// deadlock with each other or with `lock`.

var field_locks: [64]u32 = @splat(0);

pub inline fn fieldLock(owner: anytype) *u32 {
    return &field_locks[(@intFromPtr(owner) >> 4) % field_locks.len];
}

pub inline fn lockField(l: *u32) void {
    while (@cmpxchgWeak(u32, l, 0, 1, .acquire, .monotonic) != null) std.atomic.spinLoopHint();
}

pub inline fn unlockField(l: *u32) void {
    @atomicStore(u32, l, 0, .release);
}

/// `owner.field` of a reference record, with its own reference
pub inline fn loadIn(owner: anytype, comptime field: []const u8) @FieldType(@TypeOf(owner.*), field) {
    if (!isShared(owner)) return dup(@field(owner, field));
    const l = fieldLock(owner);
    lockField(l);
    const v = dup(@field(owner, field));
    unlockField(l);
    return v;
}

/// a field of an object (`place` in its class's part), with its own reference
pub inline fn objLoad(o: Obj, place: anytype) @TypeOf(place.*) {
    if (!isShared(o)) return dup(place.*);
    const l = fieldLock(o);
    lockField(l);
    const v = dup(place.*);
    unlockField(l);
    return v;
}

pub fn unstored(owner: *sgc.Hdr, old: *sgc.Hdr) void {
    thread.collector.onUnstore(owner, old);
}

pub fn stored(owner: *sgc.Hdr, child: *sgc.Hdr) void {
    thread.collector.onStore(owner, child);
}

const StoreCtx = struct {
    owner: *sgc.Hdr,
    was_new: bool,
};

fn storeOne(ctx: StoreCtx, child: *sgc.Hdr) void {
    // When `owner` enters a structure on an earlier header of the same stored value, `.close`
    // already traces the whole newly written field, so only merge headers in other structures.
    if (ctx.was_new and ctx.owner.st != 0) {
        if (child.st == 0 or thread.collector.root(child) == thread.collector.root(ctx.owner)) return;
    }
    thread.collector.onStore(ctx.owner, child);
}

/// Report a newly stored composite value to the collector without double-counting sibling headers.
pub inline fn storeValue(owner: *sgc.Hdr, value: anytype) void {
    const ctx: StoreCtx = .{ .owner = owner, .was_new = owner.st == 0 };
    eachHdr(value, ctx, storeOne);
}

/// F#'s `ref` cell.
pub fn Ref(comptime T: type) type {
    return *struct {
        pub const fable_cyclic = holdsCyclic(T);
        @"$rc": u32 = 1,
        @"$gc": GcHdr(fable_cyclic) = undefined,
        contents: T,
    };
}

/// F#'s `Result`.
pub fn Result(comptime T: type, comptime E: type) type {
    return union(enum) {
        pub const fable_type = .{ .full_name = "Microsoft.FSharp.Core.FSharpResult`2", .kind = .@"union", .args = .{ T, E } };
        Ok: struct { ResultValue: T },
        Error: struct { ErrorValue: E },
    };
}

/// F#'s `Choice` of two to seven cases.
pub fn Choice2(comptime T1: type, comptime T2: type) type {
    return union(enum) {
        pub const fable_type = .{ .full_name = "Microsoft.FSharp.Core.FSharpChoice`2", .kind = .@"union", .args = .{ T1, T2 } };
        Choice1Of2: struct { Item: T1 },
        Choice2Of2: struct { Item: T2 },
    };
}

pub fn Choice3(comptime T1: type, comptime T2: type, comptime T3: type) type {
    return union(enum) {
        pub const fable_type = .{ .full_name = "Microsoft.FSharp.Core.FSharpChoice`3", .kind = .@"union", .args = .{ T1, T2, T3 } };
        Choice1Of3: struct { Item: T1 },
        Choice2Of3: struct { Item: T2 },
        Choice3Of3: struct { Item: T3 },
    };
}

pub fn Choice4(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type) type {
    return union(enum) {
        pub const fable_type = .{ .full_name = "Microsoft.FSharp.Core.FSharpChoice`4", .kind = .@"union", .args = .{ T1, T2, T3, T4 } };
        Choice1Of4: struct { Item: T1 },
        Choice2Of4: struct { Item: T2 },
        Choice3Of4: struct { Item: T3 },
        Choice4Of4: struct { Item: T4 },
    };
}

pub fn Choice5(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type) type {
    return union(enum) {
        pub const fable_type = .{ .full_name = "Microsoft.FSharp.Core.FSharpChoice`5", .kind = .@"union", .args = .{ T1, T2, T3, T4, T5 } };
        Choice1Of5: struct { Item: T1 },
        Choice2Of5: struct { Item: T2 },
        Choice3Of5: struct { Item: T3 },
        Choice4Of5: struct { Item: T4 },
        Choice5Of5: struct { Item: T5 },
    };
}

pub fn Choice6(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type) type {
    return union(enum) {
        pub const fable_type = .{ .full_name = "Microsoft.FSharp.Core.FSharpChoice`6", .kind = .@"union", .args = .{ T1, T2, T3, T4, T5, T6 } };
        Choice1Of6: struct { Item: T1 },
        Choice2Of6: struct { Item: T2 },
        Choice3Of6: struct { Item: T3 },
        Choice4Of6: struct { Item: T4 },
        Choice5Of6: struct { Item: T5 },
        Choice6Of6: struct { Item: T6 },
    };
}

pub fn Choice7(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type) type {
    return union(enum) {
        pub const fable_type = .{ .full_name = "Microsoft.FSharp.Core.FSharpChoice`7", .kind = .@"union", .args = .{ T1, T2, T3, T4, T5, T6, T7 } };
        Choice1Of7: struct { Item: T1 },
        Choice2Of7: struct { Item: T2 },
        Choice3Of7: struct { Item: T3 },
        Choice4Of7: struct { Item: T4 },
        Choice5Of7: struct { Item: T5 },
        Choice6Of7: struct { Item: T6 },
        Choice7Of7: struct { Item: T7 },
    };
}

/// An anonymous record with these fields (F# sorts them by name): one type per shape,
/// whichever file makes it. `Anon2(.{ "Age", "Name" }).of(i32, String)`.
pub fn Anon1(comptime names: [1][]const u8) type {
    return struct {
        pub fn of(comptime T1: type) type {
            return @Struct(.auto, null, &names, &.{T1}, &@splat(.{}));
        }
    };
}

pub fn Anon2(comptime names: [2][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2 }, &@splat(.{}));
        }
    };
}

pub fn Anon3(comptime names: [3][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3 }, &@splat(.{}));
        }
    };
}

pub fn Anon4(comptime names: [4][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4 }, &@splat(.{}));
        }
    };
}

pub fn Anon5(comptime names: [5][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5 }, &@splat(.{}));
        }
    };
}

pub fn Anon6(comptime names: [6][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6 }, &@splat(.{}));
        }
    };
}

pub fn Anon7(comptime names: [7][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7 }, &@splat(.{}));
        }
    };
}

pub fn Anon8(comptime names: [8][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8 }, &@splat(.{}));
        }
    };
}

pub fn Anon9(comptime names: [9][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9 }, &@splat(.{}));
        }
    };
}

pub fn Anon10(comptime names: [10][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10 }, &@splat(.{}));
        }
    };
}

pub fn Anon11(comptime names: [11][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11 }, &@splat(.{}));
        }
    };
}

pub fn Anon12(comptime names: [12][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12 }, &@splat(.{}));
        }
    };
}

pub fn Anon13(comptime names: [13][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13 }, &@splat(.{}));
        }
    };
}

pub fn Anon14(comptime names: [14][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14 }, &@splat(.{}));
        }
    };
}

pub fn Anon15(comptime names: [15][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15 }, &@splat(.{}));
        }
    };
}

pub fn Anon16(comptime names: [16][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16 }, &@splat(.{}));
        }
    };
}

pub fn Anon17(comptime names: [17][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17 }, &@splat(.{}));
        }
    };
}

pub fn Anon18(comptime names: [18][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18 }, &@splat(.{}));
        }
    };
}

pub fn Anon19(comptime names: [19][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19 }, &@splat(.{}));
        }
    };
}

pub fn Anon20(comptime names: [20][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20 }, &@splat(.{}));
        }
    };
}

pub fn Anon21(comptime names: [21][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21 }, &@splat(.{}));
        }
    };
}

pub fn Anon22(comptime names: [22][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type, comptime T22: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22 }, &@splat(.{}));
        }
    };
}

pub fn Anon23(comptime names: [23][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type, comptime T22: type, comptime T23: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23 }, &@splat(.{}));
        }
    };
}

pub fn Anon24(comptime names: [24][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type, comptime T22: type, comptime T23: type, comptime T24: type) type {
            return @Struct(.auto, null, &names, &.{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24 }, &@splat(.{}));
        }
    };
}

/// F#'s `lazy`: the code that computes the value, then the value, or the exception the code
/// raised, which every later `Force` raises again (as on .NET).
pub fn Lazy(comptime T: type) type {
    return *struct {
        const Self = @This();
        pub const fable_identity = {};
        pub const fable_cyclic = functions_in_cycles or holdsCyclic(T);
        pub const fable_args = .{T};
        @"$rc": u32 = 1,
        @"$gc": GcHdr(fable_cyclic) = undefined,
        state: union(enum) {
            thunk: Func(*const fn (?*Env, void) Raised!T),
            value: T,
            failed: Exn,
        },

        pub fn fable_show(b: *Shower, x: *Self, depth: i32) *Layout {
            return fable_show_shape(b, x, .{}, .{ .kind = .auto }, depth);
        }

        pub fn fable_show_shape(b: *Shower, x: *Self, comptime shape: TypeShape, node: ShowNode, depth: i32) *Layout {
            const child: u16 = if (node.kind == .seq) node.a else ShowNode.auto;
            return switch (x.state) {
                // (.NET writes the value's ToString)
                .value => |v| showPlainShape(b, v, shape, child, depth),
                else => b.word("Value is not created."),
            };
        }
    };
}

/// `lazy (expr)`
pub fn lazyNew(comptime L: type, thunk: anytype) L {
    const C = @typeInfo(L).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = alloc().create(C) catch oom();
    c.* = .{ .state = .{ .thunk = dup(thunk) } };
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

/// `Lazy.CreateFromValue v`
pub fn lazyOf(comptime L: type, value: anytype) L {
    const C = @typeInfo(L).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = alloc().create(C) catch oom();
    c.* = .{ .state = .{ .value = dup(value) } };
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

pub fn lazyState(l: anytype, new_state: @TypeOf(l.state)) void {
    const old = l.state;
    l.state = new_state;
    if (gcOf(l)) |h| {
        eachHdr(old, h, unstored);
        storeValue(h, l.state);
    } else touch(l.state);
    drop(old);
}

/// `l.Force()`, `l.Value`. A lazy value shared between threads is made once, as .NET's
/// default (thread-safe) one is: under its lock, the state looked at again there.
pub fn lazyForce(l: anytype) Raised!@FieldType(@TypeOf(l.state), "value") {
    if (isShared(l)) {
        const key = @intFromPtr(l);
        lockEnter(key);
        defer lockExit(key);
        return lazyForceHere(l);
    }
    return lazyForceHere(l);
}

fn lazyForceHere(l: anytype) Raised!@FieldType(@TypeOf(l.state), "value") {
    switch (l.state) {
        .value => |v| return dup(v),
        .failed => |e| {
            throw(dup(e));
            return error.Raised;
        },
        .thunk => |f| {
            // (the code is kept alive while it runs: it may drop the last other reference)
            const code = dup(f);
            defer drop(code);
            const v = code.code(code.env, {}) catch |err| {
                const e = take();
                lazyState(l, .{ .failed = dup(e) });
                throw(e);
                return err;
            };
            lazyState(l, .{ .value = v });
            return dup(v);
        },
    }
}

pub fn lazyIsCreated(l: anytype) bool {
    return l.state == .value;
}

/// F#'s list.
pub fn List(comptime T: type) type {
    return union(enum) {
        pub const fable_cyclic = holdsCyclic(T);
        pub const fable_list = {};
        pub const fable_type = .{ .full_name = "Microsoft.FSharp.Collections.FSharpList`1", .kind = .@"union", .args = .{T} };
        Empty,
        Cons: *struct { @"$rc": u32 = 1, @"$gc": GcHdr(fable_cyclic) = undefined, Head: T, Tail: List(T) },
    };
}

pub const arrays = @import("fable_array.zig");
pub const Array = arrays.Array;
pub const ItemOf = arrays.ItemOf;
pub const arrayAbandon = arrays.arrayAbandon;
pub const arrayAppend = arrays.arrayAppend;
pub const arrayContains = arrays.arrayContains;
pub const arrayCopy = arrays.arrayCopy;
pub const arrayCreate = arrays.arrayCreate;
pub const arrayExists = arrays.arrayExists;
pub const arrayFill = arrays.arrayFill;
pub const arrayFilter = arrays.arrayFilter;
pub const arrayFilterInPlace = arrays.arrayFilterInPlace;
pub const arrayFold = arrays.arrayFold;
pub const arrayForall = arrays.arrayForall;
pub const arrayFrom = arrays.arrayFrom;
pub const arrayNull = arrays.arrayNull;
pub const arrayIsNull = arrays.arrayIsNull;
pub const arrayGet = arrays.arrayGet;
pub const arrayItemAt = arrays.arrayItemAt;
pub const arrayInit = arrays.arrayInit;
pub const arrayItems = arrays.arrayItems;
pub const arrayIter = arrays.arrayIter;
pub const arrayIteri = arrays.arrayIteri;
pub const arrayLen = arrays.arrayLen;
pub const arrayMap = arrays.arrayMap;
pub const arrayMapInPlace = arrays.arrayMapInPlace;
pub const arrayMapi = arrays.arrayMapi;
pub const arrayMapiInPlace = arrays.arrayMapiInPlace;
pub const arrayOf = arrays.arrayOf;
pub const arrayOfList = arrays.arrayOfList;
pub const arrayPut = arrays.arrayPut;
pub const arrayRev = arrays.arrayRev;
pub const arraySet = arrays.arraySet;
pub const arraySetAt = arrays.arraySetAt;
pub const arraySlice = arrays.arraySlice;
pub const arraySort = arrays.arraySort;
pub const arraySortByKeys = arrays.arraySortByKeys;
pub const arraySortDesc = arrays.arraySortDesc;
pub const arraySortInPlace = arrays.arraySortInPlace;
pub const arraySortInPlaceByKeys = arrays.arraySortInPlaceByKeys;
pub const arraySortInPlaceWith = arrays.arraySortInPlaceWith;
pub const arraySortWith = arrays.arraySortWith;
pub const arraySub = arrays.arraySub;
pub const arrayToList = arrays.arrayToList;
pub const arrayZero = arrays.arrayZero;
pub const arrayResize = arrays.arrayResize;
pub const arrayBoxAll = arrays.arrayBoxAll;
pub const arrayParallelMap = arrays.arrayParallelMap;
pub const arrayParallelMapi = arrays.arrayParallelMapi;
pub const arrayParallelInit = arrays.arrayParallelInit;
pub const arrayParallelIter = arrays.arrayParallelIter;
pub const ArrayBuf = arrays.ArrayBuf;
pub const arrayBufNew = arrays.arrayBufNew;
pub const arrayBufPush = arrays.arrayBufPush;
pub const arrayBufFinish = arrays.arrayBufFinish;
pub const arrayBufAbandon = arrays.arrayBufAbandon;
pub const MapBuf = arrays.MapBuf;
pub const arrayMapBufNew = arrays.arrayMapBufNew;
pub const arrayMapBufLen = arrays.arrayMapBufLen;
pub const arrayMapBufTake = arrays.arrayMapBufTake;
pub const arrayMapBufPush = arrays.arrayMapBufPush;
pub const arrayMapBufFinish = arrays.arrayMapBufFinish;
pub const arrayMapBufAbandon = arrays.arrayMapBufAbandon;
pub const FilterBuf = arrays.FilterBuf;
pub const arrayFilterNew = arrays.arrayFilterNew;
pub const arrayFilterSet = arrays.arrayFilterSet;
pub const arrayFilterFinish = arrays.arrayFilterFinish;
pub const arrayFilterAbandon = arrays.arrayFilterAbandon;
pub const FilterReuseBuf = arrays.FilterReuseBuf;
pub const arrayFilterBufNew = arrays.arrayFilterBufNew;
pub const arrayFilterBufLen = arrays.arrayFilterBufLen;
pub const arrayFilterBufItem = arrays.arrayFilterBufItem;
pub const arrayFilterBufStep = arrays.arrayFilterBufStep;
pub const arrayFilterBufFinish = arrays.arrayFilterBufFinish;
pub const arrayFilterBufAbandon = arrays.arrayFilterBufAbandon;
pub const indexOutside = arrays.indexOutside;
pub const listOf = arrays.listOf;
test {
    _ = arrays;
}

// ---------------------------------------------------------------------------------------------
// .NET's mutable collections: List<T> (F#'s ResizeArray), Dictionary<K, V>, HashSet<T>
//
// Counted cells like an array, equal only to themselves as on .NET. A dictionary and a hash
// set are .NET's own design (buckets that chain into an array of entries, and a list of the
// entries that were freed), so that they hold their entries in the order .NET does and a loop
// over them sees what it sees on .NET.
// ---------------------------------------------------------------------------------------------

/// `seq [a; b; c; d; ...]`: how `%A` writes a .NET collection (four items, then `...`).
pub fn showSeq(b: *Shower, items: []const *Layout, more: bool) *Layout {
    var all: std.ArrayList(*Layout) = .empty;
    all.appendSlice(b.arena, items) catch oom();
    if (more) all.append(b.arena, b.word("...")) catch oom();
    const list = if (all.items.len == 0)
        b.word("[]")
    else
        b.tight(b.tight(b.ascii(false, "[", true), b.separated(all.items, ";")), b.ascii(true, "]", false));
    return b.join(b.word("seq"), list, .{ .breakable = 2 });
}

pub fn outOfRange() Raised {
    return raise(ArgumentOutOfRangeException, str("Index was out of range. Must be non-negative and less than the size of the collection. (Parameter 'index')"));
}

/// F#'s `ResizeArray<T>`: .NET's `List<T>`.
pub fn ResizeArray(comptime T: type) type {
    return *struct {
        const Self = @This();
        pub const fable_identity = {};
        pub const fable_null_cell = {};
        pub const fable_resize_array = T;
        pub const fable_cyclic = holdsCyclic(T);
        @"$rc": u32 = 1,
        @"$gc": GcHdr(fable_cyclic) = undefined,
        /// the items, in a block of `capacity`
        items: []T = &.{},
        capacity: usize = 0,

        pub fn fable_free(c: *Self) void {
            if (c.capacity != 0) alloc().free(c.items.ptr[0..c.capacity]);
        }

        pub fn fable_show(b: *Shower, x: *Self, depth: i32) *Layout {
            return fable_show_shape(b, x, .{}, .{ .kind = .auto }, depth);
        }

        pub fn fable_show_shape(b: *Shower, x: *Self, comptime shape: TypeShape, node: ShowNode, depth: i32) *Layout {
            const shared = isShared(x);
            if (shared) lockEnter(@intFromPtr(x));
            defer if (shared) lockExit(@intFromPtr(x));
            const child: u16 = if (node.kind == .seq) node.a else ShowNode.auto;
            var items: [4]*Layout = undefined;
            const n = @min(x.items.len, 4);
            for (x.items[0..n], 0..) |item, i| items[i] = b.showShape(item, shape, child, .bracket_if_tuple, depth - 1);
            return showSeq(b, items[0..n], x.items.len > 4);
        }
    };
}

pub fn rItem(comptime R: type) type {
    return @typeInfo(@FieldType(@typeInfo(R).pointer.child, "items")).pointer.child;
}

pub fn raNew(comptime R: type) R {
    const C = @typeInfo(R).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = alloc().create(C) catch oom();
    c.* = .{};
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

pub fn raGrow(r: anytype, need: usize) void {
    if (need <= r.capacity) return;
    const cap = @max(need, @max(4, r.capacity * 2));
    const T = rItem(@TypeOf(r));
    const block = alloc().alloc(T, cap) catch oom();
    @memcpy(block[0..r.items.len], r.items);
    if (r.capacity != 0) alloc().free(r.items.ptr[0..r.capacity]);
    r.items = block[0..r.items.len];
    r.capacity = cap;
}

fn raAddUnlocked(r: anytype, x: rItem(@TypeOf(r))) void {
    raGrow(r, r.items.len + 1);
    r.items.len += 1;
    r.items[r.items.len - 1] = undefined;
    // (put in place as an assignment of the array would be, for the collector)
    const n = r.items.len - 1;
    r.items[n] = dup(x);
    if (gcOf(r)) |h| storeValue(h, r.items[n]) else touch(r.items[n]);
}

/// `r.Add x`
pub fn raAdd(r: anytype, x: rItem(@TypeOf(r))) void {
    const shared = isShared(r);
    if (shared) {
        shareStored(x);
        lockEnter(@intFromPtr(r));
    }
    defer if (shared) lockExit(@intFromPtr(r));
    raAddUnlocked(r, x);
}

/// `ResizeArray xs` of a list
pub fn raOfList(comptime R: type, xs: List(rItem(R))) R {
    const r = raNew(R);
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) raAddUnlocked(r, rest.Cons.Head);
    return r;
}

/// `r.AddRange xs` of a list
pub fn raAddList(r: anytype, xs: List(rItem(@TypeOf(r)))) void {
    const shared = isShared(r);
    if (shared) {
        var cur = xs;
        while (cur == .Cons) : (cur = cur.Cons.Tail) shareStored(cur.Cons.Head);
        lockEnter(@intFromPtr(r));
    }
    defer if (shared) lockExit(@intFromPtr(r));
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) raAddUnlocked(r, rest.Cons.Head);
}

pub fn raCount(r: anytype) i32 {
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    defer if (shared) lockExit(@intFromPtr(r));
    return @intCast(r.items.len);
}

/// `r.[i]`
pub fn raGet(r: anytype, i: i32) Raised!rItem(@TypeOf(r)) {
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    defer if (shared) lockExit(@intFromPtr(r));
    if (i < 0 or i >= r.items.len) return outOfRange();
    return dup(r.items[@intCast(i)]);
}

/// `r.[i] <- x`
pub fn raSet(r: anytype, i: i32, x: rItem(@TypeOf(r))) Raised!void {
    if (isShared(r)) {
        shareStored(x);
        lockEnter(@intFromPtr(r));
        if (i < 0 or i >= r.items.len) {
            lockExit(@intFromPtr(r));
            return outOfRange();
        }
        const at: usize = @intCast(i);
        const old = r.items[at];
        r.items[at] = dup(x);
        lockExit(@intFromPtr(r));
        drop(old);
        return;
    }
    if (i < 0 or i >= r.items.len) return outOfRange();
    arrayPut(r, @intCast(i), dup(x));
}

/// `r.Insert(i, x)`
pub fn raInsert(r: anytype, i: i32, x: rItem(@TypeOf(r))) Raised!void {
    const shared = isShared(r);
    if (shared) {
        shareStored(x);
        lockEnter(@intFromPtr(r));
    }
    defer if (shared) lockExit(@intFromPtr(r));
    if (i < 0 or i > r.items.len) return raise(ArgumentOutOfRangeException, str("Index must be within the bounds of the List. (Parameter 'index')"));
    raGrow(r, r.items.len + 1);
    const at: usize = @intCast(i);
    r.items.len += 1;
    std.mem.copyBackwards(rItem(@TypeOf(r)), r.items[at + 1 ..], r.items[at .. r.items.len - 1]);
    r.items[at] = dup(x);
    if (gcOf(r)) |h| storeValue(h, r.items[at]) else touch(r.items[at]);
}

fn raTakeDetached(r: anytype, at: usize) rItem(@TypeOf(r)) {
    const old = r.items[at];
    std.mem.copyForwards(rItem(@TypeOf(r)), r.items[at .. r.items.len - 1], r.items[at + 1 ..]);
    r.items.len -= 1;
    if (gcOf(r)) |h| eachHdr(old, h, unstored);
    return old;
}

pub fn raTake(r: anytype, at: usize) void {
    drop(raTakeDetached(r, at));
}

/// `r.RemoveRange(index, count)`: what follows moved once (not once per item); what was
/// removed given up after the lock
pub fn raRemoveRange(r: anytype, index: i32, count: i32) Raised!void {
    const T = rItem(@TypeOf(r));
    if (index < 0 or count < 0) return outOfRange();
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    const at: usize = @intCast(index);
    const n: usize = @intCast(count);
    if (at + n > r.items.len) {
        if (shared) lockExit(@intFromPtr(r));
        return raise(ArgumentException, str("Offset and length were out of bounds for the array or count is greater than the number of elements from index to the end of the source collection."));
    }
    var removed: []T = &.{};
    if (comptime isManaged(T)) {
        if (n > 0) {
            removed = alloc().alloc(T, n) catch oom();
            @memcpy(removed, r.items[at .. at + n]);
            if (gcOf(r)) |h| for (removed) |old| eachHdr(old, h, unstored);
        }
    }
    std.mem.copyForwards(T, r.items[at .. r.items.len - n], r.items[at + n ..]);
    r.items.len -= n;
    if (shared) lockExit(@intFromPtr(r));
    if (comptime isManaged(T)) {
        for (removed) |old| drop(old);
        if (n > 0) alloc().free(removed);
    }
}

/// `r.RemoveAt i`
pub fn raRemoveAt(r: anytype, i: i32) Raised!void {
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    if (i < 0 or i >= r.items.len) {
        if (shared) lockExit(@intFromPtr(r));
        return outOfRange();
    }
    const old = raTakeDetached(r, @intCast(i));
    if (shared) lockExit(@intFromPtr(r));
    drop(old);
}

fn raIndexOfUnlocked(r: anytype, x: rItem(@TypeOf(r))) i32 {
    for (r.items, 0..) |item, i| {
        if (eql(item, x)) return @intCast(i);
    }
    return -1;
}

/// `r.IndexOf x`
pub fn raIndexOf(r: anytype, x: rItem(@TypeOf(r))) i32 {
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    defer if (shared) lockExit(@intFromPtr(r));
    return raIndexOfUnlocked(r, x);
}

pub fn raContains(r: anytype, x: rItem(@TypeOf(r))) bool {
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    defer if (shared) lockExit(@intFromPtr(r));
    return raIndexOfUnlocked(r, x) >= 0;
}

/// `r.Remove x`: the first item equal to x, if there is one.
pub fn raRemove(r: anytype, x: rItem(@TypeOf(r))) bool {
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    const i = raIndexOfUnlocked(r, x);
    if (i < 0) {
        if (shared) lockExit(@intFromPtr(r));
        return false;
    }
    const old = raTakeDetached(r, @intCast(i));
    if (shared) lockExit(@intFromPtr(r));
    drop(old);
    return true;
}

/// `r.Clear()`
pub fn raClear(r: anytype) void {
    if (isShared(r)) {
        lockEnter(@intFromPtr(r));
        const old_items = r.items;
        const old_cap = r.capacity;
        r.items = &.{};
        r.capacity = 0;
        lockExit(@intFromPtr(r));
        for (old_items) |item| drop(item);
        if (old_cap != 0) alloc().free(old_items.ptr[0..old_cap]);
        return;
    }
    while (r.items.len != 0) raTake(r, r.items.len - 1);
}

/// `r.Reverse()`
pub fn raReverse(r: anytype) void {
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    defer if (shared) lockExit(@intFromPtr(r));
    std.mem.reverse(rItem(@TypeOf(r)), r.items);
}

/// `r.Sort()`: by `compare`. (Equal items stay in their order; on .NET their order is not
/// promised, and for F# values two equal items cannot be told apart.)
pub fn raSort(r: anytype) void {
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    defer if (shared) lockExit(@intFromPtr(r));
    arrays.sortSliceCmp(rItem(@TypeOf(r)), r.items, false);
}

/// `r.ToArray()`
pub fn raToArray(r: anytype) Array(rItem(@TypeOf(r))) {
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    defer if (shared) lockExit(@intFromPtr(r));
    const A = Array(rItem(@TypeOf(r)));
    const items = arrayItems(A, r.items.len);
    for (items, r.items) |*to, item| to.* = dup(item);
    return arrayFrom(A, items);
}

/// What a loop over it walks: its items now, as a list.
pub fn raToList(r: anytype) List(rItem(@TypeOf(r))) {
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    defer if (shared) lockExit(@intFromPtr(r));
    return listOf(rItem(@TypeOf(r)), r.items);
}

/// The text `string x` and `{x}` give for a key or a value: unquoted, as .NET's ToString.
fn showPlain(b: *Shower, x: anytype, depth: i32) *Layout {
    return showPlainShape(b, x, .{}, ShowNode.auto, depth);
}

fn showPlainShape(b: *Shower, x: anytype, comptime shape: TypeShape, node_idx: u16, depth: i32) *Layout {
    const T = @TypeOf(x);
    if (T == String) return b.leaf(false, b.arena.dupe(u16, unitsOf(x)) catch oom(), false);
    const node: ShowNode = if (node_idx < shape.nodes.len) shape.nodes[node_idx] else .{};
    if (T == u16 and node.kind != .u16_num) return b.leaf(false, b.arena.dupe(u16, &.{x}) catch oom(), false);
    switch (@typeInfo(T)) {
        .int, .float, .bool => {
            var scratch: [scratch_len]u8 align(2) = undefined;
            const piece = pieceOf(.{}, x, &scratch);
            return b.ascii(false, piece.ascii, false);
        },
        else => return b.showShape(x, shape, node_idx, .bracket_if_tuple, depth),
    }
}

/// .NET's `Dictionary<K, V>` (`hashed = true` and V = void: `HashSet<K>`).
pub fn HashTable(comptime K: type, comptime V: type, comptime is_set: bool) type {
    return *struct {
        const Self = @This();
        pub const fable_identity = {};
        pub const fable_null_cell = {};
        pub const fable_cyclic = functions_in_cycles or holdsCyclic(K) or holdsCyclic(V);
        pub const Entry = struct { hash: i32, next: i32, kv: ?struct { key: K, value: V } };
        @"$rc": u32 = 1,
        @"$gc": GcHdr(fable_cyclic) = undefined,
        /// the entries made so far, in a block of `capacity`; a freed one holds null
        entries: []Entry = &.{},
        capacity: usize = 0,
        /// for each bucket: the first entry of its chain, plus one (0: none)
        buckets: []i32 = &.{},
        free_list: i32 = -1,
        free_count: i32 = 0,
        /// what F#'s `dict` and `readOnlyDict` make: changing it raises
        read_only: bool = false,
        /// made by .NET's constructor without a comparer: array keys are compared by reference, as
        /// .NET's `EqualityComparer<T[]>.Default` does (F#'s `dict`, `distinct` and the like
        /// compare them by their items)
        by_ref: bool = false,
        /// an IEqualityComparer's members, when one was given: they hash and compare the keys
        cmp_eq: ?Func(*const fn (?*Env, K, K) Raised!bool) = null,
        cmp_hash: ?Func(*const fn (?*Env, K) Raised!i32) = null,

        pub fn fable_free(c: *Self) void {
            if (c.capacity != 0) {
                alloc().free(c.entries.ptr[0..c.capacity]);
                alloc().free(c.buckets);
            }
        }

        pub fn fable_show(b: *Shower, x: *Self, depth: i32) *Layout {
            return fable_show_shape(b, x, .{}, .{ .kind = .auto }, depth);
        }

        pub fn fable_show_shape(b: *Shower, x: *Self, comptime shape: TypeShape, node: ShowNode, depth: i32) *Layout {
            const shared = isShared(x);
            if (shared) lockEnter(@intFromPtr(x));
            defer if (shared) lockExit(@intFromPtr(x));
            const k_idx: u16 = if (node.kind == .map or node.kind == .seq) node.a else ShowNode.auto;
            const v_idx: u16 = if (node.kind == .map) node.b else ShowNode.auto;
            var items: [4]*Layout = undefined;
            var n: usize = 0;
            var more = false;
            for (x.entries) |e| {
                const kv = e.kv orelse continue;
                if (n == 4) {
                    more = true;
                    break;
                }
                items[n] = if (is_set)
                    b.showShape(kv.key, shape, k_idx, .bracket_if_tuple, depth - 1)
                else
                    b.tight(b.tight(b.ascii(false, "[", true), b.join(b.tight(showPlainShape(b, kv.key, shape, k_idx, depth - 1), b.ascii(true, ",", false)), showPlainShape(b, kv.value, shape, v_idx, depth - 1), .unbreakable)), b.ascii(true, "]", false));
                n += 1;
            }
            return showSeq(b, items[0..n], more);
        }
    };
}

pub fn Dictionary(comptime K: type, comptime V: type) type {
    return HashTable(K, V, false);
}

pub fn HashSet(comptime K: type) type {
    return HashTable(K, void, true);
}

pub fn KeyOf(comptime D: type) type {
    const Entry = @typeInfo(D).pointer.child.Entry;
    return @FieldType(@typeInfo(@FieldType(Entry, "kv")).optional.child, "key");
}

pub fn ValueOf(comptime D: type) type {
    const Entry = @typeInfo(D).pointer.child.Entry;
    return @FieldType(@typeInfo(@FieldType(Entry, "kv")).optional.child, "value");
}

pub fn htNew(comptime D: type) D {
    const C = @typeInfo(D).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = alloc().create(C) catch oom();
    c.* = .{};
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

/// (.NET's sizes: primes, so that the buckets spread)
fn htNextSize(min: usize) usize {
    const primes = [_]usize{ 3, 7, 11, 17, 23, 29, 37, 47, 59, 71, 89, 107, 131, 163, 197, 239, 293, 353, 431, 521, 631, 761, 919, 1103, 1327, 1597, 1931, 2333, 2801, 3371, 4049, 4861, 5839, 7013, 8419, 10103, 12143, 14591, 17519, 21023, 25229, 30293, 36353, 43627, 52361, 62851, 75431, 90523, 108631, 130363, 156437, 187751, 225307, 270371, 324449, 389357, 467237, 560689, 672827, 807403, 968897, 1162687, 1395263, 1674319, 2009191, 2411033, 2893249, 3471899, 4166287, 4999559, 5999471, 7199369 };
    for (primes) |p| {
        if (p >= min) return p;
    }
    var n = min | 1;
    while (true) : (n += 2) {
        var i: usize = 3;
        while (i * i <= n and n % i != 0) i += 2;
        if (i * i > n) return n;
    }
}

fn htInitComparers(d: anytype, eq: anytype, h: anytype) void {
    d.cmp_eq = dup(eq);
    d.cmp_hash = dup(h);
    if (gcOf(d)) |hdr| {
        storeValue(hdr, d.cmp_eq);
        storeValue(hdr, d.cmp_hash);
    } else {
        touch(d.cmp_eq);
        touch(d.cmp_hash);
    }
}

/// A new dictionary or set whose keys an IEqualityComparer hashes and compares
pub fn htNewWith(comptime D: type, comparer: anytype) D {
    const d = htNew(D);
    // (an interface's value may be null: then the keys' own equality, as .NET's default)
    const c = if (comptime @typeInfo(@TypeOf(comparer)) == .optional) (comparer orelse return d) else comparer;
    if (comptime isIface(@TypeOf(c))) {
        const HT = @typeInfo(D).pointer.child;
        const EqFn = @typeInfo(@FieldType(HT, "cmp_eq")).optional.child;
        const HashFn = @typeInfo(@FieldType(HT, "cmp_hash")).optional.child;
        const eq = ifaceMethod(EqFn, c, "Equals");
        defer drop(eq);
        const h = ifaceMethod(HashFn, c, "GetHashCode");
        defer drop(h);
        htInitComparers(d, eq, h);
    } else {
        htInitComparers(d, @field(c, "Equals"), @field(c, "GetHashCode"));
    }
    return d;
}

/// An empty dictionary or set that compares keys as `d` does
pub fn htEmptyLike(d: anytype) @TypeOf(d) {
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    defer if (shared) lockExit(@intFromPtr(d));
    const e = htNew(@TypeOf(d));
    e.by_ref = d.by_ref;
    if (d.cmp_eq != null and d.cmp_hash != null) htInitComparers(e, d.cmp_eq.?, d.cmp_hash.?);
    return e;
}

/// (what a comparer raises cannot leave a lookup here)
fn comparerFailed() noreturn {
    @panic("fable: an IEqualityComparer raised an exception (not supported inside a dictionary or set)");
}

/// Is a key of type `K` an array, which .NET's default comparer compares by reference?
fn isArrayKey(comptime K: type) bool {
    const P = switch (@typeInfo(K)) {
        .optional => |o| o.child,
        else => K,
    };
    const info = @typeInfo(P);
    return info == .pointer and info.pointer.size == .one and @typeInfo(info.pointer.child) == .@"struct" and @hasDecl(info.pointer.child, "fable_array");
}

fn keyAddress(key: anytype) usize {
    return if (comptime @typeInfo(@TypeOf(key)) == .optional)
        (if (key) |k| @intFromPtr(k) else 0)
    else
        @intFromPtr(key);
}

/// `HashSet<T>()` and `Dictionary<K, V>()` of .NET: array keys by reference
pub fn htByRef(d: anytype) @TypeOf(d) {
    d.by_ref = true;
    return d;
}

/// (the library's `distinct` and the like: keys compared by what they hold, as F# does)
pub fn htStructural(d: anytype) void {
    d.by_ref = false;
}

fn htHash(d: anytype, key: KeyOf(@TypeOf(d))) i32 {
    if (comptime isArrayKey(KeyOf(@TypeOf(d)))) {
        if (d.by_ref and d.cmp_hash == null) {
            const a: u64 = keyAddress(key);
            return @bitCast(@as(u32, @truncate(a ^ (a >> 32))));
        }
    }
    const f = d.cmp_hash orelse return hash(key);
    return f.code(f.env, dup(key)) catch comparerFailed();
}

fn htEql(d: anytype, a: KeyOf(@TypeOf(d)), b: KeyOf(@TypeOf(d))) bool {
    if (comptime isArrayKey(KeyOf(@TypeOf(d)))) {
        if (d.by_ref and d.cmp_eq == null) return keyAddress(a) == keyAddress(b);
    }
    const f = d.cmp_eq orelse return eql(a, b);
    return f.code(f.env, dup(a), dup(b)) catch comparerFailed();
}

pub fn htBucket(d: anytype, h: i32) usize {
    return @as(u32, @bitCast(h)) % @as(u32, @intCast(d.buckets.len));
}

pub fn htResize(d: anytype, size: usize) void {
    const C = @TypeOf(d.*);
    const block = alloc().alloc(C.Entry, size) catch oom();
    @memcpy(block[0..d.entries.len], d.entries);
    if (d.capacity != 0) {
        alloc().free(d.entries.ptr[0..d.capacity]);
        alloc().free(d.buckets);
    }
    d.entries = block[0..d.entries.len];
    d.capacity = size;
    d.buckets = alloc().alloc(i32, size) catch oom();
    @memset(d.buckets, 0);
    for (d.entries, 0..) |*e, i| {
        if (e.kv == null) continue;
        const bucket = htBucket(d, e.hash);
        e.next = d.buckets[bucket] - 1;
        d.buckets[bucket] = @intCast(i + 1);
    }
}

pub fn htFind(d: anytype, key: KeyOf(@TypeOf(d))) ?usize {
    if (d.buckets.len == 0) return null;
    const h = htHash(d, key);
    var i = d.buckets[htBucket(d, h)] - 1;
    while (i >= 0) {
        const e = &d.entries[@intCast(i)];
        if (e.hash == h and htEql(d, e.kv.?.key, key)) return @intCast(i);
        i = e.next;
    }
    return null;
}

/// Put an entry in: false (and nothing changed) if the key is there and `replace` is false.
/// When replacing an existing value, returns it in `displaced` so callers can drop after unlocking.
fn htPutUnlocked(d: anytype, key: KeyOf(@TypeOf(d)), value: ValueOf(@TypeOf(d)), replace: bool, displaced: *?ValueOf(@TypeOf(d))) bool {
    if (htFind(d, key)) |i| {
        if (!replace) return false;
        const e = &d.entries[i];
        const old = e.kv.?.value;
        e.kv.?.value = dup(value);
        if (gcOf(d)) |h| {
            eachHdr(old, h, unstored);
            storeValue(h, e.kv.?.value);
        } else touch(e.kv.?.value);
        displaced.* = old;
        return true;
    }
    if (d.buckets.len == 0) htResize(d, htNextSize(0));
    const h = htHash(d, key);
    var at: usize = undefined;
    if (d.free_count > 0) {
        at = @intCast(d.free_list);
        d.free_list = -3 - d.entries[at].next;
        d.free_count -= 1;
    } else {
        if (d.entries.len == d.capacity) htResize(d, htNextSize(d.capacity * 2));
        at = d.entries.len;
        d.entries.len += 1;
    }
    const bucket = htBucket(d, h);
    d.entries[at] = .{ .hash = h, .next = d.buckets[bucket] - 1, .kv = .{ .key = dup(key), .value = dup(value) } };
    d.buckets[bucket] = @intCast(at + 1);
    if (gcOf(d)) |hdr| storeValue(hdr, d.entries[at].kv.?) else touch(d.entries[at].kv.?);
    return true;
}

/// `d.Add(k, v)`
fn notMutable() Raised {
    return raise(NotSupportedException, str("This value cannot be mutated"));
}

pub fn dictAdd(d: anytype, key: KeyOf(@TypeOf(d)), value: ValueOf(@TypeOf(d))) Raised!void {
    if (d.read_only) return notMutable();
    const shared = isShared(d);
    if (shared) {
        shareStored(key);
        shareStored(value);
        lockEnter(@intFromPtr(d));
    }
    var displaced: ?ValueOf(@TypeOf(d)) = null;
    const inserted = htPutUnlocked(d, key, value, false, &displaced);
    if (shared) lockExit(@intFromPtr(d));
    if (displaced) |old| drop(old);
    if (!inserted) {
        return raise(ArgumentException, format(.{ "An item with the same key has already been added. Key: ", arg(.{ .kind = 'T' }, key) }));
    }
}

/// `d.[k] <- v`
pub fn dictSet(d: anytype, key: KeyOf(@TypeOf(d)), value: ValueOf(@TypeOf(d))) Raised!void {
    if (d.read_only) return notMutable();
    const shared = isShared(d);
    if (shared) {
        shareStored(key);
        shareStored(value);
        lockEnter(@intFromPtr(d));
    }
    var displaced: ?ValueOf(@TypeOf(d)) = null;
    _ = htPutUnlocked(d, key, value, true, &displaced);
    if (shared) lockExit(@intFromPtr(d));
    if (displaced) |old| drop(old);
}

/// `dict pairs` (`read_only`) and `Dictionary(pairs)`: a later pair of the same key replaces an
/// earlier one
pub fn dictOfList(comptime D: type, pairs: anytype, comptime read_only: bool) D {
    const d = htNew(D);
    // (`Dictionary(other)` is .NET's: its array keys by reference; `dict` is F#'s)
    d.by_ref = !read_only;
    var rest = pairs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        var displaced: ?ValueOf(D) = null;
        _ = htPutUnlocked(d, rest.Cons.Head[0], rest.Cons.Head[1], true, &displaced);
        if (displaced) |old| drop(old);
    }
    d.read_only = read_only;
    return d;
}

/// `(c :> ICollection<'T>).Contains x` of what is a list here (a map's entries, a set's items)
pub fn listContains(xs: anytype, x: anytype) bool {
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        if (eql(rest.Cons.Head, x)) return true;
    }
    return false;
}

/// `(a :> ICollection<'T>).Contains x` of an array
pub fn arrayContainsItem(a: anytype, x: anytype) bool {
    for (a.items) |y| {
        if (eql(y, x)) return true;
    }
    return false;
}

/// `c.CopyTo(array, index)` of what is a list here, or of an array: its items into `a` from
/// `index`, .NET's exceptions when they do not fit
pub fn collCopyTo(xs: anytype, a: anytype, index: i32) Raised!void {
    if (index < 0) return raise(ArgumentOutOfRangeException, str("Non-negative number required. (Parameter 'arrayIndex')"));
    const X = @TypeOf(xs);
    const n: usize = if (comptime isArrayPtr(X)) xs.items.len else @intCast(listCount(xs));
    if (@as(usize, @intCast(index)) + n > a.items.len) {
        return raise(ArgumentException, str("Destination array was not long enough. Check the destination index, length, and the array's lower bounds. (Parameter 'destinationArray')"));
    }
    var i: usize = @intCast(index);
    if (comptime isArrayPtr(X)) {
        for (xs.items) |x| {
            const v = dup(x);
            drop(a.items[i]);
            a.items[i] = v;
            i += 1;
        }
        return;
    }
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        const v = dup(rest.Cons.Head);
        drop(a.items[i]);
        a.items[i] = v;
        i += 1;
    }
}

/// `List.length`, of what `d.Keys` and `d.Values` give
pub fn listCount(xs: anytype) i32 {
    var n: i32 = 0;
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) n += 1;
    return n;
}

/// `d.[k]`
pub fn dictGet(d: anytype, key: KeyOf(@TypeOf(d))) Raised!ValueOf(@TypeOf(d)) {
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    if (htFind(d, key)) |i| {
        const res = dup(d.entries[i].kv.?.value);
        if (shared) lockExit(@intFromPtr(d));
        return res;
    }
    if (shared) lockExit(@intFromPtr(d));
    // (F#'s `dict` keeps its keys in a box of its own, which is what .NET names)
    if (d.read_only) return raise(KeyNotFoundException, str("The given key 'Microsoft.FSharp.Core.CompilerServices.RuntimeHelpers+StructBox`1[" ++ comptime netTypeName(KeyOf(@TypeOf(d))) ++ "]' was not present in the dictionary."));
    return raise(KeyNotFoundException, format(.{ "The given key '", arg(.{ .kind = 'T' }, key), "' was not present in the dictionary." }));
}

/// `d.TryGetValue(k, &v)`: the value, or null.
pub fn dictTryGet(d: anytype, key: KeyOf(@TypeOf(d))) ?ValueOf(@TypeOf(d)) {
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    defer if (shared) lockExit(@intFromPtr(d));
    const i = htFind(d, key) orelse return null;
    return dup(d.entries[i].kv.?.value);
}

pub fn dictContainsKey(d: anytype, key: KeyOf(@TypeOf(d))) bool {
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    defer if (shared) lockExit(@intFromPtr(d));
    return htFind(d, key) != null;
}

pub fn dictContainsValue(d: anytype, value: ValueOf(@TypeOf(d))) bool {
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    defer if (shared) lockExit(@intFromPtr(d));
    for (d.entries) |e| {
        if (e.kv) |kv| {
            if (eql(kv.value, value)) return true;
        }
    }
    return false;
}

/// `d.Remove k`
pub fn htRemove(d: anytype, key: KeyOf(@TypeOf(d))) Raised!bool {
    if (d.read_only) return notMutable();
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    if (d.buckets.len == 0) {
        if (shared) lockExit(@intFromPtr(d));
        return false;
    }
    const h = htHash(d, key);
    const bucket = htBucket(d, h);
    var last: i32 = -1;
    var i = d.buckets[bucket] - 1;
    while (i >= 0) {
        const e = &d.entries[@intCast(i)];
        if (e.hash == h and htEql(d, e.kv.?.key, key)) {
            if (last < 0) d.buckets[bucket] = e.next + 1 else d.entries[@intCast(last)].next = e.next;
            const old = e.kv.?;
            e.kv = null;
            e.next = -3 - d.free_list;
            d.free_list = i;
            d.free_count += 1;
            if (gcOf(d)) |hdr| eachHdr(old, hdr, unstored);
            if (shared) lockExit(@intFromPtr(d));
            drop(old);
            return true;
        }
        last = i;
        i = e.next;
    }
    if (shared) lockExit(@intFromPtr(d));
    return false;
}

pub fn htCount(d: anytype) i32 {
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    defer if (shared) lockExit(@intFromPtr(d));
    return @as(i32, @intCast(d.entries.len)) - d.free_count;
}

/// `d.Clear()`
pub fn htClear(d: anytype) Raised!void {
    if (d.read_only) return notMutable();
    if (isShared(d)) {
        lockEnter(@intFromPtr(d));
        const old_entries = d.entries;
        const old_cap = d.capacity;
        const old_buckets = d.buckets;
        d.entries = &.{};
        d.capacity = 0;
        d.buckets = &.{};
        d.free_list = -1;
        d.free_count = 0;
        lockExit(@intFromPtr(d));
        for (old_entries) |e| {
            if (e.kv) |kv| drop(kv);
        }
        if (old_cap != 0) {
            alloc().free(old_entries.ptr[0..old_cap]);
            alloc().free(old_buckets);
        }
        return;
    }
    for (d.entries) |*e| {
        if (e.kv) |kv| {
            e.kv = null;
            if (gcOf(d)) |hdr| eachHdr(kv, hdr, unstored);
            drop(kv);
        }
    }
    d.entries.len = 0;
    @memset(d.buckets, 0);
    d.free_list = -1;
    d.free_count = 0;
}

/// What a loop over a dictionary walks: its entries, as pairs, in .NET's order.
pub fn dictToList(d: anytype) List(struct { KeyOf(@TypeOf(d)), ValueOf(@TypeOf(d)) }) {
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    defer if (shared) lockExit(@intFromPtr(d));
    const P = struct { KeyOf(@TypeOf(d)), ValueOf(@TypeOf(d)) };
    var items: std.ArrayList(P) = .empty;
    defer items.deinit(alloc());
    for (d.entries) |e| {
        if (e.kv) |kv| items.append(alloc(), .{ kv.key, kv.value }) catch oom();
    }
    return listOf(P, items.items);
}

/// `Dictionary(pairs)` of an array or a list of pairs: .NET's ArgumentException on a key given
/// twice
pub fn dictOfItems(comptime D: type, items: anytype) Raised!D {
    const d = htByRef(htNew(D));
    errdefer drop(d);
    const X = @TypeOf(items);
    if (comptime isArrayPtr(X)) {
        for (items.items) |kv| try dictAdd(d, kv[0], kv[1]);
    } else {
        var rest = items;
        while (rest == .Cons) : (rest = rest.Cons.Tail) try dictAdd(d, rest.Cons.Head[0], rest.Cons.Head[1]);
    }
    return d;
}

/// `(d :> ICollection<KeyValuePair<K, V>>).Add kv`
pub fn dictAddPair(d: anytype, kv: anytype) Raised!void {
    return dictAdd(d, kv[0], kv[1]);
}

/// `(d :> ICollection<KeyValuePair<K, V>>).Contains kv`: the key, with this value
pub fn dictContainsPair(d: anytype, kv: anytype) bool {
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    defer if (shared) lockExit(@intFromPtr(d));
    const i = htFind(d, kv[0]) orelse return false;
    return eql(d.entries[i].kv.?.value, kv[1]);
}

/// `(d :> ICollection<KeyValuePair<K, V>>).Remove kv`: only the key with this value
pub fn dictRemovePair(d: anytype, kv: anytype) Raised!bool {
    if (!dictContainsPair(d, kv)) return false;
    return htRemove(d, kv[0]);
}

/// `(d :> ICollection<KeyValuePair<K, V>>).CopyTo(array, index)`: the entries, in order
pub fn dictCopyTo(d: anytype, a: anytype, index: i32) Raised!void {
    const entries = dictToList(d);
    defer drop(entries);
    return collCopyTo(entries, a, index);
}

/// `r.CopyTo(array)`, `r.CopyTo(array, index)` and `r.CopyTo(start, array, index, count)`:
/// the items into the array, .NET's exceptions when they do not fit
pub fn raCopyTo(r: anytype, start: i32, a: anytype, index: i32, count: ?i32) Raised!void {
    const shared = isShared(r);
    if (shared) lockEnter(@intFromPtr(r));
    defer if (shared) lockExit(@intFromPtr(r));
    const n: i32 = count orelse @as(i32, @intCast(r.items.len)) - start;
    if (start < 0 or index < 0 or n < 0) return raise(ArgumentOutOfRangeException, str("Non-negative number required."));
    if (@as(usize, @intCast(start)) + @as(usize, @intCast(n)) > r.items.len or
        @as(usize, @intCast(index)) + @as(usize, @intCast(n)) > a.items.len)
    {
        return raise(ArgumentException, str("Destination array was not long enough. Check the destination index, length, and the array's lower bounds. (Parameter 'destinationArray')"));
    }
    var k: usize = 0;
    while (k < n) : (k += 1) {
        const v = dup(r.items[@as(usize, @intCast(start)) + k]);
        const at = @as(usize, @intCast(index)) + k;
        drop(a.items[at]);
        a.items[at] = v;
    }
}

pub fn dictKeys(d: anytype) List(KeyOf(@TypeOf(d))) {
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    defer if (shared) lockExit(@intFromPtr(d));
    var items: std.ArrayList(KeyOf(@TypeOf(d))) = .empty;
    defer items.deinit(alloc());
    for (d.entries) |e| {
        if (e.kv) |kv| items.append(alloc(), kv.key) catch oom();
    }
    return listOf(KeyOf(@TypeOf(d)), items.items);
}

pub fn dictValues(d: anytype) List(ValueOf(@TypeOf(d))) {
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    defer if (shared) lockExit(@intFromPtr(d));
    var items: std.ArrayList(ValueOf(@TypeOf(d))) = .empty;
    defer items.deinit(alloc());
    for (d.entries) |e| {
        if (e.kv) |kv| items.append(alloc(), kv.value) catch oom();
    }
    return listOf(ValueOf(@TypeOf(d)), items.items);
}

/// `h.Add x`: false if it was there.
pub fn setAdd(h: anytype, x: KeyOf(@TypeOf(h))) bool {
    const shared = isShared(h);
    if (shared) {
        shareStored(x);
        lockEnter(@intFromPtr(h));
    }
    defer if (shared) lockExit(@intFromPtr(h));
    var displaced: ?ValueOf(@TypeOf(h)) = null;
    return htPutUnlocked(h, x, {}, false, &displaced);
}

/// `HashSet xs` of a list
pub fn setOfList(comptime H: type, xs: List(KeyOf(H))) H {
    const h = htNew(H);
    // (`HashSet(items)` is .NET's: its array items by reference)
    h.by_ref = true;
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        var displaced: ?ValueOf(H) = null;
        _ = htPutUnlocked(h, rest.Cons.Head, {}, false, &displaced);
    }
    return h;
}

/// `h.UnionWith xs` of a list
pub fn setUnionList(h: anytype, xs: List(KeyOf(@TypeOf(h)))) void {
    const shared = isShared(h);
    if (shared) {
        var cur = xs;
        while (cur == .Cons) : (cur = cur.Cons.Tail) shareStored(cur.Cons.Head);
        lockEnter(@intFromPtr(h));
    }
    defer if (shared) lockExit(@intFromPtr(h));
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        var displaced: ?ValueOf(@TypeOf(h)) = null;
        _ = htPutUnlocked(h, rest.Cons.Head, {}, false, &displaced);
    }
}

pub fn setToList(h: anytype) List(KeyOf(@TypeOf(h))) {
    return dictKeys(h);
}

const arena_mod = @import("fable_arena.zig");
pub const Arena = arena_mod.Arena;
pub const arenaEnter = arena_mod.arenaEnter;
pub const arenaLeave = arena_mod.arenaLeave;
pub const arenaOwning = arena_mod.arenaOwning;
pub const inThreadArena = arena_mod.inThreadArena;

// ---------------------------------------------------------------------------------------------
// Spans: `Span<'T>` and `ReadOnlySpan<'T>` are Zig slices of what they view (an array's items
// or a string's code units). Managed elements keep accurate reference counts on writes.
// ---------------------------------------------------------------------------------------------

fn SpanElem(comptime S: type) type {
    const child = @typeInfo(S).pointer.child;
    return if (@typeInfo(child) == .array) @typeInfo(child).array.child else child;
}

pub fn spanEmpty(comptime S: type) S {
    const Child = @typeInfo(S).pointer.child;
    const Empty = struct {
        var items: [0]Child = .{};
    };
    return &Empty.items;
}

/// `s.[i]`: where the item is (F# reads it, or assigns through it)
pub inline fn spanRef(s: anytype, i: i32) Raised!@TypeOf(&s[0]) {
    if (i < 0 or i >= s.len) return indexOutside();
    return &s[@intCast(i)];
}

/// `s.[i] <- x`
pub inline fn spanSet(s: anytype, i: i32, x: SpanElem(@TypeOf(s))) Raised!void {
    if (i < 0 or i >= s.len) return indexOutside();
    store(&s[@intCast(i)], dup(x));
}

/// `s.Slice(start)` and `s.Slice(start, length)`
pub fn spanSlice(s: anytype, start: i32, length: ?i32) Raised!@TypeOf(s) {
    const n = length orelse @as(i32, @intCast(s.len)) - start;
    if (start < 0 or n < 0 or start > s.len or n > @as(i32, @intCast(s.len)) - start) {
        return raise(ArgumentOutOfRangeException, str("Specified argument was out of the range of valid values."));
    }
    return s[@intCast(start)..][0..@intCast(n)];
}

/// `s.Fill(x)`
pub fn spanFill(s: anytype, x: SpanElem(@TypeOf(s))) void {
    for (s) |*slot| store(slot, dup(x));
}

/// `s.Clear()`
pub fn spanClear(s: anytype) Raised!void {
    const Elem = SpanElem(@TypeOf(s));
    if (comptime arrays.hasZero(Elem)) {
        const z = comptime std.mem.zeroes(Elem);
        for (s) |*slot| store(slot, z);
    } else if (s.len != 0) {
        return raise(NotSupportedException, str("Span.Clear of a type without a null value"));
    }
}

/// `s.TryCopyTo(dst)`: handles overlapping slices and keeps reference counts accurate.
pub fn spanTryCopyTo(src: anytype, dst: anytype) bool {
    if (src.len > dst.len) return false;
    const src_addr = @intFromPtr(src.ptr);
    const dst_addr = @intFromPtr(dst.ptr);
    const Elem = SpanElem(@TypeOf(dst));
    if (dst_addr > src_addr and dst_addr - src_addr < src.len * @sizeOf(Elem)) {
        var i = src.len;
        while (i > 0) {
            i -= 1;
            store(&dst[i], dup(src[i]));
        }
    } else {
        for (src, 0..) |item, i| store(&dst[i], dup(item));
    }
    return true;
}

/// `s.CopyTo(dst)`
pub fn spanCopyTo(src: anytype, dst: anytype) Raised!void {
    if (!spanTryCopyTo(src, dst)) {
        return raise(ArgumentException, str("Destination is too short. (Parameter 'destination')"));
    }
}

/// `s.ToArray()`
pub fn spanToArray(comptime A: type, s: anytype) A {
    const items = arrays.arrayItems(A, s.len);
    for (items, s) |*to, item| to.* = dup(item);
    return arrays.arrayFrom(A, items);
}

/// `MemoryExtensions.Reverse(s)`
pub fn spanReverse(s: anytype) void {
    const Elem = SpanElem(@TypeOf(s));
    var i: usize = 0;
    var j = s.len;
    while (i + 1 < j) {
        j -= 1;
        std.mem.swap(Elem, &s[i], &s[j]);
        i += 1;
    }
}

pub const bigint = @import("fable_bigint.zig");
pub const BigInt = bigint.BigInt;
pub const bigAbs = bigint.bigAbs;
pub const bigGcd = bigint.bigGcd;
pub const bigToByteArray = bigint.bigToByteArray;
pub const bigOfBytes = bigint.bigOfBytes;
pub const bigLog2 = bigint.bigLog2;
pub const bigBitLength = bigint.bigBitLength;
pub const bigAdd = bigint.bigAdd;
pub const bigAnd = bigint.bigAnd;
pub const bigCompare = bigint.bigCompare;
pub const bigDigits = bigint.bigDigits;
pub const bigDivRem = bigint.bigDivRem;
pub const bigLit = bigint.bigLit;
pub const bigMul = bigint.bigMul;
pub const bigNeg = bigint.bigNeg;
pub const bigOf = bigint.bigOf;
pub const bigOr = bigint.bigOr;
pub const bigParse = bigint.bigParse;
pub const bigPow = bigint.bigPow;
pub const bigShl = bigint.bigShl;
pub const bigShr = bigint.bigShr;
pub const bigSign = bigint.bigSign;
pub const bigSub = bigint.bigSub;
pub const bigText = bigint.bigText;
pub const bigToFloat = bigint.bigToFloat;
pub const bigToInt = bigint.bigToInt;
pub const bigXor = bigint.bigXor;
pub const isBigInt = bigint.isBigInt;
test {
    _ = bigint;
}

pub const decimal = @import("fable_decimal.zig");
pub const NetDecimal = decimal.NetDecimal;
pub const decAbs = decimal.decAbs;
pub const decAdd = decimal.decAdd;
pub const decAscii = decimal.decAscii;
pub const decCompare = decimal.decCompare;
pub const decDigits = decimal.decDigits;
pub const decDiv = decimal.decDiv;
pub const decGetBits = decimal.decGetBits;
pub const decHash = decimal.decHash;
pub const decLit = decimal.decLit;
pub const decMul = decimal.decMul;
pub const decNeg = decimal.decNeg;
pub const decOf = decimal.decOf;
pub const decOfBits = decimal.decOfBits;
pub const decOfParts = decimal.decOfParts;
pub const decParse = decimal.decParse;
pub const decRem = decimal.decRem;
pub const decRound = decimal.decRound;
pub const decRoundMode = decimal.decRoundMode;
pub const decPown = decimal.decPown;
pub const decSign = decimal.decSign;
pub const decSpecText = decimal.decSpecText;
pub const decSub = decimal.decSub;
pub const decText = decimal.decText;
pub const decToFloat = decimal.decToFloat;
pub const decToInt = decimal.decToInt;
pub const decWhole = decimal.decWhole;
const holdsDecimal = decimal.holdsDecimal;
pub const isDecimal = decimal.isDecimal;
test {
    _ = decimal;
}

// ---------------------------------------------------------------------------------------------
// Objects of classes that inherit or are inherited from
//
// Such an object is a counted cell that starts with a header naming its class, as an exception
// does: the program can make classes that derive from a class no other file has to know about.
// After the header comes the chain of the fields each class declares, the root class's first
// (`chain.base.base.own`). A class's code finds its own fields through the offset its class
// has in the object's chain, and calls a virtual member through the table of function values
// the object's class has for the class that introduced the member.
// ---------------------------------------------------------------------------------------------

pub const ObjType = struct {
    /// .NET's name of the class (`Probe+Circle`)
    name: []const u8,
    parent: ?*const ObjType,
    /// the table of the virtual members each class of the chain introduces (null for a class
    /// that introduces none, and in an abstract class)
    vtables: []const ?*const anyopaque,
    destroy: *const fn (Obj) void,
    /// marks what the object holds shared (see `markShared`)
    share: *const fn (Obj) Raised!void,
    /// the class's `ToString` (its own or the nearest one it inherits), if it has one
    to_string: ?*const fn (?*Env, Obj, void) Raised!String = null,
    /// `Equals(obj)`, `GetHashCode()` and `IComparable.CompareTo(obj)`, where the class or the
    /// boxed type has them (without `equals` an object is equal only to itself)
    equals: ?*const fn (Obj, Obj) bool = null,
    hash: ?*const fn (Obj) i32 = null,
    compare: ?*const fn (Obj, Obj) i32 = null,
    /// a boxed array (`o :? System.Array`)
    is_array: bool = false,
    /// the items of a boxed collection (an array, a list, a ResizeArray, a string), each boxed:
    /// what `o :? IEnumerable` finds and iterates
    items: ?*const fn (Obj) Array(Any) = null,
    /// the reflection information of the boxed type (when the program asks for it, see
    /// `reflection`)
    reflect: ?*const fn () reflect.Type = null,
    /// starting field bit index of each part in the initialization bitset, and byte offset of the bitset
    part_field_bases: []const usize = &.{},
    init_offset: usize = 0,
    /// unwraps a boxed interface wrapper holding a boxed value of `target_ty` (when `Box(Iface)`)
    unwrap_box: ?*const fn (Obj, *const ObjType) ?Obj = null,
    /// unwraps a boxed interface wrapper holding a class `Obj` (when `Box(Iface)`)
    unwrap_obj: ?*const fn (Obj) ?Obj = null,
    /// identity pointer of a boxed interface wrapper (when `Box(Iface)`)
    iface_id: ?*const fn (Obj) ?*anyopaque = null,
    /// the interfaces the class implements (its parents' are in theirs), with its table of
    /// each: what `o :?> I` of an object of the class finds
    ifaces: []const IfaceImpl = &.{},
};

pub const ObjHeader = struct {
    @"$rc": u32 = 1,
    /// the object's identity hash, given the first time it is asked for (.NET keeps one in the
    /// object's header too: an object made where a freed one was does not hash as it did);
    /// it fills the room after the count, so costs nothing on 64-bit targets
    stamp: u32 = 0,
    /// the collector's header of this object, if what it holds can be part of a cycle
    gc: ?*sgc.Hdr = null,
    type: *const ObjType,
};

/// An object of a class.
pub const Obj = *ObjHeader;

/// The fields each class of a chain declares, the root's first.
fn partsOf(comptime Chain: type) []const type {
    comptime {
        const own: [1]type = .{@FieldType(Chain, "own")};
        if (!@hasField(Chain, "base")) return &own;
        const before = partsOf(@FieldType(Chain, "base"));
        const all = before[0..before.len].* ++ own;
        return &all;
    }
}

pub fn PartAt(comptime C: type, comptime up: usize) type {
    return if (up == 0) @FieldType(C, "own") else PartAt(@FieldType(C, "base"), up - 1);
}

/// The fields of the class `up` steps above the last in a chain.
fn ownAt(comptime C: type, chain: C, comptime up: usize) PartAt(C, up) {
    if (up == 0) return chain.own;
    return ownAt(@FieldType(C, "base"), chain.base, up - 1);
}

/// Where the fields of the class `parts[i]` are, from the header. It depends only on the
/// classes above it, so it is the same in every object of a class that derives from it.
fn partOffset(comptime parts: []const type, comptime i: usize) usize {
    var off: usize = @sizeOf(ObjHeader);
    for (parts[0..i]) |P| off = std.mem.alignForward(usize, off, @alignOf(P)) + @sizeOf(P);
    return std.mem.alignForward(usize, off, @alignOf(parts[i]));
}

fn partBases(comptime parts: []const type) []const usize {
    comptime {
        var bases: [parts.len]usize = undefined;
        var total: usize = 0;
        for (parts, 0..) |P, i| {
            bases[i] = total;
            total += @typeInfo(P).@"struct".field_names.len;
        }
        const out = bases;
        return &out;
    }
}

/// An object whose class has the chain of fields `Chain`: the header, the fields of each class
/// in turn, the collector's header if what it holds can be part of a cycle, and the field-init bits.
pub fn ObjCell(comptime Chain: type) type {
    return struct {
        const parts = partsOf(Chain);
        const part_bases = partBases(parts);
        const total_fields = blk: {
            var total: usize = 0;
            for (parts) |P| total += @typeInfo(P).@"struct".field_names.len;
            break :blk total;
        };
        const init_bytes_len = (total_fields + 7) / 8;
        const cyclic = functions_in_cycles and holdsCyclic(Chain);
        const end = partOffset(parts, parts.len - 1) + @sizeOf(parts[parts.len - 1]);
        const gc_at = std.mem.alignForward(usize, end, @alignOf(sgc.Hdr));
        const init_at = if (cyclic) gc_at + @sizeOf(sgc.Hdr) else end;
        const size = init_at + init_bytes_len;
        const alignment = blk: {
            var a: usize = @max(@alignOf(ObjHeader), if (cyclic) @alignOf(sgc.Hdr) else 1);
            for (parts) |P| a = @max(a, @alignOf(P));
            break :blk a;
        };
        const Raw = struct {
            pub const fable_rc_header = ObjHeader;
            bytes: [size]u8 align(alignment),
        };

        pub inline fn part(o: Obj, comptime i: usize) *parts[i] {
            return @ptrFromInt(@intFromPtr(o) + comptime partOffset(parts, i));
        }

        inline fn isInit(o: Obj, comptime i: usize, comptime j: usize) bool {
            if (comptime init_bytes_len == 0) return true;
            const bit_idx = comptime part_bases[i] + j;
            const bytes: [*]const u8 = @ptrFromInt(@intFromPtr(o) + init_at);
            return (bytes[bit_idx >> 3] & (@as(u8, 1) << @intCast(bit_idx & 7))) != 0;
        }

        pub inline fn hdrOf(o: Obj) *sgc.Hdr {
            return @ptrFromInt(@intFromPtr(o) + gc_at);
        }

        pub inline fn objOfHdr(h: *sgc.Hdr) Obj {
            return @ptrFromInt(@intFromPtr(h) - gc_at);
        }

        pub fn chainPart(chain: Chain, comptime i: usize) parts[i] {
            return ownAt(Chain, chain, parts.len - 1 - i);
        }

        pub fn destroy(o: Obj) void {
            inline for (0..parts.len) |i| {
                const names = @typeInfo(parts[i]).@"struct".field_names;
                if (comptime names.len > 0) {
                    const p = part(o, i);
                    inline for (names, 0..) |fname, j| {
                        if (isInit(o, i, j)) drop(@field(p, fname));
                    }
                }
            }
            free(@as(*Raw, @ptrCast(@alignCast(o))));
        }

        pub fn share(o: Obj) Raised!void {
            inline for (0..parts.len) |i| {
                const names = @typeInfo(parts[i]).@"struct".field_names;
                if (comptime names.len > 0) {
                    const p = part(o, i);
                    inline for (names, 0..) |fname, j| {
                        if (isInit(o, i, j)) try markShared(@field(p, fname));
                    }
                }
            }
        }

        pub fn alloc(ty: *const ObjType) Obj {
            if (comptime cyclic) gcTick();
            const raw = @import("fable_rt.zig").alloc().create(Raw) catch oom();
            const o: Obj = @ptrCast(@alignCast(&raw.bytes));
            o.* = .{ .type = ty };
            if (comptime init_bytes_len > 0) {
                const bytes: [*]u8 = @ptrFromInt(@intFromPtr(o) + init_at);
                @memset(bytes[0..init_bytes_len], 0);
            }
            if (comptime cyclic) {
                hdrOf(o).* = thread.collector.hdr(&desc, true);
                o.gc = hdrOf(o);
            }
            if (track) thread.stats.allocs += 1;
            return o;
        }

        pub fn new(ty: *const ObjType, chain: Chain) Obj {
            if (comptime cyclic) gcTick();
            const raw = @import("fable_rt.zig").alloc().create(Raw) catch oom();
            const o: Obj = @ptrCast(@alignCast(&raw.bytes));
            o.* = .{ .type = ty };
            inline for (0..parts.len) |i| part(o, i).* = chainPart(chain, i);
            if (comptime init_bytes_len > 0) {
                const bytes: [*]u8 = @ptrFromInt(@intFromPtr(o) + init_at);
                @memset(bytes[0..init_bytes_len], 0xFF);
            }
            if (comptime cyclic) {
                hdrOf(o).* = thread.collector.hdr(&desc, isLeaf(o));
                o.gc = hdrOf(o);
            }
            if (track) thread.stats.allocs += 1;
            return o;
        }

        pub fn trace(n: *sgc.Hdr, v: *sgc.Visitor) void {
            const o = objOfHdr(n);
            inline for (0..parts.len) |i| {
                const names = @typeInfo(parts[i]).@"struct".field_names;
                if (comptime names.len > 0) {
                    const p = part(o, i);
                    inline for (names, 0..) |fname, j| {
                        if (isInit(o, i, j)) eachHdr(@field(p, fname), v, visit);
                    }
                }
            }
        }

        pub fn releaseOutside(n: *sgc.Hdr, _: ?*anyopaque) void {
            const o = objOfHdr(n);
            inline for (0..parts.len) |i| {
                const names = @typeInfo(parts[i]).@"struct".field_names;
                if (comptime names.len > 0) {
                    const p = part(o, i);
                    inline for (names, 0..) |fname, j| {
                        if (isInit(o, i, j)) dropOutside(@field(p, fname));
                    }
                }
            }
        }

        pub fn freeCell(n: *sgc.Hdr, _: ?*anyopaque) void {
            free(@as(*Raw, @ptrCast(@alignCast(objOfHdr(n)))));
        }

        pub fn finalize(n: *sgc.Hdr, _: ?*anyopaque) void {
            const o = objOfHdr(n);
            inline for (0..parts.len) |i| {
                const names = @typeInfo(parts[i]).@"struct".field_names;
                if (comptime names.len > 0) {
                    const p = part(o, i);
                    inline for (names, 0..) |fname, j| {
                        if (isInit(o, i, j)) drop(@field(p, fname));
                    }
                }
            }
            free(@as(*Raw, @ptrCast(@alignCast(o))));
        }

        pub fn isLeaf(o: Obj) bool {
            var n: usize = 0;
            inline for (0..parts.len) |i| {
                const names = @typeInfo(parts[i]).@"struct".field_names;
                if (comptime names.len > 0) {
                    const p = part(o, i);
                    inline for (names, 0..) |fname, j| {
                        if (isInit(o, i, j)) eachHdr(@field(p, fname), &n, countOne);
                    }
                }
            }
            return n == 0;
        }

        const desc: sgc.Desc = .{
            .rc_offset = @as(isize, @offsetOf(ObjHeader, "$rc")) - @as(isize, gc_at),
            .trace = trace,
            .release_outside = releaseOutside,
            .free = freeCell,
            .finalize = finalize,
        };
    };
}

/// The class of the objects whose fields are `Chain`.
pub fn objType(
    comptime Chain: type,
    comptime name: []const u8,
    comptime parent: ?*const ObjType,
    comptime vtables: []const ?*const anyopaque,
    comptime to_string: ?*const fn (?*Env, Obj, void) Raised!String,
) ObjType {
    return objTypeWith(Chain, name, parent, vtables, to_string, null, null, null);
}

/// (a class that overrides `Equals` or `GetHashCode`, or implements `IComparable`: the hooks
/// that call them, `Hook(...).asObj...`)
pub fn objTypeWith(
    comptime Chain: type,
    comptime name: []const u8,
    comptime parent: ?*const ObjType,
    comptime vtables: []const ?*const anyopaque,
    comptime to_string: ?*const fn (?*Env, Obj, void) Raised!String,
    comptime equals: ?*const fn (Obj, Obj) bool,
    comptime hash_: ?*const fn (Obj) i32,
    comptime compare_: ?*const fn (Obj, Obj) i32,
) ObjType {
    return .{ .name = name, .parent = parent, .vtables = vtables, .destroy = ObjCell(Chain).destroy, .share = ObjCell(Chain).share, .to_string = to_string, .equals = equals, .hash = hash_, .compare = compare_, .part_field_bases = ObjCell(Chain).part_bases, .init_offset = ObjCell(Chain).init_at };
}

// ---------------------------------------------------------------------------------------------
// `obj`: an object of a class, a boxed value, or null
// ---------------------------------------------------------------------------------------------

/// `obj`. An object of a class is one already; any other value is boxed: put in an object
/// whose type (`boxType`) knows how to compare, hash and write it.
pub const Any = ?Obj;

pub fn BoxPart(comptime T: type) type {
    return struct { value: T };
}

pub fn BoxChain(comptime T: type) type {
    return struct { own: BoxPart(T) };
}

pub fn boxed(comptime T: type, o: Obj) *BoxPart(T) {
    return objPart(*BoxPart(T), &.{BoxPart(T)}, o);
}

/// .NET's name of a type, for messages and for the text of a boxed value
pub fn netTypeName(comptime T: type) [:0]const u8 {
    return switch (T) {
        i8 => "System.SByte",
        u8 => "System.Byte",
        i16 => "System.Int16",
        c_ushort => "System.UInt16",
        u16 => "System.Char",
        i32 => "System.Int32",
        u32 => "System.UInt32",
        i64 => "System.Int64",
        u64 => "System.UInt64",
        f32 => "System.Single",
        f64 => "System.Double",
        bool => "System.Boolean",
        String => "System.String",
        BigInt => "System.Numerics.BigInteger",
        NetDecimal => "System.Decimal",
        void => "Microsoft.FSharp.Core.Unit",
        else => @typeName(T),
    };
}

/// The type of the objects that hold a boxed `T`
pub fn boxType(comptime T: type) *const ObjType {
    return &struct {
        fn unwrapIfaceBox(o: Obj, target_ty: *const ObjType) ?Obj {
            const v = boxed(T, o).value;
            return v.vt.@"$meta".find_box(v.data, target_ty);
        }
        fn unwrapIfaceObj(o: Obj) ?Obj {
            return ifaceToObjBorrow(boxed(T, o).value);
        }
        fn ifaceBoxId(o: Obj) ?*anyopaque {
            const v = boxed(T, o).value;
            if (ifaceToObjBorrow(v)) |obj| return @ptrCast(obj);
            return v.data;
        }
        const ty: ObjType = .{
            .name = netTypeName(T),
            .parent = null,
            .vtables = &.{},
            .destroy = ObjCell(BoxChain(T)).destroy,
            .share = ObjCell(BoxChain(T)).share,
            .to_string = boxText,
            .equals = boxEquals,
            .hash = boxHash,
            .compare = if (comparable(T)) boxCompare else null,
            .is_array = @typeInfo(T) == .pointer and @hasDecl(@typeInfo(T).pointer.child, "fable_array"),
            .items = if (hasItems(T)) &itemsOf else null,
            .reflect = if (reflection) &reflectOf else null,
            .unwrap_box = if (isIface(T)) &unwrapIfaceBox else null,
            .unwrap_obj = if (isIface(T)) &unwrapIfaceObj else null,
            .iface_id = if (isIface(T)) &ifaceBoxId else null,
        };
        pub fn reflectOf() reflect.Type {
            return reflect.typeOf(T);
        }
        pub fn itemsOf(o: Obj) Array(Any) {
            const x = boxed(T, o).value;
            var out: std.ArrayList(Any) = .empty;
            defer out.deinit(alloc());
            if (comptime T == String) {
                for (unitsOf(x)) |c| out.append(alloc(), box(c)) catch oom();
            } else if (comptime isListType(T)) {
                var rest = x;
                while (rest == .Cons) : (rest = rest.Cons.Tail) out.append(alloc(), box(rest.Cons.Head)) catch oom();
            } else {
                for (x.items) |item| out.append(alloc(), box(item)) catch oom();
            }
            const A = Array(Any);
            const items = arrayItems(A, out.items.len);
            @memcpy(items, out.items);
            return arrayFrom(A, items);
        }
        pub fn boxText(_: ?*Env, o: Obj, _: void) Raised!String {
            const x = boxed(T, o).value;
            if (comptime hookOf(T, "fable_to_string")) return hookType(T).fable_to_string.call(.{x});
            // (a char: the character; UInt16 is c_ushort here)
            if (T == u16) return format(.{arg(.{ .kind = 'c' }, x)});
            // (a record, a union, a list, ...: `%A`, which is their `ToString`)
            return switch (@typeInfo(T)) {
                .int, .float, .bool => format(.{x}),
                else => if (T == String or T == BigInt or T == NetDecimal) format(.{x}) else anyText(x),
            };
        }
        pub fn boxEquals(a: Obj, b: Obj) bool {
            return a.type == b.type and eql(boxed(T, a).value, boxed(T, b).value);
        }
        pub fn boxHash(o: Obj) i32 {
            return hash(boxed(T, o).value);
        }
        pub fn boxCompare(a: Obj, b: Obj) i32 {
            if (a.type != b.type) @panic("fable: Object must be of type " ++ comptime netTypeName(T) ++ ".");
            return compare(boxed(T, a).value, boxed(T, b).value);
        }
    }.ty;
}

pub fn comparable(comptime T: type) bool {
    return comparableTo(T, 6);
}

/// (what `T` holds, to `depth` levels: a function value anywhere makes it not comparable; a type
/// that holds itself is looked into that far)
fn comparableTo(comptime T: type, comptime depth: u8) bool {
    @setEvalBranchQuota(1_000_000);
    if (isFunc(T) or isIface(T) or T == Exn or T == Obj or (isCellPtr(T) and @hasDecl(@typeInfo(T).pointer.child, "fable_identity"))) return false;
    if (depth == 0 or T == String) return true;
    switch (@typeInfo(T)) {
        .@"struct" => |st| {
            inline for (st.field_types) |F| {
                if (!comptimeComparable(F, depth - 1)) return false;
            }
        },
        .@"union" => |u| {
            inline for (u.field_types) |F| {
                if (!comptimeComparable(F, depth - 1)) return false;
            }
        },
        .optional => |o| return comptimeComparable(o.child, depth - 1),
        .pointer => |ptr| if (ptr.size == .one and @typeInfo(ptr.child) == .@"struct" and !@hasDecl(ptr.child, "fable_array")) return comptimeComparable(ptr.child, depth - 1),
        else => {},
    }
    return true;
}

fn comptimeComparable(comptime T: type, comptime depth: u8) bool {
    return comptime comparableTo(T, depth);
}

/// `box x` (it borrows `x`). A null string and `None` box to null, as on .NET.
pub fn box(x: anytype) Any {
    const T = @TypeOf(x);
    if (T == void) return null;
    if (T == Any) return dup(x);
    if (T == Obj) return dup(x);
    if (comptime isIface(T)) {
        return objNew(boxType(T), BoxChain(T){ .own = .{ .value = x } });
    }
    if (T == String and x == null) return null;
    if (comptime @typeInfo(T) == .optional and T != String) {
        if (x == null) return null;
        if (comptime isIface(@typeInfo(T).optional.child)) {
            const C = @typeInfo(T).optional.child;
            const v = x.?;
            return objNew(boxType(C), BoxChain(C){ .own = .{ .value = v } });
        }
    }
    // (an array's, a record's or a function's null is null as an object too)
    if (isNullOf(x)) return null;
    return objNew(boxType(T), BoxChain(T){ .own = .{ .value = x } });
}

/// `o :? T` (of a type that is not a class: those are `anyIsClass`)
pub fn isType(comptime T: type, o: Any) bool {
    if (T == void) return o == null;
    const p = o orelse return false;
    if (p.type == boxType(T)) return true;
    if (comptime isIface(T)) {
        if (objIfaceVt(T, p) != null) return true;
    }
    if (comptime @typeInfo(T) == .optional and isIface(@typeInfo(T).optional.child)) {
        const C = @typeInfo(T).optional.child;
        if (p.type == boxType(C)) return true;
        if (p.type.unwrap_box) |f| {
            if (f(p, boxType(C)) != null) return true;
        }
        if (objIfaceVt(C, p) != null) return true;
    }
    if (p.type.unwrap_box) |f| {
        if (f(p, boxType(T)) != null) return true;
    }
    return false;
}

/// `o :? T` with what it holds: `?T`, null when it is not a `T` (`OT` is `?T`)
pub fn tryUnbox(comptime OT: type, o: Any) OT {
    const T = @typeInfo(OT).optional.child;
    if (T == void) return if (o == null) {} else null;
    const p = o orelse return null;
    if (T == Any or T == Obj) {
        if (p.type.unwrap_obj) |f| {
            if (f(p)) |inner| return dup(inner);
        }
        return dup(p);
    }
    if (p.type == boxType(T)) return dup(boxed(T, p).value);
    if (comptime isIface(T)) {
        if (objAsIface(T, p)) |v| return v;
    }
    if (comptime @typeInfo(T) == .optional and isIface(@typeInfo(T).optional.child)) {
        const C = @typeInfo(T).optional.child;
        if (p.type == boxType(C)) return @as(T, dup(boxed(C, p).value));
        if (p.type.unwrap_box) |f| {
            if (f(p, boxType(C))) |bp| return @as(T, dup(boxed(C, bp).value));
        }
        if (objAsIface(C, p)) |v| return @as(T, v);
    }
    if (p.type.unwrap_box) |f| {
        if (f(p, boxType(T))) |bp| return dup(boxed(T, bp).value);
    }
    return null;
}

/// `o :? System.Array`: a boxed array
fn hasItems(comptime T: type) bool {
    if (T == String) return true;
    if (isListType(T)) return true;
    const info = @typeInfo(T);
    if (info != .pointer or info.pointer.size != .one or @typeInfo(info.pointer.child) != .@"struct") return false;
    return @hasDecl(info.pointer.child, "fable_array") or @hasDecl(info.pointer.child, "fable_resize_array");
}

/// `o :? System.Collections.IEnumerable` of an object
pub fn objHasItems(o: Any) bool {
    const p = o orelse return false;
    return p.type.items != null;
}

/// `o :?> IEnumerable` of an object: its items, boxed (an InvalidCastException when it is not
/// a collection)
pub fn objItems(o: Any) Raised!Array(Any) {
    const p = o orelse return nullRef();
    const f = p.type.items orelse return raise(InvalidCastException, str("Unable to cast object to type 'System.Collections.IEnumerable'."));
    return f(p);
}

pub fn isArray(o: Any) bool {
    const p = o orelse return false;
    return p.type.is_array;
}

/// `o :? C` of a class
pub fn anyIsClass(o: Any, ty: *const ObjType) bool {
    const p = o orelse return false;
    return objIs(p, ty);
}

/// An object of a class used (a member called, a field read): .NET's NullReferenceException
/// for null (a reference of its own, as what the runtime gives is owned)
pub inline fn objNonNull(o: Any) Raised!Obj {
    const p = o orelse return nullRef();
    return dup(p);
}

/// Raise NullReferenceException when an optional object or interface is null, without retaining.
pub inline fn checkNonNull(x: anytype) Raised!void {
    if (comptime isKnownIface(@TypeOf(x))) return;
    if (x == null) return nullRef();
}

/// Unwrap an optional interface parameter or pass through a specialized `KnownIface` unchanged.
pub inline fn unwrapIfaceK(x: anytype) if (isKnownIface(@TypeOf(x))) @TypeOf(x) else @typeInfo(@TypeOf(x)).optional.child {
    if (comptime isKnownIface(@TypeOf(x))) return x;
    return x.?;
}

/// Raise NullReferenceException when a .NET collection (a cell with `fable_null_cell`) is the
/// null cell of its type: before a member is called on it
pub inline fn checkCellNonNull(x: anytype) Raised!void {
    if (isCellNull(x)) return nullRef();
}

/// `o :?> C` of a class: null stays null
pub fn anyToClass(o: Any, ty: *const ObjType) Raised!Any {
    return objCast(o, ty);
}

/// `unbox<T> o` and `o :?> T`
pub fn unbox(comptime T: type, x: anytype) Raised!T {
    // (a value that is a `T` already, as the items of a typed sequence that F# sees as objects)
    if (comptime @TypeOf(x) == T and T != Any) return dup(x);
    const o: Any = x;
    if (T == Any) return dup(o);
    const p = o orelse {
        if (T == void) return {};
        if (comptime @typeInfo(T) == .optional) return null;
        // (null as an array: the array's null)
        if (comptime isArrayPtr(T)) return arrayNull(T);
        return nullRef();
    };
    if (T == Obj) return dup(p);
    if (p.type == boxType(T)) return dup(boxed(T, p).value);
    if (comptime isIface(T)) {
        if (objAsIface(T, p)) |v| return v;
    }
    if (comptime @typeInfo(T) == .optional and isIface(@typeInfo(T).optional.child)) {
        const C = @typeInfo(T).optional.child;
        if (p.type == boxType(C)) return dup(boxed(C, p).value);
        if (p.type.unwrap_box) |f| {
            if (f(p, boxType(C))) |bp| return dup(boxed(C, bp).value);
        }
        if (objAsIface(C, p)) |v| return v;
    }
    if (p.type.unwrap_box) |f| {
        if (f(p, boxType(T))) |bp| return dup(boxed(T, bp).value);
    }
    // (a tuple FSharpValue.MakeTuple made of a type MakeTupleType made)
    if (comptime @typeInfo(T) == .@"struct" and @typeInfo(T).@"struct".is_tuple and T != reflect.LooseTuple) {
        if (p.type == boxType(reflect.LooseTuple)) return reflect.tupleOfLoose(T, boxed(reflect.LooseTuple, p).value);
    }
    var b: TextBuilder = .{};
    b.addAscii("Unable to cast object of type '");
    b.addAscii(p.type.name);
    b.addAscii("' to type '");
    b.addAscii(netTypeName(T));
    b.addAscii("'.");
    return raise(InvalidCastException, b.finish());
}

var next_stamp = std.atomic.Value(u32).init(0);

/// An object's identity hash: a number of its own, as .NET gives (never 0, which means none yet)
pub fn objStamp(o: Obj) i32 {
    const now = @atomicLoad(u32, &o.stamp, .monotonic);
    if (now != 0) return @bitCast(now);
    // (a sequence spread over the 32 bits, as .NET's are random-looking)
    var s = (next_stamp.fetchAdd(1, .monotonic) +% 1) *% 0x9E3779B1;
    if (s == 0) s = 1;
    if (@cmpxchgStrong(u32, &o.stamp, 0, s, .monotonic, .monotonic)) |other| return @bitCast(other);
    return @bitCast(s);
}

/// The identity hash of a cell that has no header of its own for it (a list, an array): a number
/// of its own while it lives, kept by address and forgotten when it is freed (see `free`)
fn cellStamp(addr: usize) i32 {
    const got = thread.stamps.getOrPut(bookkeeping(), addr) catch oom();
    if (!got.found_existing) {
        var s = (next_stamp.fetchAdd(1, .monotonic) +% 1) *% 0x9E3779B1;
        if (s == 0) s = 1;
        got.value_ptr.* = s;
    }
    return @bitCast(got.value_ptr.*);
}

/// `LanguagePrimitives.PhysicalHash x`: of a value that is a reference (a cell, an object, a
/// string), its identity; of any other, its hash
pub fn physicalHash(x: anytype) i32 {
    const T = @TypeOf(x);
    if (comptime isCellPtr(T)) return cellStamp(@intFromPtr(x));
    // (a list: its first cell; the empty list is one value, as on .NET)
    if (comptime isListType(T)) return switch (x) {
        .Cons => |c| cellStamp(@intFromPtr(c)),
        else => 1,
    };
    if (comptime @typeInfo(T) == .optional and isCellPtr(@typeInfo(T).optional.child)) {
        const p = x orelse return 0;
        return cellStamp(@intFromPtr(p));
    }
    if (T == Any) {
        const p = x orelse return 0;
        return objStamp(p);
    }
    if (T == Obj) return objStamp(x);
    // (a value: .NET boxes it for the call, a new object each time)
    if (comptime !isManaged(T) or @typeInfo(T) == .@"struct") {
        var st = (next_stamp.fetchAdd(1, .monotonic) +% 1) *% 0x9E3779B1;
        if (st == 0) st = 1;
        return @bitCast(st);
    }
    return hash(x);
}

// ---- C functions of the program's (`[<DllImport("lib")>] extern int f(string s)`): called
// directly, as Zig calls C. F#'s values are given as C's: a string as its UTF-8 ended by a zero
// (in a buffer of the call's stack when it fits, made for the call only), an array as a pointer
// to its items, anything else (numbers, bool, nativeint) as it is; a string C gives back is
// copied (C still owns it). The library is linked by the build (`-lc`, `-lsqlite3`). ----

/// A string given to C for one call
const CString = struct {
    small: [256]u8 = undefined,
    big: ?[]u8 = null,

    fn init(c: *CString, s: String) [*:0]const u8 {
        const units = unitsOf(s);
        const need = units.len * 3 + 1;
        const buf: []u8 = if (need <= c.small.len) &c.small else blk: {
            const b = alloc().alloc(u8, need) catch oom();
            c.big = b;
            break :blk b;
        };
        const n = std.unicode.wtf16LeToWtf8(buf, units);
        buf[n] = 0;
        return @ptrCast(buf.ptr);
    }

    fn deinit(c: *CString) void {
        if (c.big) |b| alloc().free(b);
    }
};

/// How a value crosses to C (`[<MarshalAs>]`, DllImport's `CharSet`; the compiler gives one for
/// each parameter and for the result): `.plain` as it is; a bool as a 4-byte `BOOL` (`.bool4`,
/// .NET's default) or C's 1-byte `bool` (`.bool1`, `UnmanagedType.I1`/`U1`); a string as UTF-8
/// (`.utf8`, the default) or UTF-16 (`.utf16`, `LPWStr`, `CharSet.Unicode`)
pub const CKind = enum { plain, bool4, bool1, utf8, utf16 };

/// What C is given for a value of type T, crossing as `kind`
fn CArg(comptime T: type, comptime kind: CKind) type {
    if (T == String) return if (kind == .utf16) ?[*:0]const u16 else ?[*:0]const u8;
    if (T == bool) return if (kind == .bool1) bool else i32;
    if (comptime isArrayPtr(T)) return [*]@typeInfo(@FieldType(@typeInfo(T).pointer.child, "items")).pointer.child;
    if (comptime isPlainStruct(T)) return CStruct(T);
    if (comptime isFunc(T)) return CallbackFn(T);
    if (comptime isByref(T)) {
        const V = @typeInfo(T).pointer.child;
        if (V == bool) return if (kind == .bool1) *bool else *i32;
        if (comptime isPlainStruct(V)) return *CStruct(V);
        if (comptime @typeInfo(V) == .int or @typeInfo(V) == .float) return T;
        @compileError("fable: a [<DllImport>] function's byref (out, ref) parameter is of a number, a bool or a struct of them; not " ++ @typeName(V));
    }
    if (comptime isManaged(T)) @compileError("fable: a [<DllImport>] function takes and gives numbers, bools, strings, arrays, delegates, byrefs and structs of numbers and bools (by value); not " ++ @typeName(T));
    return T;
}

/// (a byref: `*T` of a value, not a counted cell)
fn isByref(comptime T: type) bool {
    const info = @typeInfo(T);
    return info == .pointer and info.pointer.size == .one and !isCellPtr(T) and @typeInfo(info.pointer.child) != .@"fn" and @typeInfo(info.pointer.child) != .@"opaque";
}

/// What a byref's value is copied into for the call (and back after): a C struct, a `BOOL`
fn CTemp(comptime T: type, comptime kind: CKind) type {
    if (!isByref(T)) return void;
    const V = @typeInfo(T).pointer.child;
    if (V == bool) return if (kind == .bool1) void else i32;
    if (isPlainStruct(V)) return CStruct(V);
    return void;
}

/// A string given to C as UTF-16 for one call
const CWString = struct {
    small: [128]u16 = undefined,
    big: ?[]u16 = null,

    fn init(c: *CWString, s: String) [*:0]const u16 {
        const units = unitsOf(s);
        const buf: []u16 = if (units.len + 1 <= c.small.len) &c.small else blk: {
            const b = alloc().alloc(u16, units.len + 1) catch oom();
            c.big = b;
            break :blk b;
        };
        @memcpy(buf[0..units.len], units);
        buf[units.len] = 0;
        return @ptrCast(buf.ptr);
    }

    fn deinit(c: *CWString) void {
        if (c.big) |b| alloc().free(b);
    }
};

/// A result of C as F#'s `R`
fn fromC(comptime R: type, comptime kind: CKind, r: anytype) R {
    if (R == String) {
        if (kind == .utf16) {
            const p: ?[*:0]const u16 = r;
            return if (p) |q| strFrom(std.mem.span(q)) else null;
        }
        const p: ?[*:0]const u8 = r;
        return if (p) |q| io.fromUtf8(std.mem.span(q)) else null;
    }
    if (R == bool) return if (kind == .bool1) r else r != 0;
    if (comptime isPlainStruct(R)) return fromCStruct(R, r);
    return r;
}

/// An F# value as C's (a callback's result)
fn toC(comptime T: type, comptime kind: CKind, x: T) CArg(T, kind) {
    if (T == bool) return if (kind == .bool1) x else @intFromBool(x);
    if (comptime isPlainStruct(T)) return toCStruct(CStruct(T), x);
    return x;
}

// ---- structs given to C by value: an F# struct of numbers, bools and such structs (a
// `[<Struct>]` record, or a struct of `val` fields) is copied, field by field, into a struct of
// the same fields laid out as C lays them out (an `extern struct`), and back for a result ----

/// Is T a struct of numbers, bools and such structs (no tuple, nothing counted)?
fn isPlainStruct(comptime T: type) bool {
    return comptime blk: {
        const info = @typeInfo(T);
        if (info != .@"struct") break :blk false;
        if (info.@"struct".is_tuple or isManaged(T)) break :blk false;
        if (info.@"struct".layout == .@"packed") break :blk false;
        for (info.@"struct".field_types) |F| {
            switch (@typeInfo(F)) {
                .int, .float, .bool => {},
                .@"struct" => if (!isPlainStruct(F)) break :blk false,
                else => break :blk false,
            }
        }
        break :blk info.@"struct".field_names.len != 0;
    };
}

/// The C layout of a plain struct (see above)
fn CStruct(comptime T: type) type {
    const st = @typeInfo(T).@"struct";
    if (st.layout == .@"extern") return T;
    var types: [st.field_names.len]type = undefined;
    for (st.field_types, 0..) |F, i| types[i] = if (@typeInfo(F) == .@"struct") CStruct(F) else F;
    return @Struct(.@"extern", null, st.field_names, &types, &@splat(.{}));
}

/// `x` as the struct `C` (a C struct of the same field names: `CStruct(T)`, or one of a header)
fn toCStruct(comptime C: type, x: anytype) C {
    var c: C = undefined;
    inline for (@typeInfo(C).@"struct".field_names) |name| {
        if (!@hasField(@TypeOf(x), name)) @compileError("fable: the C struct " ++ @typeName(C) ++ " has a field `" ++ name ++ "` that " ++ @typeName(@TypeOf(x)) ++ " has not");
        const F = @FieldType(C, name);
        const v = @field(x, name);
        @field(c, name) = if (@typeInfo(F) == .@"struct") toCStruct(F, v) else if (@typeInfo(F) == .float and @TypeOf(v) != F) @floatCast(v) else if (@typeInfo(F) == .int and @TypeOf(v) != F) @intCast(v) else v;
    }
    return c;
}

/// A C struct `c` as the F# struct T
fn fromCStruct(comptime T: type, c: anytype) T {
    var x: T = undefined;
    inline for (@typeInfo(T).@"struct".field_names) |name| {
        const F = @FieldType(T, name);
        const v = @field(c, name);
        @field(x, name) = if (@typeInfo(F) == .@"struct") fromCStruct(F, v) else if (@typeInfo(F) == .float and @TypeOf(v) != F) @floatCast(v) else if (@typeInfo(F) == .int and @TypeOf(v) != F) @intCast(v) else v;
    }
    return x;
}

fn CFn(comptime P: []const type, comptime R: type) type {
    return switch (P.len) {
        0 => *const fn () callconv(.c) R,
        1 => *const fn (P[0]) callconv(.c) R,
        2 => *const fn (P[0], P[1]) callconv(.c) R,
        3 => *const fn (P[0], P[1], P[2]) callconv(.c) R,
        4 => *const fn (P[0], P[1], P[2], P[3]) callconv(.c) R,
        5 => *const fn (P[0], P[1], P[2], P[3], P[4]) callconv(.c) R,
        6 => *const fn (P[0], P[1], P[2], P[3], P[4], P[5]) callconv(.c) R,
        else => @compileError("fable: a C function of more than six arguments"),
    };
}

// ---- callbacks: a delegate given to C is a function of C's calling convention made for it
// (one for each callback parameter of each C function), which turns C's arguments into F#'s,
// calls the delegate and gives its result back as C's. The delegate it calls: the one given to
// the call that is running on this thread (`qsort`'s comparison), or else the one given last
// (a callback C keeps and calls later, from any thread). As on .NET, the program keeps that
// delegate alive while C may call it (no reference is taken here, as .NET's thunk does not keep
// the delegate alive either); an exception that leaves it ends the program, as on .NET. ----

fn Callback(comptime name: []const u8, comptime index: usize, comptime F: type) type {
    _ = name;
    _ = index;
    const Code = @typeInfo(@FieldType(F, "code")).pointer.child;
    const Fn = @typeInfo(Code).@"fn";
    const P = Fn.param_types[1..];
    const RR = Fn.return_type.?;
    const R = if (isRaised(RR)) Unraised(RR) else RR;
    const CR = CArg(R, .plain);
    return struct {
        threadlocal var current: ?F = null;
        var latest: ?F = null;
        var guard = std.atomic.Value(u32).init(0);

        fn setLatest(f: F) void {
            while (guard.cmpxchgWeak(0, 1, .acquire, .monotonic) != null) std.atomic.spinLoopHint();
            latest = f;
            guard.store(0, .release);
        }

        fn delegate() F {
            if (current) |f| return f;
            while (guard.cmpxchgWeak(0, 1, .acquire, .monotonic) != null) std.atomic.spinLoopHint();
            const f = latest;
            guard.store(0, .release);
            return f orelse @panic("fable: a C callback was called with no delegate given for it");
        }

        fn invoke(c_args: anytype) CR {
            const f = delegate();
            var f_args: std.meta.ArgsTuple(Code) = undefined;
            f_args[0] = f.env;
            inline for (P, 0..) |A, i| {
                const a = c_args[i];
                f_args[i + 1] = if (A.? == String) strFromCStr(a) else fromC(A.?, .plain, a);
            }
            const result = @call(.auto, f.code, f_args);
            const value = if (comptime isRaised(RR)) result catch {
                uncaught();
                std.process.abort();
            } else result;
            return toC(R, .plain, value);
        }

        const C = blk: {
            var ps: [P.len]type = undefined;
            for (P, 0..) |A, i| ps[i] = if (A.? == String) ?[*:0]const u8 else CArg(A.?, .plain);
            break :blk ps;
        };

        const code = switch (P.len) {
            0 => struct {
                fn f() callconv(.c) CR {
                    return invoke(.{});
                }
            }.f,
            1 => struct {
                fn f(a: C[0]) callconv(.c) CR {
                    return invoke(.{a});
                }
            }.f,
            2 => struct {
                fn f(a: C[0], b: C[1]) callconv(.c) CR {
                    return invoke(.{ a, b });
                }
            }.f,
            3 => struct {
                fn f(a: C[0], b: C[1], c: C[2]) callconv(.c) CR {
                    return invoke(.{ a, b, c });
                }
            }.f,
            4 => struct {
                fn f(a: C[0], b: C[1], c: C[2], d: C[3]) callconv(.c) CR {
                    return invoke(.{ a, b, c, d });
                }
            }.f,
            5 => struct {
                fn f(a: C[0], b: C[1], c: C[2], d: C[3], e: C[4]) callconv(.c) CR {
                    return invoke(.{ a, b, c, d, e });
                }
            }.f,
            else => @compileError("fable: a callback of more than five arguments"),
        };
    };
}

/// The C type of a callback for a delegate of type F
fn CallbackFn(comptime F: type) type {
    const Code = @typeInfo(@FieldType(F, "code")).pointer.child;
    const Fn = @typeInfo(Code).@"fn";
    const P = Fn.param_types[1..];
    const RR = Fn.return_type.?;
    const R = if (isRaised(RR)) Unraised(RR) else RR;
    var ps: [P.len]type = undefined;
    for (P, 0..) |A, i| ps[i] = if (A.? == String) ?[*:0]const u8 else CArg(A.?, .plain);
    return CFn(&ps, CArg(R, .plain));
}

/// `f args` of `[<DllImport>] extern R f(...)`: the C function `name`, each argument crossing as
/// its kind in `kinds`, the result as `ret`
pub fn callC(comptime R: type, comptime name: []const u8, comptime kinds: anytype, comptime ret: CKind, args: anytype) R {
    const fields = @typeInfo(@TypeOf(args)).@"struct".field_types;
    const n = fields.len;
    const params = comptime blk: {
        var ps: [n]type = undefined;
        for (fields, 0..) |F, i| ps[i] = CArg(F, kinds[i]);
        break :blk ps;
    };
    const temp_types = comptime blk: {
        var ts: [n]type = undefined;
        for (fields, 0..) |F, i| ts[i] = CTemp(F, kinds[i]);
        break :blk ts;
    };
    var c_args: @Tuple(&params) = undefined;
    var temps: @Tuple(&temp_types) = undefined;
    var strings: [n]CString = undefined;
    var wide: [n]CWString = undefined;
    inline for (0..n) |i| {
        const F = fields[i];
        const kind: CKind = kinds[i];
        if (F == String) {
            if (kind == .utf16) {
                wide[i] = .{};
                c_args[i] = if (args[i] == null) null else wide[i].init(args[i]);
            } else {
                strings[i] = .{};
                c_args[i] = if (args[i] == null) null else strings[i].init(args[i]);
            }
        } else if (comptime isArrayPtr(F)) {
            c_args[i] = args[i].items.ptr;
        } else if (comptime isPlainStruct(F)) {
            c_args[i] = toCStruct(CStruct(F), args[i]);
        } else if (comptime isFunc(F)) {
            const Cb = Callback(name, i, F);
            Cb.setLatest(args[i]);
            c_args[i] = &Cb.code;
        } else if (comptime temp_types[i] != void) {
            const V = @typeInfo(F).pointer.child;
            temps[i] = if (V == bool) @intFromBool(args[i].*) else toCStruct(temp_types[i], args[i].*);
            c_args[i] = &temps[i];
        } else if (F == bool) {
            c_args[i] = if (kind == .bool1) args[i] else @intFromBool(args[i]);
        } else {
            c_args[i] = args[i];
        }
    }
    // (the delegates of this call, for callbacks that come while it runs on this thread)
    const saved_types = comptime blk: {
        var ts: [n]type = undefined;
        for (fields, 0..) |F, i| ts[i] = if (isFunc(F)) ?F else void;
        break :blk ts;
    };
    var saved: @Tuple(&saved_types) = undefined;
    inline for (0..n) |i| {
        if (comptime isFunc(fields[i])) {
            const Cb = Callback(name, i, fields[i]);
            saved[i] = Cb.current;
            Cb.current = args[i];
        }
    }
    defer inline for (0..n) |i| {
        if (fields[i] == String) {
            if (kinds[i] == .utf16) wide[i].deinit() else strings[i].deinit();
        }
        if (comptime isFunc(fields[i])) Callback(name, i, fields[i]).current = saved[i];
    };
    const CR = comptime if (R == String) (if (ret == .utf16) ?[*:0]const u16 else ?[*:0]const u8) else CArg(R, ret);
    const f = @extern(CFn(&params, CR), .{ .name = name });
    const r = @call(.auto, f, c_args);
    // (what C wrote into the byrefs' copies, back into them)
    inline for (0..n) |i| {
        if (comptime temp_types[i] != void) {
            const V = @typeInfo(fields[i]).pointer.child;
            args[i].* = if (V == bool) temps[i] != 0 else fromCStruct(V, temps[i]);
        }
    }
    return fromC(R, ret, r);
}

/// `f args` of a C function imported with `[<Import("f", "c:module")>]` (a module of C's
/// declarations: translated from a header by the build, or `extern` functions written in Zig):
/// F#'s values given as the function's parameter types ask, as `callC` gives them; a string or
/// a number of another size given back as F#'s type `R`
pub fn cCall(comptime R: type, f: anytype, args: anytype) R {
    const P = @typeInfo(@TypeOf(f)).@"fn".param_types;
    const fields = @typeInfo(@TypeOf(args)).@"struct".field_types;
    if (P.len != fields.len) @compileError("fable: the C function takes " ++ std.fmt.comptimePrint("{d}", .{P.len}) ++ " arguments");
    const params = comptime blk: {
        var ps: [P.len]type = undefined;
        for (P, 0..) |p, i| ps[i] = p.?;
        break :blk ps;
    };
    var c_args: @Tuple(&params) = undefined;
    var strings: [fields.len]CString = undefined;
    inline for (0..fields.len) |i| {
        const F = fields[i];
        if (F == String) {
            strings[i] = .{};
            c_args[i] = if (args[i] == null) @ptrFromInt(0) else @ptrCast(strings[i].init(args[i]));
        } else if (comptime isArrayPtr(F)) {
            c_args[i] = @ptrCast(args[i].items.ptr);
        } else if (comptime @typeInfo(F) == .int and @typeInfo(params[i]) == .int) {
            c_args[i] = @intCast(args[i]);
        } else if (comptime @typeInfo(F) == .float and @typeInfo(params[i]) == .float) {
            c_args[i] = @floatCast(args[i]);
        } else if (comptime isPlainStruct(F) and @typeInfo(params[i]) == .@"struct") {
            c_args[i] = toCStruct(params[i], args[i]);
        } else {
            c_args[i] = args[i];
        }
    }
    defer inline for (0..fields.len) |i| {
        if (fields[i] == String) strings[i].deinit();
    };
    const r = @call(.auto, f, c_args);
    const T = @TypeOf(r);
    if (R == String) {
        const p: ?[*:0]const u8 = @ptrCast(r);
        return if (p) |q| io.fromUtf8(std.mem.span(q)) else null;
    }
    if (comptime T == R) return r;
    if (comptime isPlainStruct(R) and @typeInfo(T) == .@"struct") return fromCStruct(R, r);
    if (comptime @typeInfo(T) == .int and @typeInfo(R) == .int) return @intCast(r);
    if (comptime @typeInfo(T) == .float and @typeInfo(R) == .float) return @floatCast(r);
    if (comptime @typeInfo(T) == .bool and @typeInfo(R) == .bool) return r;
    return r;
}

/// For Zig code of the program's: the UTF-8 of a string, ended by a zero, which the caller frees
/// (`fable_rt.allocator`); and a string of UTF-8 bytes or of a C string (copied)
pub fn strToUtf8Z(s: String) [:0]u8 {
    const units = unitsOf(s);
    const buf = allocator.allocSentinel(u8, std.unicode.calcWtf8Len(units), 0) catch oom();
    _ = std.unicode.wtf16LeToWtf8(buf, units);
    return buf;
}

pub fn strFromUtf8(bytes: []const u8) String {
    return io.fromUtf8(bytes);
}

pub fn strFromCStr(p: ?[*:0]const u8) String {
    const q = p orelse return null;
    return io.fromUtf8(std.mem.span(q));
}

/// `Fable.Core.Zig.sameCell a b`: are both the same cell (one reference type's object, a
/// list's first cell, a function's environment)? A value (a number, a struct, a record or a union
/// kept as a value) is never the same cell as anything: false, as .NET's ReferenceEquals of two
/// boxings. For a shortcut before structural equality (`sameCell a b || a = b`).
pub fn sameCell(a: anytype, b: @TypeOf(a)) bool {
    const T = @TypeOf(a);
    if (comptime isCellPtr(T)) return a == b;
    if (T == String) return a == b;
    if (T == Any) return a == b;
    if (comptime isFunc(T)) return a.env != null and a.env == b.env and a.code == b.code;
    if (comptime isIface(T)) return a.data == b.data;
    if (comptime isListType(T)) return switch (a) {
        .Cons => |c| switch (b) {
            .Cons => |d| c == d,
            else => false,
        },
        // (the empty list is one value, as on .NET)
        else => b != .Cons,
    };
    if (comptime @typeInfo(T) == .optional and isCellPtr(@typeInfo(T).optional.child)) return a == b;
    return false;
}

/// A whole-number format (`B`, `X`, `D`) given to a float or a decimal: .NET's FormatException
pub fn formatSpecifierInvalid(comptime T: type) Raised!T {
    return raise(FormatException, str("Format specifier was invalid."));
}

/// A map changed through `IDictionary` or `ICollection`: .NET's NotSupportedException
pub fn mapNotMutable(comptime T: type) Raised!T {
    return raise(NotSupportedException, str("Map values cannot be mutated."));
}

/// `o :?> I` of an interface that has no null: null raises NullReferenceException
pub fn unboxNonNull(comptime T: type, x: Any) Raised!T {
    if (x == null) return nullRef();
    return unbox(T, x);
}

/// `o.ToString()` (null raises) and `string o` (null is "")
/// `String.Format(pattern, args)` with a pattern known only when the program runs: `{i}` and
/// `{i,width}` of the objects' text, `{{` and `}}`. (A `:format` part is refused: the objects'
/// types are not known here.) It borrows both.
pub fn strFormatObjs(pattern: String, args: Array(Any)) Raised!String {
    const p = unitsOf(pattern);
    const items = args.items;
    var b: TextBuilder = .{};
    errdefer b.deinit();
    var i: usize = 0;
    while (i < p.len) {
        const c = p[i];
        if (c == '}') {
            if (i + 1 < p.len and p[i + 1] == '}') {
                b.addOne('}');
                i += 2;
                continue;
            }
            return raise(FormatException, str("Input string was not in a correct format."));
        }
        if (c != '{') {
            b.addOne(c);
            i += 1;
            continue;
        }
        if (i + 1 < p.len and p[i + 1] == '{') {
            b.addOne('{');
            i += 2;
            continue;
        }
        // `{index[,width][:format]}`
        i += 1;
        var index: usize = 0;
        var digits: usize = 0;
        while (i < p.len and p[i] >= '0' and p[i] <= '9') : (i += 1) {
            index = index * 10 + (p[i] - '0');
            digits += 1;
        }
        var width: i64 = 0;
        if (i < p.len and p[i] == ',') {
            i += 1;
            while (i < p.len and p[i] == ' ') i += 1;
            var negative = false;
            if (i < p.len and p[i] == '-') {
                negative = true;
                i += 1;
            }
            while (i < p.len and p[i] >= '0' and p[i] <= '9') : (i += 1) width = width * 10 + (p[i] - '0');
            if (negative) width = -width;
        }
        // (`:format`, up to the closing brace)
        var spec: []const u16 = &.{};
        if (i < p.len and p[i] == ':') {
            const start = i + 1;
            i = start;
            while (i < p.len and p[i] != '}') i += 1;
            spec = p[start..i];
        }
        if (digits == 0 or i >= p.len or p[i] != '}') {
            return raise(FormatException, str("Input string was not in a correct format."));
        }
        i += 1;
        if (index >= items.len) {
            return raise(FormatException, str("Index (zero based) must be greater than or equal to zero and less than the size of the argument list."));
        }
        const text = if (spec.len != 0)
            (try formatBoxed(items[index], spec)) orelse try anyToString(items[index], true)
        else
            try anyToString(items[index], true);
        defer drop(text);
        const t = unitsOf(text);
        const pad: usize = if (@abs(width) > t.len) @intCast(@abs(width) - t.len) else 0;
        if (width > 0) for (0..pad) |_| b.addOne(' ');
        b.add(t);
        if (width < 0) for (0..pad) |_| b.addOne(' ');
    }
    return b.finish();
}

/// A boxed number with a .NET format known when the program runs (`{0:N2}` of
/// `String.Format(pattern, args)`): its text; null for a value that is not a number, whose
/// `ToString` the format does not change here
fn formatBoxed(v: Any, spec: []const u16) Raised!?String {
    var ascii: [64]u8 = undefined;
    if (spec.len > ascii.len) return raise(FormatException, str("Format specifier was invalid."));
    for (spec, 0..) |c, k| ascii[k] = if (c < 128) @intCast(c) else '?';
    const fmt = ascii[0..spec.len];
    const standard = fmt.len <= 3 and std.ascii.isAlphabetic(fmt[0]) and for (fmt[1..]) |c| {
        if (!std.ascii.isDigit(c)) break false;
    } else true;
    const given: ?i32 = if (standard and fmt.len > 1) (std.fmt.parseInt(i32, fmt[1..], 10) catch null) else null;
    inline for (.{ i32, i64, f64, f32, u8, i8, i16, c_ushort, u32, u64, NetDecimal }) |T| {
        if (tryUnbox(?T, v)) |x| {
            var out: [512]u8 = undefined;
            const text: ?[]const u8 = if (standard)
                fable_netformat.standardText(fmt[0], given, x, &out)
            else
                fable_netformat.customText(fmt, x, &out);
            const t = text orelse return raise(FormatException, str("Format specifier was invalid."));
            var b: TextBuilder = .{};
            b.addAscii(t);
            return b.finish();
        }
    }
    return null;
}

pub fn anyToString(o: Any, comptime null_is_empty: bool) Raised!String {
    const p = o orelse return if (null_is_empty) str("") else nullRef();
    return objText(p);
}

/// A `None` or an empty list whose item type F# left open, as a value of type `T`
pub fn emptyAs(comptime T: type, x: anytype) T {
    const X = @TypeOf(x);
    if (X == T) return x;
    switch (@typeInfo(T)) {
        .optional => {
            if (x != null) @panic("fable: emptyAs of a value that is not empty");
            return null;
        },
        .@"union" => {
            if (comptime !@hasField(T, "Empty")) @compileError("fable: emptyAs of " ++ @typeName(T));
            return .Empty;
        },
        else => @compileError("fable: emptyAs of " ++ @typeName(T)),
    }
}

/// `string x` and `x.ToString()` of a value whose type is a type parameter: what they give for
/// the type it stands for
pub fn genericText(x: anytype) Raised!String {
    const T = @TypeOf(x);
    if (T == void) return str("");
    if (T == String) return strConcat(x, null);
    if (T == u16) return format(.{arg(.{ .kind = 'c' }, x)});
    if (T == Any) return anyToString(x, true);
    if (T == Obj) return objText(x);
    if (comptime isIface(T)) {
        if (ifaceToObjBorrow(x)) |o| return objText(o);
        return anyText(x);
    }
    if (comptime hookOf(T, "fable_to_string")) return hookType(T).fable_to_string.call(.{x});
    return switch (@typeInfo(T)) {
        .int, .float, .bool => format(.{x}),
        else => if (T == BigInt or T == NetDecimal) format(.{x}) else anyText(x),
    };
}

/// The `k`th type argument of a type that names them (`Lazy(T)`: `T`)
pub fn typeArg(comptime P: type, comptime k: usize) type {
    const S = switch (@typeInfo(P)) {
        .pointer => |p| p.child,
        .optional => |o| switch (@typeInfo(o.child)) {
            .pointer => |p| p.child,
            else => o.child,
        },
        else => P,
    };
    if (!@hasDecl(S, "fable_args")) @compileError("fable: the type arguments of " ++ @typeName(P) ++ " are not known here");
    return S.fable_args[k];
}

/// `x :> T` of a value whose type is a type parameter constrained to `T`: `x` itself, when Zig
/// instantiates the parameter with `T`
pub fn asSame(comptime T: type, x: anytype) T {
    if (@TypeOf(x) == T) return x;
    @compileError("fable: a value of type " ++ @typeName(@TypeOf(x)) ++ " is used as a " ++ @typeName(T));
}

/// A format of printf given as a value (`Printf.StringFormat<string>`): its text and the values
/// an interpolated string captured
/// (a tuple, which the compiler counts and frees as it does any: see LowerTypes)
pub const PrintfFormat = @Tuple(&.{ String, Array(Any) });

/// `PrintfFormat(text)` and `PrintfFormat(text, captures, types)`
pub fn printfFormatNew(value: String, captures: anytype) PrintfFormat {
    const A = Array(Any);
    const C = @TypeOf(captures);
    const held: A = if (C == void)
        arrayFrom(A, arrayItems(A, 0))
    else if (comptime @typeInfo(C) == .optional)
        (if (captures) |a| dup(a) else arrayFrom(A, arrayItems(A, 0)))
    else
        dup(captures);
    return .{ dup(value), held };
}

/// `fmt.Value`
pub fn printfFormatValue(f: PrintfFormat) String {
    return dup(f[0]);
}

/// `sprintf fmt` of a format given as a value, which takes no more values: its text with each
/// hole the value the interpolated string captured for it. (Widths and flags are not applied to
/// the values here; a precision of a float is.)
pub fn printfFormatText(f: PrintfFormat) Raised!String {
    const units = unitsOf(f[0]);
    const values: []const Any = f[1].items;
    var b: TextBuilder = .{};
    var i: usize = 0;
    var hole: usize = 0;
    while (i < units.len) {
        const c = units[i];
        if (c != '%') {
            b.add(units[i .. i + 1]);
            i += 1;
            continue;
        }
        if (i + 1 < units.len and units[i + 1] == '%') {
            b.addAscii("%");
            i += 2;
            continue;
        }
        // (flags, a width, a precision, then the letter)
        var j = i + 1;
        var precision: ?u8 = null;
        while (j < units.len and !std.ascii.isAlphabetic(@truncate(units[j]))) : (j += 1) {
            if (units[j] == '.') {
                var p: u8 = 0;
                j += 1;
                while (j < units.len and units[j] >= '0' and units[j] <= '9') : (j += 1) p = p *| 10 +| @as(u8, @intCast(units[j] - '0'));
                precision = p;
                j -= 1;
            }
        }
        if (j >= units.len) return raise(FormatException, str("The format is missing its type of value."));
        const letter: u8 = @truncate(units[j]);
        j += 1;
        // (an interpolated hole: the spec is followed by `%P()`, or is `%P()` itself)
        if (letter == 'P' and j + 1 < units.len and units[j] == '(' and units[j + 1] == ')') {
            j += 2;
        } else if (j + 3 < units.len and units[j] == '%' and units[j + 1] == 'P' and units[j + 2] == '(' and units[j + 3] == ')') {
            j += 4;
        }
        if (hole >= values.len) return raise(FormatException, str("The format takes more values than it was given."));
        const v = values[hole];
        hole += 1;
        const text = try formatHole(letter, precision, v);
        defer drop(text);
        b.add(unitsOf(text));
        i = j;
    }
    return b.finish();
}

fn formatHole(letter: u8, precision: ?u8, v: Any) Raised!String {
    switch (letter) {
        'f', 'F', 'e', 'E', 'g', 'G' => {
            if (tryUnbox(?f64, v)) |x| return floatHole(letter, precision, x);
            if (tryUnbox(?f32, v)) |x| return floatHole(letter, precision, @as(f64, x));
        },
        'b' => if (tryUnbox(?bool, v)) |x| return if (x) str("true") else str("false"),
        // (`%A`, `%O`, `%d`, `%s` and the others of a boxed value: its ToString)
        else => {},
    }
    return anyToString(v, true);
}

fn floatHole(letter: u8, precision: ?u8, x: f64) String {
    const p = precision orelse return switch (letter) {
        inline 'f', 'F', 'e', 'E', 'g', 'G' => |k| format(.{arg(.{ .kind = k }, x)}),
        else => unreachable,
    };
    return switch (letter) {
        inline 'f', 'F', 'e', 'E', 'g', 'G' => |k| switch (@as(u4, @intCast(@min(p, 15)))) {
            inline else => |q| format(.{arg(.{ .kind = k, .precision = q }, x)}),
        },
        else => unreachable,
    };
}

// ---- printf of a format known only when the program runs, given its values (`sprintf fmt a b`
// with `fmt: StringFormat<'T>` made from a string). F# takes the printer type ('T, here
// `int -> string -> string`) from where the format is used, so Zig knows it: a chain of
// function values made for it, each holding the values given so far (as they are, not boxed),
// the last turning them into text. Each hole is checked against its value's type as the
// program runs, as .NET does (with .NET's classes of exception, not its messages, which are
// FSharp.Core's internals). ----

/// What is done with the text: given back (sprintf), written (printf, printfn, eprintf,
/// eprintfn) or raised (failwithf)
pub const PrintfSink = enum { text, out, out_line, err, err_line, fail };

/// `sprintf fmt` (or another of PrintfSink) of a format given as a value: a function value of
/// type `F` that takes the format's values one by one, or the result where it takes none
pub fn printfFormatFn(comptime F: type, comptime sink: PrintfSink, f: PrintfFormat) Raised!F {
    return printfStage(F, sink, f, .{});
}

/// (`args`: the values so far, owned; `f` borrowed)
fn printfStage(comptime F: type, comptime sink: PrintfSink, f: PrintfFormat, args: anytype) Raised!F {
    if (comptime isFunc(F)) {
        const Caps = struct { fmt: PrintfFormat, args: @TypeOf(args) };
        const S = PrintfStageCode(F, sink, Caps);
        const caps: Caps = .{ .fmt = dup(f), .args = args };
        if (comptime @hasField(F, "code2")) return closure2(F, Caps, caps, S.code, S.code2);
        return closure(F, Caps, caps, S.code);
    }
    return printfFinish(F, sink, f, args);
}

fn PrintfStageCode(comptime F: type, comptime sink: PrintfSink, comptime Caps: type) type {
    const Code = @typeInfo(@FieldType(F, "code")).pointer.child;
    const Fn = @typeInfo(Code).@"fn";
    const A = Fn.param_types[1].?;
    const R = Unraised(Fn.return_type.?);
    return struct {
        fn code(env: ?*Env, a: A) Raised!R {
            const c = captured(Caps, env);
            return printfStage(R, sink, c.fmt, dup(c.args) ++ .{a});
        }

        const Fn2 = if (@hasField(F, "code2")) @typeInfo(@typeInfo(Code2Of(@FieldType(F, "code"))).pointer.child).@"fn" else Fn;
        const B = if (@hasField(F, "code2")) Fn2.param_types[2].? else void;

        fn code2(env: ?*Env, a: A, b: B) Fn2.return_type.? {
            const g = code(env, a) catch |e| {
                drop(b);
                return e;
            };
            defer drop(g);
            return g.code(g.env, b);
        }
    };
}

fn printfFinish(comptime R: type, comptime sink: PrintfSink, f: PrintfFormat, args: anytype) Raised!R {
    defer drop(args);
    const text = try printfTyped(f, args);
    switch (sink) {
        .text => return text,
        .fail => return raise(Failure, text),
        else => {
            defer drop(text);
            switch (sink) {
                .out => print(.{text}, false),
                .out_line => print(.{text}, true),
                .err => printErr(.{text}, false),
                .err_line => printErr(.{text}, true),
                else => unreachable,
            }
            return if (R == void) {} else @compileError("fable: printf of a format given as a value gives unit");
        },
    }
}

const PrintfHole = struct { letter: u8, width: usize = 0, precision: ?u8 = null, left: bool = false, zero: bool = false, plus: bool = false, space: bool = false };

/// The text of the format with its holes filled by `args` in order
fn printfTyped(f: PrintfFormat, args: anytype) Raised!String {
    const n = @typeInfo(@TypeOf(args)).@"struct".field_names.len;
    const units = unitsOf(f[0]);
    var b: TextBuilder = .{};
    errdefer drop(b.finish());
    var i: usize = 0;
    var hole: usize = 0;
    while (i < units.len) {
        if (units[i] != '%') {
            b.add(units[i .. i + 1]);
            i += 1;
            continue;
        }
        if (i + 1 < units.len and units[i + 1] == '%') {
            b.addAscii("%");
            i += 2;
            continue;
        }
        var h: PrintfHole = .{ .letter = 0 };
        var j = i + 1;
        while (j < units.len) : (j += 1) {
            switch (units[j]) {
                '-' => h.left = true,
                '0' => h.zero = true,
                '+' => h.plus = true,
                ' ' => h.space = true,
                else => break,
            }
        }
        while (j < units.len and units[j] >= '0' and units[j] <= '9') : (j += 1) h.width = h.width *| 10 +| @as(usize, units[j] - '0');
        if (j < units.len and units[j] == '.') {
            j += 1;
            var p: u8 = 0;
            while (j < units.len and units[j] >= '0' and units[j] <= '9') : (j += 1) p = p *| 10 +| @as(u8, @intCast(units[j] - '0'));
            h.precision = p;
        }
        if (j >= units.len or units[j] > 0x7f) return raise(ArgumentException, str("Bad format specifier"));
        h.letter = @intCast(units[j]);
        j += 1;
        if (hole >= n) return raise(Failure, str("The format takes more values than it was given."));
        var text: String = null;
        inline for (0..n) |k| {
            if (k == hole) text = try printfHoleText(h, args[k]);
        }
        defer drop(text);
        printfPad(&b, h, unitsOf(text));
        hole += 1;
        i = j;
    }
    if (hole != n) return raise(InvalidCastException, str("The format takes fewer values than it was given."));
    return b.finish();
}

/// `text` with the hole's width: spaces before (or after, `-`), or zeros after the sign (`0`)
fn printfPad(b: *TextBuilder, h: PrintfHole, text: []const u16) void {
    const pad = if (h.width > text.len) h.width - text.len else 0;
    if (pad == 0) return b.add(text);
    if (h.left) {
        b.add(text);
        for (0..pad) |_| b.addAscii(" ");
        return;
    }
    const numeric = switch (h.letter) {
        'd', 'i', 'u', 'x', 'X', 'o', 'B', 'f', 'F', 'e', 'E', 'g', 'G', 'M' => true,
        else => false,
    };
    if (h.zero and numeric) {
        const signed = text.len > 0 and (text[0] == '-' or text[0] == '+' or text[0] == ' ');
        if (signed) b.add(text[0..1]);
        for (0..pad) |_| b.addAscii("0");
        return b.add(if (signed) text[1..] else text);
    }
    for (0..pad) |_| b.addAscii(" ");
    b.add(text);
}

/// Does a hole of this letter take a value of type T (as F# checks a format it knows)?
fn printfTakes(comptime letter: u8, comptime T: type) bool {
    return switch (letter) {
        'd', 'i', 'u', 'x', 'X', 'o', 'B' => @typeInfo(T) == .int or T == BigInt,
        'f', 'F', 'e', 'E', 'g', 'G' => @typeInfo(T) == .float or T == NetDecimal,
        'M' => T == NetDecimal,
        // (a string, or an object F# typed from `null`: its ToString, "" of null)
        's' => T == String or T == Any,
        'c' => T == u16,
        'b' => T == bool,
        'A', 'O' => true,
        else => false,
    };
}

fn printfHoleText(h: PrintfHole, v: anytype) Raised!String {
    const T = @TypeOf(v);
    switch (h.letter) {
        inline 'd', 'i', 'u', 'x', 'X', 'o', 'B', 'f', 'F', 'e', 'E', 'g', 'G', 'M', 's', 'c', 'b', 'A', 'O' => |k| {
            if (comptime !printfTakes(k, T)) return raise(Failure, str("The format's type of value does not match the value given."));
            if (comptime k == 'O' or (k == 's' and T == Any)) return printfToString(k, v);
            if (comptime k == 'A' or k == 's' or k == 'c' or k == 'b') return format(.{arg(.{ .kind = k }, v)});
            return switch (@as(u2, @intFromBool(h.plus)) * 2 + @intFromBool(h.space)) {
                inline else => |sign| printfNumber(k, sign >> 1 == 1, sign & 1 == 1, h.precision, v),
            };
        },
        else => return raise(ArgumentException, str("Bad format specifier")),
    }
}

/// `%O` (and `%s` of an object): .NET's ToString of the value; null as `<null>` (`%s`: nothing)
fn printfToString(comptime k: u8, v: anytype) Raised!String {
    const T = @TypeOf(v);
    if (T == Any or T == Obj or comptime isIface(T)) {
        if (comptime T == Any) {
            if (v == null) return str(if (k == 'O') "<null>" else "");
        }
        return genericText(v);
    }
    var b: TextBuilder = .{};
    writeNet(&b, v);
    return b.finish();
}

fn printfNumber(comptime k: u8, comptime plus: bool, comptime space: bool, precision: ?u8, v: anytype) String {
    const p = precision orelse return format(.{arg(.{ .kind = k, .plus = plus, .space = space }, v)});
    return switch (@as(u4, @intCast(@min(p, 15)))) {
        inline else => |q| format(.{arg(.{ .kind = k, .plus = plus, .space = space, .precision = q }, v)}),
    };
}

/// .NET's `default(T)` of a type that has one here (numbers, chars, bools, strings, options,
/// tuples of them)
pub fn defaultOf(comptime T: type) T {
    if (T == BigInt) return bigOf(@as(i32, 0));
    if (T == NetDecimal) return .{};
    if (comptime isArrayPtr(T)) return arrayNull(T);
    return switch (@typeInfo(T)) {
        .@"struct" => |st| blk: {
            var x: T = undefined;
            inline for (st.field_names) |name| @field(x, name) = defaultOf(@FieldType(T, name));
            break :blk x;
        },
        else => std.mem.zeroes(T),
    };
}

// ---- .NET's null of types that have none here (`Array.zeroCreate`, `Unchecked.defaultof`) ----
//
// A reference record (or another counted cell) gets a null cell of its type: one cell whose count
// starts at `null_count`, so it is never unique (never changed in place by reuse) and never freed,
// and which `isCellNull` tells from any real cell by its count alone (on any thread). Its fields
// hold their own types' nulls. A union, which is a value here, gets its first case with null
// fields (a list: the empty list); a function, one that raises NullReferenceException when
// applied. Known differences from .NET: reading a field of a null record gives the field's null
// instead of raising, and a union's or a list's null is not null to `isNull (box x)`.

/// Does the type have a null (or the nearest value of it) here?
pub fn hasNull(comptime T: type) bool {
    return comptime hasNullDepth(T, 8);
}

fn hasNullDepth(comptime T: type, comptime depth: u8) bool {
    if (depth == 0) return true;
    if (T == String or T == Any or T == BigInt or T == NetDecimal) return true;
    if (isArrayPtr(T)) return true;
    if (isFunc(T)) return @typeInfo(@typeInfo(@FieldType(T, "code")).pointer.child).@"fn".param_types.len <= 4;
    if (isIface(T)) return false;
    if (isCellPtr(T)) {
        const C = @typeInfo(T).pointer.child;
        // (.NET's mutable collections, StringBuilder and Random: a null cell, empty, which a
        // member call checks for, see checkCellNonNull)
        if (@hasDecl(C, "fable_null_cell")) return true;
        if (@hasDecl(C, "fable_identity") or @hasDecl(C, "fable_object")) return false;
        const st = @typeInfo(C).@"struct";
        for (st.field_names, st.field_types) |name, F| {
            if (std.mem.eql(u8, name, "$rc") or std.mem.eql(u8, name, "$gc")) continue;
            if (!hasNullDepth(F, depth - 1)) return false;
        }
        return true;
    }
    return switch (@typeInfo(T)) {
        .int, .float, .bool, .void, .optional, .@"enum" => true,
        .@"struct" => |st| blk: {
            for (st.field_types) |F| {
                if (!hasNullDepth(F, depth - 1)) break :blk false;
            }
            break :blk true;
        },
        .@"union" => |u| u.tag_type != null and hasNullDepth(u.field_types[0], depth - 1),
        else => false,
    };
}

/// .NET's null of a type (a reference of its own); see `hasNull`
pub fn nullOf(comptime T: type) T {
    if (T == String or T == Any) return null;
    if (comptime isArrayPtr(T)) return arrayNull(T);
    if (comptime isFunc(T)) return .{ .env = null, .code = nullCode(@FieldType(T, "code")) };
    if (comptime isCellPtr(T)) return dup(CellNull(T).get());
    if (T == BigInt or T == NetDecimal) return defaultOf(T);
    return switch (@typeInfo(T)) {
        .optional => null,
        .@"struct" => |st| blk: {
            var x: T = undefined;
            inline for (st.field_names) |name| @field(x, name) = nullOf(@FieldType(T, name));
            break :blk x;
        },
        .@"union" => |u| blk: {
            const F = u.field_types[0];
            break :blk @unionInit(T, u.field_names[0], if (F == void) {} else nullOf(F));
        },
        else => std.mem.zeroes(T),
    };
}

/// Is a counted cell the null cell of its type?
pub inline fn isCellNull(c: anytype) bool {
    return @atomicLoad(u32, &c.@"$rc", .monotonic) & immortal_bit != 0;
}

/// Is a value of a type with no null of its own .NET's null (`nullOf` made it)?
pub fn isNullOf(x: anytype) bool {
    const T = @TypeOf(x);
    if (comptime isArrayPtr(T)) return arrayIsNull(x);
    if (comptime isCellPtr(T)) return isCellNull(x);
    if (comptime isFunc(T)) return x.env == null and x.code == nullCode(@FieldType(T, "code"));
    return false;
}

fn CellNull(comptime P: type) type {
    const C = @typeInfo(P).pointer.child;
    return if (hasGc(C)) struct {
        // (the collector follows these: one of the thread's own, made as any other cell and
        // given up with the thread's null arrays)
        threadlocal var made: ?P = null;

        fn get() P {
            if (made) |c| return c;
            if (comptime hasGc(C)) gcTick();
            const c = allocator.create(C) catch oom();
            if (track) thread.stats.allocs += 1;
            made = c;
            fillNullCell(P, c, false);
            c.@"$gc" = gcHeader(C, c);
            thread.null_arrays.append(bookkeeping(), .{ .cell = c, .free = freeNull }) catch oom();
            uncount();
            return c;
        }

        fn freeNull(p: *anyopaque) void {
            const c: P = @ptrCast(@alignCast(p));
            // (shared with another thread, which may outlive this one: left as it is, one empty
            // cell per type and thread, never counted)
            if (isShared(c)) {
                made = null;
                return;
            }
            c.@"$rc" = (c.@"$rc" & weak_bit) | 1;
            recount();
            drop(c);
            made = null;
        }
    } else struct {
        var null_cell: C = undefined;
        var ready = std.atomic.Value(u8).init(0);
        threadlocal var filling = false;

        fn get() P {
            if (ready.load(.acquire) == 2 or filling) return &null_cell;
            if (ready.cmpxchgStrong(0, 1, .acquire, .monotonic) == null) {
                filling = true;
                fillNullCell(P, &null_cell, true);
                filling = false;
                ready.store(2, .release);
            } else {
                while (ready.load(.acquire) != 2) std.atomic.spinLoopHint();
            }
            return &null_cell;
        }
    };
}

/// (the null cell's fields: their own types' nulls; the count first, so that a field of the
/// cell's own type, which reads the cell back, sees it as a null cell)
fn fillNullCell(comptime P: type, c: P, comptime is_static: bool) void {
    const C = @typeInfo(P).pointer.child;
    const init_rc: u32 = if (is_static) immortal_bit | shared_bit else immortal_bit;
    if (comptime @hasDecl(C, "fable_null_cell")) {
        // (its fields' own defaults: an empty collection, never changed, as members check)
        const gc = if (comptime @hasField(C, "$gc")) c.@"$gc" else {};
        c.* = .{};
        if (comptime @hasField(C, "$gc")) c.@"$gc" = gc;
        c.@"$rc" = init_rc;
        return;
    }
    c.@"$rc" = init_rc;
    const st = @typeInfo(C).@"struct";
    inline for (st.field_names, st.field_types) |name, F| {
        if (comptime !std.mem.eql(u8, name, "$rc") and !std.mem.eql(u8, name, "$gc")) {
            @field(c, name) = nullOf(F);
        }
    }
}

/// The code of a null function: raises NullReferenceException (or stops the program, where
/// the function's type cannot raise)
fn nullCode(comptime Code: type) Code {
    const F = @typeInfo(@typeInfo(Code).pointer.child).@"fn";
    const R = F.return_type.?;
    const p = F.param_types;
    return switch (p.len) {
        1 => &struct {
            fn f(_: p[0].?) R {
                return nullCall(R);
            }
        }.f,
        2 => &struct {
            fn f(_: p[0].?, _: p[1].?) R {
                return nullCall(R);
            }
        }.f,
        3 => &struct {
            fn f(_: p[0].?, _: p[1].?, _: p[2].?) R {
                return nullCall(R);
            }
        }.f,
        4 => &struct {
            fn f(_: p[0].?, _: p[1].?, _: p[2].?, _: p[3].?) R {
                return nullCall(R);
            }
        }.f,
        else => @compileError("nullCode: a function of more than three arguments"),
    };
}

fn nullCall(comptime R: type) R {
    if (comptime isRaised(R)) return nullRef();
    @panic("Object reference not set to an instance of an object.");
}

/// What a `Find` gives: the item found, or `default(T)`
pub fn orDefault(comptime T: type, found: ?T) T {
    // (it borrows `found`: the value given is a reference of its own)
    return if (found) |v| dup(v) else defaultOf(T);
}

/// `Enum.TryParse<E>(s)`: by a name of the enum's, a number, or names and numbers joined by
/// commas (their bitwise or), as .NET reads them. `R` is the pair it gives.
pub fn enumTryParse(comptime R: type, comptime T: type, s: String, comptime names: []const []const u8, comptime values: []const T) R {
    const text = trimmed(s);
    if (text.len == 0) return .{ false, 0 };
    var result: T = 0;
    var rest = text;
    while (true) {
        const end = std.mem.indexOfScalar(u16, rest, ',') orelse rest.len;
        var part = rest[0..end];
        while (part.len != 0 and unicode.isWhiteSpace(part[0])) part = part[1..];
        while (part.len != 0 and unicode.isWhiteSpace(part[part.len - 1])) part = part[0 .. part.len - 1];
        if (part.len == 0) return .{ false, 0 };
        const one: T = blk: {
            inline for (names, values) |name, value| {
                if (part.len == name.len) {
                    var same = true;
                    for (part, name) |c, d| {
                        if (c != d) same = false;
                    }
                    if (same) break :blk value;
                }
            }
            // (a number: of the enum's type, whether it names a case or not)
            break :blk parseWhole(T, part, .dotnet) catch return .{ false, 0 };
        };
        result |= one;
        if (end == rest.len) break;
        rest = rest[end + 1 ..];
    }
    return .{ true, result };
}

/// `n.Value` of a `Nullable<T>` (an option here)
pub fn nullableValue(n: anytype) Raised!@typeInfo(@TypeOf(n)).optional.child {
    const v = n orelse return raise(InvalidOperationException, str("Nullable object must have a value."));
    return dup(v);
}

/// `Option.toObj o` (of a type that has null here: a string, `obj`)
pub fn optToObj(o: anytype) @typeInfo(@TypeOf(o)).optional.child {
    return if (o) |v| dup(v) else null;
}

/// `Option.ofObj x`
pub fn optOfObj(x: anytype) ?@TypeOf(x) {
    return if (x == null) null else dup(x);
}

pub fn objEql(a: Obj, b: Obj) bool {
    const ua = if (a.type.unwrap_obj) |f| (f(a) orelse a) else a;
    const ub = if (b.type.unwrap_obj) |f| (f(b) orelse b) else b;
    if (ua == ub) return true;
    if (ua.type.equals) |f| return f(ua, ub);
    return false;
}

/// `obj.ReferenceEquals(a, b)` and `LanguagePrimitives.PhysicalEquality`: the same cell. (A
/// value that is not a cell is boxed anew on .NET: never the same object.)
pub fn refEql(a: anytype, b: @TypeOf(a)) bool {
    const T = @TypeOf(a);
    if (comptime @typeInfo(T) == .optional and isIface(@typeInfo(T).optional.child)) {
        if (a == null or b == null) return a == null and b == null;
        return refEql(a.?, b.?);
    }
    if (comptime isIface(T)) {
        const oa = ifaceToObjBorrow(a);
        const ob = ifaceToObjBorrow(b);
        if (oa != null or ob != null) return oa != null and oa == ob;
        return (a.data != null and a.data == b.data) or (a.data == null and b.data == null and a.vt == b.vt);
    }
    if (comptime T == Any) {
        const pa = a orelse return b == null;
        const pb = b orelse return false;
        return refEql(pa, pb);
    }
    if (comptime T == Obj) {
        if (a == b) return true;
        const id_a: ?*anyopaque = if (a.type.iface_id) |f| f(a) else @ptrCast(a);
        const id_b: ?*anyopaque = if (b.type.iface_id) |f| f(b) else @ptrCast(b);
        return id_a != null and id_a == id_b;
    }
    if (comptime T == String or T == Exn or isCellPtr(T)) return a == b;
    if (comptime @typeInfo(T) == .@"union" and @hasDecl(T, "fable_cyclic")) return std.meta.eql(a, b);
    return false;
}

// ---------------------------------------------------------------------------------------------
// The `Equals`, `GetHashCode` and `CompareTo` a type declares, called by `=`, `hash` and
// `compare`: `pub const fable_equals = fable_rt.Hook(file, "name");` in the type
// ---------------------------------------------------------------------------------------------

pub fn Unraised(comptime R: type) type {
    return switch (@typeInfo(R)) {
        .error_union => |e| e.payload,
        else => R,
    };
}

pub fn Hook(comptime M: type, comptime name: []const u8) type {
    return struct {
        const f = @field(M, name);
        const F = @TypeOf(f);
        const Args = std.meta.ArgsTuple(F);
        const params = @typeInfo(Args).@"struct".field_names;
        const sig = if (@hasDecl(M, name ++ "$sig")) @field(M, name ++ "$sig") else .{ .borrows = @as([params.len]bool, @splat(true)), .result_borrowed = false };
        const R = Unraised(@typeInfo(F).@"fn".return_type.?);

        /// `f(this, ...)`: the first is lent, the others given
        pub fn call(args: anytype) R {
            var a: Args = undefined;
            comptime var uses: [params.len]Use = undefined;
            inline for (0..params.len) |i| {
                if (i < args.len) {
                    // (a struct's `this` is lent as a pointer)
                    const P = @TypeOf(a[i]);
                    a[i] = if (comptime @typeInfo(P) == .pointer and @TypeOf(args[i]) == @typeInfo(P).pointer.child) &args[i] else args[i];
                    uses[i] = if (i == 0) .keep else .give;
                } else {
                    a[i] = {};
                    uses[i] = .plain;
                }
            }
            const raw = across(f, sig, uses, a);
            const r = if (comptime isRaised(@TypeOf(raw))) raw catch @panic("fable: " ++ name ++ " raised an exception, which `=`, `hash` and `compare` cannot pass on here") else raw;
            return r;
        }

        // (as the hooks of a class's type: the object is the first argument)
        pub fn objEquals(a: Obj, b: Obj) bool {
            return call(.{ a, @as(Any, dup(b)) });
        }
        pub fn objHash(a: Obj) i32 {
            return call(.{a});
        }
        pub fn objCompare(a: Obj, b: Obj) i32 {
            return call(.{ a, @as(Any, dup(b)) });
        }
    };
}

pub fn hookOf(comptime T: type, comptime decl: []const u8) bool {
    const C = if (@typeInfo(T) == .pointer and @typeInfo(T).pointer.size == .one) @typeInfo(T).pointer.child else T;
    return switch (@typeInfo(C)) {
        .@"struct", .@"union", .@"enum", .@"opaque" => @hasDecl(C, decl),
        else => false,
    };
}

pub fn hookType(comptime T: type) type {
    return if (@typeInfo(T) == .pointer and @typeInfo(T).pointer.size == .one) @typeInfo(T).pointer.child else T;
}

/// A new object of class `ty` with these fields (which it shares).
pub fn objNew(ty: *const ObjType, chain: anytype) Obj {
    return ObjCell(@TypeOf(chain)).new(ty, dup(chain));
}

/// An empty object of class `ty` whose fields are filled by its constructor (`objInitField`).
pub fn objAlloc(comptime Chain: type, ty: *const ObjType) Obj {
    return ObjCell(Chain).alloc(ty);
}

/// Set a field of an object during construction: initializes it safely if not yet set, or replaces
/// the previous value (`objStore`) if set before.
pub inline fn objInitField(
    comptime P: type,
    comptime parts: []const type,
    comptime field_idx: usize,
    o: Obj,
    value: @FieldType(P, @typeInfo(P).@"struct".field_names[field_idx]),
) void {
    const p = objPart(*P, parts, o);
    const place = &@field(p, @typeInfo(P).@"struct".field_names[field_idx]);
    const bit_idx = o.type.part_field_bases[parts.len - 1] + field_idx;
    const bytes: [*]u8 = @ptrFromInt(@intFromPtr(o) + o.type.init_offset);
    const byte_idx = bit_idx >> 3;
    const mask: u8 = @as(u8, 1) << @intCast(bit_idx & 7);
    if ((bytes[byte_idx] & mask) != 0) {
        if (comptime isManaged(@TypeOf(value))) {
            objStore(o, place, value);
        } else {
            place.* = value;
        }
    } else {
        place.* = value;
        bytes[byte_idx] |= mask;
        if (comptime isManaged(@TypeOf(value))) {
            if (isShared(o)) {
                shareStored(value);
            } else if (o.gc) |h| {
                storeValue(h, value);
            } else {
                touch(value);
            }
        }
    }
}

/// The fields that the last class of `parts` (a class and the classes above it, the root
/// first) declares, in an object of that class or of one that derives from it.
pub inline fn objPart(comptime P: type, comptime parts: []const type, o: Obj) P {
    return @ptrFromInt(@intFromPtr(o) + comptime partOffset(parts, parts.len - 1));
}

/// `string o`: its class's `ToString`, or .NET's name of its class.
pub fn objText(x: anytype) Raised!String {
    // (`x.ToString()` of a null object: NullReferenceException)
    const o: Obj = if (comptime @typeInfo(@TypeOf(x)) == .optional) (x orelse return nullRef()) else x;
    if (o.type.to_string) |f| return f(null, o, {});
    var b: TextBuilder = .{};
    b.addAscii(o.type.name);
    return b.finish();
}

/// The table of the virtual members that the class at `depth` introduces.
pub inline fn objVt(comptime P: type, o: Obj, comptime depth: usize) P {
    return @ptrCast(@alignCast(o.type.vtables[depth].?));
}

/// `o :? C`: is the object of class `ty`, or of a class that derives from it?
pub fn objIs(o: Any, ty: *const ObjType) bool {
    // (null is of no type)
    const p0 = o orelse return false;
    const p = if (p0.type.unwrap_obj) |f| (f(p0) orelse return false) else p0;
    var t: ?*const ObjType = p.type;
    while (t) |class| : (t = class.parent) {
        if (class == ty) return true;
    }
    return false;
}

/// `o :?> C`: null stays null, as on .NET
pub fn objCast(any: Any, ty: *const ObjType) Raised!Any {
    const o0 = any orelse return null;
    const o = if (o0.type.unwrap_obj) |f| (f(o0) orelse o0) else o0;
    if (objIs(o, ty)) return dup(o);
    // (.NET names a class nested in a module without the module here)
    const Short = struct {
        pub fn of(name: []const u8) []const u8 {
            return if (std.mem.lastIndexOfScalar(u8, name, '+')) |i| name[i + 1 ..] else name;
        }
    };
    var b: TextBuilder = .{};
    b.addAscii("Unable to cast object of type '");
    b.addAscii(Short.of(o.type.name));
    b.addAscii("' to type '");
    b.addAscii(Short.of(ty.name));
    b.addAscii("'.");
    return raise(InvalidCastException, b.finish());
}

/// Store into a field of an object: the collector is told, as for a field of a reference
/// record.
pub inline fn objStore(o: Obj, place: anytype, value: @TypeOf(place.*)) void {
    if (isShared(o)) {
        shareStored(value);
        const l = fieldLock(o);
        lockField(l);
        const prev = place.*;
        place.* = value;
        unlockField(l);
        drop(prev);
        return;
    }
    const old = place.*;
    place.* = value;
    if (o.gc) |h| {
        eachHdr(old, h, unstored);
        storeValue(h, value);
    } else {
        touch(value);
    }
    drop(old);
}

pub const array2d = @import("fable_array2d.zig");
pub const RowOf = array2d.RowOf;
pub const array2DBlit = array2d.array2DBlit;
pub const array2DCopy = array2d.array2DCopy;
pub const array2DCreate = array2d.array2DCreate;
pub const array2DGet = array2d.array2DGet;
pub const array2DInit = array2d.array2DInit;
pub const array2DIter = array2d.array2DIter;
pub const array2DIteri = array2d.array2DIteri;
pub const array2DLength = array2d.array2DLength;
pub const array2DMap = array2d.array2DMap;
pub const array2DMapi = array2d.array2DMapi;
pub const array2DOfRows = array2d.array2DOfRows;
pub const array2DSet = array2d.array2DSet;
pub const array2DSlice = array2d.array2DSlice;
pub const array2DZero = array2d.array2DZero;
pub const arrayGetLength = array2d.arrayGetLength;
pub const at2D = array2d.at2D;
pub const blitRange = array2d.blitRange;
pub const dimNegative = array2d.dimNegative;
pub const isListType = array2d.isListType;
pub const rowCount = array2d.rowCount;
pub const rowFill = array2d.rowFill;
pub const shapeOf = array2d.shapeOf;
pub const shaped = array2d.shaped;
test {
    _ = array2d;
}

pub const weak_refs = @import("fable_weak.zig");
pub const Weak = weak_refs.Weak;
pub const WeakHandle = weak_refs.WeakHandle;
pub const weakGone = weak_refs.weakGone;
pub const weakHandle = weak_refs.weakHandle;
pub const weakLetGo = weak_refs.weakLetGo;
pub const weakNew = weak_refs.weakNew;
pub const weakSet = weak_refs.weakSet;
pub const weakTryGet = weak_refs.weakTryGet;
test {
    _ = weak_refs;
}

// ---------------------------------------------------------------------------------------------
// Cycles
//
// Reference counting alone never frees a structure that reaches itself. A structure can only
// do that through a field that is assigned after the cell was made, so most types cannot be
// part of a cycle at all, and their cells are exactly as above. The cells of the types that
// can (the compiler works out which) carry a header of the collector, `$gc`, next to their
// count. The collector (fable_sgc.zig) keeps one count per connected group of such cells: the
// references to its cells that are not held in a field of one of them. When that count
// reaches zero the whole group is dead, cycles included, and is freed.
//
// What the collector has to be told is all in this file: a cell is made, retained, released,
// taken apart, and a field of it is assigned. Generated code does not call the thread.collector.
// ---------------------------------------------------------------------------------------------

/// A test mode: before every allocation of a cell with a collector header, every structure's
/// count is checked against the cells and what they point at. A program turns it on with
/// `pub const fable_verify_cycles = true;` in its root file. Very slow.
const verify_cycles: bool = if (@hasDecl(@import("root"), "fable_verify_cycles")) @import("root").fable_verify_cycles else false;

/// What a file says about the records with assignable fields that its code makes:
/// - `holds`: one of them has an assignable field that can hold a function value or an
///   exception (directly or through other data);
/// - `generic`: one of them is made in generic code, with an assignable field whose type
///   depends on a type parameter;
/// - `instantiated`: a generic function is used with a type argument that can hold a function
///   value or an exception.
/// What a file and the files it uses do, that the runtime adapts to: function values in cycles
/// (see `functions_in_cycles`), and reading an exception's `StackTrace` (see `stack_traces`).
pub const Cycles = struct {
    holds: bool = false,
    generic: bool = false,
    instantiated: bool = false,
    captures: bool = false,
    cap_generic: bool = false,
    cap_instantiated: bool = false,
    stack_traces: bool = false,
    reflection: bool = false,
    exn_show: bool = true,
    /// a handler of the program can catch OutOfMemoryException
    oom_catch: bool = false,
    /// at least one function in the program uses `[<StackArena>]`
    uses_arena: bool = false,
};

/// A file's own answer joined with those of the files it uses.
pub fn joinCycles(comptime own: Cycles, comptime used: anytype) Cycles {
    var r = own;
    inline for (used) |u| {
        r.holds = r.holds or u.holds;
        r.generic = r.generic or u.generic;
        r.instantiated = r.instantiated or u.instantiated;
        if (@hasField(@TypeOf(u), "captures")) r.captures = r.captures or u.captures;
        if (@hasField(@TypeOf(u), "cap_generic")) r.cap_generic = r.cap_generic or u.cap_generic;
        if (@hasField(@TypeOf(u), "cap_instantiated")) r.cap_instantiated = r.cap_instantiated or u.cap_instantiated;
        if (@hasField(@TypeOf(u), "stack_traces")) r.stack_traces = r.stack_traces or u.stack_traces;
        if (@hasField(@TypeOf(u), "reflection")) r.reflection = r.reflection or u.reflection;
        if (@hasField(@TypeOf(u), "exn_show")) r.exn_show = r.exn_show or u.exn_show;
        if (@hasField(@TypeOf(u), "oom_catch")) r.oom_catch = r.oom_catch or u.oom_catch;
        if (@hasField(@TypeOf(u), "uses_arena")) r.uses_arena = r.uses_arena or u.uses_arena;
    }
    return r;
}

/// Can a function value or an exception be part of a cycle in this program? What they hold
/// is not in their type, so a cell that holds one would have to be taken for cycle-capable
/// always. But a cycle needs an assignable field to close it, and one through a function
/// value needs both an assignable field that can hold a function value (or exception / object)
/// and an opaque value whose captures or fields can reach an assignable cell of that kind.
/// The program's root file says in `$cycles`, joined over all the files it uses, whether both
/// exist. If either does not, function values and exceptions cannot form cycles.
pub const functions_in_cycles: bool = blk: {
    if (!@hasDecl(root, "$cycles")) break :blk true;
    const c: Cycles = root.@"$cycles";
    break :blk (c.holds or (c.generic and c.instantiated)) and (c.captures or (c.cap_generic and c.cap_instantiated));
};

/// Does an exception capture the stack where it is thrown? Only when some file of the program
/// reads `StackTrace`: the capture costs each throw, and the frames make each exception larger.
/// (Yes when the root file does not say.)
/// Does a boxed value know its type's reflection information (`GetType()` of an `obj`,
/// Fable.Core.Reflection)? Only when some file of the program reflects on values of unknown
/// type: the information of each boxed type is then part of the program. (Yes when the root
/// file does not say.)
pub const reflection: bool = blk: {
    // (yes when the root file does not say, as under `zig test`)
    if (!@hasDecl(root, "$cycles")) break :blk true;
    const c: Cycles = root.@"$cycles";
    break :blk c.reflection;
};

pub const stack_traces: bool = blk: {
    if (!@hasDecl(root, "$cycles")) break :blk true;
    const c: Cycles = root.@"$cycles";
    break :blk c.stack_traces;
};

/// Does the program ever format an F# exception (`%A` via `exnMessage`, or an unhandled exception
/// escaping `main`/`$init`)? When false, `ExnUnder` leaves `.show = null` so `%A` code is stripped.
pub const exn_show: bool = blk: {
    if (@import("builtin").is_test) break :blk true;
    if (!@hasDecl(root, "$cycles")) break :blk true;
    const c: Cycles = root.@"$cycles";
    if (c.exn_show) break :blk true;
    if (@hasDecl(root, "$init") and isRaised(@TypeOf(root.@"$init"()))) break :blk true;
    if (@hasDecl(root, "$main_raises") and root.@"$main_raises") break :blk true;
    break :blk false;
};

/// `LanguagePrimitives.GenericZero` and `GenericOne` of a type parameter: of the number type
/// Zig instantiates it with.
pub fn genericNumber(comptime T: type, comptime one: bool) T {
    const v: i32 = if (one) 1 else 0;
    if (T == BigInt) return bigOf(v);
    if (T == NetDecimal) return decLit(v, 0);
    return switch (@typeInfo(T)) {
        .int, .float => @as(T, v),
        else => @compileError("fable: GenericZero of " ++ @typeName(T) ++ ", which is no number"),
    };
}

/// The type of a cell's `$gc` field: the collector's header, or nothing.
pub fn GcHdr(comptime cyclic: bool) type {
    return if (cyclic) sgc.Hdr else void;
}

pub fn hasGc(comptime C: type) bool {
    return @hasField(C, "$gc") and @FieldType(C, "$gc") == sgc.Hdr;
}

/// The collector's header of a cell, if it has one. An environment and an exception say so
/// themselves (their type does not show what they hold); for any other cell it is in its type.
pub inline fn gcOf(c: anytype) ?*sgc.Hdr {
    const C = @TypeOf(c.*);
    if (C == Env or C == ExnHeader or C == ObjHeader) return c.gc;
    if (comptime hasGc(C)) return &c.@"$gc";
    return null;
}

/// Does a value of this type hold, directly, a reference to a cell that can be part of a
/// cycle? A function value and an exception count: what they hold is not in their type.
/// (Only declarations are looked at, never fields of cells: this is evaluated while the types
/// that ask are still being put together.)
pub fn holdsCyclic(comptime T: type) bool {
    if (T == Exn or T == Obj) return functions_in_cycles;
    switch (@typeInfo(T)) {
        .pointer => |p| {
            if (p.size == .slice) return holdsCyclic(p.child);
            if (p.size != .one or @typeInfo(p.child) != .@"struct") return false;
            return @hasDecl(p.child, "fable_cyclic") and p.child.fable_cyclic;
        },
        .optional => |o| return holdsCyclic(o.child),
        .@"struct" => |s| {
            if (@hasDecl(T, "fable_known")) return false;
            if (@hasDecl(T, "fable_func")) return functions_in_cycles;
            if (@hasDecl(T, "fable_iface")) return functions_in_cycles;
            inline for (s.field_types) |F| {
                if (holdsCyclic(F)) return true;
            }
            return false;
        },
        .@"union" => |u| {
            if (@hasDecl(T, "fable_cyclic")) return T.fable_cyclic;
            inline for (u.field_types) |F| {
                if (holdsCyclic(F)) return true;
            }
            return false;
        },
        else => return false,
    }
}

/// Call `f(ctx, header)` for every cell with a collector header that `x` refers to directly.
pub fn eachHdr(x: anytype, ctx: anytype, comptime f: anytype) void {
    const T = @TypeOf(x);
    if (comptime !holdsCyclic(T)) return;
    if (T == Exn or T == Obj) {
        if (x.gc) |h| f(ctx, h);
        return;
    }
    if (comptime isFunc(T)) {
        if (x.env) |e| {
            if (e.gc) |h| f(ctx, h);
        }
        return;
    }
    if (comptime isIface(T)) {
        if (x.vt.@"$meta".hdr_of(x.data)) |h| f(ctx, h);
        return;
    }
    if (comptime isSlice(T)) {
        for (x) |item| eachHdr(item, ctx, f);
        return;
    }
    switch (@typeInfo(T)) {
        .pointer => f(ctx, &x.@"$gc"),
        .optional => if (x) |v| eachHdr(v, ctx, f),
        .@"struct" => |s| inline for (s.field_names) |name| eachHdr(@field(x, name), ctx, f),
        .@"union" => switch (x) {
            inline else => |p| {
                if (comptime isCellPtr(@TypeOf(p))) {
                    if (comptime hasGc(@TypeOf(p.*))) f(ctx, &p.@"$gc");
                } else {
                    eachHdr(p, ctx, f);
                }
            },
        },
        else => comptime unreachable,
    }
}

/// Give up what a dead cell holds, except its references to cells that are going away with it.
fn dropOutside(x: anytype) void {
    const T = @TypeOf(x);
    if (comptime !isManaged(T)) return;
    if (comptime !holdsCyclic(T)) return drop(x);
    if (T == Exn or T == Obj) {
        if (x.gc) |h| {
            if (sgc.isGarbage(h)) return;
        }
        return drop(x);
    }
    if (comptime isFunc(T)) {
        if (x.env) |e| {
            if (e.gc) |h| {
                if (sgc.isGarbage(h)) return;
            }
        }
        return drop(x);
    }
    if (comptime isIface(T)) {
        if (x.vt.@"$meta".hdr_of(x.data)) |h| {
            if (sgc.isGarbage(h)) return;
        }
        return drop(x);
    }
    if (comptime isSlice(T)) {
        for (x) |item| dropOutside(item);
        return;
    }
    switch (@typeInfo(T)) {
        .pointer => if (!sgc.isGarbage(&x.@"$gc")) drop(x),
        .optional => if (x) |v| dropOutside(v),
        .@"struct" => |s| inline for (s.field_names) |name| dropOutside(@field(x, name)),
        .@"union" => switch (x) {
            inline else => |p| {
                if (comptime isCellPtr(@TypeOf(p))) {
                    if (comptime hasGc(@TypeOf(p.*))) {
                        if (!sgc.isGarbage(&p.@"$gc")) drop(x);
                    } else {
                        drop(x);
                    }
                } else {
                    dropOutside(p);
                }
            },
        },
        else => comptime unreachable,
    }
}

pub fn visit(v: *sgc.Visitor, h: *sgc.Hdr) void {
    v.visit(h);
}

pub fn countOne(n: *usize, _: *sgc.Hdr) void {
    n.* += 1;
}

/// What the collector needs to know about one type of cell `C`: where its count is, which
/// cells it refers to, and how to give up what it holds and free it. `gc_field` is the
/// collector's header in `C`; `payload` is the field that holds everything else (all fields
/// but the count and the header when it is null).
pub fn Collected(comptime C: type, comptime gc_field: []const u8, comptime rc_offset: isize, comptime payload: ?[]const u8) type {
    return struct {
        pub inline fn cellOf(n: *sgc.Hdr) *C {
            return @alignCast(@fieldParentPtr(gc_field, n));
        }

        pub fn trace(n: *sgc.Hdr, v: *sgc.Visitor) void {
            const c = cellOf(n);
            if (payload) |p| {
                eachHdr(@field(c, p), v, visit);
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) eachHdr(@field(c, name), v, visit);
            }
        }

        pub fn releaseOutside(n: *sgc.Hdr, _: ?*anyopaque) void {
            const c = cellOf(n);
            if (payload) |p| {
                dropOutside(@field(c, p));
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) dropOutside(@field(c, name));
            }
        }

        pub fn freeCell(n: *sgc.Hdr, _: ?*anyopaque) void {
            free(cellOf(n));
        }

        pub fn finalize(n: *sgc.Hdr, _: ?*anyopaque) void {
            const c = cellOf(n);
            if (payload) |p| {
                drop(@field(c, p));
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) drop(@field(c, name));
            }
            free(c);
        }

        /// Is the cell being made without a reference to a cell that can be part of a cycle?
        pub fn isLeaf(c: *const C) bool {
            var n: usize = 0;
            if (payload) |p| {
                eachHdr(@field(c, p), &n, countOne);
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) eachHdr(@field(c, name), &n, countOne);
            }
            return n == 0;
        }

        pub const desc: sgc.Desc = .{
            .rc_offset = rc_offset,
            .trace = trace,
            .release_outside = releaseOutside,
            .free = freeCell,
            .finalize = finalize,
        };
    };
}

pub noinline fn collectorSetup() void {
    thread.collector.init(.{}, null, bookkeeping());
    thread.collector_ready = true;
}

/// Before a cell with a collector header is allocated (its field values are computed by
/// then): the only place where the collector does work of its own accord.
pub inline fn gcTick() void {
    if (!thread.collector_ready) collectorSetup();
    if (verify_cycles) thread.collector.verify();
    if (thread.collector.tickDue()) thread.collector.tickSlow();
}

/// The header of a new cell of a recursive union or of a reference record.
pub inline fn gcHeader(comptime C: type, c: *const C) sgc.Hdr {
    const K = Collected(C, "$gc", @as(isize, @offsetOf(C, "$rc")) - @as(isize, @offsetOf(C, "$gc")), null);
    return thread.collector.hdr(&K.desc, K.isLeaf(c));
}

/// Free every cycle that is dead now. Returns how many cells that freed.
pub fn collect() i32 {
    if (!thread.collector_ready) return 0;
    return @intCast(thread.collector.collectAll());
}

/// At most `budget` cells of collector work. True while more is waiting. The collector only
/// works of its own accord when a cell that can be part of a cycle is allocated; a program
/// that has idle time, and may not allocate for a while, calls this there. With nothing to do
/// it costs two compares.
pub fn collectStep(budget: i32) bool {
    if (!thread.collector_ready or budget <= 0) return false;
    return thread.collector.step(@intCast(budget));
}

/// No collector work until `collectorResume`, for code that must not be delayed. (Counts are
/// kept all the same, and a structure whose last outside reference goes is still freed.)
pub fn collectorPause() void {
    if (!thread.collector_ready) collectorSetup();
    thread.collector.noCollectEnter();
}

pub fn collectorResume() void {
    thread.collector.noCollectLeave();
}

pub const Knob = enum {
    /// 0: checks of live structures are only started by `collect` and `collectStep`
    automatic,
    /// cells of a check per allocation (0 or less: a check runs to its end at once)
    pace,
    /// cells of a dead structure freed per allocation (0 or less: all at once, inside the
    /// release that killed it)
    free_budget,
    /// with a free budget: cells that one drop frees at once before the rest is queued
    free_now,
    /// a structure that lost a reference is checked when it has grown by 1/`check_growth`
    /// (at least `check_min` cells) since, or after max(`check_wait`, `check_factor` times
    /// its cells) allocations
    check_growth,
    check_min,
    check_wait,
    check_factor,
};

/// Tune this thread's collector.
pub fn collectorSet(comptime knob: Knob, value: i32) void {
    if (!thread.collector_ready) collectorSetup();
    var cfg = thread.collector.cfg;
    const limit: usize = if (value <= 0) sgc.unlimited else @intCast(value);
    const count: usize = if (value <= 0) 0 else @intCast(value);
    switch (knob) {
        .automatic => cfg.auto = value != 0,
        .pace => cfg.pace = limit,
        .free_budget => cfg.free_budget = limit,
        .free_now => cfg.free_now = count,
        .check_growth => cfg.check_growth = @max(count, 1),
        .check_min => cfg.check_min = count,
        .check_wait => cfg.check_wait = count,
        .check_factor => cfg.check_factor = count,
    }
    thread.collector.configure(cfg);
}

/// For programs and tests that want to see what the runtime did (0 in builds that do not
/// count): cells allocated, built in again, freed; references added to and taken off cells
/// that stayed shared.
pub fn counted(comptime what: enum { allocs, reuses, frees, shared, destroys, copies }) i32 {
    return @intCast(switch (what) {
        .destroys => thread.stats.destroys,
        .copies => thread.stats.copies,
        .allocs => thread.stats.allocs,
        .reuses => thread.stats.reuses,
        .frees => thread.stats.frees,
        .shared => thread.stats.dups + thread.stats.decs,
    });
}

/// Cells of this thread that are allocated now (0 in builds that do not count).
pub fn liveCells() i32 {
    return @intCast(live());
}

/// Give back the collector's own bookkeeping, and the table of weak references. Nothing they
/// look after may be alive.
/// The state of this thread's async scheduler (Async.fs: its timers and trampoline), made
/// when the thread first runs an async computation: each thread waits on its own timers
pub fn asyncState() Any {
    return dup(thread.async_state);
}

pub fn asyncStateSet(x: Any) void {
    const old = thread.async_state;
    thread.async_state = dup(x);
    drop(old);
}

/// (given up when the thread ends, and before the program counts what it never freed)
pub fn asyncStateRelease() void {
    const old = thread.async_state;
    thread.async_state = null;
    drop(old);
}

pub const ThreadExitSgcStats = struct {
    collected_on_exit: usize = 0,
    remaining_structures_on_exit: usize = 0,
    threads_drained: usize = 0,
};

var ended_threads_sgc_collected: usize = 0;
var ended_threads_sgc_remaining: usize = 0;
var ended_threads_sgc_drained: usize = 0;

/// Cumulative `fable_sgc` drain telemetry from threads that exited through `collectorDeinit()`.
pub fn threadExitSgcStats() ThreadExitSgcStats {
    return .{
        .collected_on_exit = @atomicLoad(usize, &ended_threads_sgc_collected, .monotonic),
        .remaining_structures_on_exit = @atomicLoad(usize, &ended_threads_sgc_remaining, .monotonic),
        .threads_drained = @atomicLoad(usize, &ended_threads_sgc_drained, .monotonic),
    };
}

pub fn collectorDeinit() void {
    asyncStateRelease();
    random.randomSharedRelease();
    // (the null arrays this thread made: given up before the collector goes)
    for (thread.null_arrays.items) |n| n.free(n.cell);
    thread.null_arrays.deinit(bookkeeping());
    thread.null_arrays = .empty;
    if (thread.collector_ready) {
        const freed = thread.collector.collectAll();
        const remaining = thread.collector.n_live;
        if (track) {
            _ = @atomicRmw(usize, &ended_threads_sgc_collected, .Add, freed, .monotonic);
            _ = @atomicRmw(usize, &ended_threads_sgc_remaining, .Add, remaining, .monotonic);
            _ = @atomicRmw(usize, &ended_threads_sgc_drained, .Add, 1, .monotonic);
        }
        thread.collector.deinit();
        thread.collector_ready = false;
    }
    thread.weak.deinit(bookkeeping());
    thread.weak = .empty;
    thread.stamps.deinit(bookkeeping());
    thread.stamps = .empty;
}

/// The collector's counters (see fable_sgc.zig), or null if no cell ever needed it.
pub fn collectorCounters() ?sgc.Counters {
    return if (thread.collector_ready) thread.collector.counters else null;
}

/// How a call that ends a function is made when the caller and the callee have the same
/// parameter and result types: as a jump, where the compiler backend can guarantee one.
pub const tail_call: std.builtin.CallModifier = if (builtin.zig_backend == .stage2_llvm and switch (builtin.cpu.arch) {
    .wasm32, .wasm64 => false,
    else => true,
}) .always_tail else .auto;

/// Maximum packed size and alignment of arguments carried through a uniform `$tc` tail call.
pub const tail_args_cap: usize = 128;
pub const tail_args_align: usize = 16;

/// Buffer passed along a tail-call chain from the chain's boundary frame.
pub const TailCtx = struct {
    self: ?*anyopaque = null,
    self_owned: bool = true,
    reuse_env: ?*anyopaque = null,
    reuse_env_size: usize = 0,
    reuse_env_align: usize = 0,
    args: [tail_args_cap]u8 align(tail_args_align) = undefined,
};

pub const TailStatus = enum(u8) { ok, raised };
pub const TailFn = *const fn (ctx: *TailCtx, ret: *anyopaque) TailStatus;

/// Next hop returned by a full `$tcbody` so its frame defers run before the `musttail` jump.
pub const TailNext = struct {
    func: ?TailFn = null,
    ret: *anyopaque = undefined,
};

fn tailLayout(comptime Params: []const type) struct { offsets: [Params.len]usize, size: usize, align_val: usize } {
    @setEvalBranchQuota(100_000);
    var offsets: [Params.len]usize = undefined;
    var off: usize = 0;
    var max_align: usize = 1;
    for (Params, 0..) |P, i| {
        if (@sizeOf(P) == 0) {
            offsets[i] = 0;
        } else {
            const a = @alignOf(P);
            if (a > max_align) max_align = a;
            off = std.mem.alignForward(usize, off, a);
            offsets[i] = off;
            off += @sizeOf(P);
        }
    }
    return .{ .offsets = offsets, .size = off, .align_val = max_align };
}

pub fn fitsTailArgs(comptime Params: []const type) bool {
    const L = comptime tailLayout(Params);
    return L.size <= tail_args_cap and L.align_val <= tail_args_align;
}

pub fn TailArgs(comptime Params: []const type) type {
    return @Tuple(Params);
}

pub inline fn tailStore(comptime Params: []const type, ctx: *TailCtx, vals: anytype) void {
    const L = comptime tailLayout(Params);
    comptime {
        if (L.size > tail_args_cap or L.align_val > tail_args_align) {
            @compileError("fable: tail call arguments exceed TailCtx buffer");
        }
    }
    inline for (Params, 0..) |P, i| {
        if (comptime @sizeOf(P) != 0) {
            @as(*P, @ptrCast(@alignCast(&ctx.args[L.offsets[i]]))).* = vals[i];
        }
    }
}

fn zeroSizedVal(comptime P: type) P {
    if (P == void) return {};
    return switch (@typeInfo(P)) {
        .@"union" => |u| @unionInit(P, u.field_names[0], zeroSizedVal(u.field_types[0])),
        .@"struct" => |s| blk: {
            var z: P = undefined;
            for (s.field_names, 0..) |fname, i| {
                @field(z, fname) = zeroSizedVal(s.field_types[i]);
            }
            break :blk z;
        },
        .@"enum" => @fromBackingInt(@intCast(0)),
        .array => |a| @splat(zeroSizedVal(a.child)),
        else => undefined,
    };
}

pub inline fn tailLoad(comptime Params: []const type, ctx: *const TailCtx) @Tuple(Params) {
    const L = comptime tailLayout(Params);
    var out: @Tuple(Params) = undefined;
    inline for (Params, 0..) |P, i| {
        if (comptime @sizeOf(P) == 0) {
            out[i] = comptime zeroSizedVal(P);
        } else {
            out[i] = @as(*const P, @ptrCast(@alignCast(&ctx.args[L.offsets[i]]))).*;
        }
    }
    return out;
}

pub inline fn takeSelf(ctx: *TailCtx) ?*anyopaque {
    const s = ctx.self;
    ctx.self = null;
    ctx.self_owned = true;
    return s;
}

pub inline fn takeSelfBorrowed(ctx: *TailCtx) struct { ptr: ?*anyopaque, owned: bool } {
    const s = ctx.self;
    const own = ctx.self_owned;
    ctx.self = null;
    ctx.self_owned = true;
    return .{ .ptr = s, .owned = own };
}

noinline fn enqueueEnvDrop(st: *EnvDropState, e: *Env) void {
    st.queue.append(bookkeeping(), e) catch oom();
}

noinline fn drainEnvQueue(st: *EnvDropState) void {
    while (st.queue.items.len > 0) {
        const idx = st.queue.items.len - 1;
        const next_e = st.queue.items[idx];
        st.queue.items.len = idx;
        var cur: ?*Env = next_e.destroy(next_e);
        while (cur) |e| {
            if (!releaseIsLast(e)) break;
            cur = e.destroy(e);
        }
    }
    st.queue.deinit(bookkeeping());
    st.queue = .empty;
}

noinline fn dropEnvSlow(first: *Env) void {
    const st = &thread.env_drop;
    if (st.depth >= 64) {
        enqueueEnvDrop(st, first);
        return;
    }
    st.depth += 1;
    var cur: ?*Env = first.destroy(first);
    while (cur) |e| {
        if (!releaseIsLast(e)) break;
        cur = e.destroy(e);
    }
    if (st.depth == 1 and st.queue.capacity != 0) drainEnvQueue(st);
    st.depth -= 1;
}

pub inline fn dropEnv(env: ?*Env) void {
    const first = env orelse return;
    if (!releaseIsLast(first)) return;
    dropEnvSlow(first);
}

fn emptyUnionField(comptime T: type) ?[]const u8 {
    const ti = @typeInfo(T);
    if (ti != .@"union") return null;
    const u = ti.@"union";
    if (u.tag_type == null) return null;
    for (u.field_names, u.field_types) |name, F| {
        if (F == void) return name;
    }
    return null;
}

/// Whether `*ret` can be filled with a droppable sentinel on a `$tc` raise.
pub fn canPlugRet(comptime R: type) bool {
    return comptime blk: {
        if (@sizeOf(R) == 0) break :blk false;
        if (emptyUnionField(R) != null) break :blk true;
        break :blk hasNull(R);
    };
}

/// Fill `*ret` with an empty case or `nullOf(R)` when a `$tc` callee raises.
pub fn plugRet(comptime R: type, ret: *anyopaque) void {
    if (comptime @sizeOf(R) == 0) return;
    const p: *R = @ptrCast(@alignCast(ret));
    if (comptime emptyUnionField(R)) |name| {
        p.* = @unionInit(R, name, {});
    } else if (comptime hasNull(R)) {
        p.* = nullOf(R);
    }
}

/// Where `printf` and `eprintf` send their text, as UTF-8. A program may replace them (a
/// freestanding one has to: there they do nothing).
pub var write_out: *const fn (bytes: []const u8) void = defaultOut;
pub var write_err: *const fn (bytes: []const u8) void = defaultErr;

// ---------------------------------------------------------------------------------------------
// (moved to fable_string.zig)
const fable_string = @import("fable_string.zig");
pub const Str = fable_string.Str;
pub const String = fable_string.String;
pub const unitsOf = fable_string.unitsOf;
pub const LiteralCell = fable_string.LiteralCell;
pub const str = fable_string.str;
pub const strOf = fable_string.strOf;
pub const strWords = fable_string.strWords;
pub const strNew = fable_string.strNew;
pub const strFrom = fable_string.strFrom;
pub const strRetain = fable_string.strRetain;
pub const strRelease = fable_string.strRelease;
pub const TextBuilder = fable_string.TextBuilder;
pub const TextEncoding = fable_string.TextEncoding;
pub const encodingGetBytes = fable_string.encodingGetBytes;
pub const encodingGetBytesRange = fable_string.encodingGetBytesRange;
pub const encodingGetString = fable_string.encodingGetString;
pub const encodingGetStringRange = fable_string.encodingGetStringRange;
pub const encodingGetByteCount = fable_string.encodingGetByteCount;
pub const strEql = fable_string.strEql;
pub const strCompare = fable_string.strCompare;
pub const compare = fable_string.compare;
pub const compareOf = fable_string.compareOf;
pub const maxOf = fable_string.maxOf;
pub const mathMax = fable_string.mathMax;
pub const mathMin = fable_string.mathMin;
pub const minOf = fable_string.minOf;
pub const hash = fable_string.hash;
pub const hashWith = fable_string.hashWith;
pub const nullRef = fable_string.nullRef;
pub const argNull = fable_string.argNull;
pub const isNullValue = fable_string.isNullValue;
pub const isArrayPtr = fable_string.isArrayPtr;
pub const nonNullValue = fable_string.nonNullValue;
pub const nullArgCheck = fable_string.nullArgCheck;
pub const nonNullUnwrap = fable_string.nonNullUnwrap;
pub const nullArgCheckUnwrap = fable_string.nullArgCheckUnwrap;
pub const argRange = fable_string.argRange;
pub const exnWithParam = fable_string.exnWithParam;
pub const exnParamName = fable_string.exnParamName;
pub const argNegative = fable_string.argNegative;
pub const argAbove = fable_string.argAbove;
pub const index_range = fable_string.index_range;
pub const strLen = fable_string.strLen;
pub const strLength = fable_string.strLength;
pub const strAt = fable_string.strAt;
pub const strConcat = fable_string.strConcat;
pub const strAppend = fable_string.strAppend;
pub const strEquals = fable_string.strEquals;
pub const strIsNullOrEmpty = fable_string.strIsNullOrEmpty;
pub const strIsNullOrWhiteSpace = fable_string.strIsNullOrWhiteSpace;
pub const strSlice = fable_string.strSlice;
pub const strSubstring = fable_string.strSubstring;
pub const strIndexOfChar = fable_string.strIndexOfChar;
pub const strIndexOf = fable_string.strIndexOf;
pub const strIndexOfCmp = fable_string.strIndexOfCmp;
pub const strLastIndexOfCmp = fable_string.strLastIndexOfCmp;
pub const strLastIndexOfChar = fable_string.strLastIndexOfChar;
pub const strLastIndexOf = fable_string.strLastIndexOf;
pub const strContains = fable_string.strContains;
pub const strContainsChar = fable_string.strContainsChar;
pub const strStartsWith = fable_string.strStartsWith;
pub const strEndsWith = fable_string.strEndsWith;
pub const strStartsWithChar = fable_string.strStartsWithChar;
pub const strEndsWithChar = fable_string.strEndsWithChar;
pub const strCase = fable_string.strCase;
pub const strTrim = fable_string.strTrim;
pub const strReplace = fable_string.strReplace;
pub const strReplaceChar = fable_string.strReplaceChar;
pub const strInsert = fable_string.strInsert;
pub const strRemove = fable_string.strRemove;
pub const strPad = fable_string.strPad;
pub const strOfChar = fable_string.strOfChar;
pub const countNegative = fable_string.countNegative;
pub const apply3 = fable_string.apply3;
pub const apply2 = fable_string.apply2;
pub const strReplicate = fable_string.strReplicate;
pub const strJoin = fable_string.strJoin;
pub const strInit = fable_string.strInit;
pub const strMap = fable_string.strMap;
pub const strMapi = fable_string.strMapi;
pub const strIter = fable_string.strIter;
pub const strIteri = fable_string.strIteri;
pub const strForall = fable_string.strForall;
pub const strExists = fable_string.strExists;
pub const strFilter = fable_string.strFilter;
pub const strCollect = fable_string.strCollect;
pub const ShowNode = fable_string.ShowNode;
pub const TypeShape = fable_string.TypeShape;
pub const Spec = fable_string.Spec;
pub const Arg = fable_string.Arg;
pub const arg = fable_string.arg;
pub const scratch_len = fable_string.scratch_len;
pub const Decimal = fable_string.Decimal;
pub const Text = fable_string.Text;
pub const floatText = fable_string.floatText;
pub const pieceOf = fable_string.pieceOf;
pub const isLiteralText = fable_string.isLiteralText;
pub const format = fable_string.format;
pub const posixWrite = fable_string.posixWrite;
pub const defaultOut = fable_string.defaultOut;
pub const defaultErr = fable_string.defaultErr;
pub const writeText = fable_string.writeText;
pub const print = fable_string.print;
pub const printErr = fable_string.printErr;
// ---------------------------------------------------------------------------------------------
// (moved to fable_netformat.zig)
const fable_netformat = @import("fable_netformat.zig");
pub const fraction = fable_netformat.fraction;
pub const isStandardFormat = fable_netformat.isStandardFormat;
pub const netText = fable_netformat.netText;
// ---------------------------------------------------------------------------------------------
// (moved to fable_show.zig)
pub const fable_show = @import("fable_show.zig");
pub const Layout = fable_show.Layout;
pub const Prec = fable_show.Prec;
pub const Shower = fable_show.Shower;
pub const writeObj = fable_show.writeObj;
pub const anyText = fable_show.anyText;
pub const anyTextShape = fable_show.anyTextShape;
const anyTextAt = fable_show.anyTextAt;
// ---------------------------------------------------------------------------------------------
// .NET's ToString of a value: what `string x`, `{x}`, `Append x` and `String.Join` give
// ---------------------------------------------------------------------------------------------

/// Write `x` as .NET's ToString writes it: a string as it is, a number as `string` writes it,
/// `Some(1)`, `(1, a)`, `[1; 2; 3; ... ]` (three items), `map [(1, a)]`; a record or a union as
/// `%A`; None (null on .NET) as nothing.
pub fn writeNet(out: *TextBuilder, x: anytype) void {
    writeNetShape(out, x, .{}, ShowNode.auto);
}

fn writeNetShape(out: *TextBuilder, x: anytype, comptime shape: TypeShape, node_idx: u16) void {
    const T = @TypeOf(x);
    if (T == String) return out.add(unitsOf(x));
    if (T == reflect.Type) return out.addAscii(x.full_name);
    // (an object: what it holds, as .NET writes it; null: nothing)
    if (T == Any) {
        if (x) |o| return writeNetShape(out, o, shape, node_idx);
        return;
    }
    if (comptime isBigInt(T)) {
        const d = bigDigits(x);
        defer alloc().free(d);
        return out.addAscii(d);
    }
    if (comptime isDecimal(T)) {
        var buf: [40]u8 = undefined;
        return out.addAscii(decAscii(x, &buf));
    }
    const node: ShowNode = if (node_idx < shape.nodes.len) shape.nodes[node_idx] else .{};
    if (T == u16) {
        if (node.kind == .u16_num) {
            var scratch: [scratch_len]u8 align(2) = undefined;
            return out.addAscii(pieceOf(.{}, x, &scratch).ascii);
        }
        return out.addOne(x);
    }
    if (T == Obj) return writeObj(out, x);
    if (comptime isIface(T)) {
        if (ifaceToObjBorrow(x)) |o| return writeObj(out, o);
        return out.addAscii("<iface>");
    }
    // (`Append(chars)`: the chars; `Append(builder)`: what it holds)
    if (comptime T == Array(u16)) return out.add(x.items);
    if (comptime T == StringBuilder) return out.add(x.units.items);
    if (T == Exn) {
        const m = exnMessage(x);
        defer drop(m);
        out.addAscii(x.type.name);
        out.addAscii(": ");
        return out.add(unitsOf(m));
    }
    switch (@typeInfo(T)) {
        .void => {},
        .int, .float, .bool => {
            var scratch: [scratch_len]u8 align(2) = undefined;
            out.addAscii(pieceOf(.{}, x, &scratch).ascii);
        },
        .optional => {
            const is_vopt = node.kind == .vopt;
            const child: u16 = if (is_vopt or node.kind == .opt) node.a else ShowNode.auto;
            if (x) |v| {
                if (is_vopt) {
                    writeNetShape(out, v, shape, child);
                } else {
                    out.addAscii("Some(");
                    writeNetShape(out, v, shape, child);
                    out.addOne(')');
                }
            } else if (is_vopt) {
                out.addAscii("ValueNone");
            }
        },
        .@"struct" => |st| {
            if (st.is_tuple) {
                const field_refs: []const u16 = if (node.kind == .struct_tuple or node.kind == .tuple) shape.refs[node.a..][0..node.b] else &.{};
                out.addOne('(');
                inline for (st.field_names, 0..) |name, i| {
                    if (i != 0) out.addAscii(", ");
                    const child_idx = if (i < field_refs.len) field_refs[i] else ShowNode.auto;
                    writeNetShape(out, @field(x, name), shape, child_idx);
                }
                out.addOne(')');
            } else {
                const text = anyTextAt(shape, node_idx, x);
                defer drop(text);
                out.add(unitsOf(text));
            }
        },
        .@"union" => {
            if (comptime @hasDecl(T, "fable_list")) {
                const child: u16 = if (node.kind == .seq) node.a else ShowNode.auto;
                out.addOne('[');
                var rest = x;
                var n: usize = 0;
                while (rest == .Cons) : (rest = rest.Cons.Tail) {
                    if (n == 3) {
                        out.addAscii("; ... ");
                        break;
                    }
                    if (n != 0) out.addAscii("; ");
                    writeNetShape(out, rest.Cons.Head, shape, child);
                    n += 1;
                }
                out.addOne(']');
                return;
            }
            if (comptime isCollection(T)) {
                const k_idx: u16 = if (node.kind == .map or node.kind == .seq) node.a else ShowNode.auto;
                const v_idx: u16 = if (node.kind == .map) node.b else ShowNode.auto;
                out.addAscii(if (T.fable_collection == .map) "map [" else "set [");
                var w = TreeWalk(T).init(x);
                var n: usize = 0;
                while (w.next()) |node_kv| {
                    if (n == 3) {
                        out.addAscii("; ... ");
                        break;
                    }
                    if (n != 0) out.addAscii("; ");
                    if (comptime T.fable_collection == .map) {
                        out.addOne('(');
                        writeNetShape(out, node_kv.key, shape, k_idx);
                        out.addAscii(", ");
                        writeNetShape(out, node_kv.value, shape, v_idx);
                        out.addOne(')');
                    } else writeNetShape(out, node_kv.key, shape, k_idx);
                    n += 1;
                }
                out.addOne(']');
                return;
            }
            const text = anyTextAt(shape, node_idx, x);
            defer drop(text);
            out.add(unitsOf(text));
        },
        else => {
            const text = anyTextAt(shape, node_idx, x);
            defer drop(text);
            out.add(unitsOf(text));
        },
    }
}

/// `string x` and `x.ToString()` of an option, a tuple, a list, a map, a set.
pub fn toText(x: anytype) String {
    return toTextShape(.{}, x);
}

pub fn toTextShape(comptime shape: TypeShape, x: anytype) String {
    var out: TextBuilder = .{};
    const start: u16 = if (shape.nodes.len != 0) 0 else ShowNode.auto;
    writeNetShape(&out, x, shape, start);
    return out.finish();
}

/// `String.Join(sep, items)` and `String.concat sep items`, of a list of any items.
pub fn joinList(sep: String, items: anytype) String {
    var out: TextBuilder = .{};
    var rest = items;
    var first = true;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        if (!first) out.add(unitsOf(sep));
        first = false;
        writeNet(&out, rest.Cons.Head);
    }
    return out.finish();
}

// ---------------------------------------------------------------------------------------------
// StringBuilder
// ---------------------------------------------------------------------------------------------

pub const random = @import("fable_random.zig");
pub const Random = random.Random;
pub const StringBuilder = random.StringBuilder;
pub const randomNew = random.randomNew;
pub const randomNext = random.randomNext;
pub const randomNextBytes = random.randomNextBytes;
pub const randomNextDouble = random.randomNextDouble;
pub const randomNextMax = random.randomNextMax;
pub const randomNextRange = random.randomNextRange;
pub const randomShared = random.randomShared;
pub const randomUnseeded = random.randomUnseeded;
pub const sbAppend = random.sbAppend;
pub const sbAppendLine = random.sbAppendLine;
pub const sbClear = random.sbClear;
pub const sbLength = random.sbLength;
pub const sbNew = random.sbNew;
pub const sbToString = random.sbToString;
test {
    _ = random;
}

pub const text_split = @import("fable_split.zig");
pub const charCategory = text_split.charCategory;
pub const charNumericValue = text_split.charNumericValue;
pub const foldUnits = text_split.foldUnits;
pub const isUnreserved = text_split.isUnreserved;
pub const newLine = text_split.newLine;
pub const pathFileName = text_split.pathFileName;
pub const sbAppendRepeat = text_split.sbAppendRepeat;
pub const sbCharAt = text_split.sbCharAt;
pub const sbReplace = text_split.sbReplace;
pub const sbReplaceChar = text_split.sbReplaceChar;
pub const sbSetChar = text_split.sbSetChar;
pub const sbRemove = text_split.sbRemove;
pub const sbSetLength = text_split.sbSetLength;
pub const sbToStringRange = text_split.sbToStringRange;
pub const splitDone = text_split.splitDone;
pub const splitPush = text_split.splitPush;
pub const strCharCategory = text_split.strCharCategory;
pub const strCharIs = text_split.strCharIs;
pub const strCompareCulture = text_split.strCompareCulture;
pub const strCompareCultureRange = text_split.strCompareCultureRange;
pub const strCompareIgnoreCase = text_split.strCompareIgnoreCase;
pub const strCompareRange = text_split.strCompareRange;
pub const strCompareRangeWith = text_split.strCompareRangeWith;
pub const strCompareTo = text_split.strCompareTo;
pub const strCompareWith = text_split.strCompareWith;
pub const strEndsWithIgnoreCase = text_split.strEndsWithIgnoreCase;
pub const strEndsWithOpt = text_split.strEndsWithOpt;
pub const strEqualsIgnoreCase = text_split.strEqualsIgnoreCase;
pub const strIndexOfAny = text_split.strIndexOfAny;
pub const strIndexOfCharIgnoreCase = text_split.strIndexOfCharIgnoreCase;
pub const strIndexOfIgnoreCase = text_split.strIndexOfIgnoreCase;
pub const strJoinRange = text_split.strJoinRange;
pub const strLastIndexOfCharFrom = text_split.strLastIndexOfCharFrom;
pub const strLastIndexOfFrom = text_split.strLastIndexOfFrom;
pub const strOfChars = text_split.strOfChars;
pub const strOfCharsRange = text_split.strOfCharsRange;
pub const strSliceRange = text_split.strSliceRange;
pub const strSplitChars = text_split.strSplitChars;
pub const strSplitString = text_split.strSplitString;
pub const strSplitStrings = text_split.strSplitStrings;
pub const strStartsWithIgnoreCase = text_split.strStartsWithIgnoreCase;
pub const strStartsWithOpt = text_split.strStartsWithOpt;
pub const strToChar = text_split.strToChar;
pub const strToChars = text_split.strToChars;
pub const strToCharsRange = text_split.strToCharsRange;
pub const strTrimAny = text_split.strTrimAny;
pub const uriEscape = text_split.uriEscape;
pub const uriUnescape = text_split.uriUnescape;
test {
    _ = text_split;
}

// ---------------------------------------------------------------------------------------------
// Function values
//
// A function value is a pointer to code and a pointer to the values the code captured:
//
//     fable_rt.Func(*const fn (?*fable_rt.Env, i32) i32)
//
// The code takes the environment first. It owns its other arguments and its result; what it
// captured stays owned by the environment, which is reference counted and frees the captures
// with itself. A function that captures nothing has no environment.
// ---------------------------------------------------------------------------------------------

/// The start of every environment.
pub const Env = struct {
    @"$rc": u32 = 1,
    /// the collector's header of this environment, if what it captured can be part of a cycle
    gc: ?*sgc.Hdr = null,
    destroy: *const fn (*Env) ?*Env,
    /// marks what the function captured shared (see `markShared`)
    share: *const fn (*Env) Raised!void,
    /// (see `withStage`) the function's first stage, its number of arguments and its type
    stage: ?*const anyopaque = null,
    stage_arity: u8 = 0,
    stage_type: ?[*:0]const u8 = null,
};

pub fn Code2Of(comptime Code: type) type {
    const Fn = @typeInfo(@typeInfo(Code).pointer.child).@"fn";
    if (Fn.param_types.len != 2 or Fn.return_type == null) return void;
    const R = Fn.return_type.?;
    if (!isRaised(R)) return void;
    const Inner = @typeInfo(R).error_union.payload;
    if (!isFunc(Inner)) return void;
    const InnerFn = @typeInfo(@typeInfo(@FieldType(Inner, "code")).pointer.child).@"fn";
    if (InnerFn.param_types.len != 2 or InnerFn.return_type == null) return void;
    return *const fn (?*Env, Fn.param_types[1].?, InnerFn.param_types[1].?) InnerFn.return_type.?;
}

pub fn Func(comptime Code: type) type {
    const Code2 = Code2Of(Code);
    if (Code2 == void) {
        return struct {
            pub const fable_func = {};
            env: ?*Env,
            code: Code,
            tcode: ?TailFn = null,
        };
    }
    return struct {
        pub const fable_func = {};
        env: ?*Env,
        code: Code,
        code2: ?Code2 = null,
        tcode: ?TailFn = null,
        tcode2: ?TailFn = null,
    };
}

pub fn isFunc(comptime T: type) bool {
    return @typeInfo(T) == .@"struct" and @hasDecl(T, "fable_func");
}

pub fn isKnown(comptime T: type) bool {
    return @typeInfo(T) == .@"struct" and @hasDecl(T, "fable_known");
}

pub fn isKnownIface(comptime T: type) bool {
    return @typeInfo(T) == .@"struct" and @hasDecl(T, "fable_known_iface");
}

const iface_mod = @import("fable_iface.zig");
pub const IfaceImpl = iface_mod.IfaceImpl;
pub const ifaceId = iface_mod.ifaceId;
pub const withIfaces = iface_mod.withIfaces;
const objIfaceVt = iface_mod.objIfaceVt;
const objAsIface = iface_mod.objAsIface;
pub const IfaceMeta = iface_mod.IfaceMeta;
pub const empty_iface_meta = iface_mod.empty_iface_meta;
pub const obj_iface_meta = iface_mod.obj_iface_meta;
pub const box_iface_meta = iface_mod.box_iface_meta;
pub const env_iface_meta = iface_mod.env_iface_meta;
pub const upcastIfaceMeta = iface_mod.upcastIfaceMeta;
pub const Iface = iface_mod.Iface;
pub const isIface = iface_mod.isIface;
pub const ifaceBox = iface_mod.ifaceBox;
pub const ifaceClosure = iface_mod.ifaceClosure;
pub const erasedConv = iface_mod.erasedConv;
pub const ifaceAdapt = iface_mod.ifaceAdapt;
pub const ifaceMethod = iface_mod.ifaceMethod;
pub const ifaceToObjBorrow = iface_mod.ifaceToObjBorrow;
pub const ifaceToAnyBorrow = iface_mod.ifaceToAnyBorrow;
pub const ifaceIsClass = iface_mod.ifaceIsClass;
pub const ifaceCastClass = iface_mod.ifaceCastClass;
pub const ifaceTryUnbox = iface_mod.ifaceTryUnbox;
pub const ifaceUnbox = iface_mod.ifaceUnbox;
pub const IfaceAnon0 = iface_mod.IfaceAnon0;
pub const IfaceAnon1 = iface_mod.IfaceAnon1;
pub const IfaceAnon2 = iface_mod.IfaceAnon2;
pub const IfaceAnon3 = iface_mod.IfaceAnon3;
pub const IfaceAnon4 = iface_mod.IfaceAnon4;
pub const IfaceAnon5 = iface_mod.IfaceAnon5;
pub const IfaceAnon6 = iface_mod.IfaceAnon6;
pub const IfaceAnon7 = iface_mod.IfaceAnon7;
pub const IfaceAnon8 = iface_mod.IfaceAnon8;
pub const IfaceAnon9 = iface_mod.IfaceAnon9;
pub const IfaceAnon10 = iface_mod.IfaceAnon10;
pub const IfaceAnon11 = iface_mod.IfaceAnon11;
pub const IfaceAnon12 = iface_mod.IfaceAnon12;
pub const IfaceAnon13 = iface_mod.IfaceAnon13;
pub const IfaceAnon14 = iface_mod.IfaceAnon14;
pub const IfaceAnon15 = iface_mod.IfaceAnon15;
pub const IfaceAnon16 = iface_mod.IfaceAnon16;
pub const IfaceAnon17 = iface_mod.IfaceAnon17;
pub const IfaceAnon18 = iface_mod.IfaceAnon18;
pub const IfaceAnon19 = iface_mod.IfaceAnon19;
pub const IfaceAnon20 = iface_mod.IfaceAnon20;
pub const IfaceAnon21 = iface_mod.IfaceAnon21;
pub const IfaceAnon22 = iface_mod.IfaceAnon22;
pub const IfaceAnon23 = iface_mod.IfaceAnon23;
pub const IfaceAnon24 = iface_mod.IfaceAnon24;

pub fn EnvOf(comptime Captures: type) type {
    return struct {
        const Self = @This();
        pub const cyclic = functions_in_cycles and holdsCyclic(Captures);
        pub const K = Collected(
            Self,
            "hdr",
            @as(isize, @offsetOf(Self, "header")) + @as(isize, @offsetOf(Env, "$rc")) - @as(isize, @offsetOf(Self, "hdr")),
            "captures",
        );

        header: Env,
        hdr: GcHdr(cyclic) = undefined,
        captures: Captures,

        const cap_info = @typeInfo(Captures).@"struct";
        const tail_field: ?usize = blk: {
            var found: ?usize = null;
            for (cap_info.field_types, 0..) |F, i| {
                if (isFunc(F) or isIface(F)) found = i;
            }
            break :blk found;
        };

        pub fn destroy(header: *Env) ?*Env {
            const self: *Self = @alignCast(@fieldParentPtr("header", header));
            inline for (cap_info.field_names, 0..) |name, i| {
                if (comptime (tail_field == null or tail_field.? != i)) {
                    drop(@field(self.captures, name));
                }
            }
            const next: ?*Env = if (comptime tail_field) |i| blk: {
                const fv = @field(self.captures, cap_info.field_names[i]);
                const F = cap_info.field_types[i];
                if (comptime isFunc(F)) {
                    break :blk fv.env;
                } else {
                    if (fv.vt.@"$meta" == &env_iface_meta) {
                        break :blk if (fv.data) |p| @ptrCast(@alignCast(p)) else null;
                    }
                    fv.vt.@"$meta".drop(fv.data);
                    break :blk null;
                }
            } else null;
            free(self);
            return next;
        }

        pub fn share(header: *Env) Raised!void {
            const self: *Self = @alignCast(@fieldParentPtr("header", header));
            if (thread.transfer_env) {
                thread.transfer_env = false;
                return transferOrShareOrRaise(self.captures);
            }
            return markShared(self.captures);
        }
    };
}

/// A function value that owns `captures`.
pub inline fn closure(comptime F: type, comptime Captures: type, captures: Captures, code: @FieldType(F, "code")) F {
    const E = EnvOf(Captures);
    if (comptime E.cyclic) gcTick();
    const e = alloc().create(E) catch oom();
    e.* = .{ .header = .{ .destroy = E.destroy, .share = E.share }, .captures = captures };
    if (comptime E.cyclic) {
        e.hdr = thread.collector.hdr(&E.K.desc, E.K.isLeaf(e));
        e.header.gc = &e.hdr;
    }
    if (track) thread.stats.allocs += 1;
    return .{ .env = &e.header, .code = code };
}

/// A function value that owns `captures` and carries a `$tc` tail entry.
pub inline fn closureTc(
    comptime F: type,
    comptime Captures: type,
    captures: Captures,
    code: @FieldType(F, "code"),
    tcode: ?TailFn,
) F {
    var f = closure(F, Captures, captures, code);
    f.tcode = tcode;
    return f;
}

/// A curried 2-argument function value that owns `captures` and carries `$tc` / `tcode2` entries.
pub inline fn closure2Tc(
    comptime F: type,
    comptime Captures: type,
    captures: Captures,
    code: @FieldType(F, "code"),
    code2: Code2Of(@FieldType(F, "code")),
    tcode: ?TailFn,
    tcode2: ?TailFn,
) F {
    var f = closure2(F, Captures, captures, code, code2);
    f.tcode = tcode;
    f.tcode2 = tcode2;
    return f;
}

/// A curried 2-argument function value that owns `captures` and carries a direct 2-arg entry point.
pub inline fn closure2(
    comptime F: type,
    comptime Captures: type,
    captures: Captures,
    code: @FieldType(F, "code"),
    code2: Code2Of(@FieldType(F, "code")),
) F {
    const E = EnvOf(Captures);
    if (comptime E.cyclic) gcTick();
    const e = alloc().create(E) catch oom();
    e.* = .{ .header = .{ .destroy = E.destroy, .share = E.share }, .captures = captures };
    if (comptime E.cyclic) {
        e.hdr = thread.collector.hdr(&E.K.desc, E.K.isLeaf(e));
        e.header.gc = &e.hdr;
    }
    if (track) thread.stats.allocs += 1;
    return .{ .env = &e.header, .code = code, .code2 = code2 };
}

/// A unique closure environment is about to be taken apart or reused without `dropEnv`.
pub inline fn forgetEnv(e: *Env) void {
    if (e.gc) |h| thread.collector.onFree(h);
}

inline fn tryReuseEnv(ctx: *TailCtx, comptime Captures: type, captures: Captures) ?*EnvOf(Captures) {
    const E = EnvOf(Captures);
    if (ctx.reuse_env) |p| {
        if (ctx.reuse_env_size == @sizeOf(E) and ctx.reuse_env_align == @alignOf(E)) {
            ctx.reuse_env = null;
            const e: *E = @ptrCast(@alignCast(p));
            e.* = .{ .header = .{ .destroy = E.destroy, .share = E.share }, .captures = captures };
            if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(e));
            if (comptime E.cyclic) {
                if (!thread.collector_ready) collectorSetup();
                thread.collector.allocs += 1;
                e.hdr = thread.collector.hdr(&E.K.desc, E.K.isLeaf(e));
                e.header.gc = &e.hdr;
            }
            if (track) thread.stats.reuses += 1;
            return e;
        }
    }
    return null;
}

/// Construct a closure, reusing `ctx.reuse_env` if its `EnvOf` layout matches.
pub inline fn closureReuse(ctx: *TailCtx, comptime F: type, comptime Captures: type, captures: Captures, code: @FieldType(F, "code")) F {
    if (tryReuseEnv(ctx, Captures, captures)) |e| {
        return .{ .env = &e.header, .code = code };
    }
    return closure(F, Captures, captures, code);
}

/// Construct a `$tc`-capable closure, reusing `ctx.reuse_env` if its `EnvOf` layout matches.
pub inline fn closureTcReuse(
    ctx: *TailCtx,
    comptime F: type,
    comptime Captures: type,
    captures: Captures,
    code: @FieldType(F, "code"),
    tcode: ?TailFn,
) F {
    var f = closureReuse(ctx, F, Captures, captures, code);
    f.tcode = tcode;
    return f;
}

/// Construct a curried 2-arg closure, reusing `ctx.reuse_env` if its `EnvOf` layout matches.
pub inline fn closure2Reuse(
    ctx: *TailCtx,
    comptime F: type,
    comptime Captures: type,
    captures: Captures,
    code: @FieldType(F, "code"),
    code2: Code2Of(@FieldType(F, "code")),
) F {
    if (tryReuseEnv(ctx, Captures, captures)) |e| {
        return .{ .env = &e.header, .code = code, .code2 = code2 };
    }
    return closure2(F, Captures, captures, code, code2);
}

/// Construct a `$tc`/`tcode2`-capable closure, reusing `ctx.reuse_env` if its `EnvOf` layout matches.
pub inline fn closure2TcReuse(
    ctx: *TailCtx,
    comptime F: type,
    comptime Captures: type,
    captures: Captures,
    code: @FieldType(F, "code"),
    code2: Code2Of(@FieldType(F, "code")),
    tcode: ?TailFn,
    tcode2: ?TailFn,
) F {
    var f = closure2Reuse(ctx, F, Captures, captures, code, code2);
    f.tcode = tcode;
    f.tcode2 = tcode2;
    return f;
}

// ---- stages: a function value of several arguments that is really a function of fewer, which
// gives a function of the rest (`let doMap setState = ...; setState`, used as a value of type
// `SetState -> 'model -> Dispatch -> unit`). Uncurried by its type, its first part would run
// again at every call; F# runs it once for each application to its first arguments. The value
// carries that first stage, which a partial application of it calls (`stageOf`). (fable-library-ts
// does the same with the curried function its uncurried adapters carry.) ----

/// `f`, carrying `s`: its first `k` arguments, which give a function of the rest
pub fn withStage(f: anytype, comptime k: u8, s: anytype) @TypeOf(f) {
    const F = @TypeOf(f);
    const S = @TypeOf(s);
    const Caps = struct { inner: F, stage: S };
    const Fwd = Forward(F, Caps);
    const out = if (comptime @hasField(F, "code2"))
        closure2(F, Caps, .{ .inner = dup(f), .stage = dup(s) }, Fwd.code, Fwd.code2)
    else
        closure(F, Caps, .{ .inner = dup(f), .stage = dup(s) }, Fwd.code);
    const e: *EnvOf(Caps) = @alignCast(@fieldParentPtr("header", out.env.?));
    e.header.stage = @ptrCast(&e.captures.stage);
    e.header.stage_arity = k;
    e.header.stage_type = @typeName(S);
    return out;
}

/// `adapter` (a function value that calls `f` with its arguments in another shape), carrying `s`
/// when `f` carries a stage of its own; otherwise `adapter` as it is
pub fn withStageIf(f: anytype, adapter: anytype, comptime k: u8, s: anytype) @TypeOf(adapter) {
    const e = f.env orelse return dup(adapter);
    if (e.stage_arity == 0) return dup(adapter);
    return withStage(adapter, k, s);
}

/// The first stage of `f` of `k` arguments, of type `S`, if it has one (a reference of its own)
pub fn stageOf(comptime OS: type, f: anytype, comptime k: u8) OS {
    const S = @typeInfo(OS).optional.child;
    const e = f.env orelse return null;
    if (e.stage_arity != k) return null;
    const t = e.stage_type orelse return null;
    if (!std.mem.eql(u8, std.mem.span(t), @typeName(S))) return null;
    const p: *const S = @ptrCast(@alignCast(e.stage.?));
    return dup(p.*);
}

/// (the code of a function value that calls the one it holds)
fn Forward(comptime F: type, comptime Caps: type) type {
    const Fn = @typeInfo(@typeInfo(@FieldType(F, "code")).pointer.child).@"fn";
    const R = Fn.return_type.?;
    const P = Fn.param_types;
    return switch (P.len) {
        2 => if (comptime @hasField(F, "code2")) struct {
            const Code2Fn = @typeInfo(Code2Of(@typeInfo(@FieldType(F, "code")).pointer.child)).pointer.child;
            const Fn2 = @typeInfo(Code2Fn).@"fn";
            const R2 = Fn2.return_type.?;
            const B = Fn2.param_types[2].?;
            fn code(env: ?*Env, a: P[1].?) R {
                const c = captured(Caps, env);
                return c.inner.code(c.inner.env, a);
            }
            fn code2(env: ?*Env, a: P[1].?, b: B) R2 {
                const c = captured(Caps, env);
                return apply2(Unraised(R2), c.inner, a, b);
            }
        } else struct {
            fn code(env: ?*Env, a: P[1].?) R {
                const c = captured(Caps, env);
                return c.inner.code(c.inner.env, a);
            }
        },
        3 => struct {
            fn code(env: ?*Env, a: P[1].?, b: P[2].?) R {
                const c = captured(Caps, env);
                return c.inner.code(c.inner.env, a, b);
            }
        },
        4 => struct {
            fn code(env: ?*Env, a: P[1].?, b: P[2].?, d: P[3].?) R {
                const c = captured(Caps, env);
                return c.inner.code(c.inner.env, a, b, d);
            }
        },
        5 => struct {
            fn code(env: ?*Env, a: P[1].?, b: P[2].?, d: P[3].?, e4: P[4].?) R {
                const c = captured(Caps, env);
                return c.inner.code(c.inner.env, a, b, d, e4);
            }
        },
        6 => struct {
            fn code(env: ?*Env, a: P[1].?, b: P[2].?, d: P[3].?, e4: P[4].?, e5: P[5].?) R {
                const c = captured(Caps, env);
                return c.inner.code(c.inner.env, a, b, d, e4, e5);
            }
        },
        else => @compileError("fable: a staged function value of this many arguments"),
    };
}

/// What the function value captured, from inside its code.
pub inline fn captured(comptime Captures: type, env: ?*Env) *const Captures {
    const e: *EnvOf(Captures) = @alignCast(@fieldParentPtr("header", env.?));
    return &e.captures;
}

// ---------------------------------------------------------------------------------------------
// (moved to fable_exn.zig)
const fable_exn = @import("fable_exn.zig");
pub const Raised = fable_exn.Raised;
pub const ExnType = fable_exn.ExnType;
pub const ExnHeader = fable_exn.ExnHeader;
pub const Exn = fable_exn.Exn;
pub const ExnOf = fable_exn.ExnOf;
pub const MatchFailureException = fable_exn.MatchFailureException;
pub const ExnUnder = fable_exn.ExnUnder;
pub const throw = fable_exn.throw;
pub const take = fable_exn.take;
/// What a call gives, as an error union: itself if it is one, else one of no errors. A call of a
/// function of another file, whether it raises known only when the Zig is compiled, is written
/// `try fable_rt.lift(f(x))` or `fable_rt.lift(f(x)) catch { ... }`: of no errors, the `try`
/// lets the value through and the handler is not compiled.
pub fn Lifted(comptime T: type) type {
    return if (@typeInfo(T) == .error_union) T else error{}!T;
}

pub inline fn lift(x: anytype) Lifted(@TypeOf(x)) {
    return x;
}

pub const isRaised = fable_exn.isRaised;
pub const MayRaise = fable_exn.MayRaise;
pub const Described = fable_exn.Described;
pub const Failure = fable_exn.Failure;
pub const SystemException = fable_exn.SystemException;
pub const ArgumentException = fable_exn.ArgumentException;
pub const ArgumentNullException = fable_exn.ArgumentNullException;
pub const ArgumentOutOfRangeException = fable_exn.ArgumentOutOfRangeException;
pub const ArithmeticException = fable_exn.ArithmeticException;
pub const DivideByZeroException = fable_exn.DivideByZeroException;
pub const OverflowException = fable_exn.OverflowException;
pub const InvalidOperationException = fable_exn.InvalidOperationException;
pub const ThreadStateException = fable_exn.ThreadStateException;
pub const NotSupportedException = fable_exn.NotSupportedException;
pub const NotImplementedException = fable_exn.NotImplementedException;
pub const IndexOutOfRangeException = fable_exn.IndexOutOfRangeException;
pub const NullReferenceException = fable_exn.NullReferenceException;
pub const FormatException = fable_exn.FormatException;
pub const KeyNotFoundException = fable_exn.KeyNotFoundException;
pub const AggregateException = fable_exn.AggregateException;
pub const InvalidCastException = fable_exn.InvalidCastException;
pub const TimeoutException = fable_exn.TimeoutException;
pub const UriFormatException = fable_exn.UriFormatException;
pub const IOException = fable_exn.IOException;
pub const FileNotFoundException = fable_exn.FileNotFoundException;
pub const DirectoryNotFoundException = fable_exn.DirectoryNotFoundException;
pub const UnauthorizedAccessException = fable_exn.UnauthorizedAccessException;
pub const ObjectDisposedException = fable_exn.ObjectDisposedException;
pub const OperationCanceledException = fable_exn.OperationCanceledException;
pub const TaskCanceledException = fable_exn.TaskCanceledException;
pub const ApplicationException = fable_exn.ApplicationException;
pub const OutOfMemoryException = fable_exn.OutOfMemoryException;
pub const NotFiniteNumberException = fable_exn.NotFiniteNumberException;
pub const RankException = fable_exn.RankException;
pub const ArrayTypeMismatchException = fable_exn.ArrayTypeMismatchException;
pub const MissingMethodException = fable_exn.MissingMethodException;
pub const raise = fable_exn.raise;
pub const div = fable_exn.div;
pub const rem = fable_exn.rem;
pub const exnWithInner = fable_exn.exnWithInner;
pub const exnWithInners = fable_exn.exnWithInners;
pub const strNormalize = @import("fable_normalize.zig").strNormalize;
pub const strIsNormalized = @import("fable_normalize.zig").strIsNormalized;
pub const exnInnerList = fable_exn.exnInnerList;
pub const exnFlatten = fable_exn.exnFlatten;
pub const exnInner = fable_exn.exnInner;
pub const exnInnerBoxed = fable_exn.exnInnerBoxed;
pub const exnHasNoInner = fable_exn.exnHasNoInner;
pub const exnToString = fable_exn.exnToString;
pub const exnMessage = fable_exn.exnMessage;
pub const exnStackTrace = fable_exn.exnStackTrace;
pub const testInit = fable_exn.testInit;
pub const uncount = fable_exn.uncount;
pub const recount = fable_exn.recount;
pub const testLiveBefore = fable_exn.testLiveBefore;
pub const testNoLeak = fable_exn.testNoLeak;
pub const testCase = fable_exn.testCase;
pub const uncaught = fable_exn.uncaught;
// ---------------------------------------------------------------------------------------------
// Calls between files
//
// A file is compiled without knowing what the functions of other files were inferred to
// borrow. So the callee's file states it, as a constant next to the function:
//
//     pub const @"sumList$sig" = .{ .borrows = .{true}, .result_borrowed = false };
//
// and the caller's file says what it does with each argument: `.keep` (it uses the value
// again), `.give` (this was its last use) or `.plain` (not a managed value). `across` puts
// the two together when the program is compiled, so the call costs what it would cost if
// both functions were in one file.
// ---------------------------------------------------------------------------------------------

pub const Use = enum { plain, keep, give };

/// A value of a type parameter constrained to a sequence (`#seq<'T>`, a flexible type) given
/// where a sequence `S` is expected. Its type is known when Zig instantiates the function: the
/// sequence itself, or the library's sequence over the array or list it is (`m` is the
/// library's Seq module). The value is borrowed.
pub fn flexSeq(comptime S: type, x: anytype, comptime m: type) Raised!S {
    const T = @TypeOf(x);
    if (comptime T == S) return dup(x);
    if (comptime isCellPtr(T) and @hasDecl(@typeInfo(T).pointer.child, "fable_array")) {
        const I = @typeInfo(T).pointer.child.fable_array;
        return across(m.ofArray(I).call, m.@"ofArray$sig", .{.keep}, .{x});
    }
    if (comptime @typeInfo(T) == .@"union" and @hasDecl(T, "fable_list")) {
        const I = @FieldType(@typeInfo(@FieldType(T, "Cons")).pointer.child, "Head");
        return across(m.ofList(I).call, m.@"ofList$sig", .{.keep}, .{x});
    }
    // (a ResizeArray: what it holds now, as an array; .NET raises if it changes while walked)
    if (comptime isCellPtr(T) and @hasField(@typeInfo(T).pointer.child, "capacity") and @hasField(@typeInfo(T).pointer.child, "items")) {
        const I = rItem(T);
        const arr = raToArray(x);
        return across(m.ofArray(I).call, m.@"ofArray$sig", .{.give}, .{arr});
    }
    @compileError("fable: " ++ @typeName(T) ++ " is not a sequence the Zig target can walk yet");
}

pub inline fn across(
    comptime f: anytype,
    comptime sig: anytype,
    comptime uses: anytype,
    args: anytype,
) @typeInfo(@TypeOf(f)).@"fn".return_type.? {
    // (inlined, its loops count against the quota of the function it is in: a function with
    // many calls of other files would run out of it)
    @setEvalBranchQuota(1_000_000);
    var a: std.meta.ArgsTuple(@TypeOf(f)) = undefined;
    inline for (uses, 0..) |use, i| {
        const u: Use = use;
        // the callee takes ownership, the caller keeps using the value: one more reference
        a[i] = if (u == .keep and !sig.borrows[i]) dup(args[i]) else args[i];
    }
    const raw = @call(.auto, f, a);
    // (If the callee raised, it has given up what it owned; what it only borrowed and the caller
    // was done with is given up here, and the caller goes on unwinding.)
    const r = if (comptime isRaised(@TypeOf(raw))) raw catch |err| {
        inline for (uses, 0..) |use, i| {
            const u: Use = use;
            if (u == .give and sig.borrows[i]) drop(args[i]);
        }
        return err;
    } else raw;
    // (a borrowed result may be part of an argument: it is made owned before they are given up)
    const result = if (sig.result_borrowed) dup(r) else r;
    inline for (uses, 0..) |use, i| {
        const u: Use = use;
        // the callee only borrowed what the caller was done with: the caller gives it up
        if (u == .give and sig.borrows[i]) drop(args[i]);
    }
    return result;
}

pub inline fn dropAll(xs: anytype) void {
    inline for (xs) |x| drop(x);
}

pub fn UnwrapRaised(comptime T: type) type {
    return if (@typeInfo(T) == .error_union) @typeInfo(T).error_union.payload else T;
}

/// Concise cross-file call with ASCII use string (`p` = plain, `k` = keep, `g` = give)
/// and an error-edge tuple `err_drops` of caller values dropped if the callee raises.
pub inline fn acrossCompact(
    comptime f: anytype,
    comptime sig: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) @typeInfo(@TypeOf(f)).@"fn".return_type.? {
    @setEvalBranchQuota(1_000_000);
    var a: std.meta.ArgsTuple(@TypeOf(f)) = undefined;
    inline for (uses, 0..) |u, i| {
        a[i] = if (u == 'k' and !sig.borrows[i]) dup(args[i]) else args[i];
    }
    const raw = @call(.auto, f, a);
    const r = if (comptime isRaised(@TypeOf(raw))) raw catch |err| {
        inline for (uses, 0..) |u, i| {
            if (u == 'g' and sig.borrows[i]) drop(args[i]);
        }
        inline for (err_drops) |d| drop(d);
        return err;
    } else raw;
    const result = if (sig.result_borrowed) dup(r) else r;
    inline for (uses, 0..) |u, i| {
        if (u == 'g' and sig.borrows[i]) drop(args[i]);
    }
    return result;
}

pub inline fn callG(
    comptime G: type,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) @typeInfo(@TypeOf(G.call)).@"fn".return_type.? {
    return acrossCompact(G.call, G.sig, uses, args, err_drops);
}

pub inline fn callM(
    comptime M: type,
    comptime name: []const u8,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) @typeInfo(@TypeOf(@field(M, name))).@"fn".return_type.? {
    return acrossCompact(@field(M, name), @field(M, name ++ "$sig"), uses, args, err_drops);
}

/// For Zig code of the program's: `name args` of a function of the F# file `M` (the Zig that
/// Fable wrote, `@import`ed). The arguments stay the caller's (dup'ed where the function keeps
/// them) and what it gives is the caller's; `error.Raised` where the F# raises (an error union
/// whether or not the function can raise).
pub inline fn callFSharp(
    comptime M: type,
    comptime name: []const u8,
    args: anytype,
) Raised!UnwrapRaised(@typeInfo(@TypeOf(@field(M, name))).@"fn".return_type.?) {
    const n = @typeInfo(@TypeOf(args)).@"struct".field_names.len;
    const uses = comptime blk: {
        var u: [n]u8 = undefined;
        @memset(&u, 'k');
        break :blk u;
    };
    return callM(M, name, &uses, args, .{});
}

pub inline fn xcallG(
    comptime G: type,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) Raised!UnwrapRaised(@typeInfo(@TypeOf(G.call)).@"fn".return_type.?) {
    return callG(G, uses, args, err_drops);
}

pub inline fn xcallM(
    comptime M: type,
    comptime name: []const u8,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) Raised!UnwrapRaised(@typeInfo(@TypeOf(@field(M, name))).@"fn".return_type.?) {
    return callM(M, name, uses, args, err_drops);
}

pub inline fn xcallPlain(
    raw: anytype,
    err_drops: anytype,
) Raised!UnwrapRaised(@TypeOf(raw)) {
    if (comptime isRaised(@TypeOf(raw))) {
        return raw catch |err| {
            inline for (err_drops) |d| drop(d);
            return err;
        };
    } else {
        return raw;
    }
}

/// Cross-file call in the let-bound owner case where the caller assumes the result borrows from
/// `assumed_from` parameter indices without dup'ing the result. Verifies `sig.result_from`,
/// `sig.result_borrowed`, `sig.borrows`, and `'k'` uses at Zig compile time.
pub inline fn acrossAssumed(
    comptime f: anytype,
    comptime sig: anytype,
    comptime assumed_from: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) @typeInfo(@TypeOf(f)).@"fn".return_type.? {
    @setEvalBranchQuota(1_000_000);
    comptime {
        if (!@hasField(@TypeOf(sig), "result_from") or !sig.result_borrowed or sig.result_from.len != assumed_from.len) {
            @compileError("fable: stale cross-file RetFrom facts; recompile caller");
        } else {
            for (0..assumed_from.len) |k| {
                const idx = assumed_from[k];
                if (sig.result_from[k] != idx or !sig.borrows[idx] or uses[idx] != 'k') {
                    @compileError("fable: stale cross-file RetFrom facts; recompile caller");
                }
            }
        }
    }
    var a: std.meta.ArgsTuple(@TypeOf(f)) = undefined;
    inline for (uses, 0..) |u, i| {
        a[i] = if (u == 'k' and !sig.borrows[i]) dup(args[i]) else args[i];
    }
    const raw = @call(.auto, f, a);
    const r = if (comptime isRaised(@TypeOf(raw))) raw catch |err| {
        inline for (uses, 0..) |u, i| {
            if (u == 'g' and sig.borrows[i]) drop(args[i]);
        }
        inline for (err_drops) |d| drop(d);
        return err;
    } else raw;
    inline for (uses, 0..) |u, i| {
        if (u == 'g' and sig.borrows[i]) drop(args[i]);
    }
    return r;
}

pub inline fn callAssumedM(
    comptime M: type,
    comptime name: []const u8,
    comptime assumed_from: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) @typeInfo(@TypeOf(@field(M, name))).@"fn".return_type.? {
    if (!@hasDecl(M, name ++ "$sig")) {
        @compileError("fable: stale or missing $sig for assumed-borrowed call " ++ name ++ "; recompile caller");
    }
    return acrossAssumed(@field(M, name), @field(M, name ++ "$sig"), assumed_from, uses, args, err_drops);
}

pub inline fn callAssumedG(
    comptime G: type,
    comptime assumed_from: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) @typeInfo(@TypeOf(G.call)).@"fn".return_type.? {
    if (!@hasDecl(G, "sig")) {
        @compileError("fable: stale or missing sig for assumed-borrowed generic call; recompile caller");
    }
    return acrossAssumed(G.call, G.sig, assumed_from, uses, args, err_drops);
}

pub inline fn xcallAssumedM(
    comptime M: type,
    comptime name: []const u8,
    comptime assumed_from: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) Raised!UnwrapRaised(@typeInfo(@TypeOf(@field(M, name))).@"fn".return_type.?) {
    return callAssumedM(M, name, assumed_from, uses, args, err_drops);
}

pub inline fn xcallAssumedG(
    comptime G: type,
    comptime assumed_from: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) Raised!UnwrapRaised(@typeInfo(@TypeOf(G.call)).@"fn".return_type.?) {
    return callAssumedG(G, assumed_from, uses, args, err_drops);
}

/// Compile-time guard asserting that a cross-file callee inferred as `RNever` still cannot raise.
pub fn assertNoRaise(comptime f: anytype) void {
    const Ret = @typeInfo(@TypeOf(f)).@"fn".return_type.?;
    if (comptime isRaised(Ret)) {
        @compileError("fable: stale cross-file Raises facts; recompile caller");
    }
}

/// Compile-time guard asserting that a cross-file callee's `$stores` remain disjoint from `disjoint_fields`,
/// make no indirect callback, and (when `check_ext_store` holds) make no unknown external store.
pub fn assertNoStore(
    comptime M: type,
    comptime name: []const u8,
    comptime disjoint_fields: anytype,
    comptime check_ext_store: bool,
) void {
    comptime {
        @setEvalBranchQuota(1_000_000);
        if (!@hasDecl(M, name ++ "$stores")) {
            @compileError("fable: stale cross-file Stores facts; recompile caller");
        }
        const s = @field(M, name ++ "$stores");
        if (s.calls_callback or (check_ext_store and s.calls_ext_store)) {
            @compileError("fable: stale cross-file Stores facts; recompile caller");
        }
        for (disjoint_fields) |df| {
            for (s.fields) |sf| {
                if (std.mem.eql(u8, df, sf)) {
                    @compileError("fable: stale cross-file Stores facts; recompile caller");
                }
            }
        }
    }
}

inline fn acrossHof(
    comptime target: anytype,
    comptime k_target: anytype,
    comptime has_k: bool,
    comptime sig: anytype,
    comptime noescape: anytype,
    comptime assumed_from: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) @typeInfo(@TypeOf(target)).@"fn".return_type.? {
    @setEvalBranchQuota(1_000_000);
    const has_sig = @TypeOf(sig) != @TypeOf(null);
    const has_noesc = @TypeOf(noescape) != @TypeOf(null);
    const is_assumed = @TypeOf(assumed_from) != @TypeOf(null);
    comptime {
        if (is_assumed) {
            if (!has_sig or !@hasField(@TypeOf(sig), "result_from") or !sig.result_borrowed or sig.result_from.len != assumed_from.len) {
                @compileError("fable: stale cross-file RetFrom facts; recompile caller");
            } else {
                for (0..assumed_from.len) |k| {
                    const idx = assumed_from[k];
                    if (sig.result_from[k] != idx or !sig.borrows[idx] or uses[idx] != 'k' or isKnown(@TypeOf(args[idx]))) {
                        @compileError("fable: stale cross-file RetFrom facts; recompile caller");
                    }
                }
            }
        }
    }
    const use_k = comptime blk: {
        if (!has_k or !has_noesc) break :blk false;
        for (0..args.len) |i| {
            if (isKnown(@TypeOf(args[i])) and noescape[i]) break :blk true;
        }
        break :blk false;
    };
    const TargetFn = @typeInfo(@TypeOf(target)).@"fn";
    const RawRet = TargetFn.return_type.?;
    const arg_types = comptime blk: {
        var ts: [args.len]type = undefined;
        for (0..args.len) |i| {
            const T = @TypeOf(args[i]);
            if (isKnown(T)) {
                const keep_k = use_k and has_noesc and noescape[i];
                ts[i] = if (keep_k) T else T.FuncType;
            } else {
                // `target` never uses `anytype`, so `param_types[i]` coerces `comptime_int`/`comptime_float` literals to concrete runtime types.
                ts[i] = TargetFn.param_types[i] orelse T;
            }
        }
        break :blk ts;
    };
    var a: @Tuple(&arg_types) = undefined;
    inline for (0..args.len) |i| {
        const T = @TypeOf(args[i]);
        if (comptime isKnown(T)) {
            if (comptime use_k and has_noesc and noescape[i]) {
                a[i] = args[i];
            } else {
                a[i] = args[i].toFunc();
            }
        } else {
            const borrows_i = if (comptime has_sig) sig.borrows[i] else false;
            a[i] = if (uses[i] == 'k' and !borrows_i) dup(args[i]) else args[i];
        }
    }
    const raw: RawRet = if (comptime use_k) @call(.auto, k_target, a) else @call(.auto, target, a);
    const r = if (comptime isRaised(RawRet)) raw catch |err| {
        inline for (0..args.len) |i| {
            const borrows_i = if (comptime has_sig) sig.borrows[i] else false;
            if (comptime isKnown(@TypeOf(args[i]))) {
                if (comptime !(use_k and has_noesc and noescape[i]) and borrows_i) drop(a[i]);
            } else {
                if (uses[i] == 'g' and borrows_i) drop(a[i]);
            }
        }
        inline for (err_drops) |d| drop(d);
        return err;
    } else raw;
    const result_borrowed = if (comptime has_sig) sig.result_borrowed else false;
    const result = if (comptime is_assumed) r else if (result_borrowed) dup(r) else r;
    inline for (0..args.len) |i| {
        const borrows_i = if (comptime has_sig) sig.borrows[i] else false;
        if (comptime isKnown(@TypeOf(args[i]))) {
            if (comptime !(use_k and has_noesc and noescape[i]) and borrows_i) drop(a[i]);
        } else {
            if (uses[i] == 'g' and borrows_i) drop(a[i]);
        }
    }
    return result;
}

/// Cross-file call where one or more arguments may be stack-allocated `Known` lambdas:
/// dispatches to `M.<name>$k` when `noescape[i]` holds for those arguments, otherwise falls back to
/// `toFunc()` on `M.<name>` while reconciling borrowing via `$sig`.
pub inline fn callHofM(
    comptime M: type,
    comptime name: []const u8,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) @typeInfo(@TypeOf(@field(M, name))).@"fn".return_type.? {
    const has_k = comptime @hasDecl(M, name ++ "$k") and @hasDecl(M, name ++ "$noescape");
    const k_target = if (comptime has_k) @field(M, name ++ "$k") else {};
    const noescape = if (comptime has_k) @field(M, name ++ "$noescape") else null;
    const sig = if (comptime @hasDecl(M, name ++ "$sig")) @field(M, name ++ "$sig") else null;
    return acrossHof(@field(M, name), k_target, has_k, sig, noescape, null, uses, args, err_drops);
}

/// Generic cross-file counterpart to `callHofM`, dispatching to `NS.callK` when `NS.noescape`
/// permits and falling back to `toFunc()` + `NS.call` otherwise.
pub inline fn callHofG(
    comptime NS: type,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) @typeInfo(@TypeOf(NS.call)).@"fn".return_type.? {
    const has_k = comptime @hasDecl(NS, "callK") and @hasDecl(NS, "noescape");
    const k_target = if (comptime has_k) NS.callK else {};
    const noescape = if (comptime has_k) NS.noescape else null;
    const sig = if (comptime @hasDecl(NS, "sig")) NS.sig else null;
    return acrossHof(NS.call, k_target, has_k, sig, noescape, null, uses, args, err_drops);
}

/// Raising wrapper for `callHofM` returning `Raised!R`.
pub inline fn xcallHofM(
    comptime M: type,
    comptime name: []const u8,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) Raised!UnwrapRaised(@typeInfo(@TypeOf(@field(M, name))).@"fn".return_type.?) {
    return callHofM(M, name, uses, args, err_drops);
}

/// Raising wrapper for `callHofG` returning `Raised!R`.
pub inline fn xcallHofG(
    comptime NS: type,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) Raised!UnwrapRaised(@typeInfo(@TypeOf(NS.call)).@"fn".return_type.?) {
    return callHofG(NS, uses, args, err_drops);
}

/// Cross-file HOF call in the let-bound owner case where the caller assumes the result borrows
/// from `assumed_from` parameter indices without dup'ing the result.
pub inline fn callHofAssumedM(
    comptime M: type,
    comptime name: []const u8,
    comptime assumed_from: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) @typeInfo(@TypeOf(@field(M, name))).@"fn".return_type.? {
    const has_k = comptime @hasDecl(M, name ++ "$k") and @hasDecl(M, name ++ "$noescape");
    const k_target = if (comptime has_k) @field(M, name ++ "$k") else {};
    const noescape = if (comptime has_k) @field(M, name ++ "$noescape") else null;
    const sig = if (comptime @hasDecl(M, name ++ "$sig")) @field(M, name ++ "$sig") else null;
    return acrossHof(@field(M, name), k_target, has_k, sig, noescape, assumed_from, uses, args, err_drops);
}

/// Generic cross-file counterpart to `callHofAssumedM`.
pub inline fn callHofAssumedG(
    comptime NS: type,
    comptime assumed_from: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) @typeInfo(@TypeOf(NS.call)).@"fn".return_type.? {
    const has_k = comptime @hasDecl(NS, "callK") and @hasDecl(NS, "noescape");
    const k_target = if (comptime has_k) NS.callK else {};
    const noescape = if (comptime has_k) NS.noescape else null;
    const sig = if (comptime @hasDecl(NS, "sig")) NS.sig else null;
    return acrossHof(NS.call, k_target, has_k, sig, noescape, assumed_from, uses, args, err_drops);
}

/// Raising wrapper for `callHofAssumedM` returning `Raised!R`.
pub inline fn xcallHofAssumedM(
    comptime M: type,
    comptime name: []const u8,
    comptime assumed_from: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) Raised!UnwrapRaised(@typeInfo(@TypeOf(@field(M, name))).@"fn".return_type.?) {
    return callHofAssumedM(M, name, assumed_from, uses, args, err_drops);
}

/// Raising wrapper for `callHofAssumedG` returning `Raised!R`.
pub inline fn xcallHofAssumedG(
    comptime NS: type,
    comptime assumed_from: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) Raised!UnwrapRaised(@typeInfo(@TypeOf(NS.call)).@"fn".return_type.?) {
    return callHofAssumedG(NS, assumed_from, uses, args, err_drops);
}

/// Call a function parameter `k` inside a specialized `callK` HOF: when `k` is a stack-allocated
/// `Known` lambda, invoke it directly while reconciling `uses` against its `$sig` (`borrows` /
/// `result_borrowed`, and `call2` for curried 2-arg lambdas); otherwise fall back to indirect
/// `Func` invocation.
pub fn InvokeKRet(comptime R: type, comptime K: type, comptime n_args: usize) type {
    if (isKnown(K)) {
        const CallFn = @typeInfo(@TypeOf(K.call)).@"fn";
        if (n_args == 2 and CallFn.param_types.len == 2) {
            if (@hasDecl(K, "call2")) {
                const R2 = @typeInfo(@TypeOf(K.call2)).@"fn".return_type.?;
                return if (isRaised(R2)) Raised!R else error{}!R;
            }
            return Raised!R;
        }
        const R1 = CallFn.return_type.?;
        return if (isRaised(R1)) Raised!R else error{}!R;
    }
    return Raised!R;
}

pub inline fn invokeK(
    comptime R: type,
    k: anytype,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) InvokeKRet(R, @TypeOf(k), args.len) {
    @setEvalBranchQuota(1_000_000);
    const K = @TypeOf(k);
    if (comptime isKnown(K)) {
        const CallFn = @typeInfo(@TypeOf(K.call)).@"fn";
        if (comptime args.len == 2 and CallFn.param_types.len == 2) {
            if (comptime @hasDecl(K, "call2")) {
                var a: std.meta.ArgsTuple(@TypeOf(K.call2)) = undefined;
                a[0] = &k;
                inline for (uses, 0..) |u, i| {
                    a[i + 1] = if (u == 'k' and !K.borrows2[i]) dup(args[i]) else args[i];
                }
                const raw = @call(.auto, K.call2, a);
                const r = if (comptime isRaised(@TypeOf(raw))) raw catch |err| {
                    inline for (uses, 0..) |u, i| {
                        if (u == 'g' and K.borrows2[i]) drop(args[i]);
                    }
                    inline for (err_drops) |d| drop(d);
                    return err;
                } else raw;
                const result = if (K.result_borrowed2) dup(r) else r;
                inline for (uses, 0..) |u, i| {
                    if (u == 'g' and K.borrows2[i]) drop(args[i]);
                }
                return result;
            } else {
                const a0 = if (uses[0] == 'k' and !K.borrows[0]) dup(args[0]) else args[0];
                const raw1 = K.call(&k, a0);
                const g_raw = if (comptime isRaised(@TypeOf(raw1))) raw1 catch |err| {
                    if (uses[0] == 'g' and K.borrows[0]) drop(args[0]);
                    if (uses[1] == 'g') drop(args[1]);
                    inline for (err_drops) |d| drop(d);
                    return err;
                } else raw1;
                const g = if (K.result_borrowed) dup(g_raw) else g_raw;
                if (uses[0] == 'g' and K.borrows[0]) drop(args[0]);
                defer drop(g);
                const a1 = if (uses[1] == 'k') dup(args[1]) else args[1];
                return g.code(g.env, a1) catch |err| {
                    inline for (err_drops) |d| drop(d);
                    return err;
                };
            }
        }
        var a: std.meta.ArgsTuple(@TypeOf(K.call)) = undefined;
        a[0] = &k;
        inline for (uses, 0..) |u, i| {
            a[i + 1] = if (u == 'k' and !K.borrows[i]) dup(args[i]) else args[i];
        }
        const raw = @call(.auto, K.call, a);
        const r = if (comptime isRaised(@TypeOf(raw))) raw catch |err| {
            inline for (uses, 0..) |u, i| {
                if (u == 'g' and K.borrows[i]) drop(args[i]);
            }
            inline for (err_drops) |d| drop(d);
            return err;
        } else raw;
        const result = if (K.result_borrowed) dup(r) else r;
        inline for (uses, 0..) |u, i| {
            if (u == 'g' and K.borrows[i]) drop(args[i]);
        }
        return result;
    } else {
        const Fn = @typeInfo(@typeInfo(@FieldType(K, "code")).pointer.child).@"fn";
        if (comptime args.len == 2 and Fn.param_types.len == 2) {
            const a0 = if (uses[0] == 'k') dup(args[0]) else args[0];
            const a1 = if (uses[1] == 'k') dup(args[1]) else args[1];
            return apply2(R, k, a0, a1) catch |err| {
                inline for (err_drops) |d| drop(d);
                return err;
            };
        }
        var a: std.meta.ArgsTuple(@typeInfo(@FieldType(K, "code")).pointer.child) = undefined;
        a[0] = k.env;
        inline for (uses, 0..) |u, i| {
            a[i + 1] = if (u == 'k') dup(args[i]) else args[i];
        }
        return @call(.auto, k.code, a) catch |err| {
            inline for (err_drops) |d| drop(d);
            return err;
        };
    }
}

/// Call a slot on an interface parameter inside a specialized `callK` HOF: when `recv` is a
/// stack-allocated `KnownIface`, dispatch directly without vtable/box overhead while reconciling
/// `uses` against its slot `$borrows` / `$result_borrowed`; otherwise fall back to `recv.vt`.
pub fn InvokeIfaceKRet(comptime R: type, comptime K: type, comptime slot: []const u8) type {
    if (isKnownIface(K)) {
        const SlotFn = @typeInfo(@TypeOf(@field(K, "slot_" ++ slot))).@"fn";
        const R1 = SlotFn.return_type.?;
        return if (isRaised(R1)) Raised!R else error{}!R;
    }
    return Raised!R;
}

pub inline fn invokeIfaceK(
    comptime R: type,
    recv: anytype,
    comptime slot: []const u8,
    comptime uses: []const u8,
    args: anytype,
    err_drops: anytype,
) InvokeIfaceKRet(R, @TypeOf(recv), slot) {
    @setEvalBranchQuota(1_000_000);
    const K = @TypeOf(recv);
    if (comptime isKnownIface(K)) {
        const slot_name = "slot_" ++ slot;
        const borrows = @field(K, slot_name ++ "$borrows");
        const res_borrowed = @field(K, slot_name ++ "$result_borrowed");
        var a: std.meta.ArgsTuple(@TypeOf(@field(K, slot_name))) = undefined;
        a[0] = &recv;
        inline for (uses, 0..) |u, i| {
            a[i + 1] = if (u == 'k' and !borrows[i]) dup(args[i]) else args[i];
        }
        const raw = @call(.auto, @field(K, slot_name), a);
        const r = if (comptime isRaised(@TypeOf(raw))) raw catch |err| {
            inline for (uses, 0..) |u, i| {
                if (u == 'g' and borrows[i]) drop(args[i]);
            }
            inline for (err_drops) |d| drop(d);
            return err;
        } else raw;
        const result = if (res_borrowed) dup(r) else r;
        inline for (uses, 0..) |u, i| {
            if (u == 'g' and borrows[i]) drop(args[i]);
        }
        return result;
    } else {
        const slot_fn_ptr = @field(recv.vt.*, slot);
        var a: std.meta.ArgsTuple(@typeInfo(@TypeOf(slot_fn_ptr)).pointer.child) = undefined;
        a[0] = recv.data;
        inline for (uses, 0..) |u, i| {
            a[i + 1] = if (u == 'k') dup(args[i]) else args[i];
        }
        return @call(.auto, slot_fn_ptr, a) catch |err| {
            inline for (err_drops) |d| drop(d);
            return err;
        };
    }
}

// ---- `NativePtr.stackalloc`: memory of the function that asks for it ----
//
// .NET's `stackalloc` (F#'s `NativePtr.stackalloc`, then `Span(ptr, n)` over it) gives memory
// that lives until the function returns, zeroed (F# compiles with `localsinit`). A function that
// asks for it has a `StackAlloc` on its own stack: small requests come from its buffer, larger
// ones from the heap, and all of it is given up when the function returns. (Its items are
// unmanaged, as `stackalloc` requires: nothing to count.)

pub const StackAlloc = struct {
    buf: [1024]u8 align(16) = undefined,
    used: usize = 0,
    blocks: ?*Block = null,

    const Block = struct { next: ?*Block, bytes: []align(16) u8 };

    pub fn alloc(self: *StackAlloc, comptime T: type, n: i32) Raised![*]T {
        if (n < 0) return raise(OverflowException, str("Arithmetic operation resulted in an overflow."));
        const size = @as(usize, @intCast(n)) * @sizeOf(T);
        const start = std.mem.alignForward(usize, self.used, @max(@alignOf(T), 1));
        if (start + size <= self.buf.len) {
            self.used = start + size;
            const bytes = self.buf[start .. start + size];
            @memset(bytes, 0);
            return @ptrCast(@alignCast(bytes.ptr));
        }
        const bytes = @import("fable_rt.zig").alloc().alignedAlloc(u8, .@"16", @max(size, 1)) catch return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
        @memset(bytes, 0);
        const b = @import("fable_rt.zig").alloc().create(Block) catch {
            @import("fable_rt.zig").alloc().free(bytes);
            return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
        };
        b.* = .{ .next = self.blocks, .bytes = bytes };
        self.blocks = b;
        return @ptrCast(@alignCast(bytes.ptr));
    }

    pub fn deinit(self: *StackAlloc) void {
        var b = self.blocks;
        while (b) |x| {
            b = x.next;
            @import("fable_rt.zig").alloc().free(x.bytes);
            @import("fable_rt.zig").alloc().destroy(x);
        }
        self.blocks = null;
    }
};

/// `Span<T>(ptr, n)` of what `stackalloc` (or another pointer) gives
pub fn spanOfPtr(comptime S: type, p: anytype, n: i32) Raised!S {
    if (n < 0) return raise(ArgumentOutOfRangeException, str("Specified argument was out of the range of valid values. (Parameter 'length')"));
    const T = @typeInfo(S).pointer.child;
    const items: [*]T = @ptrCast(@alignCast(@constCast(p)));
    return items[0..@intCast(n)];
}

/// Cells that were allocated and not freed (0 when counters are not kept).
pub fn live() i64 {
    return thread.stats.allocs - thread.stats.frees + @atomicLoad(isize, &ended_threads_live, .monotonic);
}

/// What threads that have ended allocated and did not free themselves: a cell made on one
/// thread may be freed on another (the last to let go of a shared value).
pub var ended_threads_live: isize = 0;

/// Called when the program's entry point has returned: true, with a message, if cells are
/// still allocated. Only checks in builds that keep counters.
pub fn leaked() bool {
    poolShutdown();
    asyncStateRelease();
    random.randomSharedRelease();
    // (cycles that died without anything noticing yet are not leaks)
    _ = collect();
    if (!track or live() == 0) return false;
    std.debug.print("fable: {d} cell(s) were never freed (allocated {d}, freed {d}, and threads that ended {d} more than they freed)\n", .{ live(), thread.stats.allocs, thread.stats.frees, ended_threads_live });
    const sgc_exit = threadExitSgcStats();
    if (sgc_exit.remaining_structures_on_exit != 0 or sgc_exit.collected_on_exit != 0) {
        std.debug.print("fable: thread-exit fable_sgc drain across {d} thread(s): collected {d} cells, {d} live structure(s) remained (possible cross-thread or externally referenced cycles)\n", .{ sgc_exit.threads_drained, sgc_exit.collected_on_exit, sgc_exit.remaining_structures_on_exit });
    }
    return true;
}

// ---------------------------------------------------------------------------------------------
// Numbers
// ---------------------------------------------------------------------------------------------
// (moved to fable_math.zig)
const fable_math = @import("fable_math.zig");
pub const overflow = fable_math.overflow;
pub const checkedAdd = fable_math.checkedAdd;
pub const checkedSub = fable_math.checkedSub;
pub const checkedMul = fable_math.checkedMul;
pub const checkedNeg = fable_math.checkedNeg;
pub const checkedConv = fable_math.checkedConv;
pub const absOf = fable_math.absOf;
pub const signOf = fable_math.signOf;
pub const pown = fable_math.pown;
pub const roundEven = fable_math.roundEven;
pub const roundModeOnly = fable_math.roundModeOnly;
pub const roundTo = fable_math.roundTo;
pub const roundMode = fable_math.roundMode;
pub const maxMagnitude = fable_math.maxMagnitude;
pub const minMagnitude = fable_math.minMagnitude;
pub const logBase = fable_math.logBase;
pub const clamp = fable_math.clamp;
pub const convert = fable_math.convert;
pub const arrayAverage = fable_math.arrayAverage;
pub const arrayAverageBy = fable_math.arrayAverageBy;
pub const arrayCopyRange = fable_math.arrayCopyRange;
pub const arrayIndexOf = fable_math.arrayIndexOf;
pub const arraySetSlice = fable_math.arraySetSlice;
pub const arraySum = fable_math.arraySum;
pub const arraySumBy = fable_math.arraySumBy;
pub const arraySumDec = fable_math.arraySumDec;
pub const badFormat = fable_math.badFormat;
pub const base64Of = fable_math.base64Of;
pub const base64Parse = fable_math.base64Parse;
pub const bitGetBytes = fable_math.bitGetBytes;
pub const bitTo = fable_math.bitTo;
pub const bitToString = fable_math.bitToString;
pub const conv = fable_math.conv;
pub const convFloatToInt = fable_math.convFloatToInt;
pub const convParse = fable_math.convParse;
pub const convParseBase = fable_math.convParseBase;
pub const convToStringBase = fable_math.convToStringBase;
pub const hexOf = fable_math.hexOf;
pub const hexParse = fable_math.hexParse;
pub const listAverage = fable_math.listAverage;
pub const listAverageBy = fable_math.listAverageBy;
pub const listSum = fable_math.listSum;
pub const listSumBy = fable_math.listSumBy;
pub const listSumDec = fable_math.listSumDec;
pub const netIntName = fable_math.netIntName;
pub const parseBool = fable_math.parseBool;
pub const parseFloat = fable_math.parseFloat;
pub const parseHex = fable_math.parseHex;
pub const parseInt = fable_math.parseInt;
pub const parseIntFs = fable_math.parseIntFs;
const parseWhole = fable_math.parseWhole;
pub const trimmed = fable_math.trimmed;
pub const numberText = fable_math.numberText;
pub const parseFloatFs = fable_math.parseFloatFs;
pub const parseFloatStyle = convert.parseFloatStyle;
pub const tryParseFloatStyle = convert.tryParseFloatStyle;
pub const numberStyled = convert.numberStyled;
pub const decParseStyle = decimal.decParseStyle;
pub const decTryParseStyle = decimal.decTryParseStyle;
pub const tryParseAny = fable_math.tryParseAny;
pub const tryParseFloat = fable_math.tryParseFloat;
pub const tryParseInt = fable_math.tryParseInt;

test {
    _ = @import("fable_rt_tests.zig");
}
