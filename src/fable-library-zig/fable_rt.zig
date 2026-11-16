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
    .{ .ptr = @constCast(@ptrCast(&base_allocator)), .vtable = &OomHooked.vtable }
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
};

/// A null array of a type whose arrays the collector follows, kept until the collector goes
pub const NullArray = struct { cell: *anyopaque, free: *const fn (*anyopaque) void };

/// Where the runtime's own bookkeeping (the collector's, the table of weak references) comes
/// from: the allocator, unless a stack arena stands in for it now.
pub fn bookkeeping() std.mem.Allocator {
    return thread.book orelse (arena_base orelse allocator);
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
    const c = allocator.create(C) catch oom();
    c.* = init;
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

/// Reuse: build in the dead cell that `tok` holds, if it holds one; allocate otherwise.
pub inline fn cellReuse(comptime T: type, comptime tag: std.meta.Tag(T), tok: anytype, init: Cell(T, tag)) *Cell(T, tag) {
    const C = Cell(T, tag);
    const Dead = @typeInfo(@typeInfo(@TypeOf(tok)).pointer.child).optional.child;
    // (In generic code the dead cell and the new one are the same case of one generic type,
    // with type arguments that may differ. Only when they turn out to have one layout is the
    // dead cell built in; otherwise the token is left alone and its owner frees the cell.)
    if (comptime (@sizeOf(@typeInfo(Dead).pointer.child) == @sizeOf(C) and @alignOf(@typeInfo(Dead).pointer.child) == @alignOf(C))) {
        if (tok.*) |p| {
            tok.* = null;
            const c: *C = @ptrCast(@alignCast(p));
            c.* = init;
            // (a new cell: not the identity hash the dead one was given)
            if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(c));
            if (comptime hasGc(C)) {
                // (a cell that is built in again is a new cell: it gets an age of its own)
                thread.collector.allocs += 1;
                c.@"$gc" = gcHeader(C, c);
            }
            if (track) thread.stats.reuses += 1;
            return c;
        }
    }
    return cell(T, tag, init);
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
        if (rc != Str.literal and rc & shared_bit == 0) p.rc = rc | shared_bit;
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

/// The region of `x` that only the receiver holds made its own again
pub fn adoptShared(x: anytype) void {
    if (weak_refs.shared_count.load(.acquire) != 0) return;
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
        @panic("fable: a value the cycle collector follows was stored into a value shared between threads");
    };
}

/// .NET's `Thread`: a function run on a thread of its own. What the function captured is
/// shared when the thread starts (`markShared`).
pub const ThreadStart = Func(*const fn (?*Env, void) Raised!void);

pub const ThreadOf = *struct {
    pub const fable_identity = {};
    @"$rc": u32 = 1,
    start: ThreadStart,
    /// the thread, once started and until joined
    handle: ?*std.Thread = null,
    started: bool = false,
    /// set (atomically) when the thread's function has ended
    finished: u32 = 0,
};

/// `Thread(fun () -> ...)`
pub fn threadNew(start: ThreadStart) ThreadOf {
    return new(ThreadOf, .{ .start = dup(start) });
}

/// `t.Start()`
pub fn threadStart(t: ThreadOf) Raised!void {
    if (t.started) return raise(ThreadStateException, str("Thread is running or terminated; it cannot restart."));
    // (the thread object too: the new thread holds it, and the flag in it, until it ends)
    try markShared(t);
    const h = allocator.create(std.Thread) catch oom();
    h.* = std.Thread.spawn(.{}, threadMain, .{ dup(t.start), &t.finished, dup(t) }) catch {
        allocator.destroy(h);
        return raise(OutOfMemoryException, str("Thread failed to start."));
    };
    t.handle = h;
    t.started = true;
}

/// (what a thread runs: its function, then what it kept for itself is given up; an exception
/// that leaves it ends the program, as on .NET)
fn threadMain(f: ThreadStart, finished: *u32, t: ThreadOf) void {
    f.code(f.env, {}) catch {
        uncaught();
        std.process.exit(134);
    };
    drop(f);
    // (the thread object lets go of its function once it has run: what the function captured
    // may hold the thread object, as a task of Task.Run does, and shared values are not
    // collected in cycles)
    const old = t.start;
    t.start = .{ .env = null, .code = threadRan };
    drop(old);
    // (what the function wrote is seen by whoever sees this; the thread object is kept alive
    // until then, as it holds the flag)
    @atomicStore(u32, finished, 1, .release);
    drop(t);
    collectorDeinit();
    if (track) _ = @atomicRmw(isize, &ended_threads_live, .Add, @intCast(thread.stats.allocs - thread.stats.frees), .monotonic);
}

fn threadRan(_: ?*Env, _: void) Raised!void {}

/// `t.Join()`: waits for the thread to end
pub fn threadJoin(t: ThreadOf) void {
    const h = t.handle orelse return;
    h.join();
    allocator.destroy(h);
    t.handle = null;
}

/// `t.IsAlive`: started and not ended
pub fn threadIsAlive(t: ThreadOf) bool {
    return t.started and @atomicLoad(u32, &t.finished, .acquire) == 0;
}

/// `Thread.CurrentThread.ManagedThreadId`
pub fn threadId() i32 {
    return @truncate(@as(i64, @intCast(std.Thread.getCurrentId())));
}

// ---- `lock`: .NET's Monitor, re-entrant, per object address with OS futex parking ----
//
// Each locked object address gets its own MonitorNode stored in a small table guarded by a
// spinlock only while acquiring/releasing a reference count on the node. Contended callers
// sleep in the OS kernel via futex (__ulock_wait on Darwin, futex on Linux), so unrelated
// objects never collide and waiting threads do not busy-spin.

pub fn futexWait(ptr: *const u32, expect: u32) void {
    if (comptime builtin.single_threaded) return;
    switch (builtin.os.tag) {
        .macos, .ios, .tvos, .watchos, .visionos => {
            const flags: std.c.UL = .{ .op = .COMPARE_AND_WAIT, .NO_ERRNO = true };
            _ = std.c.__ulock_wait(flags, @constCast(ptr), expect, 0);
        },
        .linux => {
            _ = std.os.linux.futex_4arg(@ptrCast(ptr), .{ .cmd = .WAIT, .private = true }, expect, null);
        },
        else => std.Thread.yield() catch {},
    }
}

pub fn futexWake(ptr: *const u32, wake_all: bool) void {
    if (comptime builtin.single_threaded) return;
    switch (builtin.os.tag) {
        .macos, .ios, .tvos, .watchos, .visionos => {
            const flags: std.c.UL = .{ .op = .COMPARE_AND_WAIT, .NO_ERRNO = true, .WAKE_ALL = wake_all };
            _ = std.c.__ulock_wake(flags, @constCast(ptr), 0);
        },
        .linux => {
            _ = std.os.linux.futex_3arg(@ptrCast(ptr), .{ .cmd = .WAKE, .private = true }, if (wake_all) std.math.maxInt(i32) else 1);
        },
        else => {},
    }
}

pub fn waitUntilSet(flag: *const u32) void {
    while (@atomicLoad(u32, flag, .acquire) == 0) {
        futexWait(flag, 0);
    }
}

pub fn setAndWakeAll(flag: *u32) void {
    @atomicStore(u32, flag, 1, .release);
    futexWake(flag, true);
}

const MonitorNode = struct {
    // state: 0 = unlocked, 1 = locked (uncontended), 2 = locked (maybe waiters)
    state: u32 = 0,
    owner_valid: u32 = 0,
    owner: usize = 0,
    depth: u32 = 0,
    refs: usize = 0,
    next_free: ?*MonitorNode = null,
};

var monitor_table_lock: u32 = 0;
var monitors: std.AutoHashMapUnmanaged(usize, *MonitorNode) = .empty;
var free_monitors: ?*MonitorNode = null;

fn acquireMonitor(key: usize) *MonitorNode {
    lockField(&monitor_table_lock);
    defer unlockField(&monitor_table_lock);
    if (monitors.get(key)) |node| {
        node.refs += 1;
        return node;
    }
    const node = if (free_monitors) |head| blk: {
        free_monitors = head.next_free;
        head.* = .{ .refs = 1 };
        break :blk head;
    } else blk: {
        const fresh = bookkeeping().create(MonitorNode) catch oom();
        fresh.* = .{ .refs = 1 };
        break :blk fresh;
    };
    monitors.put(bookkeeping(), key, node) catch oom();
    return node;
}

fn releaseMonitor(key: usize, node: *MonitorNode) void {
    lockField(&monitor_table_lock);
    defer unlockField(&monitor_table_lock);
    node.refs -= 1;
    if (node.refs == 0) {
        _ = monitors.remove(key);
        node.next_free = free_monitors;
        free_monitors = node;
    }
}

pub fn lockEnter(key: usize) void {
    const node = acquireMonitor(key);
    const me: usize = if (comptime builtin.single_threaded) 1 else @intCast(std.Thread.getCurrentId());
    if (@atomicLoad(u32, &node.state, .acquire) != 0 and
        @atomicLoad(u32, &node.owner_valid, .acquire) != 0 and
        @atomicLoad(usize, &node.owner, .monotonic) == me)
    {
        node.depth += 1;
        return;
    }
    var c = @cmpxchgStrong(u32, &node.state, 0, 1, .acquire, .monotonic);
    if (c != null) {
        if (c.? == 1) c = @atomicRmw(u32, &node.state, .Xchg, 2, .acquire);
        while (c.? != 0) : (c = @atomicRmw(u32, &node.state, .Xchg, 2, .acquire)) {
            futexWait(&node.state, 2);
        }
    }
    @atomicStore(usize, &node.owner, me, .monotonic);
    @atomicStore(u32, &node.owner_valid, 1, .release);
    node.depth = 1;
}

pub fn lockExit(key: usize) void {
    const node = blk: {
        lockField(&monitor_table_lock);
        defer unlockField(&monitor_table_lock);
        break :blk monitors.get(key) orelse unreachable;
    };
    node.depth -= 1;
    if (node.depth == 0) {
        @atomicStore(u32, &node.owner_valid, 0, .monotonic);
        if (@atomicRmw(u32, &node.state, .Xchg, 0, .release) == 2) {
            futexWake(&node.state, false);
        }
    }
    releaseMonitor(key, node);
}

/// (the address a lock is taken on: of the cell; null cannot be locked)
fn lockKey(o: anytype) ?usize {
    const T = @TypeOf(o);
    if (comptime @typeInfo(T) == .optional) {
        const p = o orelse return null;
        return lockKey(p);
    }
    if (comptime @typeInfo(T) != .pointer) @compileError("fable: `lock` needs an object of a reference type, not " ++ @typeName(T));
    return @intFromPtr(o);
}

fn LockResult(comptime F: type) type {
    return @typeInfo(@typeInfo(@FieldType(F, "code")).pointer.child).@"fn".return_type.?;
}

/// `lock o (fun () -> ...)`: the function, run while this thread holds the lock of `o`
pub fn lockRun(o: anytype, f: anytype) LockResult(@TypeOf(f)) {
    const key = lockKey(o) orelse return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'obj')"));
    lockEnter(key);
    defer lockExit(key);
    return f.code(f.env, {});
}

/// `obj ()`: an object of no class of the program's, to lock on or compare by reference
pub fn objectNew() Obj {
    return objNew(&object_type, PlainObjectChain{ .own = .{} });
}

const PlainObjectChain = struct { own: struct {} };
const object_type: ObjType = objType(PlainObjectChain, "System.Object", null, &.{}, null);

/// `step(ctx, i)` for each `i` below `n`, in chunks on up to eight threads (the calling one
/// among them); what `ctx` holds must be shared already, and so must what a step leaves behind.
/// The first exception stops the others and is raised here. (Few items: here, in order.)
pub fn parallelFor(n: usize, ctx: anytype, comptime step: fn (@TypeOf(ctx), usize) Raised!void) Raised!void {
    const cpus = std.Thread.getCpuCount() catch 1;
    const workers = @min(@min(cpus, 8), n / 256);
    if (workers < 2) {
        var i: usize = 0;
        while (i < n) : (i += 1) step(ctx, i) catch return aggregated(take());
        return;
    }
    const State = struct {
        failed: ?Exn = null,
        stop: u32 = 0,

        fn chunk(st: *@This(), c: @TypeOf(ctx), lo: usize, hi: usize) void {
            var i = lo;
            while (i < hi) : (i += 1) {
                if (@atomicLoad(u32, &st.stop, .acquire) != 0) return;
                step(c, i) catch {
                    const e = take();
                    if (@cmpxchgStrong(u32, &st.stop, 0, 1, .acq_rel, .acquire) == null) {
                        // (the exception goes to the calling thread)
                        markShared(e) catch drop(take());
                        st.failed = e;
                    } else drop(e);
                    return;
                };
            }
        }

        fn worker(st: *@This(), c: @TypeOf(ctx), lo: usize, hi: usize) void {
            st.chunk(c, lo, hi);
            collectorDeinit();
            if (track) _ = @atomicRmw(isize, &ended_threads_live, .Add, @intCast(thread.stats.allocs - thread.stats.frees), .monotonic);
        }
    };
    var state: State = .{};
    var threads: [8]std.Thread = undefined;
    var started: usize = 0;
    const size = (n + workers - 1) / workers;
    var w: usize = 1;
    while (w < workers) : (w += 1) {
        const lo = @min(n, w * size);
        const hi = @min(n, lo + size);
        threads[started] = std.Thread.spawn(.{}, State.worker, .{ &state, ctx, lo, hi }) catch {
            // (no thread: this one does that chunk too)
            state.chunk(ctx, lo, hi);
            continue;
        };
        started += 1;
    }
    state.chunk(ctx, 0, @min(n, size));
    for (threads[0..started]) |t| t.join();
    if (state.failed) |e| return aggregated(e);
}

/// `Parallel.For(from, to, fun i -> ...)`: the body for each `i` from `from` below `to`, on
/// threads; what it captured is shared first
pub fn parallelForRange(from: i32, to: i32, f: anytype) Raised!void {
    if (to <= from) return;
    try markShared(f);
    const Ctx = struct { f: @TypeOf(f), from: i32 };
    const S = struct {
        fn step(c: Ctx, i: usize) Raised!void {
            return c.f.code(c.f.env, c.from + @as(i32, @intCast(i)));
        }
    };
    return parallelFor(@intCast(@as(i64, to) - from), Ctx{ .f = f, .from = from }, S.step);
}

/// (as .NET's Parallel raises an exception of its work: an AggregateException with it inside)
fn aggregated(e: Exn) Raised {
    defer drop(e);
    const agg = AggregateException.new(.{ .Message = str("One or more errors occurred.") });
    defer drop(agg);
    throw(exnWithInner(agg, e));
    return error.Raised;
}

fn notShareable(what: []const u8) Raised {
    var b: TextBuilder = .{};
    b.addAscii("The Zig target cannot share ");
    b.addAscii(what);
    b.addAscii(" between threads.");
    return raise(NotSupportedException, b.finish());
}

/// Set the shared bit of a cell: false if it was set already
fn markCell(c: anytype) Raised!bool {
    // (shared already: other threads may be changing the count; until then, no other has it)
    if (isShared(c)) return false;
    // (made in a `[<StackArena>]` function of this thread: its memory is that function's stack,
    // which another thread would free on the heap)
    if (thread.arena != null) {
        const bytes: [*]u8 = @ptrCast(c);
        if (arenaOwning(bytes[0..@sizeOf(@TypeOf(c.*))]) != null) return notShareable("a value made in a [<StackArena>] function");
    }
    // (weak references point at it: their handle moves to the table of shared cells, which a
    // thread that frees it empties)
    if (thread.weak.count() != 0) weak_refs.shareWeakHandle(@intFromPtr(c));
    // (a cell the collector follows leaves it when it is shared, unless it is part of a
    // structure of cells already, where its count is the collector's business)
    // (a cell the collector follows leaves it when it is shared, unless it is part of a
    // structure of cells already, where its count is the collector's business. The collector
    // does not look at shared cells: a cycle made through them afterwards is not freed, as
    // Koka frees no cycles at all; see Zig_Roadmap.md)
    if (gcOf(c)) |h| {
        if (sgc.inStructure(h)) return notShareable("a value that is part of a structure of cells the cycle collector follows");
    }
    c.@"$rc" |= shared_bit;
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
    if (isShared(c)) {
        _ = @atomicRmw(u32, &c.@"$rc", .Add, 1, .monotonic);
        return;
    }
    c.@"$rc" += 1;
    if (track) thread.stats.dups += 1;
    if (gcOf(c)) |h| thread.collector.onRetain(h);
}

/// Take one reference off a cell that is known to be shared.
pub inline fn release(c: anytype) void {
    if (isShared(c)) {
        _ = @atomicRmw(u32, &c.@"$rc", .Sub, 1, .release);
        return;
    }
    c.@"$rc" -= 1;
    if (track) thread.stats.decs += 1;
    if (gcOf(c)) |h| thread.collector.onRelease(h);
}

/// Take one reference off; true when it was the last one, and the caller gives up what the
/// cell holds and frees it. (False also when the cell's whole structure died with this
/// reference: the collector frees all of it, this cell included.)
pub inline fn releaseIsLast(c: anytype) bool {
    if (isShared(c)) {
        // (the last reference of any thread: what the others wrote is seen before it is freed)
        if (@atomicRmw(u32, &c.@"$rc", .Sub, 1, .acq_rel) != shared_bit | 1) return false;
        return true;
    }
    if (c.@"$rc" != 1) {
        c.@"$rc" -= 1;
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

pub inline fn free(c: anytype) void {
    if (track) thread.stats.frees += 1;
    // (a cell that weak references point at: they see it is gone. A shared cell's are in the
    // table of all threads)
    if (thread.weak.count() != 0) weakGone(@intFromPtr(c));
    if (comptime @hasField(@TypeOf(c.*), "$rc")) {
        if (isShared(c) and weak_refs.shared_count.load(.monotonic) != 0) weak_refs.sharedWeakGone(@intFromPtr(c));
    }
    // (a cell whose identity hash was taken: the next cell made here gets a new one)
    if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(c));
    // (the blocks a cell holds besides itself: an array's items, a dictionary's entries)
    if (comptime @hasDecl(@TypeOf(c.*), "fable_array")) allocator.free(c.items);
    if (comptime @hasDecl(@TypeOf(c.*), "fable_free")) @TypeOf(c.*).fable_free(c);
    allocator.destroy(c);
}

/// The items of an array, as a field of its cell.
fn isSlice(comptime T: type) bool {
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
    // (a shared resource is told it is copied)
    if (comptime isResource(T) and @hasDecl(T, "fable_dup")) {
        callHook(T.fable_dup, x);
        thread.stats.copies += 1;
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
        if (x.env) |e| {
            if (releaseIsLast(e)) e.destroy(e);
        }
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
        thread.stats.destroys += 1;
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
    const c = allocator.create(C) catch oom();
    c.* = init;
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
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

fn ifaceVtStruct(comptime N: usize, comptime names: [N][]const u8, comptime types: [N]type) type {
    const meta_name: [1][]const u8 = .{"$meta"};
    const all_names = meta_name ++ names;
    const meta_type: [1]type = .{*const IfaceMeta};
    const all_types = meta_type ++ types;
    return @Struct(.auto, null, &all_names, &all_types, &@splat(.{}));
}

pub fn IfaceAnon0() type {
    return struct {
        pub fn of() type {
            return ifaceVtStruct(0, .{}, .{});
        }
    };
}

pub fn IfaceAnon1(comptime names: [1][]const u8) type {
    return struct {
        pub fn of(comptime T1: type) type {
            return ifaceVtStruct(1, names, .{T1});
        }
    };
}

pub fn IfaceAnon2(comptime names: [2][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type) type {
            return ifaceVtStruct(2, names, .{ T1, T2 });
        }
    };
}

pub fn IfaceAnon3(comptime names: [3][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type) type {
            return ifaceVtStruct(3, names, .{ T1, T2, T3 });
        }
    };
}

pub fn IfaceAnon4(comptime names: [4][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type) type {
            return ifaceVtStruct(4, names, .{ T1, T2, T3, T4 });
        }
    };
}

pub fn IfaceAnon5(comptime names: [5][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type) type {
            return ifaceVtStruct(5, names, .{ T1, T2, T3, T4, T5 });
        }
    };
}

pub fn IfaceAnon6(comptime names: [6][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type) type {
            return ifaceVtStruct(6, names, .{ T1, T2, T3, T4, T5, T6 });
        }
    };
}

pub fn IfaceAnon7(comptime names: [7][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type) type {
            return ifaceVtStruct(7, names, .{ T1, T2, T3, T4, T5, T6, T7 });
        }
    };
}

pub fn IfaceAnon8(comptime names: [8][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type) type {
            return ifaceVtStruct(8, names, .{ T1, T2, T3, T4, T5, T6, T7, T8 });
        }
    };
}

pub fn IfaceAnon9(comptime names: [9][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type) type {
            return ifaceVtStruct(9, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9 });
        }
    };
}

pub fn IfaceAnon10(comptime names: [10][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type) type {
            return ifaceVtStruct(10, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10 });
        }
    };
}

pub fn IfaceAnon11(comptime names: [11][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type) type {
            return ifaceVtStruct(11, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11 });
        }
    };
}

pub fn IfaceAnon12(comptime names: [12][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type) type {
            return ifaceVtStruct(12, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12 });
        }
    };
}

pub fn IfaceAnon13(comptime names: [13][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type) type {
            return ifaceVtStruct(13, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13 });
        }
    };
}

pub fn IfaceAnon14(comptime names: [14][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type) type {
            return ifaceVtStruct(14, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14 });
        }
    };
}

pub fn IfaceAnon15(comptime names: [15][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type) type {
            return ifaceVtStruct(15, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15 });
        }
    };
}

pub fn IfaceAnon16(comptime names: [16][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type) type {
            return ifaceVtStruct(16, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16 });
        }
    };
}

pub fn IfaceAnon17(comptime names: [17][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type) type {
            return ifaceVtStruct(17, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17 });
        }
    };
}

pub fn IfaceAnon18(comptime names: [18][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type) type {
            return ifaceVtStruct(18, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18 });
        }
    };
}

pub fn IfaceAnon19(comptime names: [19][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type) type {
            return ifaceVtStruct(19, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19 });
        }
    };
}

pub fn IfaceAnon20(comptime names: [20][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type) type {
            return ifaceVtStruct(20, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20 });
        }
    };
}

pub fn IfaceAnon21(comptime names: [21][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type) type {
            return ifaceVtStruct(21, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21 });
        }
    };
}

pub fn IfaceAnon22(comptime names: [22][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type, comptime T22: type) type {
            return ifaceVtStruct(22, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22 });
        }
    };
}

pub fn IfaceAnon23(comptime names: [23][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type, comptime T22: type, comptime T23: type) type {
            return ifaceVtStruct(23, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23 });
        }
    };
}

pub fn IfaceAnon24(comptime names: [24][]const u8) type {
    return struct {
        pub fn of(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type, comptime T8: type, comptime T9: type, comptime T10: type, comptime T11: type, comptime T12: type, comptime T13: type, comptime T14: type, comptime T15: type, comptime T16: type, comptime T17: type, comptime T18: type, comptime T19: type, comptime T20: type, comptime T21: type, comptime T22: type, comptime T23: type, comptime T24: type) type {
            return ifaceVtStruct(24, names, .{ T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24 });
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
    const c = allocator.create(C) catch oom();
    c.* = .{ .state = .{ .thunk = dup(thunk) } };
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

/// `Lazy.CreateFromValue v`
pub fn lazyOf(comptime L: type, value: anytype) L {
    const C = @typeInfo(L).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = allocator.create(C) catch oom();
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
pub const arrayMapi = arrays.arrayMapi;
pub const arrayOf = arrays.arrayOf;
pub const arrayOfList = arrays.arrayOfList;
pub const arrayPut = arrays.arrayPut;
pub const arrayRev = arrays.arrayRev;
pub const arraySet = arrays.arraySet;
pub const arraySetAt = arrays.arraySetAt;
pub const arraySlice = arrays.arraySlice;
pub const arraySort = arrays.arraySort;
pub const arraySortDesc = arrays.arraySortDesc;
pub const arraySortInPlace = arrays.arraySortInPlace;
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
pub const FilterBuf = arrays.FilterBuf;
pub const arrayFilterNew = arrays.arrayFilterNew;
pub const arrayFilterSet = arrays.arrayFilterSet;
pub const arrayFilterFinish = arrays.arrayFilterFinish;
pub const arrayFilterAbandon = arrays.arrayFilterAbandon;
pub const indexOutside = arrays.indexOutside;
const listOf = arrays.listOf;
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
            if (c.capacity != 0) allocator.free(c.items.ptr[0..c.capacity]);
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
    const c = allocator.create(C) catch oom();
    c.* = .{};
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

pub fn raGrow(r: anytype, need: usize) void {
    if (need <= r.capacity) return;
    const cap = @max(need, @max(4, r.capacity * 2));
    const T = rItem(@TypeOf(r));
    const block = allocator.alloc(T, cap) catch oom();
    @memcpy(block[0..r.items.len], r.items);
    if (r.capacity != 0) allocator.free(r.items.ptr[0..r.capacity]);
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
            removed = allocator.alloc(T, n) catch oom();
            @memcpy(removed, r.items[at .. at + n]);
            if (gcOf(r)) |h| for (removed) |old| eachHdr(old, h, unstored);
        }
    }
    std.mem.copyForwards(T, r.items[at .. r.items.len - n], r.items[at + n ..]);
    r.items.len -= n;
    if (shared) lockExit(@intFromPtr(r));
    if (comptime isManaged(T)) {
        for (removed) |old| drop(old);
        if (n > 0) allocator.free(removed);
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
        if (old_cap != 0) allocator.free(old_items.ptr[0..old_cap]);
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
                allocator.free(c.entries.ptr[0..c.capacity]);
                allocator.free(c.buckets);
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
    const c = allocator.create(C) catch oom();
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
    const block = allocator.alloc(C.Entry, size) catch oom();
    @memcpy(block[0..d.entries.len], d.entries);
    if (d.capacity != 0) {
        allocator.free(d.entries.ptr[0..d.capacity]);
        allocator.free(d.buckets);
    }
    d.entries = block[0..d.entries.len];
    d.capacity = size;
    d.buckets = allocator.alloc(i32, size) catch oom();
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
            allocator.free(old_entries.ptr[0..old_cap]);
            allocator.free(old_buckets);
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
    defer items.deinit(allocator);
    for (d.entries) |e| {
        if (e.kv) |kv| items.append(allocator, .{ kv.key, kv.value }) catch oom();
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
    defer items.deinit(allocator);
    for (d.entries) |e| {
        if (e.kv) |kv| items.append(allocator, kv.key) catch oom();
    }
    return listOf(KeyOf(@TypeOf(d)), items.items);
}

pub fn dictValues(d: anytype) List(ValueOf(@TypeOf(d))) {
    const shared = isShared(d);
    if (shared) lockEnter(@intFromPtr(d));
    defer if (shared) lockExit(@intFromPtr(d));
    var items: std.ArrayList(ValueOf(@TypeOf(d))) = .empty;
    defer items.deinit(allocator);
    for (d.entries) |e| {
        if (e.kv) |kv| items.append(allocator, kv.value) catch oom();
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

// ---------------------------------------------------------------------------------------------
// Stack arenas: `[<StackArena(bytes)>]`
// ---------------------------------------------------------------------------------------------

/// The frame of a `[<StackArena>]` function that is running: its buffer, the arena it was called
/// inside of (arenas nest), and how many of the cells made in it are still alive. It lives in
/// that function's own stack frame.
pub const Arena = struct {
    fba: *std.heap.FixedBufferAllocator,
    outer: ?*Arena,
    live: i64 = 0,
};

/// What `allocator` was before the first arena: once one runs, `allocator` is the router
/// below, which sends each thread's allocations to its own innermost arena, or here. (Each
/// thread has its own arenas: one thread's arena never gives cells to another thread.)
var arena_base: ?std.mem.Allocator = null;
var arena_router_installed: u32 = 0;

const arena_router: std.mem.Allocator = .{ .ptr = undefined, .vtable = &.{
    .alloc = routerAlloc,
    .resize = routerResize,
    .remap = routerRemap,
    .free = routerFree,
} };

/// (the arena of this thread that holds `memory`, if any)
fn arenaOwning(memory: []u8) ?*Arena {
    var f = thread.arena;
    while (f) |a| : (f = a.outer) if (a.fba.ownsSlice(memory)) return a;
    return null;
}

fn routerAlloc(_: *anyopaque, len: usize, alignment: std.mem.Alignment, ret_addr: usize) ?[*]u8 {
    if (thread.arena) |a| {
        const p = a.fba.allocator().rawAlloc(len, alignment, ret_addr) orelse return null;
        a.live += 1;
        return p;
    }
    return arena_base.?.rawAlloc(len, alignment, ret_addr);
}

fn routerResize(_: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
    if (arenaOwning(memory)) |a| return a.fba.allocator().rawResize(memory, alignment, new_len, ret_addr);
    return arena_base.?.rawResize(memory, alignment, new_len, ret_addr);
}

fn routerRemap(_: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
    if (arenaOwning(memory)) |a| return a.fba.allocator().rawRemap(memory, alignment, new_len, ret_addr);
    return arena_base.?.rawRemap(memory, alignment, new_len, ret_addr);
}

fn routerFree(_: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
    if (arenaOwning(memory)) |a| {
        a.fba.allocator().rawFree(memory, alignment, ret_addr);
        a.live -= 1;
        return;
    }
    arena_base.?.rawFree(memory, alignment, ret_addr);
}

/// A `[<StackArena>]` function starts: the cells this thread makes come from `fba` (a buffer on
/// its stack) until it ends; an arena it calls stands in for it until that one ends. The
/// runtime's own bookkeeping stays on the allocator.
pub fn arenaEnter(frame: *Arena, fba: *std.heap.FixedBufferAllocator) void {
    if (!thread.collector_ready) collectorSetup();
    if (@cmpxchgStrong(u32, &arena_router_installed, 0, 1, .acq_rel, .acquire) == null) {
        arena_base = allocator;
        allocator = arena_router;
    } else while (@atomicLoad(u32, &arena_router_installed, .acquire) != 1 or arena_base == null) std.atomic.spinLoopHint();
    frame.* = .{ .fba = fba, .outer = thread.arena };
    thread.arena = frame;
}

/// ... and ends. A cell made in the arena that is still alive now would point into a stack
/// frame that is gone: that is a panic (counted exactly, cell by cell, in every build).
pub fn arenaLeave(frame: *Arena) void {
    thread.arena = frame.outer;
    if (frame.live != 0) @panic("fable: a value made in a [<StackArena>] function outlived it");
}

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

/// An interface a class implements: the interface (`ifaceId`) and the class's table for it
pub const IfaceImpl = struct { id: *const anyopaque, vt: *const anyopaque };

/// What tells an interface type from the others at run time (a variable of its own: constants
/// of equal values could share an address)
pub fn ifaceId(comptime I: type) *const anyopaque {
    return @ptrCast(&IfaceIdOf(I).tag);
}

fn IfaceIdOf(comptime I: type) type {
    return struct {
        var tag: u8 = @truncate(@sizeOf(I));
    };
}

/// A class's object type with the interfaces it implements
pub fn withIfaces(comptime t: ObjType, comptime ifaces: []const IfaceImpl) ObjType {
    var r = t;
    r.ifaces = ifaces;
    return r;
}

/// The table of interface `C` of the class of `p` (or of a parent class), if it implements it
fn objIfaceVt(comptime C: type, p: Obj) ?*const anyopaque {
    var t: ?*const ObjType = p.type;
    while (t) |ty| : (t = ty.parent) {
        for (ty.ifaces) |e| {
            if (e.id == ifaceId(C)) return e.vt;
        }
    }
    return null;
}

/// `o :?> C` of an object of a class that implements interface `C` (a reference of its own)
fn objAsIface(comptime C: type, p: Obj) ?C {
    const vt = objIfaceVt(C, p) orelse return null;
    retain(p);
    return C{ .data = @ptrCast(p), .vt = @ptrCast(@alignCast(vt)) };
}

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
fn ObjCell(comptime Chain: type) type {
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
        const Raw = struct { bytes: [size]u8 align(alignment) };

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
            const raw = allocator.create(Raw) catch oom();
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
            const raw = allocator.create(Raw) catch oom();
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
fn netTypeName(comptime T: type) [:0]const u8 {
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
            defer out.deinit(allocator);
            if (comptime T == String) {
                for (unitsOf(x)) |c| out.append(allocator, box(c)) catch oom();
            } else if (comptime isListType(T)) {
                var rest = x;
                while (rest == .Cons) : (rest = rest.Cons.Tail) out.append(allocator, box(rest.Cons.Head)) catch oom();
            } else {
                for (x.items) |item| out.append(allocator, box(item)) catch oom();
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
    if (x == null) return nullRef();
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
            const b = allocator.alloc(u8, need) catch oom();
            c.big = b;
            break :blk b;
        };
        const n = std.unicode.wtf16LeToWtf8(buf, units);
        buf[n] = 0;
        return @ptrCast(buf.ptr);
    }

    fn deinit(c: *CString) void {
        if (c.big) |b| allocator.free(b);
    }
};

/// What C is given for a value of type T
fn CArg(comptime T: type) type {
    if (T == String) return ?[*:0]const u8;
    if (comptime isArrayPtr(T)) return [*]@typeInfo(@FieldType(@typeInfo(T).pointer.child, "items")).pointer.child;
    return T;
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

/// `f args` of `[<DllImport>] extern R f(...)`: the C function `name`
pub fn callC(comptime R: type, comptime name: []const u8, args: anytype) R {
    const fields = @typeInfo(@TypeOf(args)).@"struct".field_types;
    const n = fields.len;
    const params = comptime blk: {
        var ps: [n]type = undefined;
        for (fields, 0..) |F, i| ps[i] = CArg(F);
        break :blk ps;
    };
    var c_args: @Tuple(&params) = undefined;
    var strings: [n]CString = undefined;
    inline for (0..n) |i| {
        const F = fields[i];
        if (F == String) {
            strings[i] = .{};
            c_args[i] = if (args[i] == null) null else strings[i].init(args[i]);
        } else if (comptime isArrayPtr(F)) {
            c_args[i] = args[i].items.ptr;
        } else {
            c_args[i] = args[i];
        }
    }
    defer inline for (0..n) |i| {
        if (fields[i] == String) strings[i].deinit();
    };
    const CR = if (R == String) ?[*:0]const u8 else R;
    const f = @extern(CFn(&params, CR), .{ .name = name });
    const r = @call(.auto, f, c_args);
    if (R == String) return if (r) |p| io.fromUtf8(std.mem.span(p)) else null;
    return r;
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
    return (@atomicLoad(u32, &c.@"$rc", .monotonic) & ~shared_bit) >= arrays.null_count / 2;
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
            fillNullCell(P, c);
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
            c.@"$rc" = 1;
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
                fillNullCell(P, &null_cell);
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
fn fillNullCell(comptime P: type, c: P) void {
    const C = @typeInfo(P).pointer.child;
    if (comptime @hasDecl(C, "fable_null_cell")) {
        // (its fields' own defaults: an empty collection, never changed, as members check)
        const gc = if (comptime @hasField(C, "$gc")) c.@"$gc" else {};
        c.* = .{};
        if (comptime @hasField(C, "$gc")) c.@"$gc" = gc;
        c.@"$rc" = arrays.null_count;
        return;
    }
    c.@"$rc" = arrays.null_count;
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

noinline fn collectorSetup() void {
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

pub fn collectorDeinit() void {
    asyncStateRelease();
    random.randomSharedRelease();
    // (the null arrays this thread made: given up before the collector goes)
    for (thread.null_arrays.items) |n| n.free(n.cell);
    thread.null_arrays.deinit(bookkeeping());
    thread.null_arrays = .empty;
    if (thread.collector_ready) thread.collector.deinit();
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
        defer allocator.free(d);
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
    destroy: *const fn (*Env) void,
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
        };
    }
    return struct {
        pub const fable_func = {};
        env: ?*Env,
        code: Code,
        code2: ?Code2 = null,
    };
}

pub fn isFunc(comptime T: type) bool {
    return @typeInfo(T) == .@"struct" and @hasDecl(T, "fable_func");
}

// ---------------------------------------------------------------------------------------------
// Interfaces: fat pointer `{ data, vt }` with a static vtable and metadata hooks
// ---------------------------------------------------------------------------------------------

pub const IfaceMeta = struct {
    retain: *const fn (?*anyopaque) void,
    drop: *const fn (?*anyopaque) void,
    share: *const fn (?*anyopaque) Raised!void,
    hdr_of: *const fn (?*anyopaque) ?*sgc.Hdr,
    as_obj: *const fn (?*anyopaque) ?Obj,
    find_box: *const fn (?*anyopaque, *const ObjType) ?Obj,
};

fn emptyRetain(_: ?*anyopaque) void {}
fn emptyDrop(_: ?*anyopaque) void {}
fn emptyShare(_: ?*anyopaque) Raised!void {}
fn emptyHdr(_: ?*anyopaque) ?*sgc.Hdr {
    return null;
}
fn emptyAsObj(_: ?*anyopaque) ?Obj {
    return null;
}
fn emptyFindBox(_: ?*anyopaque, _: *const ObjType) ?Obj {
    return null;
}

pub const empty_iface_meta: IfaceMeta = .{
    .retain = emptyRetain,
    .drop = emptyDrop,
    .share = emptyShare,
    .hdr_of = emptyHdr,
    .as_obj = emptyAsObj,
    .find_box = emptyFindBox,
};

fn objIfaceRetain(d: ?*anyopaque) void {
    if (d) |p| retain(@as(Obj, @ptrCast(@alignCast(p))));
}
fn objIfaceDrop(d: ?*anyopaque) void {
    if (d) |p| drop(@as(Obj, @ptrCast(@alignCast(p))));
}
fn objIfaceShare(d: ?*anyopaque) Raised!void {
    if (d) |p| try markShared(@as(Obj, @ptrCast(@alignCast(p))));
}
fn objIfaceHdr(d: ?*anyopaque) ?*sgc.Hdr {
    const p = d orelse return null;
    const o: Obj = @ptrCast(@alignCast(p));
    return o.gc;
}
fn objIfaceAsObj(d: ?*anyopaque) ?Obj {
    const p = d orelse return null;
    return @ptrCast(@alignCast(p));
}
fn objIfaceFindBox(d: ?*anyopaque, target_ty: *const ObjType) ?Obj {
    const p = d orelse return null;
    const o: Obj = @ptrCast(@alignCast(p));
    if (o.type == target_ty) return o;
    if (o.type.unwrap_box) |f| return f(o, target_ty);
    return null;
}

pub const obj_iface_meta: IfaceMeta = .{
    .retain = objIfaceRetain,
    .drop = objIfaceDrop,
    .share = objIfaceShare,
    .hdr_of = objIfaceHdr,
    .as_obj = objIfaceAsObj,
    .find_box = objIfaceFindBox,
};

pub const box_iface_meta = obj_iface_meta;

fn envIfaceRetain(d: ?*anyopaque) void {
    if (d) |p| retain(@as(*Env, @ptrCast(@alignCast(p))));
}
fn envIfaceDrop(d: ?*anyopaque) void {
    if (d) |p| {
        const e: *Env = @ptrCast(@alignCast(p));
        if (releaseIsLast(e)) e.destroy(e);
    }
}
fn envIfaceShare(d: ?*anyopaque) Raised!void {
    if (d) |p| {
        const e: *Env = @ptrCast(@alignCast(p));
        if (!try markCell(e)) return;
        return e.share(e);
    }
}
fn envIfaceHdr(d: ?*anyopaque) ?*sgc.Hdr {
    const p = d orelse return null;
    const e: *Env = @ptrCast(@alignCast(p));
    return e.gc;
}

pub const env_iface_meta: IfaceMeta = .{
    .retain = envIfaceRetain,
    .drop = envIfaceDrop,
    .share = envIfaceShare,
    .hdr_of = envIfaceHdr,
    .as_obj = emptyAsObj,
    .find_box = emptyFindBox,
};

pub fn upcastIfaceMeta(comptime SubIface: type) *const IfaceMeta {
    return &struct {
        fn asObj(d: ?*anyopaque) ?Obj {
            const p = d orelse return null;
            const o: Obj = @ptrCast(@alignCast(p));
            const sub = boxed(SubIface, o).value;
            return sub.vt.@"$meta".as_obj(sub.data);
        }
        fn findBox(d: ?*anyopaque, target_ty: *const ObjType) ?Obj {
            const p = d orelse return null;
            const o: Obj = @ptrCast(@alignCast(p));
            if (o.type == target_ty) return o;
            const sub = boxed(SubIface, o).value;
            return sub.vt.@"$meta".find_box(sub.data, target_ty);
        }
        const meta: IfaceMeta = .{
            .retain = objIfaceRetain,
            .drop = objIfaceDrop,
            .share = objIfaceShare,
            .hdr_of = objIfaceHdr,
            .as_obj = asObj,
            .find_box = findBox,
        };
    }.meta;
}

pub fn Iface(comptime Vt: type) type {
    return struct {
        pub const fable_iface = {};
        data: ?*anyopaque,
        vt: *const Vt,
    };
}

pub fn isIface(comptime T: type) bool {
    return @typeInfo(T) == .@"struct" and @hasDecl(T, "fable_iface");
}

/// Box `val` directly into a fat-pointer interface (consumes `val`).
pub inline fn ifaceBox(comptime I: type, comptime T: type, val: T, vt: @FieldType(I, "vt")) I {
    const o = ObjCell(BoxChain(T)).new(boxType(T), .{ .own = .{ .value = val } });
    return .{ .data = @ptrCast(o), .vt = vt };
}

/// Allocate an environment holding `captures` for an object-expression fat-pointer interface (consumes `captures`).
pub inline fn ifaceClosure(comptime I: type, comptime Captures: type, captures: Captures, vt: @FieldType(I, "vt")) I {
    if (@sizeOf(Captures) == 0) return .{ .data = null, .vt = vt };
    const E = EnvOf(Captures);
    if (comptime E.cyclic) gcTick();
    const e = allocator.create(E) catch oom();
    e.* = .{ .header = .{ .destroy = E.destroy, .share = E.share }, .captures = captures };
    if (comptime E.cyclic) {
        e.hdr = thread.collector.hdr(&E.K.desc, E.K.isLeaf(e));
        e.header.gc = &e.hdr;
    }
    if (track) thread.stats.allocs += 1;
    return .{ .data = @ptrCast(&e.header), .vt = vt };
}

// ---- generic methods of interfaces: one slot, its type parameters erased to `obj` (as Koka
// compiles polymorphism), and values converted where the slot is called ----

fn ifaceOf(comptime T: type) ?type {
    if (isIface(T)) return T;
    if (@typeInfo(T) == .optional and isIface(@typeInfo(T).optional.child)) return @typeInfo(T).optional.child;
    return null;
}

/// `x` (borrowed) as a value of type `To` (owned): the same, boxed into an object, unboxed from
/// one, or an interface adapted to its erased instantiation (or back)
pub fn erasedConv(comptime To: type, x: anytype) To {
    const From = @TypeOf(x);
    if (From == To) return dup(x);
    if (To == Any) return box(x);
    if (From == Any) {
        if (tryUnbox(?To, x)) |v| return v;
        @panic("fable: an erased value of a generic method is not of the type it is used as");
    }
    if (comptime ifaceOf(To) != null and ifaceOf(From) != null) return ifaceAdapt(To, x);
    @compileError("fable: a generic method of an interface cannot convert " ++ @typeName(From) ++ " to " ++ @typeName(To) ++ " yet");
}

/// The interface `src` (borrowed) seen as the interface type `Target`, whose members take and give
/// the same values erased to `obj` (or the other way): each member converts what it is given
/// (a member takes its arguments over, as every slot does), calls the member of `src` with them,
/// and converts what it gives back
pub fn ifaceAdapt(comptime Target: type, src: anytype) Target {
    const S = @TypeOf(src);
    const I = ifaceOf(Target).?;
    const SI = ifaceOf(S).?;
    const s: SI = if (comptime @typeInfo(S) == .optional) (src orelse return if (comptime @typeInfo(Target) == .optional) null else nullRefPanic()) else src;
    const A = IfaceAdapter(I, SI);
    return ifaceClosure(I, A.Held, .{ .c0 = dup(s) }, &A.vt);
}

fn nullRefPanic() noreturn {
    @panic("fable: a null interface given to a generic method");
}

fn erasedBack(comptime R: type, raw: anytype) R {
    const Raw = @TypeOf(raw);
    if (comptime @typeInfo(Raw) == .error_union) {
        const v = raw catch {
            if (comptime @typeInfo(R) == .error_union) return error.Raised;
            @panic("fable: an erased member raised where its slot cannot");
        };
        return erasedBack(R, v);
    }
    const Out = if (@typeInfo(R) == .error_union) @typeInfo(R).error_union.payload else R;
    const out = erasedConv(Out, raw);
    drop(raw);
    return out;
}

fn IfaceAdapter(comptime I: type, comptime SI: type) type {
    const Vt = @typeInfo(@FieldType(I, "vt")).pointer.child;
    const SVt = @typeInfo(@FieldType(SI, "vt")).pointer.child;
    return struct {
        const Held = struct { c0: SI };

        fn Thunk(comptime name: []const u8) type {
            const F = @typeInfo(@typeInfo(@FieldType(Vt, name)).pointer.child).@"fn";
            const SF = @typeInfo(@typeInfo(@FieldType(SVt, name)).pointer.child).@"fn";
            const R = F.return_type.?;
            const P = F.param_types;
            const SP = SF.param_types;
            return switch (P.len) {
                2 => struct {
                    fn f(d: ?*anyopaque, a0: P[1].?) R {
                        const c = captured(Held, @ptrCast(@alignCast(d)));
                        const x0 = erasedConv(SP[1].?, a0);
                        drop(a0);
                        return erasedBack(R, @field(c.c0.vt, name)(c.c0.data, x0));
                    }
                },
                3 => struct {
                    fn f(d: ?*anyopaque, a0: P[1].?, a1: P[2].?) R {
                        const c = captured(Held, @ptrCast(@alignCast(d)));
                        const x0 = erasedConv(SP[1].?, a0);
                        drop(a0);
                        const x1 = erasedConv(SP[2].?, a1);
                        drop(a1);
                        return erasedBack(R, @field(c.c0.vt, name)(c.c0.data, x0, x1));
                    }
                },
                4 => struct {
                    fn f(d: ?*anyopaque, a0: P[1].?, a1: P[2].?, a2: P[3].?) R {
                        const c = captured(Held, @ptrCast(@alignCast(d)));
                        const x0 = erasedConv(SP[1].?, a0);
                        drop(a0);
                        const x1 = erasedConv(SP[2].?, a1);
                        drop(a1);
                        const x2 = erasedConv(SP[3].?, a2);
                        drop(a2);
                        return erasedBack(R, @field(c.c0.vt, name)(c.c0.data, x0, x1, x2));
                    }
                },
                else => @compileError("fable: an interface member of this many parameters cannot be adapted yet"),
            };
        }

        const vt: Vt = blk: {
            var v: Vt = undefined;
            for (@typeInfo(Vt).@"struct".field_names) |name| {
                if (std.mem.eql(u8, name, "$meta")) {
                    v.@"$meta" = &env_iface_meta;
                } else {
                    @field(v, name) = Thunk(name).f;
                }
            }
            break :blk v;
        };
    };
}

/// Extract a first-class `Func` closure from a fat-pointer interface method slot (borrows `iface`).
pub fn ifaceMethod(comptime F: type, iface: anytype, comptime field: []const u8) F {
    const I = @TypeOf(iface);
    const Caps = struct { iface: I };
    const Fn = @typeInfo(@typeInfo(@FieldType(F, "code")).pointer.child).@"fn";
    const R = Fn.return_type.?;
    const P = Fn.param_types;
    const M = switch (P.len) {
        1 => struct {
            fn code(env: ?*Env) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data);
            }
        },
        2 => struct {
            fn code(env: ?*Env, a0: P[1].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0);
            }
        },
        3 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1);
            }
        },
        4 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2);
            }
        },
        5 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?, a3: P[4].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2, a3);
            }
        },
        6 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?, a3: P[4].?, a4: P[5].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2, a3, a4);
            }
        },
        7 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?, a3: P[4].?, a4: P[5].?, a5: P[6].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2, a3, a4, a5);
            }
        },
        8 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?, a3: P[4].?, a4: P[5].?, a5: P[6].?, a6: P[7].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2, a3, a4, a5, a6);
            }
        },
        9 => struct {
            fn code(env: ?*Env, a0: P[1].?, a1: P[2].?, a2: P[3].?, a3: P[4].?, a4: P[5].?, a5: P[6].?, a6: P[7].?, a7: P[8].?) R {
                const c = captured(Caps, env);
                return @field(c.iface.vt, field)(c.iface.data, a0, a1, a2, a3, a4, a5, a6, a7);
            }
        },
        else => @compileError("fable: interface method of this many arguments"),
    };
    return closure(F, Caps, .{ .iface = dup(iface) }, M.code);
}

/// Borrow the underlying `Obj` from an interface value or optional interface, if any.
pub inline fn ifaceToObjBorrow(x: anytype) ?Obj {
    const T = @TypeOf(x);
    if (comptime @typeInfo(T) == .optional) {
        const v = x orelse return null;
        return v.vt.@"$meta".as_obj(v.data);
    }
    return x.vt.@"$meta".as_obj(x.data);
}

pub fn ifaceToAnyBorrow(x: anytype) Any {
    return ifaceToObjBorrow(x);
}

pub fn ifaceIsClass(x: anytype, ty: *const ObjType) bool {
    const o = ifaceToObjBorrow(x) orelse return false;
    return objIs(o, ty);
}

pub fn ifaceCastClass(x: anytype, ty: *const ObjType) Raised!Any {
    if (comptime @typeInfo(@TypeOf(x)) == .optional) {
        if (x == null) return null;
    }
    if (ifaceToObjBorrow(x)) |o| return objCast(o, ty);
    const Short = struct {
        pub fn of(name: []const u8) []const u8 {
            return if (std.mem.lastIndexOfScalar(u8, name, '+')) |i| name[i + 1 ..] else name;
        }
    };
    var b: TextBuilder = .{};
    b.addAscii("Unable to cast object of type '<iface>' to type '");
    b.addAscii(Short.of(ty.name));
    b.addAscii("'.");
    return raise(InvalidCastException, b.finish());
}

pub fn ifaceTryUnbox(comptime OT: type, x: anytype) OT {
    const T = @typeInfo(OT).optional.child;
    const v = if (comptime @typeInfo(@TypeOf(x)) == .optional)
        (x orelse return if (T == void) {} else null)
    else
        x;
    if (T == void) return null;
    const V = @TypeOf(v);
    if (comptime V == T) return dup(v);
    if (comptime (@typeInfo(T) == .optional and @typeInfo(T).optional.child == V)) return @as(T, dup(v));
    if (T == Any or T == Obj) {
        if (ifaceToObjBorrow(v)) |o| return dup(o);
        return box(v);
    }
    if (comptime (@typeInfo(T) == .optional and isIface(@typeInfo(T).optional.child))) {
        const C = @typeInfo(T).optional.child;
        if (v.vt.@"$meta".find_box(v.data, boxType(C))) |bp| return @as(T, dup(boxed(C, bp).value));
    }
    if (v.vt.@"$meta".find_box(v.data, boxType(T))) |bp| return dup(boxed(T, bp).value);
    if (ifaceToObjBorrow(v)) |o| return tryUnbox(OT, @as(Any, o));
    return null;
}

pub fn ifaceUnbox(comptime T: type, x: anytype) Raised!T {
    const v = if (comptime @typeInfo(@TypeOf(x)) == .optional)
        (x orelse {
            if (T == void) return {};
            if (comptime @typeInfo(T) == .optional) return null;
            if (comptime isArrayPtr(T)) return arrayNull(T);
            return nullRef();
        })
    else
        x;
    const V = @TypeOf(v);
    if (comptime V == T) return dup(v);
    if (comptime (@typeInfo(T) == .optional and @typeInfo(T).optional.child == V)) return @as(T, dup(v));
    if (T == Any) return box(v);
    if (T == Obj) {
        if (ifaceToObjBorrow(v)) |o| return dup(o);
        return box(v).?;
    }
    if (comptime (@typeInfo(T) == .optional and isIface(@typeInfo(T).optional.child))) {
        const C = @typeInfo(T).optional.child;
        if (v.vt.@"$meta".find_box(v.data, boxType(C))) |bp| return @as(T, dup(boxed(C, bp).value));
    }
    if (v.vt.@"$meta".find_box(v.data, boxType(T))) |bp| return dup(boxed(T, bp).value);
    if (ifaceToObjBorrow(v)) |o| return unbox(T, @as(Any, o));
    var b: TextBuilder = .{};
    b.addAscii("Unable to cast object of type '<iface>' to type '");
    b.addAscii(netTypeName(T));
    b.addAscii("'.");
    return raise(InvalidCastException, b.finish());
}

pub fn EnvOf(comptime Captures: type) type {
    return struct {
        const Self = @This();
        const cyclic = functions_in_cycles and holdsCyclic(Captures);
        const K = Collected(
            Self,
            "hdr",
            @as(isize, @offsetOf(Self, "header")) + @as(isize, @offsetOf(Env, "$rc")) - @as(isize, @offsetOf(Self, "hdr")),
            "captures",
        );

        header: Env,
        hdr: GcHdr(cyclic) = undefined,
        captures: Captures,

        pub fn destroy(header: *Env) void {
            const self: *Self = @alignCast(@fieldParentPtr("header", header));
            drop(self.captures);
            free(self);
        }

        pub fn share(header: *Env) Raised!void {
            const self: *Self = @alignCast(@fieldParentPtr("header", header));
            try markShared(self.captures);
        }
    };
}

/// A function value that owns `captures`.
pub inline fn closure(comptime F: type, comptime Captures: type, captures: Captures, code: @FieldType(F, "code")) F {
    const E = EnvOf(Captures);
    if (comptime E.cyclic) gcTick();
    const e = allocator.create(E) catch oom();
    e.* = .{ .header = .{ .destroy = E.destroy, .share = E.share }, .captures = captures };
    if (comptime E.cyclic) {
        e.hdr = thread.collector.hdr(&E.K.desc, E.K.isLeaf(e));
        e.header.gc = &e.hdr;
    }
    if (track) thread.stats.allocs += 1;
    return .{ .env = &e.header, .code = code };
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
    const e = allocator.create(E) catch oom();
    e.* = .{ .header = .{ .destroy = E.destroy, .share = E.share }, .captures = captures };
    if (comptime E.cyclic) {
        e.hdr = thread.collector.hdr(&E.K.desc, E.K.isLeaf(e));
        e.header.gc = &e.hdr;
    }
    if (track) thread.stats.allocs += 1;
    return .{ .env = &e.header, .code = code, .code2 = code2 };
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
        const bytes = allocator.alignedAlloc(u8, .@"16", @max(size, 1)) catch return raise(OutOfMemoryException, str("Insufficient memory to continue the execution of the program."));
        @memset(bytes, 0);
        const b = allocator.create(Block) catch {
            allocator.free(bytes);
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
            allocator.free(x.bytes);
            allocator.destroy(x);
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
var ended_threads_live: isize = 0;

/// Called when the program's entry point has returned: true, with a message, if cells are
/// still allocated. Only checks in builds that keep counters.
pub fn leaked() bool {
    asyncStateRelease();
    random.randomSharedRelease();
    // (cycles that died without anything noticing yet are not leaks)
    _ = collect();
    if (!track or live() == 0) return false;
    std.debug.print("fable: {d} cell(s) were never freed (allocated {d}, freed {d}, and threads that ended {d} more than they freed)\n", .{ live(), thread.stats.allocs, thread.stats.frees, ended_threads_live });
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
// Tests (`zig test fable_rt.zig`)
// ---------------------------------------------------------------------------------------------

const TestList = union(enum) {
    Nil,
    Cons: *struct { @"$rc": u32 = 1, head: i32, tail: TestList },
};

const TestTree = union(enum) {
    Leaf,
    Node: *struct { @"$rc": u32 = 1, left: TestTree, value: i32, right: TestTree },
};

const TestPair = struct { first: TestList, second: ?TestList, n: i32 };

pub fn testCons(head: i32, tail: TestList) TestList {
    return .{ .Cons = cell(TestList, .Cons, .{ .head = head, .tail = tail }) };
}

pub fn testRange(n: i32) TestList {
    var l: TestList = .Nil;
    var i: i32 = n;
    while (i > 0) : (i -= 1) l = testCons(i, l);
    return l;
}

pub fn testTree(depth: i32) TestTree {
    if (depth == 0) return .Leaf;
    return .{ .Node = cell(TestTree, .Node, .{ .left = testTree(depth - 1), .value = depth, .right = testTree(depth - 1) }) };
}

test "a dropped list frees every cell, without recursion" {
    const before = thread.stats;
    drop(testRange(1_000_000));
    try std.testing.expectEqual(@as(i64, 1_000_000), thread.stats.allocs - before.allocs);
    try std.testing.expectEqual(@as(i64, 1_000_000), thread.stats.frees - before.frees);
}

test "a shared cell is freed by its last owner" {
    const before = thread.stats;
    const tail = testRange(3);
    const a = testCons(10, dup(tail));
    const b = testCons(20, tail);
    drop(a);
    try std.testing.expectEqual(@as(i64, 1), thread.stats.frees - before.frees);
    try std.testing.expectEqual(@as(i32, 1), b.Cons.tail.Cons.head);
    drop(b);
    try std.testing.expectEqual(@as(i64, 5), thread.stats.frees - before.frees);
}

test "trees, and values that hold cells" {
    const before = thread.stats;
    drop(testTree(10));
    try std.testing.expectEqual(@as(i64, 1023), thread.stats.frees - before.frees);
    const p = TestPair{ .first = testRange(2), .second = testRange(3), .n = 1 };
    const q = dup(p);
    drop(p);
    try std.testing.expectEqual(@as(i64, 1023), thread.stats.frees - before.frees);
    drop(q);
    try std.testing.expectEqual(@as(i64, 1028), thread.stats.frees - before.frees);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "a dead cell is built in again" {
    const before = thread.stats;
    const l = testRange(1);
    var tok: ?*Cell(TestList, .Cons) = null;
    if (isUnique(l.Cons)) tok = l.Cons;
    const m = TestList{ .Cons = cellReuse(TestList, .Cons, &tok, .{ .head = 7, .tail = .Nil }) };
    try std.testing.expectEqual(l.Cons, m.Cons);
    try std.testing.expectEqual(@as(i64, 1), thread.stats.reuses - before.reuses);
    try std.testing.expectEqual(@as(i64, 1), thread.stats.allocs - before.allocs);
    drop(m);
}

test "structural equality looks through cells" {
    const a = testRange(4);
    const b = testRange(4);
    const c = testRange(5);
    try std.testing.expect(eql(a, b));
    try std.testing.expect(!eql(a, c));
    try std.testing.expect(eql(TestPair{ .first = a, .second = null, .n = 1 }, TestPair{ .first = b, .second = null, .n = 1 }));
    try std.testing.expect(!eql(TestPair{ .first = a, .second = c, .n = 1 }, TestPair{ .first = b, .second = null, .n = 1 }));
    try std.testing.expect(eql(@as(?TestList, a), @as(?TestList, b)));
    drop(a);
    drop(b);
    drop(c);
}

pub fn testSum(xs: TestList) i32 {
    var total: i32 = 0;
    var cur = xs;
    while (cur == .Cons) : (cur = cur.Cons.tail) total += cur.Cons.head;
    return total;
}
const testSum_sig = .{ .borrows = .{true}, .result_borrowed = false };

pub fn testTail(xs: TestList) TestList {
    return if (xs == .Cons) xs.Cons.tail else .Nil;
}
const testTail_sig = .{ .borrows = .{true}, .result_borrowed = true };

pub fn testPush(n: i32, xs: TestList) TestList {
    return testCons(n, xs);
}
const testPush_sig = .{ .borrows = .{ false, false }, .result_borrowed = false };

test "a call between files costs what the callee needs" {
    const before = thread.stats;
    const xs = testRange(3);
    // borrowed by the callee, kept by the caller: nothing is counted
    try std.testing.expectEqual(@as(i32, 6), across(testSum, testSum_sig, .{.keep}, .{xs}));
    try std.testing.expectEqual(@as(i64, 0), thread.stats.dups - before.dups);
    // a borrowed result is made owned
    const t = across(testTail, testTail_sig, .{.keep}, .{xs});
    try std.testing.expectEqual(@as(i64, 1), thread.stats.dups - before.dups);
    // owned by the callee, kept by the caller: one more reference
    const ys = across(testPush, testPush_sig, .{ .plain, .keep }, .{ 0, xs });
    try std.testing.expectEqual(@as(i64, 2), thread.stats.dups - before.dups);
    // owned by the callee, given by the caller: a move
    const zs = across(testPush, testPush_sig, .{ .plain, .give }, .{ 9, ys });
    try std.testing.expectEqual(@as(i64, 2), thread.stats.dups - before.dups);
    // borrowed by the callee, given by the caller: the caller gives it up after the call
    try std.testing.expectEqual(@as(i32, 15), across(testSum, testSum_sig, .{.give}, .{zs}));
    try std.testing.expectEqual(@as(i32, 5), across(testSum, testSum_sig, .{.give}, .{t}));
    drop(xs);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

const TestFn = Func(*const fn (?*Env, i32) i32);
const TestCaptures = struct { xs: TestList, n: i32 };

pub fn testAddSum(env: ?*Env, x: i32) i32 {
    const c = captured(TestCaptures, env);
    return x + c.n + testSum(c.xs);
}

pub fn testDouble(_: ?*Env, x: i32) i32 {
    return x * 2;
}

test "a function value owns what it captured" {
    const before = thread.stats;
    const f = closure(TestFn, TestCaptures, .{ .xs = testRange(3), .n = 10 }, testAddSum);
    try std.testing.expectEqual(@as(i32, 17), f.code(f.env, 1));
    const g = dup(f);
    drop(f);
    try std.testing.expectEqual(@as(i32, 18), g.code(g.env, 2));
    const plain = TestFn{ .env = null, .code = testDouble };
    try std.testing.expectEqual(@as(i32, 8), plain.code(plain.env, 4));
    drop(dup(plain));
    // in a value that is dropped as a whole
    const pair: struct { f: TestFn, o: ?TestFn } = .{ .f = g, .o = plain };
    drop(pair);
    try std.testing.expectEqual(@as(i64, 4), thread.stats.allocs - before.allocs);
    try std.testing.expectEqual(@as(i64, 4), thread.stats.frees - before.frees);
}

const TestParseError = ExnOf("ParseError", struct { pos: i32, items: TestList });
const TestOverflow = ExnOf("Overflow", struct { limit: i32 });

pub fn testCheck(x: i32, owned: TestList) Raised!i32 {
    if (x < 0) {
        throw(TestParseError.new(.{ .pos = x, .items = owned }));
        return error.Raised;
    }
    drop(owned);
    return x;
}
const testCheck_sig = .{ .borrows = .{ false, false }, .result_borrowed = false };

pub fn testOuter(x: i32) MayRaise(i32, .{testCheck}) {
    const xs = testRange(2);
    const raw = across(testCheck, testCheck_sig, .{ .plain, .give }, .{ x, xs });
    const r = if (comptime isRaised(@TypeOf(raw))) (raw catch return error.Raised) else raw;
    return r + 1;
}

pub fn testPlain(x: i32) MayRaise(i32, .{testSum}) {
    return x;
}

test "an exception owns its fields and is taken by one handler" {
    const before = thread.stats;
    try std.testing.expectEqual(@as(i32, 6), try testOuter(5));
    try std.testing.expectError(error.Raised, testOuter(-3));
    const e = take();
    try std.testing.expect(TestParseError.is(e));
    try std.testing.expect(!TestOverflow.is(e));
    try std.testing.expectEqual(@as(i32, -3), TestParseError.of(e).pos);
    try std.testing.expectEqual(@as(i32, 3), testSum(TestParseError.of(e).items));
    const again = dup(e);
    drop(e);
    drop(again);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
    // a function that calls nothing that raises has a plain result
    try std.testing.expect(@TypeOf(testPlain(1)) == i32);
    try std.testing.expect(@TypeOf(testOuter(1)) == Raised!i32);
}

const TestNode = *struct { @"$rc": u32 = 1, id: i32, next: ?TestNode };

test "reference records: identity, stores and long chains" {
    const before = thread.stats;
    var head: TestNode = new(TestNode, .{ .id = 0, .next = null });
    var i: i32 = 1;
    while (i < 200_000) : (i += 1) head = new(TestNode, .{ .id = i, .next = head });
    const second = dup(head.next.?);
    // the field gets a new value: the old one stays alive through `second`
    store(&head.next, null);
    try std.testing.expectEqual(@as(i32, 199_998), second.id);
    const r = new(Ref(TestList), .{ .contents = testRange(3) });
    const alias = dup(r);
    store(&alias.contents, testRange(5));
    try std.testing.expectEqual(@as(i32, 15), testSum(r.contents));
    try std.testing.expect(eql(r, alias));
    drop(head);
    drop(second);
    drop(r);
    drop(alias);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

const TestPerson = *struct {
    pub const fable_cyclic = true;
    @"$rc": u32 = 1,
    @"$gc": GcHdr(fable_cyclic) = undefined,
    id: i32,
    friend: ?TestPerson,
    friends: List(TestPerson),
    callback: ?Func(*const fn (?*Env, i32) Raised!i32),
};

pub fn testPerson(id: i32) TestPerson {
    return new(TestPerson, .{ .id = id, .friend = null, .friends = .Empty, .callback = null });
}

const TestSelf = struct { self: TestPerson };

pub fn testAddId(env: ?*Env, x: i32) Raised!i32 {
    return x + captured(TestSelf, env).self.id;
}

test "cycles are freed when their last outside reference goes" {
    const before = thread.stats;
    // two records that point at each other
    const a = testPerson(1);
    const b = testPerson(2);
    storeIn(a, "friend", dup(b));
    storeIn(b, "friend", dup(a));
    drop(a);
    try std.testing.expectEqual(@as(i64, 0), thread.stats.frees - before.frees);
    drop(b);
    try std.testing.expectEqual(@as(i64, 2), thread.stats.frees - before.frees);
    // a record that reaches itself through a list
    const c = testPerson(3);
    const cons = List(TestPerson){ .Cons = cell(List(TestPerson), .Cons, .{ .Head = dup(c), .Tail = .Empty }) };
    storeIn(c, "friends", cons);
    drop(c);
    try std.testing.expectEqual(@as(i64, 4), thread.stats.frees - before.frees);
    // a record that holds a function which captured the record
    const d = testPerson(40);
    const f = closure(Func(*const fn (?*Env, i32) Raised!i32), TestSelf, .{ .self = dup(d) }, testAddId);
    storeIn(d, "callback", f);
    try std.testing.expectEqual(@as(i32, 42), try d.callback.?.code(d.callback.?.env, 2));
    drop(d);
    try std.testing.expectEqual(@as(i64, 6), thread.stats.frees - before.frees);
    // a ring with a tail hanging off it, cut loose in the middle of a structure that lives on
    const keep = testPerson(5);
    const x = testPerson(6);
    const y = testPerson(7);
    storeIn(x, "friend", dup(y));
    storeIn(y, "friend", dup(x));
    storeIn(keep, "friend", x);
    drop(y);
    storeIn(keep, "friend", null);
    _ = collect();
    try std.testing.expectEqual(@as(i64, 8), thread.stats.frees - before.frees);
    drop(keep);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
    // cells of the same types that never form a cycle are plain reference counting
    const lone = testPerson(8);
    storeIn(lone, "friends", List(TestPerson){ .Cons = cell(List(TestPerson), .Cons, .{ .Head = testPerson(9), .Tail = .Empty }) });
    drop(lone);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
    try std.testing.expect(@sizeOf(@typeInfo(@FieldType(List(i32), "Cons")).pointer.child) == 24);
}

pub fn testThreadWork(result: *i64) void {
    const before = thread.stats;
    var round: i32 = 0;
    while (round < 2000) : (round += 1) {
        const a = testPerson(round);
        const b = testPerson(round + 1);
        storeIn(a, "friend", dup(b));
        storeIn(b, "friend", dup(a));
        drop(a);
        drop(b);
    }
    throw(TestOverflow.new(.{ .limit = 1 }));
    drop(take());
    result.* = (thread.stats.allocs - before.allocs) - (thread.stats.frees - before.frees);
}

test "every thread has its own collector" {
    if (!sgc.per_thread) return;
    var left: [4]i64 = @splat(-1);
    var threads: [4]std.Thread = undefined;
    for (&threads, &left) |*t, *l| t.* = try std.Thread.spawn(.{}, testThreadWork, .{l});
    for (threads) |t| t.join();
    for (left) |l| try std.testing.expectEqual(@as(i64, 0), l);
}

test "the collector can be stepped and tuned" {
    const before = thread.stats;
    collectorSet(.free_budget, 2);
    const a = testPerson(1);
    const b = testPerson(2);
    const c = testPerson(3);
    storeIn(a, "friend", dup(b));
    storeIn(b, "friend", dup(c));
    storeIn(c, "friend", dup(a));
    drop(a);
    drop(b);
    drop(c);
    // dead, and queued: freed a few cells at a time
    try std.testing.expect(thread.stats.frees - before.frees < 3);
    var steps: i32 = 0;
    while (collectStep(1)) steps += 1;
    try std.testing.expect(steps > 0);
    try std.testing.expectEqual(@as(i64, 3), thread.stats.frees - before.frees);
    collectorSet(.free_budget, 0);
    collectorPause();
    collectorResume();
    try std.testing.expectEqual(@as(i32, 0), collect());
}

test "storing a composite value with two cyclic cells does not double-count" {
    const before = thread.stats;
    const Fn = Func(*const fn (?*Env, i32) Raised!i32);
    const Pair = struct { first: Fn, second: Fn };
    const Cap = struct { box: Ref(?Pair) };
    const r = new(Ref(?Pair), .{ .contents = null });
    const f1 = closure(Fn, Cap, .{ .box = dup(r) }, struct {
        fn call(_: ?*Env, x: i32) Raised!i32 {
            return x;
        }
    }.call);
    const f2 = closure(Fn, Cap, .{ .box = dup(r) }, struct {
        fn call(_: ?*Env, x: i32) Raised!i32 {
            return x;
        }
    }.call);
    storeIn(r, "contents", .{ .first = f1, .second = f2 });
    const f2_keep = dup(r.contents.?.second);
    storeIn(r, "contents", null);
    drop(f2_keep);
    drop(r);
    _ = collect();
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

pub fn expectText(expected: []const u8, s: String) !void {
    var buf: [512]u8 = undefined;
    const n = std.unicode.wtf16LeToWtf8(&buf, unitsOf(s));
    try std.testing.expectEqualStrings(expected, buf[0..n]);
    drop(s);
}

test "strings: literals, concatenation, comparison" {
    const before = thread.stats;
    const hello = str("héllo");
    try std.testing.expectEqual(@as(i32, 5), try strLen(hello));
    try std.testing.expectEqual(@as(u16, 0xE9), try strAt(hello, 1));
    const both = strConcat(hello, str(" wörld"));
    try std.testing.expectEqual(@as(i32, 11), try strLen(both));
    const again = dup(both);
    try std.testing.expect(eql(both, again));
    try std.testing.expect(eql(str("ab"), str("ab")) and !eql(str("ab"), str("ac")));
    try std.testing.expect(strConcat(str(""), hello) == hello);
    drop(both);
    drop(again);
    drop(hello);
    // (a literal is never counted: only `both` was allocated)
    try std.testing.expectEqual(@as(i64, 1), thread.stats.allocs - before.allocs);
    try std.testing.expectEqual(@as(i64, 1), thread.stats.frees - before.frees);
    // an emoji is two units
    try std.testing.expectEqual(@as(i32, 2), try strLen(str("\u{1F600}")));
}

test "format follows F# and .NET" {
    const name = str("list");
    try expectText("list has 3 items", format(.{ name, " has ", @as(i32, 3), " items" }));
    try expectText("n=   42|42   |00042|-0042|+7| 7|  +42|+42  ", format(.{
        "n=", arg(.{ .kind = 'd', .width = 5 }, @as(i32, 42)),
        "|",  arg(.{ .kind = 'd', .width = 5, .left = true }, @as(i32, 42)),
        "|",  arg(.{ .kind = 'd', .width = 5, .zero = true }, @as(i32, 42)),
        "|",  arg(.{ .kind = 'd', .width = 5, .zero = true }, @as(i32, -42)),
        "|",  arg(.{ .kind = 'd', .plus = true }, @as(i32, 7)),
        "|",  arg(.{ .kind = 'd', .space = true }, @as(i32, 7)),
        "|",  arg(.{ .kind = 'd', .width = 5, .plus = true }, @as(i32, 42)),
        "|",  arg(.{ .kind = 'd', .width = 5, .plus = true, .left = true }, @as(i32, 42)),
    }));
    try expectText("ff FF 377 ffffffff 4294967295 -9223372036854775808", format(.{
        arg(.{ .kind = 'x' }, @as(i32, 255)), " ", arg(.{ .kind = 'X' }, @as(i32, 255)),                  " ",
        arg(.{ .kind = 'o' }, @as(i32, 255)), " ", arg(.{ .kind = 'x' }, @as(i32, -1)),                   " ",
        arg(.{ .kind = 'u' }, @as(i32, -1)),  " ", arg(.{ .kind = 'd' }, @as(i64, std.math.minInt(i64))),
    }));
    try expectText("true True A é", format(.{
        arg(.{ .kind = 'b' }, true), " ", true, " ", arg(.{ .kind = 'c' }, @as(u16, 'A')), " ", arg(.{ .kind = 'c' }, @as(u16, 0xE9)),
    }));
    try expectText("[  ab]", format(.{ "[", arg(.{ .kind = 's', .width = 4 }, str("ab")), "]" }));
}

pub fn expectFloat(expected: []const u8, comptime spec: Spec, value: anytype) !void {
    var buf: [scratch_len]u8 = undefined;
    try std.testing.expectEqualStrings(expected, floatText(spec, value, &buf));
}

test "floats are written as .NET writes them" {
    const f: Spec = .{ .kind = 'f' };
    const e: Spec = .{ .kind = 'e' };
    const g: Spec = .{ .kind = 'g' };
    // (every expected text here is what .NET 10 prints)
    // %f: the exact value, a tie to the even digit
    try expectFloat("3.141590", f, @as(f64, 3.14159));
    try expectFloat("2.67", .{ .kind = 'f', .precision = 2 }, @as(f64, 2.675));
    try expectFloat("0.12", .{ .kind = 'f', .precision = 2 }, @as(f64, 0.125));
    try expectFloat("0.38", .{ .kind = 'f', .precision = 2 }, @as(f64, 0.375));
    try expectFloat("0.62", .{ .kind = 'f', .precision = 2 }, @as(f64, 0.625));
    try expectFloat("1.00", .{ .kind = 'f', .precision = 2 }, @as(f64, 1.005));
    try expectFloat("0", .{ .kind = 'f', .precision = 0 }, @as(f64, 0.5));
    try expectFloat("2", .{ .kind = 'f', .precision = 0 }, @as(f64, 1.5));
    try expectFloat("2", .{ .kind = 'f', .precision = 0 }, @as(f64, 2.5));
    try expectFloat("1.000", .{ .kind = 'f', .precision = 3 }, @as(f64, 1.0005));
    try expectFloat("10000000000000000000000.000000", f, @as(f64, 1e22));
    try expectFloat("-0.000000", f, @as(f64, -0.0));
    try expectFloat("0.000000", f, @as(f64, 1e-7));
    try expectFloat("0.000", .{ .kind = 'f', .precision = 3 }, std.math.floatTrueMin(f64));
    try expectFloat("0.100000", f, @as(f32, 0.1));
    try expectFloat("0.1000000015", .{ .kind = 'f', .precision = 10 }, @as(f32, 0.1));
    try expectFloat("+1.500000", .{ .kind = 'f', .plus = true }, @as(f64, 1.5));
    try expectFloat(" 1.500000", .{ .kind = 'f', .space = true }, @as(f64, 1.5));
    try expectFloat("999.999000", f, @as(f64, 999.999));
    try expectFloat("1000.00", .{ .kind = 'f', .precision = 2 }, @as(f64, 999.999));
    // %e
    try expectFloat("1.500000e+020", e, @as(f64, 1.5e20));
    try expectFloat("1.500000E-020", .{ .kind = 'E' }, @as(f64, 1.5e-20));
    try expectFloat("1.23e+004", .{ .kind = 'e', .precision = 2 }, @as(f64, 12345.678));
    try expectFloat("0.000000e+000", e, @as(f64, 0.0));
    try expectFloat("2e+000", .{ .kind = 'e', .precision = 0 }, @as(f64, 2.5));
    try expectFloat("1.2e+000", .{ .kind = 'e', .precision = 1 }, @as(f64, 1.25));
    try expectFloat("1.4e+000", .{ .kind = 'e', .precision = 1 }, @as(f64, 1.35));
    try expectFloat("1.000000e+023", e, @as(f64, 1e23));
    try expectFloat("1.000000e+011", e, @as(f64, 9.9999999e10));
    try expectFloat("-1.234e-004", .{ .kind = 'e', .precision = 3 }, @as(f64, -0.00012345));
    try expectFloat("4.940656e-324", e, std.math.floatTrueMin(f64));
    try expectFloat("1.000000e-001", e, @as(f32, 0.1));
    // %g
    try expectFloat("3", g, @as(f64, 3.0));
    try expectFloat("1e+20", g, @as(f64, 1e20));
    try expectFloat("0.0001", g, @as(f64, 0.0001));
    try expectFloat("1e-05", g, @as(f64, 0.00001));
    try expectFloat("3.14159", g, @as(f64, 3.14159265));
    try expectFloat("123456", g, @as(f64, 123456.0));
    try expectFloat("1.23457e+06", g, @as(f64, 1234567.0));
    try expectFloat("100000", g, @as(f64, 100000.0));
    try expectFloat("1e+06", g, @as(f64, 1000000.0));
    try expectFloat("1E-20", .{ .kind = 'G' }, @as(f64, 1e-20));
    try expectFloat("3.14", .{ .kind = 'g', .precision = 3 }, @as(f64, 3.14159));
    try expectFloat("1.23e+03", .{ .kind = 'g', .precision = 3 }, @as(f64, 1234.0));
    try expectFloat("10", g, @as(f64, 9.9999995));
    try expectFloat("-0", g, @as(f64, -0.0));
    try expectFloat("0.1", g, @as(f32, 0.1));
    try expectFloat("1.79769e+308", g, std.math.floatMax(f64));
    try expectFloat("2.5", .{ .kind = 'g', .precision = 0 }, @as(f64, 2.5));
    try expectFloat("1.2345678901234568e+17", .{ .kind = 'g', .precision = 0 }, @as(f64, 123456789012345678.0));
    try expectFloat("2", .{ .kind = 'g', .precision = 1 }, @as(f64, 2.5));
    try expectFloat("0.3", .{ .kind = 'g', .precision = 1 }, @as(f64, 0.35));
    try expectFloat("0.10000000000000000555", .{ .kind = 'g', .precision = 20 }, @as(f64, 0.1));
    // `string x`
    const p: Spec = .{};
    try expectFloat("1", p, @as(f64, 1.0));
    try expectFloat("1.5", p, @as(f64, 1.5));
    try expectFloat("-0", p, @as(f64, -0.0));
    try expectFloat("0.0001", p, @as(f64, 0.0001));
    try expectFloat("1E-05", p, @as(f64, 0.00001));
    try expectFloat("1.5E-05", p, @as(f64, 1.5e-5));
    try expectFloat("100000000000000", p, @as(f64, 1e14));
    try expectFloat("10000000000000000", p, @as(f64, 1e16));
    try expectFloat("15000000000000000", p, @as(f64, 1.5e16));
    try expectFloat("1E+17", p, @as(f64, 1e17));
    try expectFloat("1.2345678901234568E+17", p, @as(f64, 123456789012345678.0));
    try expectFloat("1E+20", p, @as(f64, 1e20));
    try expectFloat("1.7976931348623157E+308", p, std.math.floatMax(f64));
    try expectFloat("5E-324", p, std.math.floatTrueMin(f64));
    try expectFloat("NaN", p, std.math.nan(f64));
    try expectFloat("-Infinity", p, -std.math.inf(f64));
    try expectFloat("0.1", p, @as(f32, 0.1));
    try expectFloat("16777216", p, @as(f32, 16777216.0));
    try expectFloat("100000000", p, @as(f32, 1e8));
    try expectFloat("1E+09", p, @as(f32, 1e9));
    try expectFloat("123456790", p, @as(f32, 123456789.0));
    try expectFloat("3E-05", p, @as(f32, 3.0e-5));
    try expectFloat("3.4028235E+38", p, std.math.floatMax(f32));
}

test "compare gives what .NET gives" {
    const P = struct { Name: String, Age: i32 };
    try std.testing.expectEqual(@as(i32, -1), compare(P{ .Name = str("a"), .Age = 2 }, P{ .Name = str("a"), .Age = 3 }));
    try std.testing.expectEqual(@as(i32, 1), compare(@as(?i32, 1), @as(?i32, null)));
    try std.testing.expectEqual(@as(i32, -1), compare(@as(struct { i32, i32 }, .{ 1, 2 }), @as(struct { i32, i32 }, .{ 1, 3 })));
    try std.testing.expect(hash(P{ .Name = str("a"), .Age = 2 }) == hash(P{ .Name = str("a"), .Age = 2 }) and hash(@as(i32, -7)) == -7);
    try std.testing.expectEqual(@as(i32, -1), compare(str("abc"), str("abd")));
    try std.testing.expectEqual(@as(i32, 1), compare(str("b"), str("abc")));
    try std.testing.expectEqual(@as(i32, 32), compare(str("a"), str("A")));
    try std.testing.expectEqual(@as(i32, 131), compare(str("é"), str("f")));
    try std.testing.expectEqual(@as(i32, -97), compare(str(""), str("a")));
    try std.testing.expectEqual(@as(i32, -2), compare(str("ab"), str("abcd")));
    try std.testing.expectEqual(@as(i32, 0), compare(str("ab"), str("ab")));
    try std.testing.expectEqual(@as(i32, -1), compare(@as(i32, 1), @as(i32, 2)));
    try std.testing.expectEqual(@as(i32, 1), compare(true, false));
    try std.testing.expectEqual(@as(i32, -1), compare(@as(u16, 'a'), @as(u16, 'c')));
    const nan = std.math.nan(f64);
    try std.testing.expectEqual(@as(i32, -1), compare(nan, @as(f64, 1.0)));
    try std.testing.expectEqual(@as(i32, 1), compare(@as(f64, 1.0), nan));
    try std.testing.expectEqual(@as(i32, 0), compare(nan, nan));
}

test "a failure carries its message" {
    const before = thread.stats;
    throw(Failure.new(.{ .Message = format(.{ "bad ", @as(i32, 7) }) }));
    const e = take();
    try std.testing.expect(Failure.is(e) and !ArgumentException.is(e));
    try expectText("bad 7", exnMessage(e));
    drop(e);
    const other = ArgumentException.new(.{ .Message = str("no") });
    try std.testing.expect(!Failure.is(other) and ArgumentException.is(other));
    try expectText("no", exnMessage(other));
    drop(other);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

pub fn expectRaised(comptime C: type, expected: []const u8, result: anytype) !void {
    if (result) |value| {
        drop(value);
        return error.TestExpectedError;
    } else |_| {}
    const e = take();
    defer drop(e);
    try std.testing.expect(C.is(e));
    try expectText(expected, exnMessage(e));
}

test "string methods do what .NET does" {
    const before = thread.stats;
    const abc = str("abc");
    const none: String = null;
    try expectText("bc", try strSubstring(abc, 1, null));
    try expectText("b", try strSubstring(abc, 1, 1));
    try expectText("", try strSubstring(abc, 3, null));
    try expectRaised(ArgumentOutOfRangeException, "startIndex cannot be larger than length of string. (Parameter 'startIndex')", strSubstring(abc, 5, null));
    try expectRaised(ArgumentOutOfRangeException, "Index and length must refer to a location within the string. (Parameter 'length')", strSubstring(abc, 1, 5));
    try expectRaised(ArgumentOutOfRangeException, "startIndex ('-1') must be a non-negative value. (Parameter 'startIndex')\nActual value was -1.", strSubstring(abc, -1, null));
    try expectRaised(ArgumentOutOfRangeException, "length ('-1') must be a non-negative value. (Parameter 'length')\nActual value was -1.", strSubstring(abc, 2, -1));
    try expectRaised(NullReferenceException, "Object reference not set to an instance of an object.", strSubstring(none, 1, null));
    try expectRaised(NullReferenceException, "Object reference not set to an instance of an object.", strLen(none));
    try expectRaised(IndexOutOfRangeException, "Index was outside the bounds of the array.", strAt(abc, 5));
    try expectRaised(IndexOutOfRangeException, "Index was outside the bounds of the array.", strAt(abc, -1));
    try std.testing.expectEqual(@as(i32, 0), strLength(none));
    try std.testing.expectEqual(@as(i32, 2), try strIndexOfChar(abc, 'c', 0));
    try std.testing.expectEqual(@as(i32, -1), try strIndexOf(abc, str("c"), 3));
    try std.testing.expectEqual(@as(i32, 0), try strIndexOf(abc, str(""), 0));
    try std.testing.expectEqual(@as(i32, 3), try strLastIndexOf(abc, str("")));
    try std.testing.expectEqual(@as(i32, 0), try strLastIndexOfChar(abc, 'a'));
    try expectRaised(ArgumentOutOfRangeException, index_range ++ " (Parameter 'startIndex')", strIndexOf(abc, str("c"), 4));
    try expectRaised(ArgumentNullException, "Value cannot be null. (Parameter 'value')", strIndexOf(abc, none, 0));
    try expectRaised(ArgumentNullException, "Value cannot be null. (Parameter 'value')", strContains(abc, none));
    try std.testing.expect(try strContains(abc, str("bc")) and try strStartsWith(abc, str("")) and try strEndsWith(abc, str("bc")));
    try std.testing.expect(try strContainsChar(abc, 'b') and try strStartsWithChar(abc, 'a') and !try strEndsWithChar(abc, 'a'));
    try expectText("Ǆ STRAßE ΐ İI", try strCase(str("ǅ straße ΐ İi"), true));
    try expectText("ǆ strasse İi σ", try strCase(str("ǅ STRASSE İI Σ"), false));
    try expectText("x y", try strTrim(str(" \t\n\u{a0}\u{2003}x y\u{3000}\u{85} "), true, true, null));
    try expectText("a ", try strTrim(str(" a "), true, false, null));
    try expectText(" a", try strTrim(str(" a "), false, true, null));
    try expectText("a", try strTrim(str("xxaxx"), true, true, 'x'));
    try expectText("azcazc", try strReplaceChar(str("abcabc"), 'b', 'z'));
    try expectText("aa", try strReplace(str("abcabc"), str("bc"), str("")));
    try expectText("ac", try strReplace(abc, str("b"), none));
    try expectRaised(ArgumentException, "The value cannot be an empty string. (Parameter 'oldValue')", strReplace(abc, str(""), str("x")));
    try expectRaised(ArgumentNullException, "Value cannot be null. (Parameter 'oldValue')", strReplace(abc, none, str("x")));
    try expectText("aXYbc", try strInsert(abc, 1, str("XY")));
    try expectRaised(ArgumentOutOfRangeException, "startIndex ('5') must be less than or equal to '3'. (Parameter 'startIndex')\nActual value was 5.", strInsert(abc, 5, str("x")));
    try expectRaised(ArgumentOutOfRangeException, "startIndex ('4294967295') must be less than or equal to '3'. (Parameter 'startIndex')\nActual value was 4294967295.", strInsert(abc, -1, str("x")));
    try expectText("a", try strRemove(abc, 1, null));
    try expectText("ac", try strRemove(abc, 1, 1));
    try expectRaised(ArgumentOutOfRangeException, "startIndex cannot be larger than length of string. (Parameter 'startIndex')", strRemove(abc, 5, null));
    try expectRaised(ArgumentOutOfRangeException, "StartIndex cannot be less than zero. (Parameter 'startIndex')", strRemove(abc, -1, null));
    try expectRaised(ArgumentOutOfRangeException, "count ('5') must be less than or equal to '2'. (Parameter 'count')\nActual value was 5.", strRemove(abc, 1, 5));
    try expectText("  abc", try strPad(abc, true, 5, ' '));
    try expectText("abc..", try strPad(abc, false, 5, '.'));
    try expectRaised(ArgumentOutOfRangeException, "totalWidth ('-1') must be a non-negative value. (Parameter 'totalWidth')\nActual value was -1.", strPad(abc, true, -1, ' '));
    try expectText("xxx", try strOfChar('x', 3));
    try expectText("ababab", try strReplicate(3, str("ab")));
    try expectRaised(ArgumentException, "The input must be non-negative.\ncount = -1 (Parameter 'count')", strReplicate(-1, str("a")));
    try expectText("", strConcat(none, none));
    try std.testing.expect(strConcat(none, none) != null and strIsNullOrEmpty(none) and strIsNullOrWhiteSpace(str(" \t")));
    try std.testing.expect(!eql(none, str("")) and eql(none, none));
    try std.testing.expectEqual(@as(i32, -1), compare(none, str("")));
    try std.testing.expectEqual(@as(i32, 1), compare(str(""), none));
    try expectText("|     |<null>|", format(.{ arg(.{ .kind = 's' }, none), "|", arg(.{ .kind = 's', .width = 5 }, none), "|", arg(.{ .kind = 'O' }, none), "|", none }));
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "case mapping is .NET's for every code unit" {
    var upper: u32 = 0;
    var lower: u32 = 0;
    for (0..0x10000) |c| {
        upper = upper *% 31 +% unicode.toUpper(@intCast(c));
        lower = lower *% 31 +% unicode.toLower(@intCast(c));
    }
    // (the same sums over Char.ToUpperInvariant and Char.ToLowerInvariant on .NET 10)
    try std.testing.expectEqual(@as(u32, 4105874476), upper);
    try std.testing.expectEqual(@as(u32, 3480348820), lower);
}

pub fn expectNet(expected: []const u8, comptime fmt: []const u8, value: anytype) !void {
    var buf: [scratch_len]u8 = undefined;
    try std.testing.expectEqualStrings(expected, netText(fmt, value, &buf));
}

test ".NET's standard numeric formats" {
    const x: f64 = 1234.5678;
    try expectNet("1,234.57", "N2", x);
    try expectNet("1,235", "N0", x);
    try expectNet("1,234.57", "N", x);
    try expectNet("1234.6", "F1", x);
    try expectNet("1235", "F0", x);
    try expectNet("1.23E+003", "E2", x);
    try expectNet("1.234568e+003", "e", x);
    try expectNet("1234.5678", "G", x);
    try expectNet("1.23E+03", "G3", x);
    try expectNet("1.2e+03", "g2", x);
    try expectNet("1234.5678", "R", x);
    try expectNet("123,456.8 %", "P1", x);
    try expectNet("123,456.78 %", "P", x);
    try expectNet("\xA41,234.57", "C", x);
    try expectNet("(\xA41,234.57)", "C", -x);
    try expectNet("-123,456.78 %", "P", -x);
    try expectNet("1E+03", "G1", x);
    try expectNet("1234.5678", "G10", x);
    try expectNet("42", "D", @as(i32, 42));
    try expectNet("00042", "D5", @as(i32, 42));
    try expectNet("2A", "X", @as(i32, 42));
    try expectNet("002a", "x4", @as(i32, 42));
    try expectNet("42.00", "N2", @as(i32, 42));
    try expectNet("4.20E+001", "E2", @as(i32, 42));
    try expectNet("4,200 %", "P0", @as(i32, 42));
    try expectNet("\xA442.00", "C", @as(i32, 42));
    try expectNet("00101010", "B8", @as(i32, 42));
    try expectNet("-0001234567", "D10", @as(i32, -1234567));
    try expectNet("FFED2979", "X", @as(i32, -1234567));
    try expectNet("-1,234,567.0", "N1", @as(i32, -1234567));
    try expectNet("(\xA41,234,567.00)", "C", @as(i32, -1234567));
    try expectNet("-123,456,700 %", "P0", @as(i32, -1234567));
    try expectNet("-1.235E+006", "E3", @as(i32, -1234567));
    try expectNet("-1.235E+06", "G4", @as(i32, -1234567));
    try expectNet("1,234,567,890,123", "N0", @as(i64, 1234567890123));
    try expectNet("FF", "X", @as(i8, -1));
    try expectNet("ffffffffffffffff", "x", @as(i64, -1));
    try expectNet("00065535", "D8", @as(u16, 65535));
    try expectNet("0", "N0", @as(i32, 0));
    try expectNet("0.00E+000", "E2", @as(i32, 0));
    try expectNet("1.23E+04", "G3", @as(i32, 12345));
    try expectNet("12345", "G", @as(i32, 12345));
    try expectNet("1.2E+04", "G2", @as(i64, 12345));
    try expectNet("0.00", "N2", @as(f64, 0.0));
    try expectNet("-0", "N0", @as(f64, -0.5));
    try expectNet("-0.0", "F1", @as(f64, -0.0));
    try expectNet("0.12", "F2", @as(f64, 0.125));
    try expectNet("2.67", "F2", @as(f64, 2.675));
    try expectNet("2", "F0", @as(f64, 2.5));
    try expectNet("2", "N0", @as(f64, 1.5));
    try expectNet("100,000,000,000,000,000,000", "N0", @as(f64, 1e20));
    try expectNet("1E+008", "E0", @as(f64, 123456789.0));
    try expectNet("0.00012", "G2", @as(f64, 0.000123));
    try expectNet("1000000000000000", "G", @as(f64, 1e15));
    try expectNet("1E-05", "G", @as(f64, 1e-5));
    try expectNet("1.2345678901234568E+17", "G", @as(f64, 123456789012345678.0));
    try expectNet("1E+02", "G2", @as(f64, 100.0));
    try expectNet("0.10000000000000001", "G17", @as(f64, 0.1));
    try expectNet("NaN", "N2", std.math.nan(f64));
    try expectNet("-Infinity", "E2", -std.math.inf(f64));
    try expectNet("0.100", "F3", @as(f32, 0.1));
    try expectNet("0.1", "G", @as(f32, 0.1));
    try expectNet("0.1000000015", "N10", @as(f32, 0.1));
    try expectText("   42|42   |     1,234.6", format(.{
        arg(.{ .width = 5 }, @as(i32, 42)), "|", arg(.{ .width = 5, .left = true }, @as(i32, 42)), "|", arg(.{ .width = 12, .net = "N1" }, x),
    }));
}

pub fn run(comptime c: u8, comptime n: usize) *const [n]u8 {
    return &@as([n]u8, @splat(c));
}

const ShowPerson = struct { Name: String, Age: i32 };
const ShowShape = union(enum) {
    A,
    B: struct { Item: i32 },
    C: struct { Item1: String, Item2: i32 },
    D: struct { Item: ShowPerson },
    F: struct { Item: struct { i32, i32 } },
};
const ShowTree = union(enum) {
    Leaf,
    Node: *struct { @"$rc": u32 = 1, Item1: ShowTree, Item2: i32, Item3: ShowTree },
};
const ShowRing = *struct { @"$rc": u32 = 1, Count: i32, Next: ?ShowRing };
const ShowErr = ExnOf("MyErr", struct { Data0: i32, Data1: String });

pub fn testList(comptime T: type, items: []const T) List(T) {
    var all: List(T) = .Empty;
    var i = items.len;
    while (i > 0) {
        i -= 1;
        const tail = all;
        all = .{ .Cons = cell(List(T), .Cons, .{ .Head = dup(items[i]), .Tail = tail }) };
    }
    return all;
}

pub fn expectAny(expected: []const u8, x: anytype) !void {
    try expectText(expected, anyText(x));
}

test "%A writes what F# writes" {
    const before = thread.stats;
    try expectAny("1", @as(i32, 1));
    try expectAny("1uy", @as(u8, 1));
    try expectAny("-1y", @as(i8, -1));
    try expectAny("1L", @as(i64, 1));
    try expectAny("1UL", @as(u64, 1));
    try expectAny("1.0", @as(f64, 1.0));
    try expectAny("-0.0", @as(f64, -0.0));
    try expectAny("1e+20", @as(f64, 1e20));
    try expectAny("1e-05", @as(f64, 1e-5));
    try expectAny("123456789.1", @as(f64, 123456789.123456789));
    try expectAny("1.23456789e+12", @as(f64, 1234567890123.0));
    try expectAny("1.0f", @as(f32, 1.0));
    try expectAny("1.5f", @as(f32, 1.5));
    try expectAny("1e+10f", @as(f32, 1e10));
    try expectAny("nan", std.math.nan(f64));
    try expectAny("nanf", std.math.nan(f32));
    try expectAny("-infinity", -std.math.inf(f64));
    try expectAny("'a'", @as(u16, 'a'));
    try expectAny("'\\010'", @as(u16, '\n'));
    try expectAny("'\\''", @as(u16, '\''));
    try expectAny("'\"'", @as(u16, '"'));
    try expectAny("'\\\\'", @as(u16, '\\'));
    try expectAny("'\\000'", @as(u16, 0));
    try expectAny("\"q\"uote\"", str("q\"uote"));
    try expectAny("<null>", @as(String, null));
    try expectAny("()", {});
    try expectAny("(1, \"a\")", @as(struct { i32, String }, .{ 1, str("a") }));
    try expectAny("Some 1", @as(?i32, 1));
    try expectAny("None", @as(?i32, null));
    try expectAny("Some (Some 1)", @as(??i32, @as(?i32, 1)));
    try expectAny("Some None", @as(??i32, @as(?i32, null)));
    try expectAny("Some (1, 2)", @as(?struct { i32, i32 }, .{ 1, 2 }));
    try expectAny("Some -1", @as(?i32, -1));
    try expectAny("A", @as(ShowShape, .A));
    try expectAny("B 1", @as(ShowShape, .{ .B = .{ .Item = 1 } }));
    try expectAny("C (\"x\", 2)", @as(ShowShape, .{ .C = .{ .Item1 = str("x"), .Item2 = 2 } }));
    try expectAny("F (1, 2)", @as(ShowShape, .{ .F = .{ .Item = .{ 1, 2 } } }));
    try expectAny("Some A", @as(?ShowShape, .A));
    try expectAny("Some (B 1)", @as(?ShowShape, .{ .B = .{ .Item = 1 } }));
    const ann: ShowPerson = .{ .Name = str("Ann"), .Age = 3 };
    try expectAny("{ Name = \"Ann\"\n  Age = 3 }", ann);
    try expectAny("D { Name = \"Ann\"\n    Age = 3 }", @as(ShowShape, .{ .D = .{ .Item = ann } }));
    try expectAny("{ Name = null\n  Age = 3 }", @as(ShowPerson, .{ .Name = null, .Age = 3 }));
    try expectAny(
        "{ Inner = { Name = \"Ann\"\n            Age = 3 }\n  Opt = Some 1 }",
        @as(struct { Inner: ShowPerson, Opt: ?i32 }, .{ .Inner = ann, .Opt = 1 }),
    );

    const three = testList(i32, &.{ 1, 2, 3 });
    try expectAny("[1; 2; 3]", three);
    try expectAny("Some [1; 2; 3]", @as(?List(i32), three));
    drop(three);
    try expectAny("[]", @as(List(i32), .Empty));
    var numbers: [120]i32 = undefined;
    for (&numbers, 1..) |*n, i| n.* = @intCast(i);
    const forty = testList(i32, numbers[0..40]);
    try expectAny(
        "[1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22;\n" ++
            " 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40]",
        forty,
    );
    drop(forty);
    const many = testList(i32, &numbers);
    try expectAny(
        "[1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22;\n" ++
            " 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35; 36; 37; 38; 39; 40; 41; 42;\n" ++
            " 43; 44; 45; 46; 47; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58; 59; 60; 61; 62;\n" ++
            " 63; 64; 65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82;\n" ++
            " 83; 84; 85; 86; 87; 88; 89; 90; 91; 92; 93; 94; 95; 96; 97; 98; 99; 100; ...]",
        many,
    );
    drop(many);
    const people = testList(ShowPerson, &.{ ann, .{ .Name = str("Bob"), .Age = 4 } });
    try expectAny("[{ Name = \"Ann\"\n   Age = 3 }; { Name = \"Bob\"\n                Age = 4 }]", people);
    drop(people);

    const z80 = str(run('z', 80));
    try expectAny("C (\"" ++ run('z', 80) ++ "\",\n   1)", @as(ShowShape, .{ .C = .{ .Item1 = z80, .Item2 = 1 } }));
    try expectAny("Some\n  \"" ++ run('z', 80) ++ "\"", @as(?String, z80));
    try expectAny(
        "(\"" ++ run('z', 70) ++ "\",\n \"" ++ run('w', 70) ++ "\")",
        @as(struct { String, String }, .{ str(run('z', 70)), str(run('w', 70)) }),
    );

    const leafT: ShowTree = .Leaf;
    const node = struct {
        pub fn of(l: ShowTree, v: i32, r: ShowTree) ShowTree {
            return .{ .Node = cell(ShowTree, .Node, .{ .Item1 = l, .Item2 = v, .Item3 = r }) };
        }
    }.of;
    const small = node(node(leafT, 1, leafT), 2, node(leafT, 3, leafT));
    try expectAny("Node (Node (Leaf, 1, Leaf), 2, Node (Leaf, 3, Leaf))", small);
    drop(small);
    const big = node(
        node(node(node(leafT, 1111111111, leafT), 222222222, leafT), 333333333, node(leafT, 444444444, leafT)),
        555555555,
        node(leafT, 666666666, node(leafT, 777777777, leafT)),
    );
    try expectAny(
        "Node\n  (Node\n     (Node (Node (Leaf, 1111111111, Leaf), 222222222, Leaf), 333333333,\n" ++
            "      Node (Leaf, 444444444, Leaf)), 555555555,\n   Node (Leaf, 666666666, Node (Leaf, 777777777, Leaf)))",
        big,
    );
    drop(big);

    // a record that contains itself
    const first = new(ShowRing, .{ .Count = 1, .Next = null });
    const second = new(ShowRing, .{ .Count = 2, .Next = first });
    first.Next = second;
    try expectAny("{ Count = 1\n  Next = Some { Count = 2\n                Next = Some ... } }", first);
    first.Next = null;
    drop(second);

    // an F# exception: `%A`, and its message
    const e = ShowErr.new(.{ .Data0 = 1, .Data1 = str("a") });
    try expectAny("MyErr (1, \"a\")", e);
    try expectText("MyErr (1, \"a\")", exnMessage(e));
    try expectText("x=MyErr (1, \"a\")!", format(.{ "x=", arg(.{ .kind = 'A' }, e), "!" }));
    drop(e);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "exception classes derive as on .NET, division raises" {
    const e = ArgumentNullException.new(.{ .Message = str("no") });
    try std.testing.expect(ArgumentNullException.is(e) and ArgumentException.is(e) and SystemException.is(e));
    try std.testing.expect(!ArgumentOutOfRangeException.is(e) and !Failure.is(e) and !ArithmeticException.is(e));
    drop(e);
    try std.testing.expectEqual(@as(i32, -3), try div(i32, 7, -2));
    try std.testing.expectEqual(@as(i32, 1), try rem(i32, 7, -2));
    try std.testing.expectEqual(@as(i8, -128), try div(i8, -128, -1));
    try std.testing.expectEqual(@as(i8, 0), try rem(i8, -128, -1));
    try expectRaised(DivideByZeroException, "Attempted to divide by zero.", div(i32, 5, 0));
    try expectRaised(DivideByZeroException, "Attempted to divide by zero.", rem(u8, 5, 0));
    try expectRaised(OverflowException, "Arithmetic operation resulted in an overflow.", div(i32, std.math.minInt(i32), -1));
    try expectRaised(OverflowException, "Arithmetic operation resulted in an overflow.", rem(i64, std.math.minInt(i64), -1));
}

test "arrays: identity, items, what they raise" {
    const before = thread.stats;
    const A = Array(String);
    const bc = strConcat(str("b"), str("c"));
    const a = arrayOf(A, .{ str("a"), bc, str("d") });
    drop(bc);
    try std.testing.expectEqual(@as(i32, 3), arrayLen(a));
    try expectText("bc", try arrayGet(a, 1));
    const made = strConcat(str("x"), str("y"));
    try arraySet(a, 0, made);
    drop(made);
    try expectText("xy", try arrayGet(a, 0));
    try expectRaised(IndexOutOfRangeException, "Index was outside the bounds of the array.", arrayGet(a, 3));
    try expectRaised(IndexOutOfRangeException, "Index was outside the bounds of the array.", arraySet(a, -1, str("z")));
    const copy = arrayCopy(a);
    try std.testing.expect(eql(a, copy) and a != copy);
    try expectAny("[|\"xy\"; \"bc\"; \"d\"|]", a);
    const part = arraySlice(a, 1, 5);
    try expectAny("[|\"bc\"; \"d\"|]", part);
    const none = arraySlice(a, 2, 1);
    try expectAny("[||]", none);
    try expectRaised(ArgumentOutOfRangeException, "The index is outside the legal range.\ncount = 5, array.Length = 3 (Parameter 'count')", arraySub(a, 1, 5));
    const zeros = try arrayZero(Array(?i32), 2);
    try expectAny("[|None; None|]", zeros);
    try expectRaised(ArgumentException, "The input must be non-negative.\ncount = -1 (Parameter 'count')", arrayZero(Array(i32), -1));
    const list = arrayToList(a);
    const back = arrayOfList(A, list);
    try std.testing.expect(eql(a, back));
    for ([_]A{ a, copy, part, none, back }) |x| drop(x);
    drop(zeros);
    drop(list);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "numbers: what .NET raises and returns" {
    try std.testing.expectEqual(@as(i32, 5), try absOf(@as(i32, -5)));
    try expectRaised(OverflowException, "Negating the minimum value of a twos complement number is invalid.", absOf(@as(i32, std.math.minInt(i32))));
    try expectRaised(ArithmeticException, "Function does not accept floating point Not-a-Number values.", signOf(std.math.nan(f64)));
    try std.testing.expectEqual(@as(i32, 1024), pown(@as(i32, 2), 10));
    try std.testing.expectEqual(@as(f64, 0.25), pown(@as(f64, 2), -2));
    try std.testing.expectEqual(@as(f64, 2), roundEven(@as(f64, 2.5)));
    try std.testing.expectEqual(@as(f64, 4), roundEven(@as(f64, 3.5)));
    try std.testing.expectEqual(@as(f64, -2), roundEven(@as(f64, -2.5)));
    try std.testing.expectEqual(@as(f64, 2.57), try roundTo(@as(f64, 2.567), 2));
    try std.testing.expectEqual(@as(i32, -7), try parseIntFs(i32, str(" -7 ")));
    try std.testing.expectEqual(@as(i32, 31), try parseIntFs(i32, str("0x1F")));
    try std.testing.expectEqual(@as(i32, 5), try parseIntFs(i32, str("0b101")));
    try std.testing.expectEqual(@as(i32, 10), try parseIntFs(i32, str("1_0")));
    try std.testing.expectEqual(@as(i64, 9223372036854775807), try parseIntFs(i64, str("9223372036854775807")));
    try expectRaised(FormatException, "The input string '4x' was not in a correct format.", parseIntFs(i32, str("4x")));
    try expectRaised(FormatException, "Input string was not in a correct format.", parseIntFs(i32, str("")));
    try expectRaised(OverflowException, "Value was either too large or too small for an Int32.", parseIntFs(i32, str("99999999999")));
    try expectRaised(OverflowException, "Arithmetic operation resulted in an overflow.", parseIntFs(u8, str("256")));
    try expectRaised(OverflowException, "Arithmetic operation resulted in an overflow.", parseIntFs(i16, str("40000")));
    try expectRaised(OverflowException, "Value was either too large or too small for a UInt32.", parseIntFs(u16, str("-1")));
    try expectRaised(FormatException, "The input string '0x1F' was not in a correct format.", parseInt(i32, str("0x1F")));
    try expectRaised(OverflowException, "Value was either too large or too small for an unsigned byte.", parseInt(u8, str("300")));
    try std.testing.expectEqual(@as(?i32, 12), tryParseInt(i32, str("12")));
    try std.testing.expectEqual(@as(?i32, null), tryParseInt(i32, str("x")));
    try std.testing.expectEqual(@as(f64, 1000), try parseFloat(f64, str(" 1e3 ")));
    try std.testing.expectEqual(@as(f64, 0.5), try parseFloat(f64, str(".5")));
    try std.testing.expect(std.math.isNan(try parseFloat(f64, str("NaN"))));
    try std.testing.expectEqual(-std.math.inf(f64), try parseFloat(f64, str("-Infinity")));
    try expectRaised(FormatException, "The input string 'abc' was not in a correct format.", parseFloat(f64, str("abc")));
    try expectRaised(FormatException, "The input string 'inf' was not in a correct format.", parseFloat(f64, str("inf")));
    try std.testing.expect(try parseBool(str("True")) and !try parseBool(str("false")));
}

test ".NET's collections: ResizeArray, Dictionary, HashSet" {
    const before = thread.stats;
    const R = ResizeArray(i32);
    const r = raOfList(R, listOf(i32, &.{ 3, 1, 2 }));
    defer drop(r);
    raAdd(r, 5);
    try expectAny("seq [3; 1; 2; 5]", r);
    try expectRaised(ArgumentOutOfRangeException, "Index was out of range. Must be non-negative and less than the size of the collection. (Parameter 'index')", raGet(r, 9));
    try expectRaised(ArgumentOutOfRangeException, "Index must be within the bounds of the List. (Parameter 'index')", raInsert(r, 9, 1));
    try raInsert(r, 0, 9);
    try raRemoveAt(r, 1);
    raSort(r);
    try expectAny("seq [1; 2; 5; 9]", r);
    try std.testing.expect(!raContains(r, 3) and raIndexOf(r, 5) == 2 and !raRemove(r, 3));
    const D = Dictionary(i32, String);
    const d = htNew(D);
    defer drop(d);
    try dictAdd(d, 2, str("b"));
    try dictAdd(d, 1, str("a"));
    try dictSet(d, 3, str("c"));
    try dictSet(d, 2, str("B"));
    try expectAny("seq [[2, B]; [1, a]; [3, c]]", d);
    try expectRaised(ArgumentException, "An item with the same key has already been added. Key: 1", dictAdd(d, 1, str("x")));
    try expectRaised(KeyNotFoundException, "The given key '9' was not present in the dictionary.", dictGet(d, 9));
    try std.testing.expect(try htRemove(d, 2));
    try dictSet(d, 7, str("g"));
    try expectAny("seq [[7, g]; [1, a]; [3, c]]", d);
    try std.testing.expectEqual(@as(i32, 3), htCount(d));
    const h = setOfList(HashSet(i32), listOf(i32, &.{ 3, 1, 3 }));
    defer drop(h);
    try std.testing.expect(setAdd(h, 4) and !setAdd(h, 1));
    try expectAny("seq [3; 1; 4]", h);
    for (0..1000) |i| try dictSet(d, @intCast(i), str("n"));
    try std.testing.expectEqual(@as(i32, 1000), htCount(d));
    _ = before;
}

test ".NET's ToString, Split, StringBuilder, categories" {
    try expectText("Some(1)|(1, a)|[1; 2; 3; ... ]|[a]", format(.{
        toText(@as(?i32, 1)), "|", toText(@as(struct { i32, String }, .{ 1, str("a") })), "|", toText(listOf(i32, &.{ 1, 2, 3, 4 })), "|", toText(listOf(String, &.{str("a")})),
    }));
    try expectAny("[|\"a\"; \"b\"; \"\"; \"c\"|]", try strSplitChars(str("a,b,,c"), &.{','}, std.math.maxInt(i32), 0));
    try expectAny("[|\"a\"; \"b\"|]", try strSplitChars(str("a,,b"), &.{','}, std.math.maxInt(i32), 1));
    try expectAny("[|\"a\"; \"b\"; \"c\"|]", try strSplitString(str("a--b--c"), str("--"), std.math.maxInt(i32), 0));
    try expectAny("[|\"a\"; \"b\"; \"c\"|]", try strSplitChars(str("a b\tc"), &.{}, std.math.maxInt(i32), 0));
    const sb = sbNew(str(""));
    drop(sbAppend(sb, str("a")));
    drop(sbAppend(sb, @as(i32, 1)));
    drop(sbAppend(sb, @as(u16, 'c')));
    drop(sbAppend(sb, @as(f64, 2.5)));
    drop(sbAppend(sb, true));
    try expectText("a1c2.5True", sbToString(sb));
    drop(sb);
    var sum: u32 = 0;
    for (0..0x10000) |c| sum = sum *% 31 +% @backingInt(unicode.category(@intCast(c)));
    // (the same sum over Char.GetUnicodeCategory on .NET 10)
    try std.testing.expectEqual(@as(u32, 3966132137), sum);
    try std.testing.expect(strEqualsIgnoreCase(str("abc"), str("ABC")) and strCompareIgnoreCase(str("a"), str("A")) == 0);
    try std.testing.expectEqual(@as(f64, 7), charNumericValue('7'));
}

test "weak references see their target go" {
    const before = thread.stats;
    const R = *struct { @"$rc": u32 = 1, value: i32 };
    const a = new(R, .{ .value = 7 });
    const w = try weakNew(Weak(R), a);
    const w2 = try weakNew(Weak(R), a);
    const got = weakTryGet(w).?;
    try std.testing.expectEqual(@as(i32, 7), got.value);
    drop(got);
    drop(a);
    try std.testing.expect(weakTryGet(w) == null and weakTryGet(w2) == null);
    const b = new(R, .{ .value = 8 });
    try weakSet(w, b);
    try std.testing.expectEqual(@as(i32, 8), weakTryGet(w).?.value);
    drop(b);
    drop(b);
    drop(w);
    drop(w2);
    try std.testing.expectEqual(@as(usize, 0), thread.weak.count());
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "objects: parts, virtual members, type tests, cycles" {
    const before = thread.stats;
    const Shape = struct {
        const Part = struct { name: String };
        const Chain = struct { own: Part };
        const VT = struct { area: *const fn (Obj) f64 };
        const ty: ObjType = objType(Chain, "Probe+Shape", null, &.{null}, null);
        pub fn name(o: Obj) String {
            return objPart(*Part, &.{Part}, o).name;
        }
    };
    const Circle = struct {
        const Part = struct { r: f64, next: ?Obj };
        const Chain = struct { base: Shape.Chain, own: Part };
        pub fn area(o: Obj) f64 {
            const r = objPart(*Part, &.{ Shape.Part, Part }, o).r;
            return 3 * r * r;
        }
        const vt: Shape.VT = .{ .area = area };
        const ty: ObjType = objType(Chain, "Probe+Circle", &Shape.ty, &.{ @ptrCast(&vt), null }, null);
    };
    const chain: Circle.Chain = .{ .base = .{ .own = .{ .name = str("circle") } }, .own = .{ .r = 2, .next = null } };
    const c = objNew(&Circle.ty, chain);
    drop(chain);
    try expectText("circle", dup(Shape.name(c)));
    try std.testing.expectEqual(@as(f64, 12), objVt(*const Shape.VT, c, 0).area(c));
    try std.testing.expect(objIs(c, &Shape.ty) and objIs(c, &Circle.ty));
    const s = try objCast(c, &Shape.ty);
    drop(s);
    try expectText("Probe+Circle", anyText(c));
    // (a cycle through an object field: freed by the collector when functions can be in cycles)
    objStore(c, &objPart(*Circle.Part, &.{ Shape.Part, Circle.Part }, c).next, dup(c));
    drop(c);
    _ = collect();
    _ = before;
}

test "equality of a long list does not use the stack" {
    var a: List(i32) = .Empty;
    var b: List(i32) = .Empty;
    for (0..1_000_000) |i| {
        const na = cell(List(i32), .Cons, .{ .Head = @as(i32, @intCast(i)), .Tail = a });
        a = .{ .Cons = na };
        const nb = cell(List(i32), .Cons, .{ .Head = @as(i32, @intCast(i)), .Tail = b });
        b = .{ .Cons = nb };
    }
    try std.testing.expect(eql(a, b));
    const c: List(i32) = .{ .Cons = cell(List(i32), .Cons, .{ .Head = 7, .Tail = b }) };
    try std.testing.expect(!eql(a, c));
    drop(a);
    drop(c);
}

test "decimal does what .NET does" {
    const D = struct {
        pub fn p(comptime text: []const u8) NetDecimal {
            return decParse(str(text), true) catch unreachable;
        }
        pub fn is(expected: []const u8, d: NetDecimal) !void {
            var buf: [40]u8 = undefined;
            try std.testing.expectEqualStrings(expected, decAscii(d, &buf));
        }
    };
    const p = D.p;
    try D.is("1.10", p("1.10"));
    try D.is("0.3333333333333333333333333333", try decDiv(p("1"), p("3")));
    try D.is("0.6666666666666666666666666667", try decDiv(p("2"), p("3")));
    try D.is("0.25", try decDiv(p("1"), p("4")));
    try D.is("5", try decDiv(p("10"), p("2")));
    try D.is("1.00", try decDiv(p("1.00"), p("1")));
    try D.is("1.0000", try decMul(p("1.000"), p("1.0")));
    try D.is("0.30", try decAdd(p("0.1"), p("0.20")));
    try D.is("0.0000000000000000000000000000", try decMul(p("1e-28"), p("0.5")));
    try D.is("0.0000000000000000000000000002", try decMul(p("3e-28"), p("0.5")));
    try D.is("33.333333333333333333333333333", try decDiv(p("100"), p("3")));
    try D.is("0.1428571428571428571428571429", try decDiv(p("1"), p("7")));
    try D.is("10.000", try decSub(p("12.345"), p("2.345")));
    try D.is("1", try decRem(p("7"), p("3")));
    try D.is("-1.5", try decRem(p("-7.5"), p("2")));
    try D.is("1.358024679135802467913580237", try decMul(p("1.23456789012345678901234567"), p("1.1")));
    try D.is("20", try decDiv(p("10"), p("0.5")));
    try D.is("0.125", try decDiv(p("1"), p("8")));
    try D.is("2.00", try decDiv(p("4.00"), p("2")));
    try D.is("2.5", try decDiv(p("5"), p("2.0")));
    try D.is("0", try decDiv(p("0"), p("5.00")));
    try D.is("1.0000000000000000000000000001", try decAdd(p("1e-28"), p("1")));
    try D.is("79228162514264337593543950334", try decSub(p("79228162514264337593543950335"), p("0.5")));
    try D.is("79228162514264337593543950334", try decAdd(p("79228162514264337593543950334"), p("0.5")));
    try D.is("79.22816251426433759354395030", try decMul(p("7.92281625142643375935439503"), p("10")));
    try expectRaised(OverflowException, "Value was either too large or too small for a Decimal.", decAdd(p("79228162514264337593543950335"), p("1")));
    try expectRaised(DivideByZeroException, "Attempted to divide by zero.", decDiv(p("1"), p("0")));
    try expectRaised(OverflowException, "Value was either too large or too small for an Int32.", decToInt(i32, p("1e20")));
    try expectRaised(OverflowException, "Value was either too large or too small for an unsigned byte.", decToInt(u8, p("300")));
    try D.is("0.1", try decOf(@as(f64, 0.1)));
    try D.is("0.333333333333333", try decOf(@as(f64, 1.0 / 3.0)));
    try D.is("123456789.123457", try decOf(@as(f64, 123456789.123456789)));
    try D.is("0", try decOf(@as(f64, 1e-30)));
    try D.is("2.5", try decOf(@as(f32, 2.5)));
    try D.is("10000000000000000000000000000", try decOf(@as(f64, 1e28)));
    try D.is("0.0000000000000000000123456789", try decOf(@as(f64, 1.23456789e-20)));
    try D.is("-1234567890123460000", try decOf(@as(f64, -1234567890123456789.0)));
    try expectRaised(OverflowException, "Value was either too large or too small for a Decimal.", decOf(@as(f64, 1e29)));
    try std.testing.expectEqual(@as(i32, -2), try decToInt(i32, p("-2.7")));
    try std.testing.expectEqual(@as(f64, 1.1), decToFloat(f64, p("1.1")));
    try std.testing.expectEqual(@as(f64, 7.922816251426434e28), decToFloat(f64, p("79228162514264337593543950335")));
    try D.is("2", decRound(p("2.5"), 0, true));
    try D.is("-2", decRound(p("-2.5"), 0, true));
    try D.is("3", decRound(p("2.5"), 0, false));
    try D.is("2.34", decRound(p("2.345"), 2, true));
    try D.is("1.00", decRound(p("1.005"), 2, true));
    try D.is("-2", decWhole(p("-1.5"), .down));
    try D.is("2", decWhole(p("1.2"), .up));
    try D.is("-1", decWhole(p("-1.7"), .toward_zero));
    try std.testing.expect(eql(p("1.0"), p("1.00")) and compare(p("2"), p("10")) == -1 and hash(p("1.0")) == hash(p("1.00")));
    try D.is("1000.5", try decParse(str("1,000.5"), false));
    try expectRaised(FormatException, "The input string '1e3' was not in a correct format.", decParse(str("1e3"), false));
    try D.is("1000", p("1e3"));
    try D.is("0.1234567890123456789012345679", p("0.123456789012345678901234567890123"));
    try expectRaised(OverflowException, "Value was either too large or too small for a Decimal.", decParse(str("99999999999999999999999999999"), false));
    try expectRaised(FormatException, "The input string '1.5x' was not in a correct format.", decParse(str("1.5x"), false));
    try D.is("0.000", p("-0.000"));
    try expectText("2.35|1,234.50|1.500000|1.57|1.5|1.10|  2.25|1.10M", format(.{ arg(.{ .net = "F2" }, p("2.345")), "|", arg(.{ .net = "N2" }, p("1234.5")), "|", arg(.{ .kind = 'f' }, p("1.5")), "|", arg(.{ .kind = 'f', .precision = 2 }, p("1.567")), "|", arg(.{ .kind = 'g' }, p("1.5")), "|", p("1.10"), "|", arg(.{ .kind = 'M', .width = 6 }, p("2.25")), "|", anyText(p("1.10")) }));
}

test "bigint does what .NET does" {
    const before = thread.stats;
    const a = bigLit("123456789012345678901234567890");
    defer drop(a);
    const sq = bigMul(a, a);
    defer drop(sq);
    try expectText("15241578753238836750495351562536198787501905199875019052100", bigText(sq));
    const seven = bigOf(@as(i32, 7));
    defer drop(seven);
    const q = try bigDivRem(a, seven, true);
    defer drop(q);
    try expectText("17636684144620811271604938270", bigText(q));
    const na = bigNeg(a);
    defer drop(na);
    const nq = try bigDivRem(na, seven, true);
    defer drop(nq);
    try expectText("-17636684144620811271604938270", bigText(nq));
    const two = bigOf(@as(i32, 2));
    defer drop(two);
    const p = try bigPow(two, 100);
    defer drop(p);
    try expectText("1267650600228229401496703205376", bigText(p));
    const zero = bigOf(@as(i32, 0));
    defer drop(zero);
    try expectRaised(DivideByZeroException, "Attempted to divide by zero.", bigDivRem(a, zero, true));
    try expectRaised(OverflowException, "Value was either too large or too small for an Int32.", bigToInt(i32, a));
    try expectRaised(FormatException, "The value could not be parsed.", bigParse(str("12x")));
    const parsed = try bigParse(str(" -123 "));
    defer drop(parsed);
    try expectText("-123", bigText(parsed));
    try std.testing.expect(compare(a, seven) == 1 and eql(a, a) and !eql(a, seven));
    try std.testing.expectEqual(@as(i32, 42), try bigToInt(i32, bigOf(@as(i32, 42))));
    try std.testing.expectEqual(@as(f64, 1.2345678901234568e29), bigToFloat(f64, a));
    try expectText("a=123456789012345678901234567890", format(.{ "a=", a }));
    _ = before;
}

test "conv follows .NET" {
    try std.testing.expectEqual(@as(i32, -1), conv(i32, @as(u32, 0xFFFF_FFFF)));
    try std.testing.expectEqual(@as(u8, 0x34), conv(u8, @as(i32, 0x1234)));
    try std.testing.expectEqual(@as(i64, -5), conv(i64, @as(i32, -5)));
    try std.testing.expectEqual(@as(u64, 0xFFFF_FFFF_FFFF_FFFB), conv(u64, @as(i32, -5)));
    try std.testing.expectEqual(@as(i32, 3), conv(i32, @as(f64, 3.99)));
    try std.testing.expectEqual(@as(i32, -3), conv(i32, @as(f64, -3.99)));
    try std.testing.expectEqual(@as(i32, 2147483647), conv(i32, @as(f64, 1e30)));
    try std.testing.expectEqual(@as(i32, 0), conv(i32, std.math.nan(f64)));
    try std.testing.expectEqual(@as(f64, 7.0), conv(f64, @as(i32, 7)));
}

test "box" {
    const a = box(@as(i32, 5));
    const b = box(@as(i32, 5));
    const c = box(str("x"));
    defer drop(a);
    defer drop(b);
    defer drop(c);
    try std.testing.expect(eql(a, b));
    try std.testing.expect(!eql(a, c));
    try std.testing.expect(!refEql(a, b));
    try std.testing.expect(isType(i32, a));
    try std.testing.expect(!isType(i64, a));
    try std.testing.expectEqual(@as(i32, 5), try unbox(i32, a));
    try std.testing.expectEqual(hash(@as(i32, 5)), hash(a));
    try std.testing.expectEqual(@as(i32, 0), compare(a, b));
    try std.testing.expectError(error.Raised, unbox(i64, a));
    drop(take());
    const t = try anyToString(c, false);
    defer drop(t);
    try std.testing.expect(strEql(t, str("x")));
    try std.testing.expect(box(@as(String, null)) == null);
    try std.testing.expect(box({}) == null);
    try std.testing.expect(isType(void, null));
    try std.testing.expect(!isType(void, a));
    try std.testing.expect(tryUnbox(?void, null) != null);
    try std.testing.expect(tryUnbox(?void, a) == null);
    try std.testing.expectEqual({}, try unbox(void, box({})));
    try std.testing.expectError(error.Raised, unbox(void, a));
    drop(take());
}

test "Random(seed) gives .NET's numbers" {
    const r = randomNew(1234);
    defer drop(r);
    // (what `Random(1234)` gives on .NET: Next(), Next(100), Next(1000, 10000), NextDouble())
    try std.testing.expectEqual(@as(i32, 857019877), randomNext(r));
    try std.testing.expectEqual(@as(i32, 89), try randomNextMax(r, 100));
    try std.testing.expectEqual(@as(i32, 3872), try randomNextRange(r, 1000, 10000));
    try std.testing.expectEqual(@as(f64, 0.9467375338760845), randomNextDouble(r));
    const b = arrayFrom(Array(u8), allocator.alloc(u8, 6) catch unreachable);
    defer drop(b);
    const r2 = randomNew(5432);
    defer drop(r2);
    randomNextBytes(r2, b);
    try std.testing.expectEqualSlices(u8, &.{ 152, 238, 227, 30, 153, 56 }, b.items);
    const r3 = randomNew(-7);
    defer drop(r3);
    try std.testing.expectEqual(@as(i32, 766440938), try randomNextRange(r3, -2000000000, 2000000000));
    try std.testing.expectEqual(@as(i32, 1419354884), randomNext(r3));
}

test "TypeShape formats voption, struct tuple, u16_num, and recursive unions" {
    const vopt_int: TypeShape = .{ .nodes = &.{.{ .kind = .vopt, .a = ShowNode.auto }} };
    try expectText("ValueSome 42", anyTextShape(vopt_int, @as(?i32, 42)));
    try expectText("ValueNone", anyTextShape(vopt_int, @as(?i32, null)));
    try expectText("42", toTextShape(vopt_int, @as(?i32, 42)));
    try expectText("ValueNone", toTextShape(vopt_int, @as(?i32, null)));

    const vopt_st_num: TypeShape = .{
        .nodes = &.{
            .{ .kind = .vopt, .a = 1 },
            .{ .kind = .struct_tuple, .a = 0, .b = 2 },
            .{ .kind = .u16_num },
        },
        .refs = &.{ ShowNode.auto, 2 },
    };
    const p1: ?struct { i32, c_ushort } = .{ 7, 16 };
    try expectText("ValueSome struct (7, 16us)", anyTextShape(vopt_st_num, p1));
    try expectText("(7, 16)", toTextShape(vopt_st_num, p1));

    const Tree = union(enum) {
        Leaf: struct { Value: ?c_ushort },
        Pair: struct { Left: struct { ?i32, bool }, Right: void },
    };
    const tree_shape: TypeShape = .{
        .nodes = &.{
            .{ .kind = .@"union", .a = 0, .b = 2 },
            .{ .kind = .record, .a = 2, .b = 1 },
            .{ .kind = .vopt, .a = 3 },
            .{ .kind = .u16_num },
            .{ .kind = .record, .a = 3, .b = 2 },
            .{ .kind = .struct_tuple, .a = 5, .b = 2 },
        },
        .refs = &.{ 1, 4, 2, 5, ShowNode.auto, ShowNode.auto, ShowNode.auto },
    };
    const t1: Tree = .{ .Leaf = .{ .Value = 65 } };
    const t2: Tree = .{ .Pair = .{ .Left = .{ 9, true }, .Right = {} } };
    const t3: Tree = .{ .Leaf = .{ .Value = null } };
    try expectText("Leaf (ValueSome 65us)", anyTextShape(tree_shape, t1));
    try expectText("Leaf ValueNone", anyTextShape(tree_shape, t3));
    try expectText("Pair (struct (Some 9, true), ())", anyTextShape(tree_shape, t2));
}

test "managed span operations maintain reference counts" {
    const start_stats = thread.stats;
    {
        const arr = arrays.arrayOf(Array(String), .{ str("a"), str("b"), str("c") });
        defer drop(arr);
        const sp = arr.items;

        const dyn1 = strConcat(str("d"), str("1"));
        defer drop(dyn1);
        try spanSet(sp, 1, dyn1);
        try std.testing.expect(strEql(sp[1], str("d1")));

        const dyn2 = strConcat(str("f"), str("2"));
        defer drop(dyn2);
        spanFill(sp[0..2], dyn2);
        try std.testing.expect(strEql(sp[0], str("f2")));
        try std.testing.expect(strEql(sp[1], str("f2")));
        try std.testing.expect(strEql(sp[2], str("c")));

        const copied = spanToArray(Array(String), sp[1..]);
        defer drop(copied);
        try std.testing.expectEqual(@as(usize, 2), copied.items.len);
        try std.testing.expect(strEql(copied.items[0], str("f2")));
        try std.testing.expect(strEql(copied.items[1], str("c")));

        // Overlapping forward & backward CopyTo
        const s_hi = strConcat(str("h"), str("i"));
        defer drop(s_hi);
        try spanSet(sp, 0, s_hi);
        try spanCopyTo(sp[0..2], sp[1..3]);
        try std.testing.expect(strEql(sp[0], str("hi")));
        try std.testing.expect(strEql(sp[1], str("hi")));
        try std.testing.expect(strEql(sp[2], str("f2")));

        try spanClear(sp);
        try std.testing.expect(sp[0] == null and sp[1] == null and sp[2] == null);
    }
    try std.testing.expectEqual(start_stats.allocs - start_stats.frees, thread.stats.allocs - thread.stats.frees);
}

test "culture string comparison matches .NET InvariantCulture weights" {
    try std.testing.expectEqual(@as(i32, 1), try strCompareTo(str("ABC"), str("abc")));
    try std.testing.expectEqual(@as(i32, -1), try strCompareTo(str("aBc"), str("Abc")));
    try std.testing.expectEqual(@as(i32, -1), strCompareCulture(str("ab"), str("ABC"), false));
    try std.testing.expectEqual(@as(i32, -1), strCompareCulture(str("_"), str("0"), false));
    try std.testing.expectEqual(@as(i32, -1), strCompareCulture(str("0"), str("a"), false));
    try std.testing.expectEqual(@as(i32, 0), strCompareCulture(str("ABC"), str("abc"), true));
    try std.testing.expect(try strCompareCultureRange(str("ABC"), 1, str("bcd"), 0, 2, false) > 0);
    try std.testing.expectEqual(@as(i32, 0), try strCompareRangeWith(str("ABC"), 1, str("bcd"), 0, 2, 5));
    try std.testing.expect(try strStartsWithOpt(str("ABCD"), str("ab"), true));
    try std.testing.expect(try strEndsWithOpt(str("ABCD"), str("cd"), true));
    try std.testing.expectEqual(@as(i32, 1), try strIndexOfCharIgnoreCase(str("aBc"), 'B'));
    // (pairs checked with .NET: accents after the base letter, expansions, ignorable control
    // chars, letters without a base after their neighbour; the table was also checked against
    // 3,000 random pairs over U+0000..U+024F, see fable_collation.zig)
    const pairs = .{
        .{ "e", "é", -1 },
        .{ "é", "f", -1 },
        .{ "z", "é", 1 },
        .{ "co-op", "coop", -1 },
        .{ "a-b", "ab", -1 },
        .{ "Æ", "AE", 1 },
        .{ "ss", "ß", -1 },
        .{ "résumé", "resume", 1 },
        .{ "ı", "z", -1 },
        .{ "o", "ı", 1 },
        .{ "\u{1}", "", 0 },
        .{ "\u{a0}", " ", 1 },
        .{ "file10", "file9", -1 },
        .{ "a", "A", -1 },
    };
    inline for (pairs) |t| {
        try std.testing.expectEqual(@as(i32, t[2]), strCompareCulture(str(t[0]), str(t[1]), false));
    }
}

test "exception stack trace is null before throw and captured on throw" {
    const start_stats = thread.stats;
    {
        const e0 = Failure.new(.{ .Message = str("unthrown") });
        defer drop(e0);
        try std.testing.expect(exnStackTrace(e0) == null);

        throw(dup(e0));
        const caught = take();
        defer drop(caught);
        const trace = exnStackTrace(caught);
        defer drop(trace);
        try std.testing.expect(trace != null);
        try std.testing.expect(unitsOf(trace).len > 0);
    }
    try std.testing.expectEqual(start_stats.allocs - start_stats.frees, thread.stats.allocs - thread.stats.frees);
}


// ---- values shared between threads ----

const ShareTestList = List(String);
const ShareTestRec = *struct { @"$rc": u32 = 1, name: String, items: ShareTestList };

fn shareTestList(n: usize) ShareTestList {
    var l: ShareTestList = .Empty;
    var i: usize = 0;
    while (i < n) : (i += 1) l = ShareTestList{ .Cons = cell(ShareTestList, .Cons, .{ .Head = strConcat(str("x"), str("y")), .Tail = l }) };
    return l;
}

fn shareTestReader(r: ShareTestRec, out: *usize) void {
    var k: usize = 0;
    var round: usize = 0;
    while (round < 2000) : (round += 1) {
        const mine = dup(r);
        var cur = dup(mine.items);
        while (true) {
            switch (cur) {
                .Empty => break,
                .Cons => |c| {
                    k += 1;
                    const next = dup(c.Tail);
                    drop(cur);
                    cur = next;
                },
            }
        }
        drop(mine);
    }
    out.* = k;
    drop(r);
}

test "a value shared between threads is counted atomically and freed once" {
    const before = thread.stats;
    const r = new(ShareTestRec, .{ .name = strConcat(str("a"), str("b")), .items = shareTestList(100_000) });
    try markShared(r);
    var outs: [4]usize = @splat(0);
    var ts: [4]std.Thread = undefined;
    for (&ts, &outs) |*t, *o| t.* = try std.Thread.spawn(.{}, shareTestReader, .{ dup(r), o });
    for (ts) |t| t.join();
    for (outs) |o| try std.testing.expectEqual(@as(usize, 2000 * 100_000), o);
    drop(r);
    // (allocations on this thread; frees happened on whichever thread let go last: this one)
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "native integers and SGC header compile cleanly across pointer widths" {
    try std.testing.expectEqual(@sizeOf(sgc.Hdr), 3 * @sizeOf(*sgc.Hdr) + 12);
    const n: isize = -7;
    const u: usize = 42;
    try std.testing.expectEqual(@as(i32, -7), conv(i32, n));
    try std.testing.expectEqual(@as(u32, 42), conv(u32, u));
    try std.testing.expectEqual(@as(usize, 42), conv(usize, @as(u64, 42)));
    try std.testing.expectEqual(@as(isize, -7), conv(isize, @as(i64, -7)));
    try std.testing.expectEqual(@as(i32, 42), hash(u));
    try std.testing.expectEqual(if (@bitSizeOf(isize) == 64) @as(i32, 6) else @as(i32, -7), hash(n));
    const big_u: u64 = std.math.maxInt(u64);
    _ = hash(big_u);
}

test "fat-pointer interface: zero-alloc class cast, upcast, and round-trip downcast" {
    const Part = struct { x: i32 };
    const Chain = struct { own: Part };
    const cls_ty: ObjType = objType(Chain, "RtTestClass", null, &.{}, null);

    const ISubVt = struct {
        @"$meta": *const IfaceMeta,
        Get: *const fn (?*anyopaque, void) Raised!i32,
    };
    const ISub = Iface(ISubVt);
    const IBaseVt = struct {
        @"$meta": *const IfaceMeta,
        Get: *const fn (?*anyopaque, void) Raised!i32,
    };
    const IBase = Iface(IBaseVt);

    const SubClsImpl = struct {
        fn get(d: ?*anyopaque, _: void) Raised!i32 {
            const o: Obj = @ptrCast(@alignCast(d.?));
            return objPart(*Part, &.{Part}, o).x;
        }
        const vt: ISubVt = .{
            .@"$meta" = &obj_iface_meta,
            .Get = &get,
        };
    };
    const BaseUpcastImpl = struct {
        fn get(d: ?*anyopaque, u: void) Raised!i32 {
            const sub = boxed(ISub, @ptrCast(@alignCast(d.?))).value;
            return sub.vt.Get(sub.data, u);
        }
        const vt: IBaseVt = .{
            .@"$meta" = upcastIfaceMeta(ISub),
            .Get = &get,
        };
    };

    const before = thread.stats;
    {
        const obj = objNew(&cls_ty, Chain{ .own = .{ .x = 42 } });
        const after_obj = thread.stats.allocs;

        // Zero-alloc class -> interface view
        const sub: ?ISub = ISub{ .data = @ptrCast(obj), .vt = &SubClsImpl.vt };
        try std.testing.expectEqual(after_obj, thread.stats.allocs);
        try std.testing.expectEqual(@as(i32, 42), try sub.?.vt.Get(sub.?.data, {}));
        try std.testing.expect(ifaceIsClass(sub, &cls_ty));

        // Round-trip class downcast
        const back_any = try ifaceCastClass(sub, &cls_ty);
        defer drop(back_any);
        try std.testing.expectEqual(obj, back_any.?);

        // Upcast ISub -> IBase & round-trip downcasts to both ISub and class
        const base: ?IBase = ifaceBox(IBase, ISub, sub.?, &BaseUpcastImpl.vt);
        defer drop(base);
        try std.testing.expectEqual(@as(i32, 42), try base.?.vt.Get(base.?.data, {}));
        try std.testing.expect(ifaceIsClass(base, &cls_ty));

        const back_sub = try ifaceUnbox(?ISub, base);
        defer drop(back_sub);
        try std.testing.expectEqual(@as(i32, 42), try back_sub.?.vt.Get(back_sub.?.data, {}));

        const back_cls = try ifaceCastClass(base, &cls_ty);
        defer drop(back_cls);
        try std.testing.expectEqual(obj, back_cls.?);

        // Boxed interface preserves wrapper for unbox(?ISub) while delegating class identity & refEql
        const boxed_sub = box(sub);
        defer drop(boxed_sub);
        try std.testing.expect(isType(?ISub, boxed_sub));
        const unboxed_sub = try unbox(?ISub, boxed_sub);
        defer drop(unboxed_sub);
        try std.testing.expectEqual(@as(i32, 42), try unboxed_sub.?.vt.Get(unboxed_sub.?.data, {}));
        try std.testing.expect(anyIsClass(boxed_sub, &cls_ty));
        const cast_cls = try anyToClass(boxed_sub, &cls_ty);
        defer drop(cast_cls);
        try std.testing.expectEqual(obj, cast_cls.?);
        try std.testing.expect(refEql(sub, sub));
        try std.testing.expect(refEql(sub, back_sub));
        try std.testing.expect(refEql(@as(Any, obj), boxed_sub));
        try std.testing.expect(refEql(@as(?ISub, null), @as(?ISub, null)));
        try std.testing.expect(!refEql(sub, @as(?ISub, null)));
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "closure2 and apply2: zero intermediate closure alloc and exception-edge drops" {
    const Inner = Func(*const fn (?*Env, String) Raised!i32);
    const Outer = Func(*const fn (?*Env, i32) Raised!Inner);
    const Caps = struct { base: i32 };
    const Impl = struct {
        fn innerCode(env: ?*Env, b: String) Raised!i32 {
            defer drop(b);
            const c = captured(Caps, env);
            return c.base + @as(i32, @intCast(unitsOf(b).len));
        }
        fn code(env: ?*Env, a: i32) Raised!Inner {
            const c = captured(Caps, env);
            return closure(Inner, Caps, .{ .base = c.base + a }, innerCode);
        }
        fn code2(env: ?*Env, a: i32, b: String) Raised!i32 {
            defer drop(b);
            const c = captured(Caps, env);
            return c.base + a + @as(i32, @intCast(unitsOf(b).len));
        }
        fn raisingFirst(_: ?*Env, _: i32) Raised!Inner {
            return raise(ArgumentException, str("boom"));
        }
    };

    const before = thread.stats;
    {
        const f = closure2(Outer, Caps, .{ .base = 10 }, Impl.code, Impl.code2);
        defer drop(f);

        const s1 = strConcat(str("he"), str("llo"));
        const after_s1 = thread.stats.allocs;
        const r1 = try apply2(i32, f, 5, s1);
        try std.testing.expectEqual(@as(i32, 20), r1);
        // apply2 invoked code2 directly without allocating an Inner closure Env.
        try std.testing.expectEqual(after_s1, thread.stats.allocs);

        // Partial application still works through 1-arg code.
        const g = try f.code(f.env, 5);
        defer drop(g);
        const s2 = strConcat(str("wo"), str("rld"));
        try std.testing.expectEqual(@as(i32, 20), try g.code(g.env, s2));

        // When 1-arg code raises inside apply2, owned second argument b must be dropped.
        const failing: Outer = .{ .env = null, .code = Impl.raisingFirst };
        const s3 = strConcat(str("le"), str("ak?"));
        const res = apply2(i32, failing, 1, s3);
        try std.testing.expectError(error.Raised, res);
        drop(take());
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "arraySetAt, dropAll, callM/xcallM, and exn_show" {
    const before = thread.stats;
    {
        const A = Array(String);
        const arr = arrayOf(A, .{ str("a"), str("b") });
        const s = strConcat(str("c"), str("d"));
        arraySetAt(arr, 1, s);
        drop(s);
        try expectText("cd", try arrayGet(arr, 1));

        const p1 = strConcat(str("p"), str("1"));
        const p2 = strConcat(str("p"), str("2"));
        dropAll(.{ arr, p1, p2 });

        const Nums = Array(i32);
        const nums = arrayOf(Nums, .{ 1, 2, 3 });
        arraySetAt(nums, 0, 42);
        try std.testing.expectEqual(@as(i32, 42), arrayItemAt(nums, 0));
        drop(nums);

        const Mod = struct {
            pub fn echo(x: String) Raised!String {
                if (unitsOf(x).len == 0) return raise(ArgumentException, str("empty"));
                return dup(x);
            }
            pub const @"echo$sig" = .{ .borrows = .{ true }, .result_borrowed = false };

            pub fn plainOk(n: i32) i32 {
                return n + 1;
            }
        };

        const src = strConcat(str("hi"), str("!"));
        const echoed = try xcallM(Mod, "echo", "k", .{ src }, .{});
        try expectText("hi!", echoed);
        try expectText("hi!", dup(src));

        const held = strConcat(str("he"), str("ld"));
        const fail_arg = str("");
        try std.testing.expectError(error.Raised, xcallM(Mod, "echo", "g", .{ fail_arg }, .{ src, held }));
        drop(take());

        try std.testing.expectEqual(@as(i32, 8), try xcallPlain(Mod.plainOk(7), .{}));
        try std.testing.expect(exn_show);
    }
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
}

test "an array that does not fit raises OutOfMemoryException" {
    const saved = allocator;
    defer allocator = saved;
    // (an allocator that refuses what is larger than a page, as a heap does what it cannot fit)
    const Big = struct {
        var base: std.mem.Allocator = undefined;
        fn bigAlloc(_: *anyopaque, len: usize, a: std.mem.Alignment, ra: usize) ?[*]u8 {
            if (len > 4096) return null;
            return base.rawAlloc(len, a, ra);
        }
        fn bigResize(_: *anyopaque, m: []u8, a: std.mem.Alignment, n: usize, ra: usize) bool {
            return base.rawResize(m, a, n, ra);
        }
        fn bigRemap(_: *anyopaque, m: []u8, a: std.mem.Alignment, n: usize, ra: usize) ?[*]u8 {
            return base.rawRemap(m, a, n, ra);
        }
        fn bigFree(_: *anyopaque, m: []u8, a: std.mem.Alignment, ra: usize) void {
            base.rawFree(m, a, ra);
        }
        const vt: std.mem.Allocator.VTable = .{ .alloc = bigAlloc, .resize = bigResize, .remap = bigRemap, .free = bigFree };
    };
    Big.base = saved;
    allocator = .{ .ptr = undefined, .vtable = &Big.vt };
    const A = Array(i64);
    try std.testing.expectError(error.Raised, arrayZero(A, 1000));
    allocator = saved;
    const e = take();
    try std.testing.expectEqualStrings("System.OutOfMemoryException", e.type.name);
    drop(e);
}
