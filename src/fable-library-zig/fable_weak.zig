//! Weak references (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");
const Layout = rt.Layout;
const Raised = rt.Raised;
const Shower = rt.Shower;
const bookkeeping = rt.bookkeeping;
const dup = rt.dup;
const isCellPtr = rt.isCellPtr;
const thread = rt.thread;
const track = rt.track;

// ---------------------------------------------------------------------------------------------
// Weak references
//
// `WeakReference<'T>` points at a cell without keeping it alive. It holds a handle, shared by
// every weak reference to the same cell and found through a table of this thread; when the
// cell is freed (its last reference went, or the cycle collector found it dead) the handle is
// cleared and every weak reference to it sees None from then on. While no weak reference
// exists the table is empty, and freeing a cell costs one more compare.
//
// A cell shared between threads has its handle in one table for all threads, under a lock: the
// handle moves there when the cell is shared. Any thread may free the cell, which clears the
// handle under the lock; `TryGetTarget` takes a reference only while the count is not zero (as
// Rust's `Weak::upgrade`), so it never brings back a cell another thread is freeing. Weak
// references to the cells of a cyclic shared graph let its back edges go, as `Arc` and `Weak` do.
// ---------------------------------------------------------------------------------------------

pub const WeakHandle = struct {
    /// the cell, or null once it is freed
    target: ?usize,
    /// the weak references that hold this handle
    refs: u32,
    /// in the table of cells shared between threads: read and changed under its lock
    shared: bool = false,
};

/// (held for a few instructions at a time: a spin lock)
const SpinLock = struct {
    state: std.atomic.Value(u32) = .init(0),

    fn lock(l: *SpinLock) void {
        while (l.state.cmpxchgWeak(0, 1, .acquire, .monotonic) != null) std.atomic.spinLoopHint();
    }

    fn unlock(l: *SpinLock) void {
        l.state.store(0, .release);
    }
};

var shared_lock: SpinLock = .{};
var shared_table: std.AutoHashMapUnmanaged(usize, *WeakHandle) = .empty;
/// the handles in the shared table: a shared cell that is freed looks at it only when there are any
pub var shared_count = std.atomic.Value(usize).init(0);

/// (handles outlive the thread that made them, once shared: the global allocator)
fn handles() std.mem.Allocator {
    return rt.allocator;
}

/// A shared cell was freed: its weak references see it is gone
pub fn sharedWeakGone(addr: usize) void {
    shared_lock.lock();
    defer shared_lock.unlock();
    if (shared_table.fetchRemove(addr)) |kv| {
        kv.value.target = null;
        _ = shared_count.fetchSub(1, .monotonic);
    }
}

/// A cell that weak references of this thread point at is being shared: its handle moves to the
/// shared table
pub fn shareWeakHandle(addr: usize) void {
    const kv = thread.weak.fetchRemove(addr) orelse return;
    shared_lock.lock();
    defer shared_lock.unlock();
    kv.value.shared = true;
    shared_table.put(handles(), addr, kv.value) catch rt.oom();
    _ = shared_count.fetchAdd(1, .monotonic);
}

fn sharedHandle(addr: usize) *WeakHandle {
    shared_lock.lock();
    defer shared_lock.unlock();
    const entry = shared_table.getOrPut(handles(), addr) catch rt.oom();
    if (!entry.found_existing) {
        const h = handles().create(WeakHandle) catch rt.oom();
        h.* = .{ .target = addr, .refs = 0, .shared = true };
        entry.value_ptr.* = h;
        _ = shared_count.fetchAdd(1, .monotonic);
    }
    entry.value_ptr.*.refs += 1;
    return entry.value_ptr.*;
}

pub fn weakGone(addr: usize) void {
    if (thread.weak.fetchRemove(addr)) |kv| kv.value.target = null;
}

pub fn weakHandle(addr: usize) *WeakHandle {
    const entry = thread.weak.getOrPut(bookkeeping(), addr) catch rt.oom();
    if (!entry.found_existing) {
        const h = handles().create(WeakHandle) catch rt.oom();
        h.* = .{ .target = addr, .refs = 0 };
        entry.value_ptr.* = h;
    }
    entry.value_ptr.*.refs += 1;
    return entry.value_ptr.*;
}

/// (a class's value may be null: the cell it points at, if any)
fn CellOf(comptime T: type) type {
    return if (@typeInfo(T) == .optional) @typeInfo(T).optional.child else T;
}

/// The handle for a target: none for null (a handle of its own, never filled)
fn handleOf(target: anytype) *WeakHandle {
    if (comptime @typeInfo(@TypeOf(target)) == .optional) {
        const p = target orelse {
            const h = handles().create(WeakHandle) catch rt.oom();
            h.* = .{ .target = null, .refs = 1 };
            return h;
        };
        return handleOf(p);
    }
    if (rt.isShared(target)) {
        _ = @atomicRmw(u32, &target.@"$rc", .Or, rt.weak_bit, .release);
        return sharedHandle(@intFromPtr(target));
    }
    target.@"$rc" |= rt.weak_bit;
    return weakHandle(@intFromPtr(target));
}

pub fn weakLetGo(h: *WeakHandle) void {
    if (h.shared) {
        shared_lock.lock();
        defer shared_lock.unlock();
        h.refs -= 1;
        if (h.refs != 0) return;
        if (h.target) |addr| {
            _ = shared_table.remove(addr);
            _ = shared_count.fetchSub(1, .monotonic);
        }
        handles().destroy(h);
        return;
    }
    h.refs -= 1;
    if (h.refs != 0) return;
    if (h.target) |addr| _ = thread.weak.remove(addr);
    handles().destroy(h);
}

/// .NET's `WeakReference<'T>` of a reference type (a class, a record with mutable fields, an
/// array, ...: a cell).
pub fn Weak(comptime T: type) type {
    if (comptime !isCellPtr(CellOf(T))) @compileError("fable: a weak reference needs a reference type (a class, a record with mutable fields, an array, ...), not " ++ @typeName(T));
    return *struct {
        const Self = @This();
        pub const fable_identity = {};
        pub const fable_weak = T;
        @"$rc": u32 = 1,
        handle: *WeakHandle,

        pub fn fable_free(c: *Self) void {
            weakLetGo(c.handle);
        }

        /// (the weak reference is being shared: so is its target, and its handle with it)
        pub fn fable_on_share(c: *Self) Raised!void {
            if (c.handle.shared) return;
            const addr = c.handle.target orelse {
                if (rt.thread.share_probe == null) {
                    shared_lock.lock();
                    defer shared_lock.unlock();
                    c.handle.shared = true;
                }
                return;
            };
            const target: CellOf(T) = @ptrFromInt(addr);
            try rt.markShared(target);
            // (shared already, without a weak reference of this thread's table: none to move)
            if (rt.thread.share_probe == null and !c.handle.shared) shareWeakHandle(addr);
        }

        pub fn fable_show(b: *Shower, x: *Self, depth: i32) *Layout {
            _ = x;
            _ = depth;
            return b.word("System.WeakReference`1");
        }
    };
}

/// `WeakReference<'T>(target)`
pub fn weakNew(comptime W: type, target: @typeInfo(W).pointer.child.fable_weak) Raised!W {
    const c = rt.alloc().create(@typeInfo(W).pointer.child) catch rt.oom();
    c.* = .{ .handle = handleOf(target) };
    if (track) thread.stats.allocs += 1;
    return c;
}

/// `w.TryGetTarget(&target)`: the target (a reference of its own), or null once it is freed.
pub fn weakTryGet(w: anytype) ?@typeInfo(@TypeOf(w)).pointer.child.fable_weak {
    const T = @typeInfo(@TypeOf(w)).pointer.child.fable_weak;
    if (w.handle.shared) {
        shared_lock.lock();
        defer shared_lock.unlock();
        const addr = w.handle.target orelse return null;
        const target: CellOf(T) = @ptrFromInt(addr);
        // (a reference only while there is one: a count of zero is a cell being freed)
        var rc = @atomicLoad(u32, &target.@"$rc", .monotonic);
        if (rc & rt.immortal_bit != 0) return @as(T, target);
        while (rc & rt.count_mask != 0) {
            rc = @cmpxchgWeak(u32, &target.@"$rc", rc, rc + 1, .acquire, .monotonic) orelse return @as(T, target);
        }
        return null;
    }
    const addr = w.handle.target orelse return null;
    const target: CellOf(T) = @ptrFromInt(addr);
    return @as(T, dup(target));
}

/// `w.SetTarget(target)`
pub fn weakSet(w: anytype, target: @typeInfo(@TypeOf(w)).pointer.child.fable_weak) Raised!void {
    const old = w.handle;
    w.handle = handleOf(target);
    // (a weak reference shared between threads points at shared values only)
    if (rt.isShared(w)) try @typeInfo(@TypeOf(w)).pointer.child.fable_on_share(w);
    weakLetGo(old);
}
