//! Weak references (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");
const Layout = rt.Layout;
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
// ---------------------------------------------------------------------------------------------

pub const WeakHandle = struct {
    /// the cell, or null once it is freed
    target: ?usize,
    /// the weak references that hold this handle
    refs: u32,
};

pub fn weakGone(addr: usize) void {
    if (thread.weak.fetchRemove(addr)) |kv| kv.value.target = null;
}

pub fn weakHandle(addr: usize) *WeakHandle {
    const entry = thread.weak.getOrPut(bookkeeping(), addr) catch @panic("fable: out of memory");
    if (!entry.found_existing) {
        const h = bookkeeping().create(WeakHandle) catch @panic("fable: out of memory");
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
            const h = bookkeeping().create(WeakHandle) catch @panic("fable: out of memory");
            h.* = .{ .target = null, .refs = 1 };
            return h;
        };
        return weakHandle(@intFromPtr(p));
    }
    return weakHandle(@intFromPtr(target));
}

pub fn weakLetGo(h: *WeakHandle) void {
    h.refs -= 1;
    if (h.refs != 0) return;
    if (h.target) |addr| _ = thread.weak.remove(addr);
    bookkeeping().destroy(h);
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

        pub fn fable_show(b: *Shower, x: *Self, depth: i32) *Layout {
            _ = x;
            _ = depth;
            return b.word("System.WeakReference`1");
        }
    };
}

/// `WeakReference<'T>(target)`
pub fn weakNew(comptime W: type, target: @typeInfo(W).pointer.child.fable_weak) W {
    const c = rt.allocator.create(@typeInfo(W).pointer.child) catch @panic("fable: out of memory");
    c.* = .{ .handle = handleOf(target) };
    if (track) thread.stats.allocs += 1;
    return c;
}

/// `w.TryGetTarget(&target)`: the target (a reference of its own), or null once it is freed.
pub fn weakTryGet(w: anytype) ?@typeInfo(@TypeOf(w)).pointer.child.fable_weak {
    const T = @typeInfo(@TypeOf(w)).pointer.child.fable_weak;
    const addr = w.handle.target orelse return null;
    const target: CellOf(T) = @ptrFromInt(addr);
    return @as(T, dup(target));
}

/// `w.SetTarget(target)`
pub fn weakSet(w: anytype, target: @typeInfo(@TypeOf(w)).pointer.child.fable_weak) void {
    const old = w.handle;
    w.handle = handleOf(target);
    weakLetGo(old);
}
