//! Stack arenas: `[<StackArena(bytes)>]` (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const rt = @import("fable_rt.zig");
const thread = rt.thread;

/// (a cell of this thread's `[<StackArena>]`: its memory is that function's stack)
pub inline fn inThreadArena(c: anytype) bool {
    if (comptime !rt.uses_arena) return false;
    if (thread.arena == null) return false;
    const bytes: [*]u8 = @ptrCast(c);
    return arenaOwning(bytes[0..@sizeOf(@TypeOf(c.*))]) != null;
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

/// Allocator vtable routing the current thread's `[<StackArena>]` allocations to its
/// innermost active `Arena`, falling back to `rt.allocator` when unowned.
pub const arena_router: std.mem.Allocator = .{ .ptr = undefined, .vtable = &.{
    .alloc = routerAlloc,
    .resize = routerResize,
    .remap = routerRemap,
    .free = routerFree,
} };

/// (the arena of this thread that holds `memory`, if any)
pub fn arenaOwning(memory: []u8) ?*Arena {
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
    return rt.allocator.rawAlloc(len, alignment, ret_addr);
}

fn routerResize(_: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) bool {
    if (arenaOwning(memory)) |a| return a.fba.allocator().rawResize(memory, alignment, new_len, ret_addr);
    return rt.allocator.rawResize(memory, alignment, new_len, ret_addr);
}

fn routerRemap(_: *anyopaque, memory: []u8, alignment: std.mem.Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
    if (arenaOwning(memory)) |a| return a.fba.allocator().rawRemap(memory, alignment, new_len, ret_addr);
    return rt.allocator.rawRemap(memory, alignment, new_len, ret_addr);
}

fn routerFree(_: *anyopaque, memory: []u8, alignment: std.mem.Alignment, ret_addr: usize) void {
    if (arenaOwning(memory)) |a| {
        a.fba.allocator().rawFree(memory, alignment, ret_addr);
        a.live -= 1;
        return;
    }
    rt.allocator.rawFree(memory, alignment, ret_addr);
}

/// A `[<StackArena>]` function starts: the cells this thread makes come from `fba` (a buffer on
/// its stack) until it ends; an arena it calls stands in for it until that one ends.
/// Bookkeeping (`fable_sgc` / weak tables) stays on `rt.allocator` via `rt.bookkeeping()`.
pub fn arenaEnter(frame: *Arena, fba: *std.heap.FixedBufferAllocator) void {
    frame.* = .{ .fba = fba, .outer = thread.arena };
    thread.arena = frame;
}

/// ... and ends. A cell made in the arena that is still alive now would point into a stack
/// frame that is gone: that is a panic (counted exactly, cell by cell, in every build).
pub fn arenaLeave(frame: *Arena) void {
    thread.arena = frame.outer;
    if (frame.live != 0) @panic("fable: a value made in a [<StackArena>] function outlived it");
}
