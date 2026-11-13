//! The hand-written part of the Zig runtime library: reference-counted cells, reuse tokens,
//! the generic dup/drop/equality that generated code calls, and conversions between numbers.
//! The cycle collector will live here too.
const std = @import("std");
const builtin = @import("builtin");
const root = @import("root");
pub const sgc = @import("fable_sgc.zig");
pub const unicode = @import("fable_unicode.zig");

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
pub var allocator: std.mem.Allocator = if (builtin.link_libc)
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
const thread = if (sgc.per_thread) struct {
    threadlocal var stats: Stats = .{};
    threadlocal var collector: sgc.Gc = undefined;
    threadlocal var collector_ready: bool = false;
    threadlocal var current: ?Exn = null;
    threadlocal var weak: std.AutoHashMapUnmanaged(usize, *WeakHandle) = .empty;
    threadlocal var book: ?std.mem.Allocator = null;
} else struct {
    var stats: Stats = .{};
    var collector: sgc.Gc = undefined;
    var collector_ready: bool = false;
    var current: ?Exn = null;
    var weak: std.AutoHashMapUnmanaged(usize, *WeakHandle) = .empty;
    var book: ?std.mem.Allocator = null;
};

/// Where the runtime's own bookkeeping (the collector's, the table of weak references) comes
/// from: the allocator, unless a stack arena stands in for it now.
fn bookkeeping() std.mem.Allocator {
    return thread.book orelse allocator;
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
    const c = allocator.create(C) catch @panic("fable: out of memory");
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

pub inline fn isUnique(c: anytype) bool {
    return c.@"$rc" == 1;
}

pub inline fn retain(c: anytype) void {
    c.@"$rc" += 1;
    if (track) thread.stats.dups += 1;
    if (gcOf(c)) |h| thread.collector.onRetain(h);
}

/// Take one reference off a cell that is known to be shared.
pub inline fn release(c: anytype) void {
    c.@"$rc" -= 1;
    if (track) thread.stats.decs += 1;
    if (gcOf(c)) |h| thread.collector.onRelease(h);
}

/// Take one reference off; true when it was the last one, and the caller gives up what the
/// cell holds and frees it. (False also when the cell's whole structure died with this
/// reference: the collector frees all of it, this cell included.)
pub inline fn releaseIsLast(c: anytype) bool {
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

fn movedOut(_: void, h: *sgc.Hdr) void {
    thread.collector.onMoveOut(h);
}

pub inline fn free(c: anytype) void {
    if (track) thread.stats.frees += 1;
    // (a cell that weak references point at: they see it is gone)
    if (thread.weak.count() != 0) weakGone(@intFromPtr(c));
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
fn isCount(comptime field_name: []const u8) bool {
    return std.mem.eql(u8, field_name, "$rc") or std.mem.eql(u8, field_name, "$gc");
}

fn isCellPtr(comptime T: type) bool {
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
                if (!isCellPtr(F) or F == Exn) return false;
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

fn retainAll(x: anytype) void {
    const T = @TypeOf(x);
    if (comptime !isManaged(T)) return;
    if (comptime isFunc(T)) {
        if (x.env) |e| retain(e);
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
    if (T == Exn) {
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

fn isCollection(comptime T: type) bool {
    return @typeInfo(T) == .@"union" and @hasDecl(T, "fable_collection");
}

/// The entries of a map or a set, in order: the cells of its tree from left to right.
fn TreeWalk(comptime T: type) type {
    const Node = @typeInfo(@typeInfo(T).@"union".field_types[1]).pointer.child;
    return struct {
        stack: [64]*Node = undefined,
        len: usize = 0,

        fn init(tree: T) @This() {
            var w: @This() = .{};
            w.pushLeft(tree);
            return w;
        }

        fn pushLeft(w: *@This(), tree: T) void {
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

        fn next(w: *@This()) ?*Node {
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

fn entryCompare(a: anytype, b: @TypeOf(a)) i32 {
    const c = compare(a.key, b.key);
    if (c != 0) return c;
    if (comptime @hasField(@TypeOf(a.*), "value")) return compare(a.value, b.value);
    return 0;
}

fn treeEql(a: anytype, b: @TypeOf(a)) bool {
    var x = TreeWalk(@TypeOf(a)).init(a);
    var y = TreeWalk(@TypeOf(a)).init(b);
    while (true) {
        const p = x.next();
        const q = y.next();
        if (p == null or q == null) return p == null and q == null;
        if (!entryEql(p.?, q.?)) return false;
    }
}

fn treeCompare(a: anytype, b: @TypeOf(a)) i32 {
    var x = TreeWalk(@TypeOf(a)).init(a);
    var y = TreeWalk(@TypeOf(a)).init(b);
    while (true) {
        const p = x.next() orelse return if (y.next() == null) 0 else -1;
        const q = y.next() orelse return 1;
        const c = entryCompare(p, q);
        if (c != 0) return c;
    }
}

fn treeHash(x: anytype) i32 {
    var w = TreeWalk(@TypeOf(x)).init(x);
    var h: i32 = 17;
    while (w.next()) |n| {
        h = hashWith(h, hash(n.key));
        if (comptime @hasField(@TypeOf(n.*), "value")) h = hashWith(h, hash(n.value));
    }
    return h;
}

/// Structural equality, as F#'s `=` on records, unions, tuples and options.
pub fn eql(a: anytype, b: @TypeOf(a)) bool {
    const T = @TypeOf(a);
    if (comptime isCollection(T)) return treeEql(a, b);
    if (comptime isSlice(T)) {
        if (a.len != b.len) return false;
        for (a, b) |x, y| {
            if (!eql(x, y)) return false;
        }
        return true;
    }
    // (.NET's mutable collections are equal only to themselves)
    if (comptime isCellPtr(T) and @hasDecl(@typeInfo(T).pointer.child, "fable_identity")) return a == b;
    // (an array is equal to another with equal items, as F#'s `=` has it)
    if (comptime isCellPtr(T) and @hasDecl(@typeInfo(T).pointer.child, "fable_array")) return a == b or eql(a.items, b.items);
    if (comptime !isManaged(T)) return std.meta.eql(a, b);
    if (comptime isFunc(T)) @compileError("function values cannot be compared");
    if (T == Exn) return a == b;
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
            if (std.meta.activeTag(a) != std.meta.activeTag(b)) return false;
            switch (a) {
                inline else => |pa, tag| return eql(pa, @field(b, @tagName(tag))),
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
    const c = allocator.create(C) catch @panic("fable: out of memory");
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
    const old = @field(owner, field);
    @field(owner, field) = value;
    if (gcOf(owner)) |h| {
        eachHdr(old, h, unstored);
        eachHdr(value, h, stored);
    } else {
        touch(value);
    }
    drop(old);
}

fn unstored(owner: *sgc.Hdr, old: *sgc.Hdr) void {
    thread.collector.onUnstore(owner, old);
}

fn stored(owner: *sgc.Hdr, child: *sgc.Hdr) void {
    thread.collector.onStore(owner, child);
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
        Ok: struct { ResultValue: T },
        Error: struct { ErrorValue: E },
    };
}

/// F#'s `Choice` of two to seven cases.
pub fn Choice2(comptime T1: type, comptime T2: type) type {
    return union(enum) { Choice1Of2: struct { Item: T1 }, Choice2Of2: struct { Item: T2 } };
}

pub fn Choice3(comptime T1: type, comptime T2: type, comptime T3: type) type {
    return union(enum) { Choice1Of3: struct { Item: T1 }, Choice2Of3: struct { Item: T2 }, Choice3Of3: struct { Item: T3 } };
}

pub fn Choice4(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type) type {
    return union(enum) { Choice1Of4: struct { Item: T1 }, Choice2Of4: struct { Item: T2 }, Choice3Of4: struct { Item: T3 }, Choice4Of4: struct { Item: T4 } };
}

pub fn Choice5(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type) type {
    return union(enum) { Choice1Of5: struct { Item: T1 }, Choice2Of5: struct { Item: T2 }, Choice3Of5: struct { Item: T3 }, Choice4Of5: struct { Item: T4 }, Choice5Of5: struct { Item: T5 } };
}

pub fn Choice6(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type) type {
    return union(enum) { Choice1Of6: struct { Item: T1 }, Choice2Of6: struct { Item: T2 }, Choice3Of6: struct { Item: T3 }, Choice4Of6: struct { Item: T4 }, Choice5Of6: struct { Item: T5 }, Choice6Of6: struct { Item: T6 } };
}

pub fn Choice7(comptime T1: type, comptime T2: type, comptime T3: type, comptime T4: type, comptime T5: type, comptime T6: type, comptime T7: type) type {
    return union(enum) { Choice1Of7: struct { Item: T1 }, Choice2Of7: struct { Item: T2 }, Choice3Of7: struct { Item: T3 }, Choice4Of7: struct { Item: T4 }, Choice5Of7: struct { Item: T5 }, Choice6Of7: struct { Item: T6 }, Choice7Of7: struct { Item: T7 } };
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
        @"$rc": u32 = 1,
        @"$gc": GcHdr(fable_cyclic) = undefined,
        state: union(enum) {
            thunk: Func(*const fn (?*Env, void) Raised!T),
            value: T,
            failed: Exn,
        },

        pub fn fable_show(b: *Shower, x: *Self, depth: i32) *Layout {
            return switch (x.state) {
                // (.NET writes the value's ToString)
                .value => |v| showPlain(b, v, depth),
                else => b.word("Value is not created."),
            };
        }
    };
}

/// `lazy (expr)`
pub fn lazyNew(comptime L: type, thunk: anytype) L {
    const C = @typeInfo(L).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = allocator.create(C) catch @panic("fable: out of memory");
    c.* = .{ .state = .{ .thunk = dup(thunk) } };
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

/// `Lazy.CreateFromValue v`
pub fn lazyOf(comptime L: type, value: anytype) L {
    const C = @typeInfo(L).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = allocator.create(C) catch @panic("fable: out of memory");
    c.* = .{ .state = .{ .value = dup(value) } };
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

fn lazyState(l: anytype, new_state: @TypeOf(l.state)) void {
    const old = l.state;
    l.state = new_state;
    if (gcOf(l)) |h| {
        eachHdr(old, h, unstored);
        eachHdr(l.state, h, stored);
    } else touch(l.state);
    drop(old);
}

/// `l.Force()`, `l.Value`
pub fn lazyForce(l: anytype) Raised!@FieldType(@TypeOf(l.state), "value") {
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
        Empty,
        Cons: *struct { @"$rc": u32 = 1, @"$gc": GcHdr(fable_cyclic) = undefined, Head: T, Tail: List(T) },
    };
}

// ---------------------------------------------------------------------------------------------
// Arrays
//
// An F# array is a counted cell that holds its items, with an identity as on .NET: two names
// for one array see each other's assignments. An item that is read is a reference of its own;
// an item that is assigned gives up the one that was there. An index outside the array raises
// what it raises on .NET.
// ---------------------------------------------------------------------------------------------

/// F#'s array of `T`.
pub fn Array(comptime T: type) type {
    return *struct {
        pub const fable_array = T;
        pub const fable_cyclic = holdsCyclic(T);
        @"$rc": u32 = 1,
        @"$gc": GcHdr(fable_cyclic) = undefined,
        items: []T,
    };
}

/// The type of the items of the array type `A`.
pub fn ItemOf(comptime A: type) type {
    return @typeInfo(A).pointer.child.fable_array;
}

fn arrayItems(comptime A: type, n: usize) []ItemOf(A) {
    return allocator.alloc(ItemOf(A), n) catch @panic("fable: out of memory");
}

/// A new array that owns `items`.
fn arrayFrom(comptime A: type, items: []ItemOf(A)) A {
    const C = @typeInfo(A).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = allocator.create(C) catch @panic("fable: out of memory");
    c.* = .{ .items = items };
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

/// `[| a; b; c |]`
pub fn arrayOf(comptime A: type, values: anytype) A {
    const items = arrayItems(A, values.len);
    inline for (values, 0..) |v, i| items[i] = dup(@as(ItemOf(A), v));
    return arrayFrom(A, items);
}

/// Is all-zero memory a value of this type? (It is .NET's null, zero, false and None.)
fn hasZero(comptime T: type) bool {
    if (T == String) return true;
    return switch (@typeInfo(T)) {
        .int, .float, .bool, .void, .optional => true,
        .@"struct" => |s| blk: {
            if (@hasDecl(T, "fable_func")) break :blk false;
            for (s.field_types) |F| {
                if (!hasZero(F)) break :blk false;
            }
            break :blk true;
        },
        else => false,
    };
}

/// `Array.zeroCreate n`. .NET fills the array with null where the items are records, unions
/// or functions; here those have no null, so only an empty array of them can be made this
/// way (anything longer raises `NotSupportedException`).
pub fn arrayZero(comptime A: type, n: i32) Raised!A {
    if (n < 0) return countNegative(n);
    const items = arrayItems(A, @intCast(n));
    if (comptime hasZero(ItemOf(A))) {
        @memset(items, comptime std.mem.zeroes(ItemOf(A)));
    } else if (n != 0) {
        allocator.free(items);
        return raise(NotSupportedException, str("Array.zeroCreate of a type without a null value: use Array.create or Array.init"));
    }
    return arrayFrom(A, items);
}

/// `Array.create n x`
pub fn arrayCreate(comptime A: type, n: i32, x: ItemOf(A)) Raised!A {
    if (n < 0) return countNegative(n);
    const items = arrayItems(A, @intCast(n));
    for (items) |*item| item.* = dup(x);
    return arrayFrom(A, items);
}

/// Give up the first `n` of the items that were being made for an array.
fn arrayAbandon(items: anytype, n: usize) void {
    for (items[0..n]) |item| drop(item);
    allocator.free(items);
}

/// `Array.init n f`
pub fn arrayInit(comptime A: type, n: i32, f: anytype) Raised!A {
    if (n < 0) return countNegative(n);
    const items = arrayItems(A, @intCast(n));
    for (items, 0..) |*item, i| {
        item.* = f.code(f.env, @as(i32, @intCast(i))) catch |e| {
            arrayAbandon(items, i);
            return e;
        };
    }
    return arrayFrom(A, items);
}

pub inline fn arrayLen(a: anytype) i32 {
    return @intCast(a.items.len);
}

fn indexOutside() Raised {
    return raise(IndexOutOfRangeException, str("Index was outside the bounds of the array."));
}

/// `a.[i]`: a reference of its own to the item.
pub inline fn arrayGet(a: anytype, i: i32) Raised!ItemOf(@TypeOf(a)) {
    if (i < 0 or i >= a.items.len) return indexOutside();
    return dup(a.items[@intCast(i)]);
}

/// `a.[i] <- value`. The collector is told what the array no longer points at and what it
/// points at now: this is where a cycle can be closed.
pub inline fn arraySet(a: anytype, i: i32, value: ItemOf(@TypeOf(a))) Raised!void {
    if (i < 0 or i >= a.items.len) return indexOutside();
    arrayPut(a, @intCast(i), dup(value));
}

fn arrayPut(a: anytype, i: usize, value: @typeInfo(@TypeOf(a.items)).pointer.child) void {
    const old = a.items[i];
    a.items[i] = value;
    if (gcOf(a)) |h| {
        eachHdr(old, h, unstored);
        eachHdr(value, h, stored);
    } else {
        touch(value);
    }
    drop(old);
}

/// A new array of the items of `a` from `from` that are `n`: they are known to be inside.
fn arrayPart(a: anytype, from: usize, n: usize) @TypeOf(a) {
    const A = @TypeOf(a);
    const items = arrayItems(A, n);
    for (items, a.items[from..][0..n]) |*to, item| to.* = dup(item);
    return arrayFrom(A, items);
}

/// `a.[lo..hi]`: what of it is inside the array.
pub fn arraySlice(a: anytype, lo: ?i32, hi: ?i32) @TypeOf(a) {
    const len: i32 = @intCast(a.items.len);
    const from: i32 = @max(lo orelse 0, 0);
    const to: i32 = @min(hi orelse len - 1, len - 1);
    if (to < from) return arrayPart(a, 0, 0);
    return arrayPart(a, @intCast(from), @intCast(to - from + 1));
}

/// `Array.copy a`
pub fn arrayCopy(a: anytype) @TypeOf(a) {
    return arrayPart(a, 0, a.items.len);
}

/// `Array.sub a start count`
pub fn arraySub(a: anytype, start: i32, count: i32) Raised!@TypeOf(a) {
    if (start < 0) return raise(ArgumentException, format(.{ "The input must be non-negative.\nstartIndex = ", start, " (Parameter 'startIndex')" }));
    if (count < 0) return countNegative(count);
    const len: i32 = @intCast(a.items.len);
    if (start + count > len) return raise(ArgumentOutOfRangeException, format(.{ "The index is outside the legal range.\ncount = ", count, ", array.Length = ", len, " (Parameter 'count')" }));
    return arrayPart(a, @intCast(start), @intCast(count));
}

/// `Array.append a b`
pub fn arrayAppend(a: anytype, b: @TypeOf(a)) @TypeOf(a) {
    const A = @TypeOf(a);
    const items = arrayItems(A, a.items.len + b.items.len);
    for (items[0..a.items.len], a.items) |*to, item| to.* = dup(item);
    for (items[a.items.len..], b.items) |*to, item| to.* = dup(item);
    return arrayFrom(A, items);
}

/// `Array.rev a`
pub fn arrayRev(a: anytype) @TypeOf(a) {
    const A = @TypeOf(a);
    const n = a.items.len;
    const items = arrayItems(A, n);
    for (items, 0..) |*to, i| to.* = dup(a.items[n - 1 - i]);
    return arrayFrom(A, items);
}

/// `Array.fill a start count x`
pub fn arrayFill(a: anytype, start: i32, count: i32, x: ItemOf(@TypeOf(a))) Raised!void {
    if (start < 0) return raise(ArgumentException, format(.{ "The input must be non-negative.\nstartIndex = ", start, " (Parameter 'startIndex')" }));
    if (count < 0) return countNegative(count);
    var i = start;
    while (i < start + count) : (i += 1) {
        if (i >= a.items.len) return indexOutside();
        arrayPut(a, @intCast(i), dup(x));
    }
}

/// `Array.ofList xs`
pub fn arrayOfList(comptime A: type, xs: List(ItemOf(A))) A {
    var n: usize = 0;
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) n += 1;
    const items = arrayItems(A, n);
    rest = xs;
    for (items) |*to| {
        to.* = dup(rest.Cons.Head);
        rest = rest.Cons.Tail;
    }
    return arrayFrom(A, items);
}

/// The list of `items`, each a new reference.
fn listOf(comptime T: type, items: []const T) List(T) {
    var all: List(T) = .Empty;
    var i = items.len;
    while (i > 0) {
        i -= 1;
        const tail = all;
        all = .{ .Cons = cell(List(T), .Cons, .{ .Head = dup(items[i]), .Tail = tail }) };
    }
    return all;
}

/// `Array.toList a`
pub fn arrayToList(a: anytype) List(ItemOf(@TypeOf(a))) {
    return listOf(ItemOf(@TypeOf(a)), a.items);
}

/// `Array.contains x a`
pub fn arrayContains(x: anytype, a: Array(@TypeOf(x))) bool {
    for (a.items) |item| {
        if (eql(item, x)) return true;
    }
    return false;
}

/// `Array.map f a`
pub fn arrayMap(comptime A: type, f: anytype, a: anytype) Raised!A {
    const items = arrayItems(A, a.items.len);
    for (items, 0..) |*to, i| {
        to.* = f.code(f.env, dup(a.items[i])) catch |e| {
            arrayAbandon(items, i);
            return e;
        };
    }
    return arrayFrom(A, items);
}

/// `Array.mapi f a`
pub fn arrayMapi(comptime A: type, f: anytype, a: anytype) Raised!A {
    const items = arrayItems(A, a.items.len);
    for (items, 0..) |*to, i| {
        to.* = apply2(ItemOf(A), f, @as(i32, @intCast(i)), dup(a.items[i])) catch |e| {
            arrayAbandon(items, i);
            return e;
        };
    }
    return arrayFrom(A, items);
}

/// `Array.iter f a`
pub fn arrayIter(f: anytype, a: anytype) Raised!void {
    for (0..a.items.len) |i| try f.code(f.env, dup(a.items[i]));
}

/// `Array.iteri f a`
pub fn arrayIteri(f: anytype, a: anytype) Raised!void {
    for (0..a.items.len) |i| try apply2(void, f, @as(i32, @intCast(i)), dup(a.items[i]));
}

/// `Array.fold f state a`: `state` is the caller's, the result is a reference of its own.
pub fn arrayFold(f: anytype, state: anytype, a: anytype) Raised!@TypeOf(state) {
    var acc = dup(state);
    for (0..a.items.len) |i| acc = try apply2(@TypeOf(state), f, acc, dup(a.items[i]));
    return acc;
}

/// `Array.filter f a`
pub fn arrayFilter(f: anytype, a: anytype) Raised!@TypeOf(a) {
    const A = @TypeOf(a);
    const keep = allocator.alloc(bool, a.items.len) catch @panic("fable: out of memory");
    defer allocator.free(keep);
    var n: usize = 0;
    for (keep, 0..) |*k, i| {
        k.* = try f.code(f.env, dup(a.items[i]));
        n += @intFromBool(k.*);
    }
    const items = arrayItems(A, n);
    var at: usize = 0;
    for (keep, 0..) |k, i| {
        if (k and i < a.items.len and at < n) {
            items[at] = dup(a.items[i]);
            at += 1;
        }
    }
    return arrayFrom(A, items);
}

/// `Array.exists f a`
pub fn arrayExists(f: anytype, a: anytype) Raised!bool {
    for (0..a.items.len) |i| {
        if (try f.code(f.env, dup(a.items[i]))) return true;
    }
    return false;
}

/// `Array.forall f a`
pub fn arrayForall(f: anytype, a: anytype) Raised!bool {
    for (0..a.items.len) |i| {
        if (!try f.code(f.env, dup(a.items[i]))) return false;
    }
    return true;
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
fn showSeq(b: *Shower, items: []const *Layout, more: bool) *Layout {
    var all: std.ArrayList(*Layout) = .empty;
    all.appendSlice(b.arena, items) catch @panic("fable: out of memory");
    if (more) all.append(b.arena, b.word("...")) catch @panic("fable: out of memory");
    const list = if (all.items.len == 0)
        b.word("[]")
    else
        b.tight(b.tight(b.ascii(false, "[", true), b.separated(all.items, ";")), b.ascii(true, "]", false));
    return b.join(b.word("seq"), list, .{ .breakable = 2 });
}

fn outOfRange() Raised {
    return raise(ArgumentOutOfRangeException, str("Index was out of range. Must be non-negative and less than the size of the collection. (Parameter 'index')"));
}

/// F#'s `ResizeArray<T>`: .NET's `List<T>`.
pub fn ResizeArray(comptime T: type) type {
    return *struct {
        const Self = @This();
        pub const fable_identity = {};
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
            var items: [4]*Layout = undefined;
            const n = @min(x.items.len, 4);
            for (x.items[0..n], 0..) |item, i| items[i] = b.show(item, .bracket_if_tuple, depth - 1);
            return showSeq(b, items[0..n], x.items.len > 4);
        }
    };
}

fn rItem(comptime R: type) type {
    return @typeInfo(@FieldType(@typeInfo(R).pointer.child, "items")).pointer.child;
}

pub fn raNew(comptime R: type) R {
    const C = @typeInfo(R).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = allocator.create(C) catch @panic("fable: out of memory");
    c.* = .{};
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

fn raGrow(r: anytype, need: usize) void {
    if (need <= r.capacity) return;
    const cap = @max(need, @max(4, r.capacity * 2));
    const T = rItem(@TypeOf(r));
    const block = allocator.alloc(T, cap) catch @panic("fable: out of memory");
    @memcpy(block[0..r.items.len], r.items);
    if (r.capacity != 0) allocator.free(r.items.ptr[0..r.capacity]);
    r.items = block[0..r.items.len];
    r.capacity = cap;
}

/// `r.Add x`
pub fn raAdd(r: anytype, x: rItem(@TypeOf(r))) void {
    raGrow(r, r.items.len + 1);
    r.items.len += 1;
    r.items[r.items.len - 1] = undefined;
    // (put in place as an assignment of the array would be, for the collector)
    const n = r.items.len - 1;
    r.items[n] = dup(x);
    if (gcOf(r)) |h| eachHdr(r.items[n], h, stored) else touch(r.items[n]);
}

/// `ResizeArray xs` of a list
pub fn raOfList(comptime R: type, xs: List(rItem(R))) R {
    const r = raNew(R);
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) raAdd(r, rest.Cons.Head);
    return r;
}

/// `r.AddRange xs` of a list
pub fn raAddList(r: anytype, xs: List(rItem(@TypeOf(r)))) void {
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) raAdd(r, rest.Cons.Head);
}

pub inline fn raCount(r: anytype) i32 {
    return @intCast(r.items.len);
}

/// `r.[i]`
pub fn raGet(r: anytype, i: i32) Raised!rItem(@TypeOf(r)) {
    if (i < 0 or i >= r.items.len) return outOfRange();
    return dup(r.items[@intCast(i)]);
}

/// `r.[i] <- x`
pub fn raSet(r: anytype, i: i32, x: rItem(@TypeOf(r))) Raised!void {
    if (i < 0 or i >= r.items.len) return outOfRange();
    arrayPut(r, @intCast(i), dup(x));
}

/// `r.Insert(i, x)`
pub fn raInsert(r: anytype, i: i32, x: rItem(@TypeOf(r))) Raised!void {
    if (i < 0 or i > r.items.len) return raise(ArgumentOutOfRangeException, str("Index must be within the bounds of the List. (Parameter 'index')"));
    raGrow(r, r.items.len + 1);
    const at: usize = @intCast(i);
    r.items.len += 1;
    std.mem.copyBackwards(rItem(@TypeOf(r)), r.items[at + 1 ..], r.items[at .. r.items.len - 1]);
    r.items[at] = dup(x);
    if (gcOf(r)) |h| eachHdr(r.items[at], h, stored) else touch(r.items[at]);
}

fn raTake(r: anytype, at: usize) void {
    const old = r.items[at];
    std.mem.copyForwards(rItem(@TypeOf(r)), r.items[at .. r.items.len - 1], r.items[at + 1 ..]);
    r.items.len -= 1;
    if (gcOf(r)) |h| eachHdr(old, h, unstored);
    drop(old);
}

/// `r.RemoveAt i`
pub fn raRemoveAt(r: anytype, i: i32) Raised!void {
    if (i < 0 or i >= r.items.len) return outOfRange();
    raTake(r, @intCast(i));
}

/// `r.IndexOf x`
pub fn raIndexOf(r: anytype, x: rItem(@TypeOf(r))) i32 {
    for (r.items, 0..) |item, i| {
        if (eql(item, x)) return @intCast(i);
    }
    return -1;
}

pub fn raContains(r: anytype, x: rItem(@TypeOf(r))) bool {
    return raIndexOf(r, x) >= 0;
}

/// `r.Remove x`: the first item equal to x, if there is one.
pub fn raRemove(r: anytype, x: rItem(@TypeOf(r))) bool {
    const i = raIndexOf(r, x);
    if (i < 0) return false;
    raTake(r, @intCast(i));
    return true;
}

/// `r.Clear()`
pub fn raClear(r: anytype) void {
    while (r.items.len != 0) raTake(r, r.items.len - 1);
}

/// `r.Reverse()`
pub fn raReverse(r: anytype) void {
    std.mem.reverse(rItem(@TypeOf(r)), r.items);
}

/// `r.Sort()`: by `compare`. (Equal items stay in their order; on .NET their order is not
/// promised, and for F# values two equal items cannot be told apart.)
pub fn raSort(r: anytype) void {
    const T = rItem(@TypeOf(r));
    std.sort.insertion(T, r.items, {}, struct {
        fn lt(_: void, a: T, b: T) bool {
            return compare(a, b) < 0;
        }
    }.lt);
}

/// `r.ToArray()`
pub fn raToArray(r: anytype) Array(rItem(@TypeOf(r))) {
    const A = Array(rItem(@TypeOf(r)));
    const items = arrayItems(A, r.items.len);
    for (items, r.items) |*to, item| to.* = dup(item);
    return arrayFrom(A, items);
}

/// What a loop over it walks: its items now, as a list.
pub fn raToList(r: anytype) List(rItem(@TypeOf(r))) {
    return listOf(rItem(@TypeOf(r)), r.items);
}

/// The text `string x` and `{x}` give for a key or a value: unquoted, as .NET's ToString.
fn showPlain(b: *Shower, x: anytype, depth: i32) *Layout {
    const T = @TypeOf(x);
    if (T == String) return b.leaf(false, b.arena.dupe(u16, unitsOf(x)) catch @panic("fable: out of memory"), false);
    if (T == u16) return b.leaf(false, b.arena.dupe(u16, &.{x}) catch @panic("fable: out of memory"), false);
    switch (@typeInfo(T)) {
        .int, .float, .bool => {
            var scratch: [scratch_len]u8 align(2) = undefined;
            const piece = pieceOf(.{}, x, &scratch);
            return b.ascii(false, piece.ascii, false);
        },
        else => return b.show(x, .bracket_if_tuple, depth),
    }
}

/// .NET's `Dictionary<K, V>` (`hashed = true` and V = void: `HashSet<K>`).
pub fn HashTable(comptime K: type, comptime V: type, comptime is_set: bool) type {
    return *struct {
        const Self = @This();
        pub const fable_identity = {};
        pub const fable_cyclic = holdsCyclic(K) or holdsCyclic(V);
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

        pub fn fable_free(c: *Self) void {
            if (c.capacity != 0) {
                allocator.free(c.entries.ptr[0..c.capacity]);
                allocator.free(c.buckets);
            }
        }

        pub fn fable_show(b: *Shower, x: *Self, depth: i32) *Layout {
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
                    b.show(kv.key, .bracket_if_tuple, depth - 1)
                else
                    b.tight(b.tight(b.ascii(false, "[", true), b.join(b.tight(showPlain(b, kv.key, depth - 1), b.ascii(true, ",", false)), showPlain(b, kv.value, depth - 1), .unbreakable)), b.ascii(true, "]", false));
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

fn KeyOf(comptime D: type) type {
    const Entry = @typeInfo(D).pointer.child.Entry;
    return @FieldType(@typeInfo(@FieldType(Entry, "kv")).optional.child, "key");
}

fn ValueOf(comptime D: type) type {
    const Entry = @typeInfo(D).pointer.child.Entry;
    return @FieldType(@typeInfo(@FieldType(Entry, "kv")).optional.child, "value");
}

pub fn htNew(comptime D: type) D {
    const C = @typeInfo(D).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = allocator.create(C) catch @panic("fable: out of memory");
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

fn htBucket(d: anytype, h: i32) usize {
    return @as(u32, @bitCast(h)) % @as(u32, @intCast(d.buckets.len));
}

fn htResize(d: anytype, size: usize) void {
    const C = @TypeOf(d.*);
    const block = allocator.alloc(C.Entry, size) catch @panic("fable: out of memory");
    @memcpy(block[0..d.entries.len], d.entries);
    if (d.capacity != 0) {
        allocator.free(d.entries.ptr[0..d.capacity]);
        allocator.free(d.buckets);
    }
    d.entries = block[0..d.entries.len];
    d.capacity = size;
    d.buckets = allocator.alloc(i32, size) catch @panic("fable: out of memory");
    @memset(d.buckets, 0);
    for (d.entries, 0..) |*e, i| {
        if (e.kv == null) continue;
        const bucket = htBucket(d, e.hash);
        e.next = d.buckets[bucket] - 1;
        d.buckets[bucket] = @intCast(i + 1);
    }
}

fn htFind(d: anytype, key: KeyOf(@TypeOf(d))) ?usize {
    if (d.buckets.len == 0) return null;
    const h = hash(key);
    var i = d.buckets[htBucket(d, h)] - 1;
    while (i >= 0) {
        const e = &d.entries[@intCast(i)];
        if (e.hash == h and eql(e.kv.?.key, key)) return @intCast(i);
        i = e.next;
    }
    return null;
}

/// Put an entry in: false (and nothing changed) if the key is there and `replace` is false.
fn htPut(d: anytype, key: KeyOf(@TypeOf(d)), value: ValueOf(@TypeOf(d)), replace: bool) bool {
    if (htFind(d, key)) |i| {
        if (!replace) return false;
        const e = &d.entries[i];
        const old = e.kv.?.value;
        e.kv.?.value = dup(value);
        if (gcOf(d)) |h| {
            eachHdr(old, h, unstored);
            eachHdr(e.kv.?.value, h, stored);
        } else touch(e.kv.?.value);
        drop(old);
        return true;
    }
    if (d.buckets.len == 0) htResize(d, htNextSize(0));
    const h = hash(key);
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
    if (gcOf(d)) |hdr| eachHdr(d.entries[at].kv.?, hdr, stored) else touch(d.entries[at].kv.?);
    return true;
}

/// `d.Add(k, v)`
pub fn dictAdd(d: anytype, key: KeyOf(@TypeOf(d)), value: ValueOf(@TypeOf(d))) Raised!void {
    if (!htPut(d, key, value, false)) {
        return raise(ArgumentException, format(.{ "An item with the same key has already been added. Key: ", arg(.{ .kind = 'O' }, key) }));
    }
}

/// `d.[k] <- v`
pub fn dictSet(d: anytype, key: KeyOf(@TypeOf(d)), value: ValueOf(@TypeOf(d))) void {
    _ = htPut(d, key, value, true);
}

/// `d.[k]`
pub fn dictGet(d: anytype, key: KeyOf(@TypeOf(d))) Raised!ValueOf(@TypeOf(d)) {
    const i = htFind(d, key) orelse return raise(KeyNotFoundException, format(.{ "The given key '", arg(.{ .kind = 'O' }, key), "' was not present in the dictionary." }));
    return dup(d.entries[i].kv.?.value);
}

/// `d.TryGetValue(k, &v)`: the value, or null.
pub fn dictTryGet(d: anytype, key: KeyOf(@TypeOf(d))) ?ValueOf(@TypeOf(d)) {
    const i = htFind(d, key) orelse return null;
    return dup(d.entries[i].kv.?.value);
}

pub fn dictContainsKey(d: anytype, key: KeyOf(@TypeOf(d))) bool {
    return htFind(d, key) != null;
}

pub fn dictContainsValue(d: anytype, value: ValueOf(@TypeOf(d))) bool {
    for (d.entries) |e| {
        if (e.kv) |kv| {
            if (eql(kv.value, value)) return true;
        }
    }
    return false;
}

/// `d.Remove k`
pub fn htRemove(d: anytype, key: KeyOf(@TypeOf(d))) bool {
    if (d.buckets.len == 0) return false;
    const h = hash(key);
    const bucket = htBucket(d, h);
    var last: i32 = -1;
    var i = d.buckets[bucket] - 1;
    while (i >= 0) {
        const e = &d.entries[@intCast(i)];
        if (e.hash == h and eql(e.kv.?.key, key)) {
            if (last < 0) d.buckets[bucket] = e.next + 1 else d.entries[@intCast(last)].next = e.next;
            const old = e.kv.?;
            e.kv = null;
            e.next = -3 - d.free_list;
            d.free_list = i;
            d.free_count += 1;
            if (gcOf(d)) |hdr| eachHdr(old, hdr, unstored);
            drop(old);
            return true;
        }
        last = i;
        i = e.next;
    }
    return false;
}

pub fn htCount(d: anytype) i32 {
    return @as(i32, @intCast(d.entries.len)) - d.free_count;
}

/// `d.Clear()`
pub fn htClear(d: anytype) void {
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
    const P = struct { KeyOf(@TypeOf(d)), ValueOf(@TypeOf(d)) };
    var items: std.ArrayList(P) = .empty;
    defer items.deinit(allocator);
    for (d.entries) |e| {
        if (e.kv) |kv| items.append(allocator, .{ kv.key, kv.value }) catch @panic("fable: out of memory");
    }
    return listOf(P, items.items);
}

pub fn dictKeys(d: anytype) List(KeyOf(@TypeOf(d))) {
    var items: std.ArrayList(KeyOf(@TypeOf(d))) = .empty;
    defer items.deinit(allocator);
    for (d.entries) |e| {
        if (e.kv) |kv| items.append(allocator, kv.key) catch @panic("fable: out of memory");
    }
    return listOf(KeyOf(@TypeOf(d)), items.items);
}

pub fn dictValues(d: anytype) List(ValueOf(@TypeOf(d))) {
    var items: std.ArrayList(ValueOf(@TypeOf(d))) = .empty;
    defer items.deinit(allocator);
    for (d.entries) |e| {
        if (e.kv) |kv| items.append(allocator, kv.value) catch @panic("fable: out of memory");
    }
    return listOf(ValueOf(@TypeOf(d)), items.items);
}

/// `h.Add x`: false if it was there.
pub fn setAdd(h: anytype, x: KeyOf(@TypeOf(h))) bool {
    return htPut(h, x, {}, false);
}

/// `HashSet xs` of a list
pub fn setOfList(comptime H: type, xs: List(KeyOf(H))) H {
    const h = htNew(H);
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) _ = setAdd(h, rest.Cons.Head);
    return h;
}

/// `h.UnionWith xs` of a list
pub fn setUnionList(h: anytype, xs: List(KeyOf(@TypeOf(h)))) void {
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) _ = setAdd(h, rest.Cons.Head);
}

pub fn setToList(h: anytype) List(KeyOf(@TypeOf(h))) {
    return dictKeys(h);
}

// ---------------------------------------------------------------------------------------------
// Stack arenas: `[<StackArena(bytes)>]`
// ---------------------------------------------------------------------------------------------

pub const Arena = struct {
    saved: std.mem.Allocator,
    live: i64,
};

/// A `[<StackArena>]` function starts: its cells come from `buffer` (on its stack) until it
/// ends. The runtime's own bookkeeping stays where it was.
pub fn arenaEnter(fba: *std.heap.FixedBufferAllocator) Arena {
    if (!thread.collector_ready) collectorSetup();
    const a: Arena = .{ .saved = allocator, .live = live() };
    thread.book = allocator;
    allocator = fba.allocator();
    return a;
}

/// ... and ends. (In builds that count, a cell made in the arena that is still alive now
/// would point into a stack frame that is gone: that is a panic.)
pub fn arenaLeave(a: Arena) void {
    allocator = a.saved;
    thread.book = null;
    if (track and live() != a.live) @panic("fable: a value made in a [<StackArena>] function outlived it");
}

// ---------------------------------------------------------------------------------------------
// Spans: `Span<'T>` and `ReadOnlySpan<'T>` are Zig slices of what they view (an array's items)
// ---------------------------------------------------------------------------------------------

/// `s.[i]`: where the item is (F# reads it, or assigns through it)
pub inline fn spanRef(s: anytype, i: i32) Raised!@TypeOf(&s[0]) {
    if (i < 0 or i >= s.len) return indexOutside();
    return &s[@intCast(i)];
}

/// `s.[i] <- x`
pub inline fn spanSet(s: anytype, i: i32, x: @typeInfo(@TypeOf(s)).pointer.child) Raised!void {
    if (i < 0 or i >= s.len) return indexOutside();
    s[@intCast(i)] = x;
}

/// `s.Slice(start)` and `s.Slice(start, length)`
pub fn spanSlice(s: anytype, start: i32, length: ?i32) Raised!@TypeOf(s) {
    const n = length orelse @as(i32, @intCast(s.len)) - start;
    if (start < 0 or n < 0 or start > s.len or n > @as(i32, @intCast(s.len)) - start) {
        return raise(ArgumentOutOfRangeException, str("Specified argument was out of the range of valid values."));
    }
    return s[@intCast(start)..][0..@intCast(n)];
}

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

fn weakGone(addr: usize) void {
    if (thread.weak.fetchRemove(addr)) |kv| kv.value.target = null;
}

fn weakHandle(addr: usize) *WeakHandle {
    const entry = thread.weak.getOrPut(bookkeeping(), addr) catch @panic("fable: out of memory");
    if (!entry.found_existing) {
        const h = bookkeeping().create(WeakHandle) catch @panic("fable: out of memory");
        h.* = .{ .target = addr, .refs = 0 };
        entry.value_ptr.* = h;
    }
    entry.value_ptr.*.refs += 1;
    return entry.value_ptr.*;
}

fn weakLetGo(h: *WeakHandle) void {
    h.refs -= 1;
    if (h.refs != 0) return;
    if (h.target) |addr| _ = thread.weak.remove(addr);
    bookkeeping().destroy(h);
}

/// .NET's `WeakReference<'T>` of a reference type (a class, a record with mutable fields, an
/// array, ...: a cell).
pub fn Weak(comptime T: type) type {
    if (comptime !isCellPtr(T)) @compileError("fable: a weak reference needs a reference type (a class, a record with mutable fields, an array, ...), not " ++ @typeName(T));
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
    const c = allocator.create(@typeInfo(W).pointer.child) catch @panic("fable: out of memory");
    c.* = .{ .handle = weakHandle(@intFromPtr(target)) };
    if (track) thread.stats.allocs += 1;
    return c;
}

/// `w.TryGetTarget(&target)`: the target (a reference of its own), or null once it is freed.
pub fn weakTryGet(w: anytype) ?@typeInfo(@TypeOf(w)).pointer.child.fable_weak {
    const T = @typeInfo(@TypeOf(w)).pointer.child.fable_weak;
    const addr = w.handle.target orelse return null;
    const target: T = @ptrFromInt(addr);
    return dup(target);
}

/// `w.SetTarget(target)`
pub fn weakSet(w: anytype, target: @typeInfo(@TypeOf(w)).pointer.child.fable_weak) void {
    const old = w.handle;
    w.handle = weakHandle(@intFromPtr(target));
    weakLetGo(old);
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
pub const Cycles = struct { holds: bool = false, generic: bool = false, instantiated: bool = false };

/// A file's own answer joined with those of the files it uses.
pub fn joinCycles(comptime own: Cycles, comptime used: anytype) Cycles {
    var r = own;
    inline for (used) |u| {
        r.holds = r.holds or u.holds;
        r.generic = r.generic or u.generic;
        r.instantiated = r.instantiated or u.instantiated;
    }
    return r;
}

/// Can a function value or an exception be part of a cycle in this program? What they hold
/// is not in their type, so a cell that holds one would have to be taken for cycle-capable
/// always. But a cycle needs an assignable field to close it, and one through a function
/// value needs an assignable field that can hold a function value. The program's root file
/// (the one with the entry point) says in `$cycles` whether the program makes a record with
/// such a field anywhere, joined over all the files it uses. If it does not, function values
/// and exceptions are never part of a cycle, and neither they nor the cells that hold them
/// need the collector. (Yes when the root file does not say.)
pub const functions_in_cycles: bool = blk: {
    if (!@hasDecl(root, "$cycles")) break :blk true;
    const c: Cycles = root.@"$cycles";
    break :blk c.holds or (c.generic and c.instantiated);
};

/// The type of a cell's `$gc` field: the collector's header, or nothing.
pub fn GcHdr(comptime cyclic: bool) type {
    return if (cyclic) sgc.Hdr else void;
}

fn hasGc(comptime C: type) bool {
    return @hasField(C, "$gc") and @FieldType(C, "$gc") == sgc.Hdr;
}

/// The collector's header of a cell, if it has one. An environment and an exception say so
/// themselves (their type does not show what they hold); for any other cell it is in its type.
inline fn gcOf(c: anytype) ?*sgc.Hdr {
    const C = @TypeOf(c.*);
    if (C == Env or C == ExnHeader) return c.gc;
    if (comptime hasGc(C)) return &c.@"$gc";
    return null;
}

/// Does a value of this type hold, directly, a reference to a cell that can be part of a
/// cycle? A function value and an exception count: what they hold is not in their type.
/// (Only declarations are looked at, never fields of cells: this is evaluated while the types
/// that ask are still being put together.)
pub fn holdsCyclic(comptime T: type) bool {
    if (T == Exn) return functions_in_cycles;
    switch (@typeInfo(T)) {
        .pointer => |p| {
            if (p.size == .slice) return holdsCyclic(p.child);
            if (p.size != .one or @typeInfo(p.child) != .@"struct") return false;
            return @hasDecl(p.child, "fable_cyclic") and p.child.fable_cyclic;
        },
        .optional => |o| return holdsCyclic(o.child),
        .@"struct" => |s| {
            if (@hasDecl(T, "fable_func")) return functions_in_cycles;
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
fn eachHdr(x: anytype, ctx: anytype, comptime f: anytype) void {
    const T = @TypeOf(x);
    if (comptime !holdsCyclic(T)) return;
    if (T == Exn) {
        if (x.gc) |h| f(ctx, h);
        return;
    }
    if (comptime isFunc(T)) {
        if (x.env) |e| {
            if (e.gc) |h| f(ctx, h);
        }
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
    if (T == Exn) {
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

fn visit(v: *sgc.Visitor, h: *sgc.Hdr) void {
    v.visit(h);
}

fn countOne(n: *usize, _: *sgc.Hdr) void {
    n.* += 1;
}

/// What the collector needs to know about one type of cell `C`: where its count is, which
/// cells it refers to, and how to give up what it holds and free it. `gc_field` is the
/// collector's header in `C`; `payload` is the field that holds everything else (all fields
/// but the count and the header when it is null).
fn Collected(comptime C: type, comptime gc_field: []const u8, comptime rc_offset: isize, comptime payload: ?[]const u8) type {
    return struct {
        inline fn cellOf(n: *sgc.Hdr) *C {
            return @alignCast(@fieldParentPtr(gc_field, n));
        }

        fn trace(n: *sgc.Hdr, v: *sgc.Visitor) void {
            const c = cellOf(n);
            if (payload) |p| {
                eachHdr(@field(c, p), v, visit);
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) eachHdr(@field(c, name), v, visit);
            }
        }

        fn releaseOutside(n: *sgc.Hdr, _: ?*anyopaque) void {
            const c = cellOf(n);
            if (payload) |p| {
                dropOutside(@field(c, p));
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) dropOutside(@field(c, name));
            }
        }

        fn freeCell(n: *sgc.Hdr, _: ?*anyopaque) void {
            free(cellOf(n));
        }

        fn finalize(n: *sgc.Hdr, _: ?*anyopaque) void {
            const c = cellOf(n);
            if (payload) |p| {
                drop(@field(c, p));
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) drop(@field(c, name));
            }
            free(c);
        }

        /// Is the cell being made without a reference to a cell that can be part of a cycle?
        fn isLeaf(c: *const C) bool {
            var n: usize = 0;
            if (payload) |p| {
                eachHdr(@field(c, p), &n, countOne);
            } else inline for (@typeInfo(C).@"struct".field_names) |name| {
                if (comptime !isCount(name)) eachHdr(@field(c, name), &n, countOne);
            }
            return n == 0;
        }

        const desc: sgc.Desc = .{
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
inline fn gcTick() void {
    if (!thread.collector_ready) collectorSetup();
    if (verify_cycles) thread.collector.verify();
    if (thread.collector.tickDue()) thread.collector.tickSlow();
}

/// The header of a new cell of a recursive union or of a reference record.
inline fn gcHeader(comptime C: type, c: *const C) sgc.Hdr {
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
pub fn collectorDeinit() void {
    if (thread.collector_ready) thread.collector.deinit();
    thread.weak.deinit(bookkeeping());
    thread.weak = .empty;
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

// ---------------------------------------------------------------------------------------------
// Strings
//
// A string is what it is on .NET: an immutable sequence of UTF-16 code units, so that its
// length, its characters and their order are the same here and there. It is a pointer to a
// header that the units follow. A literal is static data: it is never counted and never
// freed, and making one costs nothing.
// ---------------------------------------------------------------------------------------------

pub const Str = extern struct {
    /// the number of references, or `literal` for a string that is static data
    rc: u32,
    len: u32,

    pub const literal: u32 = std.math.maxInt(u32);

    /// The UTF-16 code units.
    pub inline fn units(s: *const Str) []const u16 {
        const first: [*]const u16 = @ptrCast(@as([*]const Str, @ptrCast(s)) + 1);
        return first[0..s.len];
    }
};

/// F#'s `string`: a pointer to the text, or null as on .NET. (The pointer is not to a
/// constant: the count behind it changes. A literal is constant data all the same, and is
/// never written: its count says so.)
pub const String = ?*Str;

/// The code units of a string. A null string has none.
pub inline fn unitsOf(s: String) []const u16 {
    return if (s) |p| p.units() else &.{};
}

fn LiteralCell(comptime n: usize) type {
    return extern struct { header: Str, units: [n]u16 };
}

/// A string literal, from UTF-8 text.
pub inline fn str(comptime utf8: []const u8) String {
    const static = comptime blk: {
        // (the conversion is a loop at compile time, and a function with many literals runs it
        // many times: the compiler's guard against endless loops is not for this)
        @setEvalBranchQuota(std.math.maxInt(u32));
        const u = std.unicode.utf8ToUtf16LeStringLiteral(utf8);
        break :blk LiteralCell(u.len){ .header = .{ .rc = Str.literal, .len = u.len }, .units = u.* };
    };
    return @constCast(&static.header);
}

/// A string literal that is not well-formed text (F# allows a surrogate on its own).
pub inline fn strOf(comptime u: []const u16) String {
    const static = comptime LiteralCell(u.len){ .header = .{ .rc = Str.literal, .len = u.len }, .units = u[0..u.len].* };
    return @constCast(&static.header);
}

fn strWords(len: usize) usize {
    return @sizeOf(Str) / 4 + (len + 1) / 2;
}

/// A new string of `len` units, to be filled in by the caller. Its count is one.
fn strNew(len: usize) struct { *Str, []u16 } {
    const words = allocator.alloc(u32, strWords(len)) catch @panic("fable: out of memory");
    const s: *Str = @ptrCast(words.ptr);
    s.* = .{ .rc = 1, .len = @intCast(len) };
    if (track) thread.stats.allocs += 1;
    const first: [*]u16 = @ptrCast(@as([*]Str, @ptrCast(s)) + 1);
    return .{ s, first[0..len] };
}

/// A new string with these units.
fn strFrom(u: []const u16) String {
    if (u.len == 0) return str("");
    const s, const out = strNew(u.len);
    @memcpy(out, u);
    return s;
}

inline fn strRetain(s: String) void {
    const p = s orelse return;
    if (p.rc == Str.literal) return;
    p.rc += 1;
    if (track) thread.stats.dups += 1;
}

inline fn strRelease(s: String) void {
    const p = s orelse return;
    if (p.rc == Str.literal) return;
    const m = p;
    if (m.rc != 1) {
        m.rc -= 1;
        if (track) thread.stats.decs += 1;
        return;
    }
    if (track) thread.stats.frees += 1;
    const words: [*]u32 = @ptrCast(@alignCast(m));
    allocator.free(words[0..strWords(m.len)]);
}

/// Text that grows: what the functions below build a string of unknown length in.
const TextBuilder = struct {
    list: std.ArrayList(u16) = .empty,

    fn add(b: *TextBuilder, u: []const u16) void {
        b.list.appendSlice(allocator, u) catch @panic("fable: out of memory");
    }

    fn addOne(b: *TextBuilder, c: u16) void {
        b.list.append(allocator, c) catch @panic("fable: out of memory");
    }

    fn addAscii(b: *TextBuilder, text: []const u8) void {
        for (text) |c| b.addOne(c);
    }

    fn deinit(b: *TextBuilder) void {
        b.list.deinit(allocator);
    }

    /// The text as a string; the builder is empty afterwards.
    fn finish(b: *TextBuilder) String {
        const s = strFrom(b.list.items);
        b.deinit();
        b.* = .{};
        return s;
    }
};

pub fn strEql(a: String, b: String) bool {
    if (a == b) return true;
    const x = a orelse return false;
    const y = b orelse return false;
    return std.mem.eql(u16, x.units(), y.units());
}

/// The order of two strings by their code units: negative, zero or positive, and the same
/// number as .NET's `String.CompareOrdinal`, which is what F#'s `compare` gives for strings.
/// A null string comes before every other.
pub fn strCompare(a: String, b: String) i32 {
    if (a == null or b == null) return @as(i32, @intFromBool(a != null)) - @as(i32, @intFromBool(b != null));
    const x = unitsOf(a);
    const y = unitsOf(b);
    const x0: i32 = if (x.len != 0) x[0] else 0;
    const y0: i32 = if (y.len != 0) y[0] else 0;
    if (x0 != y0) return x0 - y0;
    for (x[0..@min(x.len, y.len)], y[0..@min(x.len, y.len)]) |c, d| {
        if (c != d) return @as(i32, c) - @as(i32, d);
    }
    return @as(i32, @intCast(x.len)) - @as(i32, @intCast(y.len));
}

/// F#'s `compare`: negative, zero or positive. Numbers, chars and booleans by value (on a
/// float, not-a-number comes first); strings by code unit; records and tuples field by field;
/// unions by case, then by field; an option with None first; lists item by item, the shorter
/// first when one starts the other; arrays by length, then item by item.
pub fn compare(a: anytype, b: @TypeOf(a)) i32 {
    const T = @TypeOf(a);
    if (T == String) return strCompare(a, b);
    if (T == bool) return @as(i32, @intFromBool(a)) - @as(i32, @intFromBool(b));
    if (T == void) return 0;
    if (T == Exn) @compileError("fable: exceptions cannot be compared");
    if (comptime isFunc(T)) @compileError("fable: function values cannot be compared");
    switch (@typeInfo(T)) {
        .int, .float, .comptime_int, .comptime_float => {
            if (a < b) return -1;
            if (a > b) return 1;
            if (a == b) return 0;
            // (not a number: it comes before every number, and equals itself)
            if (a == a) return 1;
            return if (b == b) -1 else 0;
        },
        .optional => {
            const x = a orelse return if (b == null) 0 else -1;
            const y = b orelse return 1;
            return compare(x, y);
        },
        .pointer => |p| {
            if (comptime p.size == .slice) {
                if (a.len != b.len) return if (a.len < b.len) -1 else 1;
                for (a, b) |x, y| {
                    const c = compare(x, y);
                    if (c != 0) return c;
                }
                return 0;
            }
            // a cell: a reference record, an array, or what a case of a recursive union holds
            if (a == b) return 0;
            inline for (@typeInfo(p.child).@"struct".field_names) |name| {
                if (comptime !isCount(name)) {
                    const c = compare(@field(a, name), @field(b, name));
                    if (c != 0) return c;
                }
            }
            return 0;
        },
        .@"struct" => |st| {
            inline for (st.field_names) |name| {
                const c = compare(@field(a, name), @field(b, name));
                if (c != 0) return c;
            }
            return 0;
        },
        .@"union" => {
            if (comptime isCollection(T)) return treeCompare(a, b);
            if (comptime @hasDecl(T, "fable_list")) {
                var x = a;
                var y = b;
                while (true) {
                    if (x == .Empty) return if (y == .Empty) 0 else -1;
                    if (y == .Empty) return 1;
                    if (x.Cons == y.Cons) return 0;
                    const c = compare(x.Cons.Head, y.Cons.Head);
                    if (c != 0) return c;
                    x = x.Cons.Tail;
                    y = y.Cons.Tail;
                }
            }
            const ta = @backingInt(std.meta.activeTag(a));
            const tb = @backingInt(std.meta.activeTag(b));
            if (ta != tb) return if (ta < tb) -1 else 1;
            switch (a) {
                inline else => |pa, tag| return compare(pa, @field(b, @tagName(tag))),
            }
        },
        else => @compileError("fable: values of type " ++ @typeName(T) ++ " cannot be compared"),
    }
}

/// `compare a b` where one of them may be a number that is written out.
pub inline fn compareOf(a: anytype, b: anytype) i32 {
    const T = @TypeOf(a, b);
    return compare(@as(T, a), @as(T, b));
}

/// `max a b` and `min a b`: a reference of its own to the one that is chosen. (With a
/// not-a-number among two floats the result is not a number, as on .NET.)
pub fn maxOf(a: anytype, b: @TypeOf(a)) @TypeOf(a) {
    if (comptime @typeInfo(@TypeOf(a)) == .float) {
        if (a != a) return a;
        if (b != b) return b;
    }
    return dup(if (compare(a, b) < 0) b else a);
}

pub fn minOf(a: anytype, b: @TypeOf(a)) @TypeOf(a) {
    if (comptime @typeInfo(@TypeOf(a)) == .float) {
        if (a != a) return a;
        if (b != b) return b;
    }
    return dup(if (compare(a, b) > 0) b else a);
}

/// F#'s `hash`: equal values have equal hashes. A number is its own hash, as on .NET; the
/// hash of anything else is this library's.
pub fn hash(x: anytype) i32 {
    const T = @TypeOf(x);
    if (T == String) {
        var h: u32 = 5381;
        for (unitsOf(x)) |c| h = (h *% 33) ^ c;
        return @bitCast(h);
    }
    if (T == Exn) return @truncate(@as(isize, @bitCast(@intFromPtr(x))));
    if (comptime isFunc(T)) @compileError("fable: function values cannot be hashed");
    switch (@typeInfo(T)) {
        .void => return 0,
        .bool => return @intFromBool(x),
        .int => |info| {
            if (info.bits <= 32) return if (info.signedness == .signed) @as(i32, x) else @bitCast(@as(u32, x));
            // (as .NET folds a 64-bit number)
            const wide: u64 = @bitCast(@as(i64, @intCast(x)));
            return @bitCast(@as(u32, @truncate(wide)) ^ @as(u32, @truncate(wide >> 32)));
        },
        .float => {
            const wide: u64 = @bitCast(@as(f64, if (x == 0) 0 else x));
            return @bitCast(@as(u32, @truncate(wide)) ^ @as(u32, @truncate(wide >> 32)));
        },
        .optional => return if (x) |v| hashWith(1, hash(v)) else 0,
        .pointer => |p| {
            var h: i32 = 17;
            if (comptime p.size != .slice and @hasDecl(p.child, "fable_identity")) return @truncate(@as(isize, @bitCast(@intFromPtr(x))));
            if (comptime p.size == .slice) {
                for (x) |item| h = hashWith(h, hash(item));
                return h;
            }
            inline for (@typeInfo(p.child).@"struct".field_names) |name| {
                if (comptime !isCount(name)) h = hashWith(h, hash(@field(x, name)));
            }
            return h;
        },
        .@"struct" => |st| {
            var h: i32 = 17;
            inline for (st.field_names) |name| h = hashWith(h, hash(@field(x, name)));
            return h;
        },
        .@"union" => {
            if (comptime isCollection(T)) return treeHash(x);
            if (comptime @hasDecl(T, "fable_list")) {
                var h: i32 = 17;
                var rest = x;
                while (rest == .Cons) : (rest = rest.Cons.Tail) h = hashWith(h, hash(rest.Cons.Head));
                return h;
            }
            switch (x) {
                inline else => |payload, tag| return hashWith(@backingInt(tag), hash(payload)),
            }
        },
        else => @compileError("fable: values of type " ++ @typeName(T) ++ " cannot be hashed"),
    }
}

fn hashWith(h: i32, next: i32) i32 {
    return (h *% 31) +% next;
}

// ---- what .NET raises for a string that is null or an argument that is out of range ----

fn nullRef() Raised {
    return raise(NullReferenceException, str("Object reference not set to an instance of an object."));
}

fn argNull(comptime param: []const u8) Raised {
    return raise(ArgumentNullException, str("Value cannot be null. (Parameter '" ++ param ++ "')"));
}

fn argRange(comptime param: []const u8, comptime text: []const u8) Raised {
    return raise(ArgumentOutOfRangeException, str(text ++ " (Parameter '" ++ param ++ "')"));
}

fn argNegative(comptime param: []const u8, value: i32) Raised {
    return raise(ArgumentOutOfRangeException, format(.{
        param ++ " ('",                                                                      value,
        "') must be a non-negative value. (Parameter '" ++ param ++ "')\nActual value was ", value,
        ".",
    }));
}

fn argAbove(comptime param: []const u8, value: anytype, limit: i32) Raised {
    return raise(ArgumentOutOfRangeException, format(.{
        param ++ " ('",                                        value,
        "') must be less than or equal to '",                  limit,
        "'. (Parameter '" ++ param ++ "')\nActual value was ", value,
        ".",
    }));
}

const index_range = "Index was out of range. Must be non-negative and less than or equal to the size of the collection.";

/// `s.Length`
pub inline fn strLen(s: String) Raised!i32 {
    const p = s orelse return nullRef();
    return @intCast(p.len);
}

/// `String.length s`, and `s.Length` of a string that cannot be null.
pub inline fn strLength(s: String) i32 {
    return @intCast(unitsOf(s).len);
}

/// `s.[i]`
pub inline fn strAt(s: String, i: i32) Raised!u16 {
    const p = s orelse return nullRef();
    if (i < 0 or i >= p.len) return raise(IndexOutOfRangeException, str("Index was outside the bounds of the array."));
    return p.units()[@intCast(i)];
}

/// `a + b`: a new string, unless one of them is empty. (Null counts as empty, and the result
/// is never null.)
pub fn strConcat(a: String, b: String) String {
    const x = unitsOf(a);
    const y = unitsOf(b);
    if (x.len == 0) return if (y.len == 0) str("") else dup(b);
    if (y.len == 0) return dup(a);
    const s, const u = strNew(x.len + y.len);
    @memcpy(u[0..x.len], x);
    @memcpy(u[x.len..], y);
    return s;
}

/// `s.Equals(other)`
pub fn strEquals(s: String, other: String) Raised!bool {
    if (s == null) return nullRef();
    return strEql(s, other);
}

pub inline fn strIsNullOrEmpty(s: String) bool {
    return unitsOf(s).len == 0;
}

pub fn strIsNullOrWhiteSpace(s: String) bool {
    for (unitsOf(s)) |c| {
        if (!unicode.isWhiteSpace(c)) return false;
    }
    return true;
}

/// The part of `s` from `start` that is `n` long. Both are known to be inside the string.
fn strSlice(s: String, start: usize, n: usize) String {
    const u = unitsOf(s);
    if (n == 0) return str("");
    if (n == u.len) return dup(s);
    return strFrom(u[start..][0..n]);
}

/// `s.Substring(start)` and `s.Substring(start, length)`
pub fn strSubstring(s: String, start: i32, length: ?i32) Raised!String {
    const p = s orelse return nullRef();
    const total: i32 = @intCast(p.len);
    if (start < 0) return argNegative("startIndex", start);
    if (start > total) return argRange("startIndex", "startIndex cannot be larger than length of string.");
    const n = length orelse total - start;
    if (n < 0) return argNegative("length", n);
    if (start > total - n) return argRange("length", "Index and length must refer to a location within the string.");
    return strSlice(s, @intCast(start), @intCast(n));
}

/// `s.IndexOf(c)` and `s.IndexOf(c, start)`
pub fn strIndexOfChar(s: String, c: u16, start: i32) Raised!i32 {
    const p = s orelse return nullRef();
    const u = p.units();
    if (start < 0 or start > u.len) return argRange("startIndex", index_range);
    const at = std.mem.indexOfScalarPos(u16, u, @intCast(start), c) orelse return -1;
    return @intCast(at);
}

/// `s.IndexOf(value)` and `s.IndexOf(value, start)`
pub fn strIndexOf(s: String, value: String, start: i32) Raised!i32 {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    const u = p.units();
    if (start < 0 or start > u.len) return argRange("startIndex", index_range);
    if (v.len == 0) return start;
    const at = std.mem.indexOfPos(u16, u, @intCast(start), v.units()) orelse return -1;
    return @intCast(at);
}

pub fn strLastIndexOfChar(s: String, c: u16) Raised!i32 {
    const p = s orelse return nullRef();
    const at = std.mem.lastIndexOfScalar(u16, p.units(), c) orelse return -1;
    return @intCast(at);
}

pub fn strLastIndexOf(s: String, value: String) Raised!i32 {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    if (v.len == 0) return @intCast(p.len);
    const at = std.mem.lastIndexOf(u16, p.units(), v.units()) orelse return -1;
    return @intCast(at);
}

pub fn strContains(s: String, value: String) Raised!bool {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    return std.mem.indexOf(u16, p.units(), v.units()) != null;
}

pub fn strContainsChar(s: String, c: u16) Raised!bool {
    const p = s orelse return nullRef();
    return std.mem.indexOfScalar(u16, p.units(), c) != null;
}

pub fn strStartsWith(s: String, value: String) Raised!bool {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    return std.mem.startsWith(u16, p.units(), v.units());
}

pub fn strEndsWith(s: String, value: String) Raised!bool {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    return std.mem.endsWith(u16, p.units(), v.units());
}

pub fn strStartsWithChar(s: String, c: u16) Raised!bool {
    const p = s orelse return nullRef();
    return p.len != 0 and p.units()[0] == c;
}

pub fn strEndsWithChar(s: String, c: u16) Raised!bool {
    const p = s orelse return nullRef();
    return p.len != 0 and p.units()[p.len - 1] == c;
}

/// `s.ToUpperInvariant()` (`upper`) and `s.ToLowerInvariant()`: each code unit to the one
/// .NET maps it to. `ToUpper` and `ToLower` are the same here: there is no current culture.
pub fn strCase(s: String, comptime upper: bool) Raised!String {
    const p = s orelse return nullRef();
    const u = p.units();
    const change = if (upper) unicode.toUpper else unicode.toLower;
    for (u, 0..) |c, i| {
        if (change(c) != c) {
            const r, const out = strNew(u.len);
            @memcpy(out[0..i], u[0..i]);
            for (u[i..], out[i..]) |from, *to| to.* = change(from);
            return r;
        }
    }
    return dup(s);
}

/// `s.Trim()`, `s.TrimStart()`, `s.TrimEnd()`: white space, or the one character given.
pub fn strTrim(s: String, comptime start: bool, comptime end: bool, only: ?u16) Raised!String {
    const p = s orelse return nullRef();
    const u = p.units();
    var from: usize = 0;
    var to: usize = u.len;
    if (start) {
        while (from < to and (if (only) |c| u[from] == c else unicode.isWhiteSpace(u[from]))) from += 1;
    }
    if (end) {
        while (to > from and (if (only) |c| u[to - 1] == c else unicode.isWhiteSpace(u[to - 1]))) to -= 1;
    }
    return strSlice(s, from, to - from);
}

/// `s.Replace(old, new)`
pub fn strReplace(s: String, old: String, new_: String) Raised!String {
    const p = s orelse return nullRef();
    const o = old orelse return argNull("oldValue");
    if (o.len == 0) return raise(ArgumentException, str("The value cannot be an empty string. (Parameter 'oldValue')"));
    const u = p.units();
    const with = unitsOf(new_);
    var at = std.mem.indexOf(u16, u, o.units()) orelse return dup(s);
    var b: TextBuilder = .{};
    var done: usize = 0;
    while (true) {
        b.add(u[done..at]);
        b.add(with);
        done = at + o.len;
        at = std.mem.indexOfPos(u16, u, done, o.units()) orelse break;
    }
    b.add(u[done..]);
    return b.finish();
}

pub fn strReplaceChar(s: String, old: u16, new_: u16) Raised!String {
    const p = s orelse return nullRef();
    const u = p.units();
    const first = std.mem.indexOfScalar(u16, u, old) orelse return dup(s);
    const r, const out = strNew(u.len);
    @memcpy(out[0..first], u[0..first]);
    for (u[first..], out[first..]) |from, *to| to.* = if (from == old) new_ else from;
    return r;
}

/// `s.Insert(start, value)`
pub fn strInsert(s: String, start: i32, value: String) Raised!String {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    const u = p.units();
    // (.NET compares the index as an unsigned number, and says so in its message)
    const index: u32 = @bitCast(start);
    if (index > u.len) return argAbove("startIndex", index, @intCast(u.len));
    if (v.len == 0) return dup(s);
    if (u.len == 0) return dup(value);
    const r, const out = strNew(u.len + v.len);
    @memcpy(out[0..index], u[0..index]);
    @memcpy(out[index..][0..v.len], v.units());
    @memcpy(out[index + v.len ..], u[index..]);
    return r;
}

/// `s.Remove(start)` and `s.Remove(start, count)`
pub fn strRemove(s: String, start: i32, count: ?i32) Raised!String {
    const p = s orelse return nullRef();
    const u = p.units();
    const total: i32 = @intCast(u.len);
    if (count) |n| {
        if (start < 0) return argNegative("startIndex", start);
        if (n < 0) return argNegative("count", n);
        if (n > total - start) return argAbove("count", n, total - start);
        if (n == 0) return dup(s);
        const from: usize = @intCast(start);
        const r, const out = strNew(u.len - @as(usize, @intCast(n)));
        @memcpy(out[0..from], u[0..from]);
        @memcpy(out[from..], u[from + @as(usize, @intCast(n)) ..]);
        return if (out.len == 0) blk: {
            strRelease(r);
            break :blk str("");
        } else r;
    }
    if (start < 0) return argRange("startIndex", "StartIndex cannot be less than zero.");
    if (start > total) return argRange("startIndex", "startIndex cannot be larger than length of string.");
    return strSlice(s, 0, @intCast(start));
}

/// `s.PadLeft(width, c)` (`left`) and `s.PadRight(width, c)`
pub fn strPad(s: String, comptime left: bool, width: i32, c: u16) Raised!String {
    const p = s orelse return nullRef();
    if (width < 0) return argNegative("totalWidth", width);
    const u = p.units();
    const total: usize = @intCast(width);
    if (total <= u.len) return dup(s);
    const r, const out = strNew(total);
    const pad = total - u.len;
    if (left) {
        @memset(out[0..pad], c);
        @memcpy(out[pad..], u);
    } else {
        @memcpy(out[0..u.len], u);
        @memset(out[u.len..], c);
    }
    return r;
}

/// `String(c, count)`
pub fn strOfChar(c: u16, count: i32) Raised!String {
    if (count < 0) return argNegative("count", count);
    if (count == 0) return str("");
    const r, const out = strNew(@intCast(count));
    @memset(out, c);
    return r;
}

// ---- F#'s `String` module: a null string is an empty one ----

fn countNegative(count: i32) Raised {
    return raise(ArgumentException, format(.{ "The input must be non-negative.\ncount = ", count, " (Parameter 'count')" }));
}

/// Apply a function value to two values: at once if it takes both, one after the other if it
/// is a function that gives a function.
inline fn apply2(comptime R: type, f: anytype, a: anytype, b: anytype) Raised!R {
    const Code = @typeInfo(@FieldType(@TypeOf(f), "code")).pointer.child;
    if (comptime @typeInfo(Code).@"fn".param_types.len == 3) return f.code(f.env, a, b);
    const g = try f.code(f.env, a);
    defer drop(g);
    return g.code(g.env, b);
}

/// `String.replicate count s`
pub fn strReplicate(count: i32, s: String) Raised!String {
    if (count < 0) return countNegative(count);
    const u = unitsOf(s);
    const n: usize = @intCast(count);
    if (n == 0 or u.len == 0) return str("");
    if (n == 1) return dup(s);
    const r, const out = strNew(u.len * n);
    for (0..n) |i| @memcpy(out[i * u.len ..][0..u.len], u);
    return r;
}

/// `String.concat sep strings`, for a list of strings
pub fn strJoin(sep: String, strings: List(String)) String {
    var b: TextBuilder = .{};
    var rest = strings;
    var first = true;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        if (!first) b.add(unitsOf(sep));
        first = false;
        b.add(unitsOf(rest.Cons.Head));
    }
    return b.finish();
}

/// `String.init count f`
pub fn strInit(count: i32, f: anytype) Raised!String {
    if (count < 0) return countNegative(count);
    var b: TextBuilder = .{};
    errdefer b.deinit();
    var i: i32 = 0;
    while (i < count) : (i += 1) {
        const part: String = try f.code(f.env, i);
        b.add(unitsOf(part));
        drop(part);
    }
    return b.finish();
}

/// `String.map f s`
pub fn strMap(f: anytype, s: String) Raised!String {
    const u = unitsOf(s);
    if (u.len == 0) return str("");
    const r, const out = strNew(u.len);
    errdefer strRelease(r);
    for (u, out) |c, *to| to.* = try f.code(f.env, c);
    return r;
}

/// `String.mapi f s`
pub fn strMapi(f: anytype, s: String) Raised!String {
    const u = unitsOf(s);
    if (u.len == 0) return str("");
    const r, const out = strNew(u.len);
    errdefer strRelease(r);
    for (u, out, 0..) |c, *to, i| to.* = try apply2(u16, f, @as(i32, @intCast(i)), c);
    return r;
}

/// `String.iter f s`
pub fn strIter(f: anytype, s: String) Raised!void {
    for (unitsOf(s)) |c| try f.code(f.env, c);
}

/// `String.iteri f s`
pub fn strIteri(f: anytype, s: String) Raised!void {
    for (unitsOf(s), 0..) |c, i| try apply2(void, f, @as(i32, @intCast(i)), c);
}

/// `String.forall f s`
pub fn strForall(f: anytype, s: String) Raised!bool {
    for (unitsOf(s)) |c| {
        if (!try f.code(f.env, c)) return false;
    }
    return true;
}

/// `String.exists f s`
pub fn strExists(f: anytype, s: String) Raised!bool {
    for (unitsOf(s)) |c| {
        if (try f.code(f.env, c)) return true;
    }
    return false;
}

/// `String.filter f s`
pub fn strFilter(f: anytype, s: String) Raised!String {
    var b: TextBuilder = .{};
    errdefer b.deinit();
    for (unitsOf(s)) |c| {
        if (try f.code(f.env, c)) b.addOne(c);
    }
    return b.finish();
}

/// `String.collect f s`
pub fn strCollect(f: anytype, s: String) Raised!String {
    var b: TextBuilder = .{};
    errdefer b.deinit();
    for (unitsOf(s)) |c| {
        const part: String = try f.code(f.env, c);
        b.add(unitsOf(part));
        drop(part);
    }
    return b.finish();
}

/// How a value is turned into text: an F# format specifier (`%5d`, `%.2f`, `%s`, ...), or
/// what `string x` and `$"{x}"` do (kind 'P').
pub const Spec = struct {
    kind: u8 = 'P',
    width: u16 = 0,
    precision: ?u8 = null,
    zero: bool = false,
    left: bool = false,
    plus: bool = false,
    space: bool = false,
    /// a .NET format (`N2`), for a hole of an interpolated string that has one
    net: []const u8 = "",
};

fn Arg(comptime T: type, comptime spec: Spec) type {
    return struct {
        pub const fable_spec = spec;
        value: T,
    };
}

/// A value with its format specifier, as a part of `format`.
pub inline fn arg(comptime spec: Spec, value: anytype) Arg(@TypeOf(value), spec) {
    return .{ .value = value };
}

/// The text of one part: ASCII in `scratch`, or the units of a string.
const Piece = union(enum) {
    ascii: []const u8,
    units: []const u16,

    fn len(p: Piece) usize {
        return switch (p) {
            .ascii => |a| a.len,
            .units => |u| u.len,
        };
    }
};

const scratch_len = 640;

/// The decimal digits of a number: 0.d0 d1 d2 ... x 10^point.
const Decimal = struct {
    /// (a double has at most 309 digits before the point, or 1074 after it)
    digits: [1100]u8 = undefined,
    len: usize = 0,
    point: i32 = 1,

    /// The exact digits of a finite number that is not negative.
    fn exact(x: f64) Decimal {
        var d: Decimal = .{};
        if (x == 0) return d;
        const bits: u64 = @bitCast(x);
        const biased: i32 = @intCast((bits >> 52) & 0x7FF);
        var m: u64 = bits & ((1 << 52) - 1);
        var e: i32 = undefined;
        if (biased == 0) {
            e = -1074;
        } else {
            m |= 1 << 52;
            e = biased - 1075;
        }
        const zeros: u6 = @intCast(@ctz(m));
        m >>= zeros;
        e += zeros;

        var limbs: [36]u32 = @splat(0);
        if (e >= 0) {
            // a whole number, m * 2^e: its digits, nine at a time from the last
            const at: usize = @intCast(@divTrunc(e, 32));
            const wide: u128 = @as(u128, m) << @intCast(@mod(e, 32));
            limbs[at] = @truncate(wide);
            limbs[at + 1] = @truncate(wide >> 32);
            limbs[at + 2] = @truncate(wide >> 64);
            var n: usize = at + 3;
            var end: usize = d.digits.len;
            while (n > 0) {
                var carry: u64 = 0;
                var i = n;
                while (i > 0) {
                    i -= 1;
                    const cur = (carry << 32) | limbs[i];
                    limbs[i] = @intCast(cur / 1_000_000_000);
                    carry = cur % 1_000_000_000;
                }
                while (n > 0 and limbs[n - 1] == 0) n -= 1;
                for (0..9) |_| {
                    end -= 1;
                    d.digits[end] = @intCast(carry % 10);
                    carry /= 10;
                }
            }
            while (d.digits[end] == 0) end += 1;
            d.len = d.digits.len - end;
            std.mem.copyForwards(u8, d.digits[0..d.len], d.digits[end..]);
            d.point = @intCast(d.len);
            return d;
        }

        // m / 2^shift: the whole part, then one digit of the rest at a time
        const shift: usize = @intCast(-e);
        const whole: u64 = if (shift >= 64) 0 else m >> @intCast(shift);
        const rest: u64 = if (shift >= 64) m else m & ((@as(u64, 1) << @intCast(shift)) - 1);
        if (whole != 0) {
            const text = std.fmt.bufPrint(&d.digits, "{d}", .{whole}) catch unreachable;
            for (d.digits[0..text.len]) |*c| c.* -= '0';
            d.len = text.len;
        }
        d.point = @intCast(d.len);
        limbs[0] = @truncate(rest);
        limbs[1] = @truncate(rest >> 32);
        const top = shift / 32;
        const bit: u5 = @intCast(shift % 32);
        for (0..shift) |_| {
            var carry: u64 = 0;
            for (limbs[0 .. top + 2]) |*l| {
                const cur = @as(u64, l.*) * 10 + carry;
                l.* = @truncate(cur);
                carry = cur >> 32;
            }
            var next: u32 = limbs[top] >> bit;
            if (bit != 0) {
                next |= limbs[top + 1] << @intCast(32 - @as(u6, bit));
                limbs[top] &= (@as(u32, 1) << bit) - 1;
            } else {
                limbs[top] = 0;
            }
            limbs[top + 1] = 0;
            if (d.len == 0 and next == 0) {
                d.point -= 1;
            } else {
                d.digits[d.len] = @intCast(next);
                d.len += 1;
            }
        }
        return d;
    }

    /// The shortest digits that read back as the same number, of its own type.
    fn shortest(x: anytype) Decimal {
        var d: Decimal = .{};
        if (x == 0) return d;
        var buf: [64]u8 = undefined;
        const text = std.fmt.bufPrint(&buf, "{e}", .{x}) catch unreachable;
        const e = std.mem.indexOfScalar(u8, text, 'e').?;
        for (text[0..e]) |c| {
            if (c == '.') continue;
            d.digits[d.len] = c - '0';
            d.len += 1;
        }
        d.point = (std.fmt.parseInt(i32, text[e + 1 ..], 10) catch unreachable) + 1;
        return d;
    }

    /// Keep `n` digits, rounding to the nearest and a tie to the even digit, as .NET does.
    fn round(d: *Decimal, n: i32) void {
        d.roundTo(n, true);
    }

    /// Keep `n` digits, rounding to the nearest; a tie goes to the even digit, or up.
    fn roundTo(d: *Decimal, n: i32, even: bool) void {
        if (n >= d.len) return;
        if (n < 0) {
            d.len = 0;
            return;
        }
        const keep: usize = @intCast(n);
        const next = d.digits[keep];
        var up = next > 5;
        if (next == 5) {
            up = !even or (keep > 0 and d.digits[keep - 1] % 2 == 1);
            for (d.digits[keep + 1 .. d.len]) |c| {
                if (c != 0) up = true;
            }
        }
        d.len = keep;
        if (!up) return;
        var i = keep;
        while (i > 0) {
            i -= 1;
            if (d.digits[i] != 9) {
                d.digits[i] += 1;
                return;
            }
            d.digits[i] = 0;
        }
        // (all nines, or no digit at all: one, a place higher)
        d.digits[0] = 1;
        d.len = @max(keep, 1);
        d.point += 1;
    }

    inline fn digit(d: *const Decimal, i: i32) u8 {
        return if (i >= 0 and i < d.len) '0' + d.digits[@intCast(i)] else '0';
    }
};

const Text = struct {
    buf: []u8,
    len: usize = 0,

    inline fn put(t: *Text, c: u8) void {
        t.buf[t.len] = c;
        t.len += 1;
    }

    /// e+005: the exponent with its sign and at least `width` digits
    fn exponent(t: *Text, letter: u8, exp: i32, width: usize) void {
        t.put(letter);
        t.put(if (exp < 0) '-' else '+');
        var digits: [8]u8 = undefined;
        const text = std.fmt.bufPrint(&digits, "{d}", .{@abs(exp)}) catch unreachable;
        for (@min(text.len, width)..width) |_| t.put('0');
        for (text) |c| t.put(c);
    }

    /// The digits without the zeros at their end: plainly while the exponent is above -5 and
    /// below `limit`, as d.ddde+xx otherwise.
    fn general(t: *Text, d: *const Decimal, limit: i32, letter: u8) void {
        var n: i32 = @intCast(d.len);
        while (n > 0 and d.digits[@intCast(n - 1)] == 0) n -= 1;
        const exp = d.point - 1;
        if (exp > -5 and exp < limit) {
            if (d.point <= 0) {
                t.put('0');
            } else {
                var i: i32 = 0;
                while (i < d.point) : (i += 1) t.put(d.digit(i));
            }
            if (n > d.point) {
                t.put('.');
                var i: i32 = @min(d.point, 0);
                while (i < 0) : (i += 1) t.put('0');
                i = @max(d.point, 0);
                while (i < n) : (i += 1) t.put(d.digit(i));
            }
        } else {
            t.put(d.digit(0));
            if (n > 1) {
                t.put('.');
                var i: i32 = 1;
                while (i < n) : (i += 1) t.put(d.digit(i));
            }
            t.exponent(letter, exp, 2);
        }
    }
};

/// A float as F# and .NET write it. `%f` and `%e` round the exact value of the number; `%g`
/// keeps six digits; everything else (`string x`, `$"{x}"`, `%O`) is the shortest text that
/// reads back as the same number.
fn floatText(comptime spec: Spec, value: anytype, out: []u8) []const u8 {
    const x: f64 = value;
    if (std.math.isNan(x)) return "NaN";
    if (std.math.isInf(x)) return if (x > 0) "Infinity" else "-Infinity";
    var t: Text = .{ .buf = out };
    if (std.math.signbit(x)) t.put('-') else if (spec.plus) t.put('+') else if (spec.space) t.put(' ');
    const precision: i32 = @min(spec.precision orelse 6, 80);
    switch (spec.kind) {
        'f', 'F' => {
            var d = Decimal.exact(@abs(x));
            d.round(d.point + precision);
            var i: i32 = @min(d.point, 1) - 1;
            while (i < d.point) : (i += 1) t.put(d.digit(i));
            if (precision > 0) {
                t.put('.');
                var k: i32 = 0;
                while (k < precision) : (k += 1) t.put(d.digit(d.point + k));
            }
        },
        'e', 'E' => {
            var d = Decimal.exact(@abs(x));
            d.round(precision + 1);
            t.put(d.digit(0));
            if (precision > 0) {
                t.put('.');
                var k: i32 = 1;
                while (k <= precision) : (k += 1) t.put(d.digit(k));
            }
            t.exponent(spec.kind, d.point - 1, 3);
        },
        'g', 'G' => {
            const letter: u8 = if (spec.kind == 'g') 'e' else 'E';
            if (precision == 0) {
                const d = Decimal.shortest(@abs(value));
                t.general(&d, if (@TypeOf(value) == f32) 9 else 17, letter);
            } else {
                var d = Decimal.exact(@abs(x));
                d.round(precision);
                t.general(&d, precision, letter);
            }
        },
        else => {
            const d = Decimal.shortest(@abs(value));
            t.general(&d, if (@TypeOf(value) == f32) 9 else 17, 'E');
        },
    }
    return out[0..t.len];
}

fn pieceOf(comptime spec: Spec, value: anytype, scratch: *[scratch_len]u8) Piece {
    const T = @TypeOf(value);
    if (T == String) {
        // (only `%O` shows that a string is null)
        if (value == null and spec.kind == 'O') return .{ .ascii = "<null>" };
        return .{ .units = unitsOf(value) };
    }
    switch (@typeInfo(T)) {
        .bool => return .{ .ascii = if (spec.kind == 'b')
            (if (value) "true" else "false")
        else
            (if (value) "True" else "False") },
        .int => |info| {
            if (spec.net.len != 0) return .{ .ascii = netText(spec.net, value, scratch) };
            if (spec.kind == 'c') {
                // (a char: one UTF-16 unit, kept in the scratch space as such)
                const u: *[1]u16 = @ptrCast(@alignCast(scratch));
                u[0] = @intCast(value);
                return .{ .units = u };
            }
            const Bits = @Int(.unsigned, info.bits);
            const sign: []const u8 = if (value >= 0 and spec.plus) "+" else if (value >= 0 and spec.space) " " else "";
            const text = switch (spec.kind) {
                'x' => std.fmt.bufPrint(scratch, "{x}", .{@as(Bits, @bitCast(value))}),
                'X' => std.fmt.bufPrint(scratch, "{X}", .{@as(Bits, @bitCast(value))}),
                'o' => std.fmt.bufPrint(scratch, "{o}", .{@as(Bits, @bitCast(value))}),
                'u' => std.fmt.bufPrint(scratch, "{d}", .{@as(Bits, @bitCast(value))}),
                else => std.fmt.bufPrint(scratch, "{s}{d}", .{ sign, value }),
            };
            return .{ .ascii = text catch unreachable };
        },
        .comptime_int => return pieceOf(spec, @as(i64, value), scratch),
        .float => return .{ .ascii = if (spec.net.len != 0) netText(spec.net, value, scratch) else floatText(spec, value, scratch) },
        .comptime_float => return .{ .ascii = floatText(spec, @as(f64, value), scratch) },
        else => @compileError("fable: a value of type " ++ @typeName(T) ++ " cannot be formatted yet"),
    }
}

fn isLiteralText(comptime T: type) bool {
    const info = @typeInfo(T);
    if (info != .pointer) return false;
    if (info.pointer.size == .slice) return info.pointer.child == u8;
    if (info.pointer.size != .one) return false;
    const child = @typeInfo(info.pointer.child);
    return child == .array and child.array.child == u8;
}

/// Text from parts: literal text (a Zig string literal), strings, and values, bare or with a
/// format specifier (`fable_rt.arg`). This is `sprintf`, string interpolation and `string x`.
pub fn format(parts: anytype) String {
    @setEvalBranchQuota(std.math.maxInt(u32));
    const names = @typeInfo(@TypeOf(parts)).@"struct".field_names;
    var pieces: [names.len]Piece = undefined;
    var pad: [names.len]usize = @splat(0);
    var scratch: [names.len][scratch_len]u8 align(2) = undefined;
    // (the text of a `%A` is a string of its own until it is copied into the result)
    var written: [names.len]String = @splat(null);
    defer for (written) |text| strRelease(text);
    var total: usize = 0;
    inline for (names, 0..) |name, i| {
        const part = @field(parts, name);
        const T = @TypeOf(part);
        if (comptime isLiteralText(T)) {
            pieces[i] = .{ .units = comptime std.unicode.utf8ToUtf16LeStringLiteral(part) };
        } else if (comptime (@typeInfo(T) == .@"struct" and @hasDecl(T, "fable_spec"))) {
            if (comptime T.fable_spec.kind == 'A') {
                written[i] = anyText(part.value);
                pieces[i] = .{ .units = unitsOf(written[i]) };
            } else {
                pieces[i] = pieceOf(T.fable_spec, part.value, &scratch[i]);
            }
            if (T.fable_spec.width > pieces[i].len()) pad[i] = T.fable_spec.width - pieces[i].len();
        } else {
            pieces[i] = pieceOf(.{}, part, &scratch[i]);
        }
        total += pieces[i].len() + pad[i];
    }
    const s, const out = strNew(total);
    var at: usize = 0;
    inline for (names, 0..) |name, i| {
        const T = @TypeOf(@field(parts, name));
        const spec: Spec = if (comptime (@typeInfo(T) == .@"struct" and @hasDecl(T, "fable_spec"))) T.fable_spec else .{};
        at = writePiece(out, at, pieces[i], pad[i], spec);
    }
    return s;
}

/// Write one part at `at`, padded to its width; returns where the next part starts.
fn writePiece(out: []u16, start: usize, piece: Piece, pad: usize, spec: Spec) usize {
    var at = start;
    if (pad != 0 and !spec.left) {
        if (spec.zero and piece == .ascii) {
            // (zeros go between the sign and the digits)
            const a = piece.ascii;
            const signed = a.len > 0 and (a[0] == '-' or a[0] == '+' or a[0] == ' ');
            if (signed) {
                out[at] = a[0];
                at += 1;
            }
            @memset(out[at..][0..pad], '0');
            at += pad;
            for (a[@intFromBool(signed)..]) |c| {
                out[at] = c;
                at += 1;
            }
            return at;
        }
        @memset(out[at..][0..pad], ' ');
        at += pad;
    }
    switch (piece) {
        .ascii => |a| for (a) |c| {
            out[at] = c;
            at += 1;
        },
        .units => |u| {
            @memcpy(out[at..][0..u.len], u);
            at += u.len;
        },
    }
    if (pad != 0 and spec.left) {
        @memset(out[at..][0..pad], ' ');
        at += pad;
    }
    return at;
}

fn posixWrite(fd: i32, bytes: []const u8) void {
    if (builtin.os.tag == .freestanding) return;
    var done: usize = 0;
    while (done < bytes.len) {
        const n = std.posix.system.write(fd, bytes.ptr + done, bytes.len - done);
        if (n <= 0) return;
        done += @intCast(n);
    }
}

fn defaultOut(bytes: []const u8) void {
    posixWrite(1, bytes);
}

fn defaultErr(bytes: []const u8) void {
    posixWrite(2, bytes);
}

/// Where `printf` and `eprintf` send their text, as UTF-8. A program may replace them (a
/// freestanding one has to: there they do nothing).
pub var write_out: *const fn (bytes: []const u8) void = defaultOut;
pub var write_err: *const fn (bytes: []const u8) void = defaultErr;

fn writeText(write: *const fn ([]const u8) void, s: String, newline: bool) void {
    var buf: [512]u8 = undefined;
    var rest = unitsOf(s);
    while (rest.len != 0) {
        // (a pair of surrogates is not split between two chunks)
        var n = @min(rest.len, buf.len / 3);
        if (n < rest.len and rest[n - 1] >= 0xD800 and rest[n - 1] < 0xDC00) n -= 1;
        if (n == 0) n = 1;
        const len = std.unicode.wtf16LeToWtf8(&buf, rest[0..n]);
        write(buf[0..len]);
        rest = rest[n..];
    }
    if (newline) write("\n");
}

/// `printf` / `printfn`: the text of `parts` (see `format`) to standard output.
pub fn print(parts: anytype, comptime newline: bool) void {
    const s = format(parts);
    writeText(write_out, s, newline);
    drop(s);
}

/// `eprintf` / `eprintfn`
pub fn printErr(parts: anytype, comptime newline: bool) void {
    const s = format(parts);
    writeText(write_err, s, newline);
    drop(s);
}

// ---------------------------------------------------------------------------------------------
// .NET's standard numeric formats: what `{x:N2}` in an interpolated string asks for
// ---------------------------------------------------------------------------------------------

/// The digits before the point, in groups of three if `grouped`.
fn wholeDigits(t: *Text, d: *const Decimal, comptime grouped: bool) void {
    const count: i32 = @max(d.point, 1);
    var i: i32 = 0;
    while (i < count) : (i += 1) {
        if (grouped and i != 0 and @mod(count - i, 3) == 0) t.put(',');
        t.put(d.digit(i + d.point - count));
    }
}

fn fraction(t: *Text, d: *const Decimal, places: i32) void {
    if (places <= 0) return;
    t.put('.');
    var k: i32 = 0;
    while (k < places) : (k += 1) t.put(d.digit(d.point + k));
}

/// A number as .NET's `ToString(format)` writes it in the invariant culture, for the
/// standard formats: D, X, B, N, F, E, G, R, P and C with an optional precision.
fn netText(comptime fmt: []const u8, value: anytype, out: []u8) []const u8 {
    const T = @TypeOf(value);
    const whole = @typeInfo(T) == .int;
    const letter = fmt[0];
    const given: ?i32 = comptime if (fmt.len > 1) (std.fmt.parseInt(i32, fmt[1..], 10) catch @compileError("fable: the format " ++ fmt)) else null;
    var t: Text = .{ .buf = out };

    if (comptime (letter == 'X' or letter == 'x' or letter == 'B' or letter == 'b')) {
        if (!whole) @compileError("fable: the format " ++ fmt ++ " is for whole numbers");
        const bits: @Int(.unsigned, @typeInfo(T).int.bits) = @bitCast(value);
        var raw: [140]u8 = undefined;
        const text = switch (letter) {
            'X' => std.fmt.bufPrint(&raw, "{X}", .{bits}),
            'x' => std.fmt.bufPrint(&raw, "{x}", .{bits}),
            else => std.fmt.bufPrint(&raw, "{b}", .{bits}),
        } catch unreachable;
        var pad: i32 = (given orelse 0) - @as(i32, @intCast(text.len));
        while (pad > 0) : (pad -= 1) t.put('0');
        for (text) |c| t.put(c);
        return out[0..t.len];
    }
    if (!whole) {
        if (std.math.isNan(value)) return "NaN";
        if (std.math.isInf(value)) return if (value > 0) "Infinity" else "-Infinity";
    }

    const negative = if (whole) value < 0 else std.math.signbit(value);
    const shortest = !whole and (letter == 'R' or letter == 'r' or ((letter == 'G' or letter == 'g') and (given orelse 0) == 0));
    var d: Decimal = .{};
    if (whole) {
        if (value != 0) {
            const text = std.fmt.bufPrint(&d.digits, "{d}", .{@abs(@as(i128, value))}) catch unreachable;
            for (d.digits[0..text.len]) |*c| c.* -= '0';
            d.len = text.len;
            d.point = @intCast(text.len);
        }
    } else if (shortest) {
        d = Decimal.shortest(@abs(value));
    } else {
        d = Decimal.exact(@abs(@as(f64, value)));
    }
    // (a whole number has no exact half to decide: .NET rounds its digits half up)
    const even = !whole;

    switch (letter) {
        'D', 'd' => {
            if (!whole) @compileError("fable: the format " ++ fmt ++ " is for whole numbers");
            if (negative) t.put('-');
            const have: i32 = @max(d.point, 1);
            var pad: i32 = @as(i32, given orelse 0) - have;
            while (pad > 0) : (pad -= 1) t.put('0');
            wholeDigits(&t, &d, false);
        },
        'N', 'n', 'F', 'f', 'P', 'p', 'C', 'c' => {
            const places: i32 = @min(given orelse 2, 80);
            const percent = letter == 'P' or letter == 'p';
            const currency = letter == 'C' or letter == 'c';
            if (percent and d.len != 0) d.point += 2;
            d.roundTo(d.point + places, even);
            if (negative) t.put(if (currency) '(' else '-');
            if (currency) t.put(0xA4);
            wholeDigits(&t, &d, !(letter == 'F' or letter == 'f'));
            fraction(&t, &d, places);
            if (percent) {
                t.put(' ');
                t.put('%');
            }
            if (negative and currency) t.put(')');
        },
        'E', 'e' => {
            const places: i32 = @min(given orelse 6, 80);
            d.roundTo(places + 1, even);
            if (negative) t.put('-');
            t.put(d.digit(0));
            if (places > 0) {
                t.put('.');
                var k: i32 = 1;
                while (k <= places) : (k += 1) t.put(d.digit(k));
            }
            t.exponent(letter, d.point - 1, 3);
        },
        'G', 'g', 'R', 'r' => {
            const e: u8 = if (letter == 'g' or letter == 'r') 'e' else 'E';
            if (negative) t.put('-');
            const limit: i32 = if (shortest)
                (if (T == f32) 9 else 17)
            else if (whole and (letter == 'R' or letter == 'r' or (given orelse 0) == 0))
                std.math.maxInt(i32)
            else
                given.?;
            if (!shortest) d.roundTo(limit, even);
            if (d.len == 0) t.put('0') else t.general(&d, limit, e);
        },
        else => @compileError("fable: the format " ++ fmt ++ " is not supported"),
    }
    return out[0..t.len];
}

// ---------------------------------------------------------------------------------------------
// %A: a value as F# would write it
//
// This is the printer of FSharp.Core, rule for rule, so that the text is the same: the value
// becomes a layout (text, and joints that may or must break), the layout is fitted into lines
// of 80 characters by breaking the outermost joints first, and the result is written with the
// indentation the breaks ask for. A list shows its first 100 items; a record that contains
// itself is cut where it comes round again.
// ---------------------------------------------------------------------------------------------

const Joint = union(enum) { unbreakable, breakable: i32, broken: i32 };

const Layout = struct {
    /// no space is wanted before this text (`tight_left`) or after it (`tight_right`)
    tight_left: bool,
    tight_right: bool,
    what: union(enum) {
        leaf: []const u16,
        node: struct { l: *Layout, r: *Layout, joint: Joint },
    },
};

/// Where a value stands decides whether it needs brackets.
pub const Prec = enum(u8) { bracket_if_tuple_or_not_atomic = 2, bracket_if_tuple = 3, never_bracket = 4 };

const print_width = 80;
const print_length = 100;
const print_depth = 100;

pub const Shower = struct {
    arena: std.mem.Allocator,
    /// the reference records that are being written, to find one that contains itself
    path: [print_depth]*const anyopaque = undefined,
    on_path: usize = 0,
    /// the breaks that could still be made to gain room: the columns each would save (negative
    /// once it was made), the innermost last
    savings: std.ArrayList(i32) = .empty,
    outer: usize = 0,

    fn leaf(b: *Shower, tight_left: bool, text: []const u16, tight_right: bool) *Layout {
        const l = b.arena.create(Layout) catch @panic("fable: out of memory");
        l.* = .{ .tight_left = tight_left, .tight_right = tight_right, .what = .{ .leaf = text } };
        return l;
    }

    fn ascii(b: *Shower, tight_left: bool, text: []const u8, tight_right: bool) *Layout {
        const u = b.arena.alloc(u16, text.len) catch @panic("fable: out of memory");
        for (text, u) |c, *to| to.* = c;
        return b.leaf(tight_left, u, tight_right);
    }

    fn word(b: *Shower, text: []const u8) *Layout {
        return b.ascii(false, text, false);
    }

    fn join(b: *Shower, l: *Layout, r: *Layout, joint: Joint) *Layout {
        const n = b.arena.create(Layout) catch @panic("fable: out of memory");
        n.* = .{ .tight_left = l.tight_left, .tight_right = r.tight_right, .what = .{ .node = .{ .l = l, .r = r, .joint = joint } } };
        return n;
    }

    fn tight(b: *Shower, l: *Layout, r: *Layout) *Layout {
        return b.join(l, r, .unbreakable);
    }

    fn bracket(b: *Shower, l: *Layout) *Layout {
        return b.tight(b.tight(b.ascii(false, "(", true), l), b.ascii(true, ")", false));
    }

    /// The items with `sep` after each but the last, and a possible break after each `sep`.
    fn separated(b: *Shower, items: []const *Layout, sep: []const u8) *Layout {
        var all = items[0];
        for (items[1..]) |item| all = b.join(b.tight(all, b.ascii(true, sep, false)), item, .{ .breakable = 0 });
        return all;
    }

    /// `Case`, `Case x` or `Case (x, y)`: a union case, `Some`, or an F# exception.
    fn case(b: *Shower, name: []const u8, payload: anytype, prec: Prec, depth: i32) *Layout {
        const P = @TypeOf(payload);
        if (P == void) return b.word(name);
        const fields = if (@typeInfo(P) == .pointer) payload else &payload;
        const names = @typeInfo(@TypeOf(fields.*)).@"struct".field_names;
        comptime var n = 0;
        inline for (names) |field| {
            if (comptime !isCount(field)) n += 1;
        }
        if (n == 0) return b.word(name);
        var items: [n]*Layout = undefined;
        comptime var i = 0;
        inline for (names) |field| {
            if (comptime !isCount(field)) {
                items[i] = b.show(@field(fields, field), if (n == 1) .bracket_if_tuple_or_not_atomic else .bracket_if_tuple, depth - 1);
                i += 1;
            }
        }
        const args = if (n == 1) items[0] else b.bracket(b.separated(&items, ","));
        const whole = b.join(b.word(name), args, .{ .breakable = 2 });
        return if (@backingInt(prec) <= @backingInt(Prec.bracket_if_tuple_or_not_atomic)) b.bracket(whole) else whole;
    }

    /// `{ A = 1` and every further field on a line of its own.
    fn record(b: *Shower, fields: anytype, depth: i32) *Layout {
        var all: ?*Layout = null;
        inline for (@typeInfo(@TypeOf(fields.*)).@"struct".field_names) |field| {
            if (comptime !isCount(field)) {
                const value = b.show(@field(fields, field), .bracket_if_tuple, depth - 1);
                const item = b.join(b.tight(b.word(field), b.word("=")), value, .{ .breakable = 1 });
                all = if (all) |above| b.join(above, item, .{ .broken = 0 }) else item;
            }
        }
        return b.tight(b.tight(b.word("{"), all.?), b.word("}"));
    }

    fn number(b: *Shower, x: anytype) *Layout {
        const T = @TypeOf(x);
        var buf: [scratch_len + 4]u8 = undefined;
        switch (@typeInfo(T)) {
            .int => |info| {
                const suffix = switch (T) {
                    i8 => "y",
                    u8 => "uy",
                    i16 => "s",
                    i32 => "",
                    u32 => "u",
                    i64 => "L",
                    u64 => "UL",
                    isize => "n",
                    usize => "un",
                    else => if (info.signedness == .signed) "" else "u",
                };
                return b.word(std.fmt.bufPrint(&buf, "{d}{s}", .{ x, suffix }) catch unreachable);
            },
            .float => {
                const suffix = if (T == f32) "f" else "";
                if (std.math.isNan(x)) return b.word("nan" ++ suffix);
                if (std.math.isInf(x)) return if (x > 0) b.word("infinity" ++ suffix) else b.word("-infinity" ++ suffix);
                if (T == f32 and x > -2147483648.0 and x < 2147483648.0 and @trunc(x) == x) {
                    return b.word(std.fmt.bufPrint(&buf, "{d}.0f", .{@as(i32, @intFromFloat(x))}) catch unreachable);
                }
                const text = floatText(.{ .kind = 'g', .precision = 10 }, x, buf[0..scratch_len]);
                var plain = T == f64;
                for (text) |c| {
                    if (!(std.ascii.isDigit(c) or c == '-')) plain = false;
                }
                const tail = if (plain) ".0" else suffix;
                var all: [scratch_len + 4]u8 = undefined;
                return b.word(std.fmt.bufPrint(&all, "{s}{s}", .{ text, tail }) catch unreachable);
            },
            else => comptime unreachable,
        }
    }

    fn char(b: *Shower, c: u16) *Layout {
        var text: [8]u16 = undefined;
        var n: usize = 0;
        text[n] = '\'';
        n += 1;
        if (c == '\'' or c == '\\') {
            text[n] = '\\';
            text[n + 1] = c;
            n += 2;
        } else if (c == 8) {
            text[n] = '\\';
            text[n + 1] = 'b';
            n += 2;
        } else if (c < 0x20 or (c >= 0x7F and c <= 0x9F)) {
            text[n] = '\\';
            text[n + 1] = '0' + c / 100;
            text[n + 2] = '0' + (c / 10) % 10;
            text[n + 3] = '0' + c % 10;
            n += 4;
        } else {
            text[n] = c;
            n += 1;
        }
        text[n] = '\'';
        n += 1;
        return b.leaf(false, b.arena.dupe(u16, text[0..n]) catch @panic("fable: out of memory"), false);
    }

    fn quoted(b: *Shower, u: []const u16) *Layout {
        const text = b.arena.alloc(u16, u.len + 2) catch @panic("fable: out of memory");
        text[0] = '"';
        @memcpy(text[1..][0..u.len], u);
        text[u.len + 1] = '"';
        return b.leaf(false, text, false);
    }

    /// The layout of a value. A `u16` is taken to be a char.
    pub fn show(b: *Shower, x: anytype, prec: Prec, depth: i32) *Layout {
        const T = @TypeOf(x);
        if (depth <= 0) return b.word("...");
        if (T == String) return if (x) |p| b.quoted(p.units()) else b.word("null");
        if (T == Exn) return x.type.show(b, x, prec, depth);
        if (comptime isFunc(T)) return b.word("<fun>");
        switch (@typeInfo(T)) {
            .void => return b.word("()"),
            .bool => return b.word(if (x) "true" else "false"),
            .int => return if (T == u16) b.char(x) else b.number(x),
            .float => return b.number(x),
            .optional => return if (x) |v| b.case("Some", .{v}, prec, depth) else b.word("None"),
            .pointer => |ptr| {
                if (comptime @hasDecl(ptr.child, "fable_identity")) return ptr.child.fable_show(b, x, depth);
                if (comptime @hasDecl(ptr.child, "fable_array")) {
                    if (x.items.len == 0) return b.word("[||]");
                    var items: std.ArrayList(*Layout) = .empty;
                    for (x.items) |item| {
                        if (items.items.len == print_length) {
                            items.append(b.arena, b.word("...")) catch @panic("fable: out of memory");
                            break;
                        }
                        items.append(b.arena, b.show(item, .bracket_if_tuple, depth - 1)) catch @panic("fable: out of memory");
                    }
                    return b.tight(b.tight(b.ascii(false, "[|", true), b.separated(items.items, ";")), b.ascii(true, "|]", false));
                }
                // a reference record
                const addr: *const anyopaque = @ptrCast(x);
                for (b.path[0..b.on_path]) |seen| {
                    if (seen == addr) return b.word("...");
                }
                if (b.on_path == b.path.len) return b.word("...");
                b.path[b.on_path] = addr;
                b.on_path += 1;
                defer b.on_path -= 1;
                return b.record(x, depth);
            },
            .@"struct" => |s| {
                // a sequence (Seq.fs): `seq [a; b; c; d; ...]`, which walks it, as .NET does
                if (comptime @hasField(T, "fable_seq")) {
                    var items: [4]*Layout = undefined;
                    var n: usize = 0;
                    var more = false;
                    const walk = x.fable_seq.code(x.fable_seq.env, {}) catch {
                        drop(take());
                        return b.word("seq [...]");
                    };
                    defer drop(walk);
                    while (true) {
                        const next = walk.next.code(walk.next.env, {}) catch {
                            drop(take());
                            break;
                        };
                        const item = next orelse break;
                        defer drop(item);
                        if (n == 4) {
                            more = true;
                            break;
                        }
                        items[n] = b.show(item, .bracket_if_tuple, depth - 1);
                        n += 1;
                    }
                    return showSeq(b, items[0..n], more);
                }
                if (!s.is_tuple) return b.record(&x, depth);
                var items: [s.field_names.len]*Layout = undefined;
                inline for (s.field_names, 0..) |field, i| items[i] = b.show(@field(x, field), .bracket_if_tuple, depth - 1);
                return b.bracket(b.separated(&items, ","));
            },
            .@"union" => {
                if (comptime isCollection(T)) {
                    // `map [(1, "a"); ...]`, `set [1; 2]`: nine entries, then `...`
                    const name = if (T.fable_collection == .map) "map" else "set";
                    var items: std.ArrayList(*Layout) = .empty;
                    var w = TreeWalk(T).init(x);
                    while (w.next()) |n| {
                        if (items.items.len == 9) {
                            items.append(b.arena, b.word("...")) catch @panic("fable: out of memory");
                            break;
                        }
                        const item = if (comptime T.fable_collection == .map)
                            b.show(.{ n.key, n.value }, .bracket_if_tuple, depth - 1)
                        else
                            b.show(n.key, .bracket_if_tuple, depth - 1);
                        items.append(b.arena, item) catch @panic("fable: out of memory");
                    }
                    const list = if (items.items.len == 0)
                        b.word("[]")
                    else
                        b.tight(b.tight(b.ascii(false, "[", true), b.separated(items.items, ";")), b.ascii(true, "]", false));
                    const whole = b.join(b.word(name), list, .{ .breakable = 2 });
                    return if (@backingInt(prec) <= @backingInt(Prec.bracket_if_tuple_or_not_atomic)) b.bracket(whole) else whole;
                }
                if (comptime @hasDecl(T, "fable_list")) {
                    if (x == .Empty) return b.word("[]");
                    var items: std.ArrayList(*Layout) = .empty;
                    var rest = x;
                    while (rest == .Cons) : (rest = rest.Cons.Tail) {
                        if (items.items.len == print_length) {
                            items.append(b.arena, b.word("...")) catch @panic("fable: out of memory");
                            break;
                        }
                        items.append(b.arena, b.show(rest.Cons.Head, .bracket_if_tuple, depth - 1)) catch @panic("fable: out of memory");
                    }
                    return b.tight(b.tight(b.ascii(false, "[", true), b.separated(items.items, ";")), b.ascii(true, "]", false));
                }
                switch (x) {
                    inline else => |payload, tag| return b.case(@tagName(tag), payload, prec, depth),
                }
            },
            else => @compileError("fable: a value of type " ++ @typeName(T) ++ " cannot be written with %A"),
        }
    }

    /// Make the next break that is still open, the outermost first; the columns it saves.
    fn forceBreak(b: *Shower) ?i32 {
        if (b.outer == b.savings.items.len) return null;
        const saving = b.savings.items[b.outer];
        b.savings.items[b.outer] = -saving;
        b.outer += 1;
        return saving;
    }

    /// Fit `layout`, which starts at column `start`, into the width by turning joints that may
    /// break into breaks. Returns the column after it, and the width of its last line.
    fn fit(b: *Shower, start: i32, layout: *Layout) struct { i32, i32 } {
        switch (layout.what) {
            .leaf => |text| {
                const width: i32 = @intCast(text.len);
                var pos = start;
                while (pos + width > print_width) {
                    pos -= b.forceBreak() orelse break;
                }
                return .{ pos + width, width };
            },
            .node => |*n| {
                const mid: i32 = if (n.l.tight_right or n.r.tight_left) 0 else 1;
                var pos, const left = b.fit(start, n.l);
                switch (n.joint) {
                    .unbreakable => {
                        pos, const right = b.fit(pos + mid, n.r);
                        return .{ pos, left + mid + right };
                    },
                    .broken => |indent| {
                        pos, const right = b.fit(pos - left + indent, n.r);
                        return .{ pos, indent + right };
                    },
                    .breakable => |indent| {
                        const saving = left + mid - indent;
                        if (saving <= 0) {
                            pos, const right = b.fit(pos + mid, n.r);
                            return .{ pos, left + mid + right };
                        }
                        b.savings.append(b.arena, saving) catch @panic("fable: out of memory");
                        pos, const right = b.fit(pos + mid, n.r);
                        const made = b.savings.pop().? < 0;
                        if (b.outer > b.savings.items.len) b.outer = b.savings.items.len;
                        if (!made) return .{ pos, left + mid + right };
                        n.joint = .{ .broken = indent };
                        return .{ pos, indent + right };
                    },
                }
            },
        }
    }

    fn write(out: *TextBuilder, column: *i32, layout: *const Layout, tab: i32) void {
        switch (layout.what) {
            .leaf => |text| {
                out.add(text);
                column.* += @intCast(text.len);
            },
            .node => |n| {
                write(out, column, n.l, tab);
                switch (n.joint) {
                    .broken => |indent| {
                        out.addOne('\n');
                        var i: i32 = 0;
                        while (i < tab + indent) : (i += 1) out.addOne(' ');
                        column.* = tab + indent;
                        write(out, column, n.r, tab + indent);
                    },
                    else => {
                        if (!(n.l.tight_right or n.r.tight_left)) {
                            out.addOne(' ');
                            column.* += 1;
                        }
                        write(out, column, n.r, column.*);
                    },
                }
            },
        }
    }
};

/// `%A`: the value as F# would write it.
pub fn anyText(x: anytype) String {
    if (@TypeOf(x) == String and x == null) return str("<null>");
    var arena = std.heap.ArenaAllocator.init(allocator);
    defer arena.deinit();
    var b: Shower = .{ .arena = arena.allocator() };
    const layout = b.show(x, .bracket_if_tuple, print_depth);
    _ = b.fit(0, layout);
    var out: TextBuilder = .{};
    var column: i32 = 0;
    Shower.write(&out, &column, layout, 0);
    return out.finish();
}

// ---------------------------------------------------------------------------------------------
// .NET's ToString of a value: what `string x`, `{x}`, `Append x` and `String.Join` give
// ---------------------------------------------------------------------------------------------

/// Write `x` as .NET's ToString writes it: a string as it is, a number as `string` writes it,
/// `Some(1)`, `(1, a)`, `[1; 2; 3; ... ]` (three items), `map [(1, a)]`; a record or a union as
/// `%A`; None (null on .NET) as nothing.
fn writeNet(out: *TextBuilder, x: anytype) void {
    const T = @TypeOf(x);
    if (T == String) return out.add(unitsOf(x));
    if (T == u16) return out.addOne(x);
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
        .optional => if (x) |v| {
            out.addAscii("Some(");
            writeNet(out, v);
            out.addOne(')');
        },
        .@"struct" => |st| {
            if (st.is_tuple) {
                out.addOne('(');
                inline for (st.field_names, 0..) |name, i| {
                    if (i != 0) out.addAscii(", ");
                    writeNet(out, @field(x, name));
                }
                out.addOne(')');
            } else {
                const text = anyText(x);
                defer drop(text);
                out.add(unitsOf(text));
            }
        },
        .@"union" => {
            if (comptime @hasDecl(T, "fable_list")) {
                out.addOne('[');
                var rest = x;
                var n: usize = 0;
                while (rest == .Cons) : (rest = rest.Cons.Tail) {
                    if (n == 3) {
                        out.addAscii("; ... ");
                        break;
                    }
                    if (n != 0) out.addAscii("; ");
                    writeNet(out, rest.Cons.Head);
                    n += 1;
                }
                out.addOne(']');
                return;
            }
            if (comptime isCollection(T)) {
                out.addAscii(if (T.fable_collection == .map) "map [" else "set [");
                var w = TreeWalk(T).init(x);
                var n: usize = 0;
                while (w.next()) |node| {
                    if (n == 3) {
                        out.addAscii("; ... ");
                        break;
                    }
                    if (n != 0) out.addAscii("; ");
                    if (comptime T.fable_collection == .map) {
                        out.addOne('(');
                        writeNet(out, node.key);
                        out.addAscii(", ");
                        writeNet(out, node.value);
                        out.addOne(')');
                    } else writeNet(out, node.key);
                    n += 1;
                }
                out.addOne(']');
                return;
            }
            const text = anyText(x);
            defer drop(text);
            out.add(unitsOf(text));
        },
        else => {
            const text = anyText(x);
            defer drop(text);
            out.add(unitsOf(text));
        },
    }
}

/// `string x` and `x.ToString()` of an option, a tuple, a list, a map, a set.
pub fn toText(x: anytype) String {
    var out: TextBuilder = .{};
    writeNet(&out, x);
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

pub const StringBuilder = *struct {
    pub const fable_identity = {};
    @"$rc": u32 = 1,
    units: std.ArrayList(u16) = .empty,

    pub fn fable_free(c: anytype) void {
        c.units.deinit(allocator);
    }

    pub fn fable_show(b: *Shower, x: anytype, depth: i32) *Layout {
        _ = depth;
        return b.leaf(false, b.arena.dupe(u16, x.units.items) catch @panic("fable: out of memory"), false);
    }
};

pub fn sbNew(init: String) StringBuilder {
    const c = allocator.create(@typeInfo(StringBuilder).pointer.child) catch @panic("fable: out of memory");
    c.* = .{};
    c.units.appendSlice(allocator, unitsOf(init)) catch @panic("fable: out of memory");
    if (track) thread.stats.allocs += 1;
    return c;
}

/// `sb.Append x`: the builder again (a reference of its own).
pub fn sbAppend(sb: StringBuilder, x: anytype) StringBuilder {
    var out: TextBuilder = .{ .list = sb.units };
    writeNet(&out, x);
    sb.units = out.list;
    return dup(sb);
}

pub fn sbAppendLine(sb: StringBuilder, x: anytype) StringBuilder {
    var out: TextBuilder = .{ .list = sb.units };
    writeNet(&out, x);
    out.addOne('\n');
    sb.units = out.list;
    return dup(sb);
}

pub fn sbToString(sb: StringBuilder) String {
    return strFrom(sb.units.items);
}

pub fn sbLength(sb: StringBuilder) i32 {
    return @intCast(sb.units.items.len);
}

pub fn sbClear(sb: StringBuilder) StringBuilder {
    sb.units.clearRetainingCapacity();
    return dup(sb);
}

// ---------------------------------------------------------------------------------------------
// Split, Join, characters, comparison that ignores case
// ---------------------------------------------------------------------------------------------

fn splitPush(parts: *std.ArrayList(String), piece: []const u16, remove_empty: bool, trim: bool) void {
    var p = piece;
    if (trim) {
        while (p.len != 0 and unicode.isWhiteSpace(p[0])) p = p[1..];
        while (p.len != 0 and unicode.isWhiteSpace(p[p.len - 1])) p = p[0 .. p.len - 1];
    }
    if (remove_empty and p.len == 0) return;
    parts.append(allocator, strFrom(p)) catch @panic("fable: out of memory");
}

fn splitDone(parts: *std.ArrayList(String)) Array(String) {
    const A = Array(String);
    const items = arrayItems(A, parts.items.len);
    @memcpy(items, parts.items);
    parts.deinit(allocator);
    return arrayFrom(A, items);
}

/// `s.Split(chars, options)`: by any of the chars (white space if there are none). `options`
/// is .NET's StringSplitOptions: 1 removes empty parts, 2 trims each part.
pub fn strSplitChars(s: String, chars: []const u16, options: i32) Raised!Array(String) {
    const p = s orelse return nullRef();
    const u = p.units();
    var parts: std.ArrayList(String) = .empty;
    var start: usize = 0;
    for (u, 0..) |c, i| {
        const sep = if (chars.len == 0) unicode.isWhiteSpace(c) else std.mem.indexOfScalar(u16, chars, c) != null;
        if (sep) {
            splitPush(&parts, u[start..i], options & 1 != 0, options & 2 != 0);
            start = i + 1;
        }
    }
    splitPush(&parts, u[start..], options & 1 != 0, options & 2 != 0);
    return splitDone(&parts);
}

/// `s.Split(separators, options)` by strings (the first that matches at each place).
pub fn strSplitStrings(s: String, separators: []const String, options: i32) Raised!Array(String) {
    const p = s orelse return nullRef();
    const u = p.units();
    var parts: std.ArrayList(String) = .empty;
    var start: usize = 0;
    var i: usize = 0;
    outer: while (i < u.len) {
        for (separators) |sepStr| {
            const sep = unitsOf(sepStr);
            if (sep.len != 0 and std.mem.startsWith(u16, u[i..], sep)) {
                splitPush(&parts, u[start..i], options & 1 != 0, options & 2 != 0);
                i += sep.len;
                start = i;
                continue :outer;
            }
        }
        i += 1;
    }
    splitPush(&parts, u[start..], options & 1 != 0, options & 2 != 0);
    return splitDone(&parts);
}

pub fn strSplitString(s: String, separator: String, options: i32) Raised!Array(String) {
    return strSplitStrings(s, &.{separator}, options);
}

/// `s.ToCharArray()`
pub fn strToChars(s: String) Raised!Array(u16) {
    const p = s orelse return nullRef();
    const A = Array(u16);
    const items = arrayItems(A, p.len);
    @memcpy(items, p.units());
    return arrayFrom(A, items);
}

/// `String(chars)`
pub fn strOfChars(a: Array(u16)) String {
    return strFrom(a.items);
}

fn foldUnits(a: []const u16, b: []const u16) bool {
    if (a.len != b.len) return false;
    for (a, b) |x, y| {
        if (unicode.toUpper(x) != unicode.toUpper(y)) return false;
    }
    return true;
}

/// Comparisons with `StringComparison.OrdinalIgnoreCase`: each code unit by its upper case.
pub fn strEqualsIgnoreCase(a: String, b: String) bool {
    if (a == null or b == null) return a == b;
    return foldUnits(unitsOf(a), unitsOf(b));
}

pub fn strCompareIgnoreCase(a: String, b: String) i32 {
    if (a == null or b == null) return @as(i32, @intFromBool(a != null)) - @as(i32, @intFromBool(b != null));
    const x = unitsOf(a);
    const y = unitsOf(b);
    for (x[0..@min(x.len, y.len)], y[0..@min(x.len, y.len)]) |c, d| {
        const cu: i32 = unicode.toUpper(c);
        const du: i32 = unicode.toUpper(d);
        if (cu != du) return cu - du;
    }
    return @as(i32, @intCast(x.len)) - @as(i32, @intCast(y.len));
}

pub fn strStartsWithIgnoreCase(s: String, value: String) Raised!bool {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    return p.len >= v.len and foldUnits(p.units()[0..v.len], v.units());
}

pub fn strEndsWithIgnoreCase(s: String, value: String) Raised!bool {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    return p.len >= v.len and foldUnits(p.units()[p.len - v.len ..], v.units());
}

pub fn strIndexOfIgnoreCase(s: String, value: String) Raised!i32 {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    const u = p.units();
    if (v.len > u.len) return -1;
    var i: usize = 0;
    while (i + v.len <= u.len) : (i += 1) {
        if (foldUnits(u[i..][0..v.len], v.units())) return @intCast(i);
    }
    return -1;
}

/// `Char.GetNumericValue c`: the value of a digit, -1 for anything else. (Digits of every
/// script; .NET also knows fractions and roman numerals, which give -1 here.)
pub fn charNumericValue(c: u16) f64 {
    if (!unicode.isDigit(c)) return -1;
    // (the digits of a script are ten code units in a row, 0 first)
    var zero = c;
    while (zero > 0 and unicode.isDigit(zero - 1) and c - (zero - 1) < 10) zero -= 1;
    return @floatFromInt(c - zero);
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
};

pub fn Func(comptime Code: type) type {
    return struct {
        pub const fable_func = {};
        env: ?*Env,
        code: Code,
    };
}

fn isFunc(comptime T: type) bool {
    return @typeInfo(T) == .@"struct" and @hasDecl(T, "fable_func");
}

fn EnvOf(comptime Captures: type) type {
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

        fn destroy(header: *Env) void {
            const self: *Self = @fieldParentPtr("header", header);
            drop(self.captures);
            free(self);
        }
    };
}

/// A function value that owns `captures`.
pub inline fn closure(comptime F: type, comptime Captures: type, captures: Captures, code: @FieldType(F, "code")) F {
    const E = EnvOf(Captures);
    if (comptime E.cyclic) gcTick();
    const e = allocator.create(E) catch @panic("fable: out of memory");
    e.* = .{ .header = .{ .destroy = E.destroy }, .captures = captures };
    if (comptime E.cyclic) {
        e.hdr = thread.collector.hdr(&E.K.desc, E.K.isLeaf(e));
        e.header.gc = &e.hdr;
    }
    if (track) thread.stats.allocs += 1;
    return .{ .env = &e.header, .code = code };
}

/// What the function value captured, from inside its code.
pub inline fn captured(comptime Captures: type, env: ?*Env) *const Captures {
    const e: *EnvOf(Captures) = @fieldParentPtr("header", env.?);
    return &e.captures;
}

// ---------------------------------------------------------------------------------------------
// Exceptions
//
// A function that can raise returns `Raised!T`. `raise` moves the exception into `current` and
// returns `error.Raised`; every caller on the way gives up what it still owns and returns the
// error too, until a `with` handler takes the exception out. The exception is always owned in
// exactly one place.
//
// An exception is a reference-counted cell that starts with a header naming its type, so that
// a file can declare exception types that no other file has to know about.
// ---------------------------------------------------------------------------------------------

pub const Raised = error{Raised};

pub const ExnType = struct {
    name: []const u8,
    destroy: *const fn (Exn) void,
    /// the message, for an exception that was made with one
    message: ?*const fn (Exn) String = null,
    /// the .NET class this one derives from, if a program can name it
    parent: ?*const ExnType = null,
    /// the exception as `%A` writes it
    show: *const fn (*Shower, Exn, Prec, i32) *Layout,
};

pub const ExnHeader = struct {
    @"$rc": u32 = 1,
    /// the collector's header of this exception, if what it holds can be part of a cycle
    gc: ?*sgc.Hdr = null,
    type: *const ExnType,
};

/// F#'s `exn`.
pub const Exn = *ExnHeader;

/// An F# `exception` declaration with the given fields.
pub fn ExnOf(comptime name: []const u8, comptime Payload: type) type {
    return ExnUnder(name, Payload, null, true);
}

/// A .NET exception class with a message, derived from `Parent` (or from `System.Exception`).
fn Class(comptime name: []const u8, comptime Parent: ?type) type {
    return ExnUnder(name, Described, if (Parent) |P| &P.info else null, false);
}

fn ExnUnder(comptime name: []const u8, comptime Payload: type, comptime parent: ?*const ExnType, comptime sealed: bool) type {
    return struct {
        const cyclic = functions_in_cycles and holdsCyclic(Payload);
        const Whole = struct { header: ExnHeader, hdr: GcHdr(cyclic) = undefined, payload: Payload };
        const K = Collected(
            Whole,
            "hdr",
            @as(isize, @offsetOf(Whole, "header")) + @as(isize, @offsetOf(ExnHeader, "$rc")) - @as(isize, @offsetOf(Whole, "hdr")),
            "payload",
        );

        pub const info: ExnType = .{
            .name = name,
            .destroy = destroy,
            .message = if (Payload == Described) message else null,
            .parent = parent,
            .show = show,
        };

        fn show(b: *Shower, e: Exn, prec: Prec, depth: i32) *Layout {
            if (Payload != Described) return b.case(name, of(e), prec, depth);
            // a .NET exception: its class and its message
            const text = unitsOf(of(e).Message);
            const all = b.arena.alloc(u16, name.len + 2 + text.len) catch @panic("fable: out of memory");
            for (name ++ ": ", all[0 .. name.len + 2]) |c, *to| to.* = c;
            @memcpy(all[name.len + 2 ..], text);
            return b.leaf(false, all, false);
        }

        fn message(e: Exn) String {
            return dup(of(e).Message);
        }

        pub fn new(payload: Payload) Exn {
            if (comptime cyclic) gcTick();
            const c = allocator.create(Whole) catch @panic("fable: out of memory");
            c.* = .{ .header = .{ .type = &info }, .payload = payload };
            if (comptime cyclic) {
                c.hdr = thread.collector.hdr(&K.desc, K.isLeaf(c));
                c.header.gc = &c.hdr;
            }
            if (track) thread.stats.allocs += 1;
            return &c.header;
        }

        /// Is `e` an exception of this type, or of a class that derives from it?
        pub inline fn is(e: Exn) bool {
            if (sealed) return e.type == &info;
            var t: ?*const ExnType = e.type;
            while (t) |class| : (t = class.parent) {
                if (class == &info) return true;
            }
            return false;
        }

        /// The fields of an exception of this type.
        pub inline fn of(e: Exn) *const Payload {
            const c: *Whole = @fieldParentPtr("header", e);
            return &c.payload;
        }

        fn destroy(e: Exn) void {
            const c: *Whole = @fieldParentPtr("header", e);
            drop(c.payload);
            free(c);
        }
    };
}

/// The exception in flight is `thread.current`.
pub fn throw(e: Exn) void {
    std.debug.assert(thread.current == null);
    thread.current = e;
}

pub fn take() Exn {
    const e = thread.current.?;
    thread.current = null;
    return e;
}

/// Can a call with a result of this type have raised?
pub fn isRaised(comptime T: type) bool {
    return @typeInfo(T) == .error_union;
}

/// The result type of a function that raises only if one of the functions of other files it
/// calls does. (A file is compiled without knowing whether they do; Zig knows.)
pub fn MayRaise(comptime T: type, comptime callees: anytype) type {
    inline for (callees) |callee| {
        if (isRaised(@typeInfo(@TypeOf(callee)).@"fn".return_type.?)) return Raised!T;
    }
    return T;
}

/// What a .NET exception class holds: its message.
pub const Described = struct { Message: String };

/// What `failwith` raises: .NET's `System.Exception` with a message. (Every exception is a
/// `System.Exception`, so a test for that class is not a test at all; this is the test for
/// exactly this class, which is what the `Failure` pattern is.)
pub const Failure = ExnUnder("System.Exception", Described, null, true);

/// The .NET exception classes that a program can raise and handle by name, each under the
/// class it derives from on .NET.
pub const SystemException = Class("System.SystemException", null);
pub const ArgumentException = Class("System.ArgumentException", SystemException);
pub const ArgumentNullException = Class("System.ArgumentNullException", ArgumentException);
pub const ArgumentOutOfRangeException = Class("System.ArgumentOutOfRangeException", ArgumentException);
pub const ArithmeticException = Class("System.ArithmeticException", SystemException);
pub const DivideByZeroException = Class("System.DivideByZeroException", ArithmeticException);
pub const OverflowException = Class("System.OverflowException", ArithmeticException);
pub const InvalidOperationException = Class("System.InvalidOperationException", SystemException);
pub const NotSupportedException = Class("System.NotSupportedException", SystemException);
pub const NotImplementedException = Class("System.NotImplementedException", SystemException);
pub const IndexOutOfRangeException = Class("System.IndexOutOfRangeException", SystemException);
pub const NullReferenceException = Class("System.NullReferenceException", SystemException);
pub const FormatException = Class("System.FormatException", SystemException);
pub const KeyNotFoundException = Class("System.Collections.Generic.KeyNotFoundException", SystemException);
pub const MatchFailureException = Class("Microsoft.FSharp.Core.MatchFailureException", null);
pub const AggregateException = Class("System.AggregateException", null);

/// Raise an exception of a .NET class with a message.
pub fn raise(comptime C: type, message: String) Raised {
    throw(C.new(.{ .Message = message }));
    return error.Raised;
}

/// `a / b` for whole numbers: as .NET, a division by zero raises, and so does the smallest
/// number of 32 or 64 bits divided by -1 (its result does not fit).
pub fn div(comptime T: type, a: T, b: T) Raised!T {
    if (b == 0) return raise(DivideByZeroException, str("Attempted to divide by zero."));
    const info = @typeInfo(T).int;
    if (info.signedness == .signed and b == -1) {
        if (info.bits >= 32 and a == std.math.minInt(T)) {
            return raise(OverflowException, str("Arithmetic operation resulted in an overflow."));
        }
        return 0 -% a;
    }
    return @divTrunc(a, b);
}

/// `a % b` for whole numbers, with the sign of `a`.
pub fn rem(comptime T: type, a: T, b: T) Raised!T {
    if (b == 0) return raise(DivideByZeroException, str("Attempted to divide by zero."));
    const info = @typeInfo(T).int;
    if (info.signedness == .signed and b == -1) {
        if (info.bits >= 32 and a == std.math.minInt(T)) {
            return raise(OverflowException, str("Arithmetic operation resulted in an overflow."));
        }
        return 0;
    }
    return @rem(a, b);
}

/// `e.Message`: the message an exception was made with; for an F# exception, the exception
/// as `%A` writes it.
pub fn exnMessage(e: Exn) String {
    if (e.type.message) |message| return message(e);
    return anyText(e);
}

/// The program's entry point let an exception escape: say which, and give it up.
pub fn uncaught() void {
    const e = take();
    const text = exnMessage(e);
    write_err("Unhandled exception. ");
    write_err(e.type.name);
    write_err(": ");
    writeText(write_err, text, true);
    drop(text);
    drop(e);
}

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

pub inline fn across(
    comptime f: anytype,
    comptime sig: anytype,
    comptime uses: anytype,
    args: anytype,
) @typeInfo(@TypeOf(f)).@"fn".return_type.? {
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

/// Cells that were allocated and not freed (0 when counters are not kept).
pub fn live() i64 {
    return thread.stats.allocs - thread.stats.frees;
}

/// Called when the program's entry point has returned: true, with a message, if cells are
/// still allocated. Only checks in builds that keep counters.
pub fn leaked() bool {
    // (cycles that died without anything noticing yet are not leaks)
    _ = collect();
    if (!track or live() == 0) return false;
    std.debug.print("fable: {d} cell(s) were never freed (allocated {d}, freed {d})\n", .{ live(), thread.stats.allocs, thread.stats.frees });
    return true;
}

// ---------------------------------------------------------------------------------------------
// Numbers
// ---------------------------------------------------------------------------------------------
// Numbers: what F#'s operators and System.Math do, raising what they raise on .NET
// ---------------------------------------------------------------------------------------------

fn overflow() Raised {
    return raise(OverflowException, str("Arithmetic operation resulted in an overflow."));
}

/// `a + b` under `open Checked`
pub fn checkedAdd(a: anytype, b: @TypeOf(a)) Raised!@TypeOf(a) {
    const r = @addWithOverflow(a, b);
    if (r[1] != 0) return overflow();
    return r[0];
}

pub fn checkedSub(a: anytype, b: @TypeOf(a)) Raised!@TypeOf(a) {
    const r = @subWithOverflow(a, b);
    if (r[1] != 0) return overflow();
    return r[0];
}

pub fn checkedMul(a: anytype, b: @TypeOf(a)) Raised!@TypeOf(a) {
    const r = @mulWithOverflow(a, b);
    if (r[1] != 0) return overflow();
    return r[0];
}

pub fn checkedNeg(a: anytype) Raised!@TypeOf(a) {
    return checkedSub(@as(@TypeOf(a), 0), a);
}

/// `int x` under `open Checked`: a value that does not fit raises.
pub fn checkedConv(comptime To: type, x: anytype) Raised!To {
    switch (@typeInfo(@TypeOf(x))) {
        .int, .comptime_int => {
            if (x < std.math.minInt(To) or x > std.math.maxInt(To)) return overflow();
            return @intCast(x);
        },
        .float, .comptime_float => {
            const t = @trunc(x);
            if (t != t or t < @as(f64, @floatFromInt(std.math.minInt(To))) or t > @as(f64, @floatFromInt(std.math.maxInt(To)))) return overflow();
            return @intFromFloat(t);
        },
        else => @compileError("checkedConv: " ++ @typeName(@TypeOf(x))),
    }
}

/// `abs x`: the smallest whole number has no absolute value, and .NET raises for it.
pub fn absOf(x: anytype) Raised!@TypeOf(x) {
    const T = @TypeOf(x);
    if (comptime @typeInfo(T) == .int and @typeInfo(T).int.signedness == .signed) {
        if (x == std.math.minInt(T)) return raise(OverflowException, str("Negating the minimum value of a twos complement number is invalid."));
    }
    return if (comptime @typeInfo(T) == .float) @abs(x) else if (x < 0) -x else x;
}

/// `sign x`: -1, 0 or 1; not a number has no sign.
pub fn signOf(x: anytype) Raised!i32 {
    if (comptime @typeInfo(@TypeOf(x)) == .float) {
        if (x != x) return raise(ArithmeticException, str("Function does not accept floating point Not-a-Number values."));
    }
    return if (x < 0) -1 else if (x > 0) 1 else 0;
}

/// `pown x n`: by squaring, wrapping for whole numbers; a negative power of a whole number
/// raises nothing on .NET and is 0 unless x is 1 or -1 (F# divides 1 by the power).
pub fn pown(x: anytype, n: i32) @TypeOf(x) {
    const T = @TypeOf(x);
    if (n < 0) {
        if (comptime @typeInfo(T) == .float) return 1 / pown(x, -%n);
        return if (x == 1) 1 else if (x == -1 and @rem(n, 2) != 0) -1 else if (x == -1) 1 else 0;
    }
    var result: T = 1;
    var base = x;
    var e: u32 = @intCast(n);
    while (e != 0) : (e >>= 1) {
        if (e & 1 != 0) result = if (comptime @typeInfo(T) == .float) result * base else result *% base;
        base = if (comptime @typeInfo(T) == .float) base * base else base *% base;
    }
    return result;
}

/// `round x`: to the nearest, a tie to the even number, as .NET.
pub fn roundEven(x: anytype) @TypeOf(x) {
    const r = @round(x);
    if (@abs(x - @trunc(x)) == 0.5) return 2 * @round(x / 2);
    return r;
}

/// `Math.Round(x, digits)`
pub fn roundTo(x: f64, digits: i32) f64 {
    if (digits <= 0) return roundEven(x);
    const scale = std.math.pow(f64, 10, @floatFromInt(digits));
    return roundEven(x * scale) / scale;
}

/// `Math.Log(x, b)`
pub fn logBase(x: f64, b: f64) f64 {
    return @log(x) / @log(b);
}

/// `Math.Clamp(x, lo, hi)`
pub fn clamp(x: anytype, lo: @TypeOf(x), hi: @TypeOf(x)) Raised!@TypeOf(x) {
    if (lo > hi) return raise(ArgumentException, format(.{ "'", lo, "' cannot be greater than ", hi, "." }));
    return if (x < lo) lo else if (x > hi) hi else x;
}

/// The name .NET gives a whole-number type in an overflow message.
fn netIntName(comptime T: type) []const u8 {
    return switch (T) {
        i8 => "a signed byte",
        u8 => "an unsigned byte",
        i16 => "an Int16",
        u16 => "a UInt16",
        i32 => "an Int32",
        u32 => "a UInt32",
        i64 => "an Int64",
        u64 => "a UInt64",
        else => @typeName(T),
    };
}

fn trimmed(s: String) []const u16 {
    var u = unitsOf(s);
    while (u.len != 0 and unicode.isWhiteSpace(u[0])) u = u[1..];
    while (u.len != 0 and unicode.isWhiteSpace(u[u.len - 1])) u = u[0 .. u.len - 1];
    return u;
}

fn badFormat(s: String) Raised {
    return raise(FormatException, format(.{ "The input string '", s, "' was not in a correct format." }));
}

const ParseStyle = enum {
    /// `Int32.Parse`: white space, a sign, decimal digits
    dotnet,
    /// F#'s `int s`: also `0x`, `0o` and `0b` and `_` between digits
    fsharp,
};

/// A whole number from text, or null if the text is not one; error.Overflow if it is one
/// that does not fit in 64 bits (or in `T`, for which the caller says what to raise).
fn parseWhole(comptime T: type, u: []const u16, comptime style: ParseStyle) error{ Format, Overflow }!T {
    var i: usize = 0;
    var negative = false;
    if (u.len != 0 and (u[0] == '-' or u[0] == '+')) {
        negative = u[0] == '-';
        i = 1;
    }
    var radix: u8 = 10;
    if (style == .fsharp and u.len >= i + 2 and u[i] == '0') {
        switch (u[i + 1]) {
            'x', 'X' => radix = 16,
            'o', 'O' => radix = 8,
            'b', 'B' => radix = 2,
            else => {},
        }
        if (radix != 10) i += 2;
    }
    if (i == u.len) return error.Format;
    var value: u128 = 0;
    var digits: usize = 0;
    while (i < u.len) : (i += 1) {
        const c = u[i];
        if (style == .fsharp and c == '_' and digits != 0 and i + 1 < u.len) continue;
        const d: u8 = switch (c) {
            '0'...'9' => @intCast(c - '0'),
            'a'...'f' => @intCast(c - 'a' + 10),
            'A'...'F' => @intCast(c - 'A' + 10),
            else => return error.Format,
        };
        if (d >= radix) return error.Format;
        value = value * radix + d;
        digits += 1;
        if (value > std.math.maxInt(u64) + 1) return error.Overflow;
    }
    const info = @typeInfo(T).int;
    // (F# reads 0x, 0o and 0b numbers as the bits of the type: 0xFFFFFFFF is -1)
    if (radix != 10) {
        if (value > std.math.maxInt(@Int(.unsigned, info.bits))) return error.Overflow;
        const bits: @Int(.unsigned, info.bits) = @intCast(value);
        const v: T = @bitCast(bits);
        return if (negative) 0 -% v else v;
    }
    if (negative) {
        if (value > @as(u128, @intCast(-@as(i129, std.math.minInt(T))))) return error.Overflow;
        return @intCast(-@as(i129, @intCast(value)));
    }
    if (value > std.math.maxInt(T)) return error.Overflow;
    return @intCast(value);
}

/// `Int32.Parse s` and the others.
pub fn parseInt(comptime T: type, s: String) Raised!T {
    if (s == null) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 's')"));
    return parseWhole(T, trimmed(s), .dotnet) catch |e| switch (e) {
        error.Format => badFormat(s),
        error.Overflow => raise(OverflowException, str("Value was either too large or too small for " ++ netIntName(T) ++ ".")),
    };
}

/// F#'s `int s`, `byte s`, ...: the types of 32 bits and less are read as 32 bits and then
/// converted with a check, as F# does.
pub fn parseIntFs(comptime T: type, s: String) Raised!T {
    const u = trimmed(s);
    if (u.len == 0) return raise(FormatException, str("Input string was not in a correct format."));
    const info = @typeInfo(T).int;
    const Wide = if (info.bits >= 64) T else if (info.signedness == .signed) i32 else u32;
    const wide = parseWhole(Wide, u, .fsharp) catch |e| return switch (e) {
        error.Format => badFormat(s),
        error.Overflow => raise(OverflowException, str("Value was either too large or too small for " ++ netIntName(Wide) ++ ".")),
    };
    if (Wide == T) return wide;
    if (wide < std.math.minInt(T) or wide > std.math.maxInt(T)) return raise(OverflowException, str("Arithmetic operation resulted in an overflow."));
    return @intCast(wide);
}

/// `Int32.TryParse(s, &v)`: the number, or null.
pub fn tryParseInt(comptime T: type, s: String) ?T {
    if (s == null) return null;
    return parseWhole(T, trimmed(s), .dotnet) catch null;
}

fn parseReal(comptime T: type, u: []const u16) ?T {
    var buf: [128]u8 = undefined;
    if (u.len == 0 or u.len > buf.len) return null;
    for (u, 0..) |c, i| {
        // (Zig reads `_`, hexadecimal and `inf`, which .NET does not)
        if (c > 0x7F or c == '_' or c == 'x' or c == 'X' or c == 'p' or c == 'P') return null;
        buf[i] = @intCast(c);
    }
    const text = buf[0..u.len];
    const body = if (text[0] == '-' or text[0] == '+') text[1..] else text;
    const negative = text[0] == '-';
    if (std.mem.eql(u8, body, "NaN")) return std.math.nan(T);
    if (std.mem.eql(u8, body, "Infinity") or std.mem.eql(u8, body, "∞")) return if (negative) -std.math.inf(T) else std.math.inf(T);
    for (body) |c| {
        if (std.ascii.isAlphabetic(c) and c != 'e' and c != 'E') return null;
    }
    return std.fmt.parseFloat(T, text) catch null;
}

/// `Double.Parse s` and F#'s `float s`
pub fn parseFloat(comptime T: type, s: String) Raised!T {
    if (s == null) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 's')"));
    return parseReal(T, trimmed(s)) orelse badFormat(s);
}

pub fn tryParseFloat(comptime T: type, s: String) ?T {
    if (s == null) return null;
    return parseReal(T, trimmed(s));
}

/// `Boolean.Parse s`
pub fn parseBool(s: String) Raised!bool {
    const u = trimmed(s);
    if (u.len == 4 and unicode.toLower(u[0]) == 't' and unicode.toLower(u[1]) == 'r' and unicode.toLower(u[2]) == 'u' and unicode.toLower(u[3]) == 'e') return true;
    if (u.len == 5 and unicode.toLower(u[0]) == 'f' and unicode.toLower(u[1]) == 'a' and unicode.toLower(u[2]) == 'l' and unicode.toLower(u[3]) == 's' and unicode.toLower(u[4]) == 'e') return false;
    return raise(FormatException, format(.{ "String '", s, "' was not recognized as a valid Boolean." }));
}

fn addOf(a: anytype, b: @TypeOf(a)) @TypeOf(a) {
    return if (comptime @typeInfo(@TypeOf(a)) == .float) a + b else a +% b;
}

/// `List.sum xs`
pub fn listSum(xs: anytype) @FieldType(@typeInfo(@FieldType(@TypeOf(xs), "Cons")).pointer.child, "Head") {
    var total: @TypeOf(xs.Cons.Head) = 0;
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) total = addOf(total, rest.Cons.Head);
    return total;
}

/// `List.sumBy f xs`
pub fn listSumBy(comptime R: type, f: anytype, xs: anytype) Raised!R {
    var total: R = 0;
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) total = addOf(total, try f.code(f.env, dup(rest.Cons.Head)));
    return total;
}

fn emptyInput(comptime what: []const u8) Raised {
    return raise(ArgumentException, str("The input " ++ what ++ " was empty. (Parameter 'source')"));
}

/// `List.average xs`
pub fn listAverage(xs: anytype) Raised!@TypeOf(xs.Cons.Head) {
    var total: @TypeOf(xs.Cons.Head) = 0;
    var n: usize = 0;
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        total += rest.Cons.Head;
        n += 1;
    }
    if (n == 0) return emptyInput("sequence");
    return total / @as(@TypeOf(total), @floatFromInt(n));
}

/// `List.averageBy f xs`
pub fn listAverageBy(comptime R: type, f: anytype, xs: anytype) Raised!R {
    var total: R = 0;
    var n: usize = 0;
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        total += try f.code(f.env, dup(rest.Cons.Head));
        n += 1;
    }
    if (n == 0) return emptyInput("sequence");
    return total / @as(R, @floatFromInt(n));
}

/// `Array.sum a`
pub fn arraySum(a: anytype) ItemOf(@TypeOf(a)) {
    var total: ItemOf(@TypeOf(a)) = 0;
    for (a.items) |x| total = addOf(total, x);
    return total;
}

/// `Array.average a`
pub fn arrayAverage(a: anytype) Raised!ItemOf(@TypeOf(a)) {
    if (a.items.len == 0) return raise(ArgumentException, str("The input array was empty. (Parameter 'array')"));
    var total: ItemOf(@TypeOf(a)) = 0;
    for (a.items) |x| total += x;
    return total / @as(ItemOf(@TypeOf(a)), @floatFromInt(a.items.len));
}

// ---------------------------------------------------------------------------------------------

/// A conversion between number types with the result .NET gives:
/// - integer to integer keeps the low bits (sign- or zero-extending the source first);
/// - float to integer truncates toward zero, saturates at the target's limits, NaN is 0;
/// - integer to float and float to float round to nearest.
pub fn conv(comptime To: type, x: anytype) To {
    const From = @TypeOf(x);
    switch (@typeInfo(To)) {
        .int => |to| switch (@typeInfo(From)) {
            .int => |from| {
                const bits = @max(to.bits, from.bits);
                const WideFrom = @Int(from.signedness, bits);
                const WideTo = @Int(to.signedness, bits);
                return @truncate(@as(WideTo, @bitCast(@as(WideFrom, x))));
            },
            .float => {
                if (std.math.isNan(x)) return 0;
                const t = @trunc(x);
                if (t >= @as(From, @floatFromInt(std.math.maxInt(To)))) return std.math.maxInt(To);
                if (t <= @as(From, @floatFromInt(std.math.minInt(To)))) return std.math.minInt(To);
                return @intFromFloat(t);
            },
            .comptime_int, .comptime_float => return x,
            else => @compileError("conv: unsupported source type " ++ @typeName(From)),
        },
        .float => switch (@typeInfo(From)) {
            .int => return @floatFromInt(x),
            .float => return @floatCast(x),
            .comptime_int, .comptime_float => return x,
            else => @compileError("conv: unsupported source type " ++ @typeName(From)),
        },
        else => @compileError("conv: unsupported target type " ++ @typeName(To)),
    }
}

// ---------------------------------------------------------------------------------------------
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

fn testCons(head: i32, tail: TestList) TestList {
    return .{ .Cons = cell(TestList, .Cons, .{ .head = head, .tail = tail }) };
}

fn testRange(n: i32) TestList {
    var l: TestList = .Nil;
    var i: i32 = n;
    while (i > 0) : (i -= 1) l = testCons(i, l);
    return l;
}

fn testTree(depth: i32) TestTree {
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

fn testSum(xs: TestList) i32 {
    var total: i32 = 0;
    var cur = xs;
    while (cur == .Cons) : (cur = cur.Cons.tail) total += cur.Cons.head;
    return total;
}
const testSum_sig = .{ .borrows = .{true}, .result_borrowed = false };

fn testTail(xs: TestList) TestList {
    return if (xs == .Cons) xs.Cons.tail else .Nil;
}
const testTail_sig = .{ .borrows = .{true}, .result_borrowed = true };

fn testPush(n: i32, xs: TestList) TestList {
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

fn testAddSum(env: ?*Env, x: i32) i32 {
    const c = captured(TestCaptures, env);
    return x + c.n + testSum(c.xs);
}

fn testDouble(_: ?*Env, x: i32) i32 {
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

fn testCheck(x: i32, owned: TestList) Raised!i32 {
    if (x < 0) {
        throw(TestParseError.new(.{ .pos = x, .items = owned }));
        return error.Raised;
    }
    drop(owned);
    return x;
}
const testCheck_sig = .{ .borrows = .{ false, false }, .result_borrowed = false };

fn testOuter(x: i32) MayRaise(i32, .{testCheck}) {
    const xs = testRange(2);
    const raw = across(testCheck, testCheck_sig, .{ .plain, .give }, .{ x, xs });
    const r = if (comptime isRaised(@TypeOf(raw))) (raw catch return error.Raised) else raw;
    return r + 1;
}

fn testPlain(x: i32) MayRaise(i32, .{testSum}) {
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
    const box = new(Ref(TestList), .{ .contents = testRange(3) });
    const alias = dup(box);
    store(&alias.contents, testRange(5));
    try std.testing.expectEqual(@as(i32, 15), testSum(box.contents));
    try std.testing.expect(eql(box, alias));
    drop(head);
    drop(second);
    drop(box);
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

fn testPerson(id: i32) TestPerson {
    return new(TestPerson, .{ .id = id, .friend = null, .friends = .Empty, .callback = null });
}

const TestSelf = struct { self: TestPerson };

fn testAddId(env: ?*Env, x: i32) Raised!i32 {
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

fn testThreadWork(result: *i64) void {
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

fn expectText(expected: []const u8, s: String) !void {
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

fn expectFloat(expected: []const u8, comptime spec: Spec, value: anytype) !void {
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

fn expectRaised(comptime C: type, expected: []const u8, result: anytype) !void {
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

fn expectNet(expected: []const u8, comptime fmt: []const u8, value: anytype) !void {
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

fn run(comptime c: u8, comptime n: usize) *const [n]u8 {
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

fn testList(comptime T: type, items: []const T) List(T) {
    var all: List(T) = .Empty;
    var i = items.len;
    while (i > 0) {
        i -= 1;
        const tail = all;
        all = .{ .Cons = cell(List(T), .Cons, .{ .Head = dup(items[i]), .Tail = tail }) };
    }
    return all;
}

fn expectAny(expected: []const u8, x: anytype) !void {
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
        fn of(l: ShowTree, v: i32, r: ShowTree) ShowTree {
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
    try std.testing.expectEqual(@as(f64, 2.57), roundTo(2.567, 2));
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
    dictSet(d, 3, str("c"));
    dictSet(d, 2, str("B"));
    try expectAny("seq [[2, B]; [1, a]; [3, c]]", d);
    try expectRaised(ArgumentException, "An item with the same key has already been added. Key: 1", dictAdd(d, 1, str("x")));
    try expectRaised(KeyNotFoundException, "The given key '9' was not present in the dictionary.", dictGet(d, 9));
    try std.testing.expect(htRemove(d, 2));
    dictSet(d, 7, str("g"));
    try expectAny("seq [[7, g]; [1, a]; [3, c]]", d);
    try std.testing.expectEqual(@as(i32, 3), htCount(d));
    const h = setOfList(HashSet(i32), listOf(i32, &.{ 3, 1, 3 }));
    defer drop(h);
    try std.testing.expect(setAdd(h, 4) and !setAdd(h, 1));
    try expectAny("seq [3; 1; 4]", h);
    for (0..1000) |i| dictSet(d, @intCast(i), str("n"));
    try std.testing.expectEqual(@as(i32, 1000), htCount(d));
    _ = before;
}

test ".NET's ToString, Split, StringBuilder, categories" {
    try expectText("Some(1)|(1, a)|[1; 2; 3; ... ]|[a]", format(.{
        toText(@as(?i32, 1)), "|", toText(@as(struct { i32, String }, .{ 1, str("a") })), "|", toText(listOf(i32, &.{ 1, 2, 3, 4 })), "|", toText(listOf(String, &.{str("a")})),
    }));
    try expectAny("[|\"a\"; \"b\"; \"\"; \"c\"|]", try strSplitChars(str("a,b,,c"), &.{','}, 0));
    try expectAny("[|\"a\"; \"b\"|]", try strSplitChars(str("a,,b"), &.{','}, 1));
    try expectAny("[|\"a\"; \"b\"; \"c\"|]", try strSplitString(str("a--b--c"), str("--"), 0));
    try expectAny("[|\"a\"; \"b\"; \"c\"|]", try strSplitChars(str("a b\tc"), &.{}, 0));
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
    const w = weakNew(Weak(R), a);
    const w2 = weakNew(Weak(R), a);
    const got = weakTryGet(w).?;
    try std.testing.expectEqual(@as(i32, 7), got.value);
    drop(got);
    drop(a);
    try std.testing.expect(weakTryGet(w) == null and weakTryGet(w2) == null);
    const b = new(R, .{ .value = 8 });
    weakSet(w, b);
    try std.testing.expectEqual(@as(i32, 8), weakTryGet(w).?.value);
    drop(b);
    drop(b);
    drop(w);
    drop(w2);
    try std.testing.expectEqual(@as(usize, 0), thread.weak.count());
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);
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
