//! Arrays (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");
const ArgumentException = rt.ArgumentException;
const ArgumentOutOfRangeException = rt.ArgumentOutOfRangeException;
const GcHdr = rt.GcHdr;
const IndexOutOfRangeException = rt.IndexOutOfRangeException;
const List = rt.List;
const NotSupportedException = rt.NotSupportedException;
const Raised = rt.Raised;
const String = rt.String;
const apply2 = rt.apply2;
const cell = rt.cell;
const countNegative = rt.countNegative;
const drop = rt.drop;
const dup = rt.dup;
const eachHdr = rt.eachHdr;
const eql = rt.eql;
const format = rt.format;
const gcHeader = rt.gcHeader;
const gcOf = rt.gcOf;
const gcTick = rt.gcTick;
const hasGc = rt.hasGc;
const holdsCyclic = rt.holdsCyclic;
const raise = rt.raise;
const storeValue = rt.storeValue;
const str = rt.str;
const thread = rt.thread;
const touch = rt.touch;
const track = rt.track;
const unstored = rt.unstored;

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
        /// allocated slice length in `items.ptr[0..capacity]`, allowing O(1) in-place shrink
        capacity: usize = 0,
        /// a two-dimensional array: its rows and columns, the items row after row
        shape: ?[2]usize = null,
    };
}

/// The type of the items of the array type `A`.
pub fn ItemOf(comptime A: type) type {
    return @typeInfo(A).pointer.child.fable_array;
}

pub fn arrayItems(comptime A: type, n: usize) []ItemOf(A) {
    return rt.alloc().alloc(ItemOf(A), n) catch rt.oom();
}

/// The items of an array of a length the program computed: OutOfMemoryException when they do
/// not fit (see `rt.oom_policy`)
pub fn arrayItemsOrRaise(comptime A: type, n: usize) Raised![]ItemOf(A) {
    return rt.alloc().alloc(ItemOf(A), n) catch return rt.oomRaise();
}

/// A new array that owns `items`.
pub fn arrayFrom(comptime A: type, items: []ItemOf(A)) A {
    const C = @typeInfo(A).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = rt.alloc().create(C) catch rt.oom();
    c.* = .{ .items = items, .capacity = items.len };
    if (comptime hasGc(C)) c.@"$gc" = gcHeader(C, c);
    if (track) thread.stats.allocs += 1;
    return c;
}

/// .NET's null of an array type: one array of no items for each type, which no reference ever
/// frees (its count stays far from one) and which is never changed in place. Code that walks
/// arrays sees no items in it; what .NET raises NullReferenceException for, `Length` and an
/// index, raise it here when given it.
fn NullOf(comptime A: type) type {
    const C = @typeInfo(A).pointer.child;
    return if (hasGc(C)) struct {
        // (the collector follows these: one of the thread's own, made as any other array, given
        // up when the collector goes)
        threadlocal var made: ?A = null;

        fn get() A {
            if (made) |c| return c;
            // Allocate thread-lifetime null array cells on the global heap (`rt.allocator`),
            // never inside a stack arena that may return before the thread exits.
            rt.gcTick();
            const c = rt.allocator.create(C) catch rt.oom();
            c.* = .{ .items = &.{}, .capacity = 0 };
            c.@"$rc" = null_count;
            c.@"$gc" = gcHeader(C, c);
            if (track) thread.stats.allocs += 1;
            rt.thread.null_arrays.append(rt.bookkeeping(), .{ .cell = c, .free = free }) catch rt.oom();
            rt.uncount();
            made = c;
            return c;
        }

        fn free(p: *anyopaque) void {
            const c: A = @ptrCast(@alignCast(p));
            // (shared with another thread, which may outlive this one: left as it is, one empty
            // array per type and thread, never counted)
            if (rt.isShared(c)) {
                made = null;
                return;
            }
            c.@"$rc" = (c.@"$rc" & rt.weak_bit) | 1;
            rt.recount();
            rt.drop(c);
            made = null;
        }
    } else struct {
        var static: C = .{ .@"$rc" = null_count | rt.shared_bit, .items = &.{}, .capacity = 0 };

        fn get() A {
            return &static;
        }
    };
}

/// Null array marker reusing `rt.immortal_bit` so null arrays never contend on `$rc` atomics.
pub const null_count: u32 = rt.immortal_bit;

/// The null of an array type (a reference of its own)
pub fn arrayNull(comptime A: type) A {
    return rt.dup(NullOf(A).get());
}

/// Is an array .NET's null?
pub inline fn arrayIsNull(a: anytype) bool {
    return rt.isCellNull(a);
}

/// `xs :> System.Array`: the items as objects (a new array: what is set through it is not seen
/// in the one it was made of)
pub fn arrayBoxAll(a: anytype) Array(rt.Any) {
    const A = Array(rt.Any);
    const items = arrayItems(A, a.items.len);
    for (items, 0..) |*to, i| {
        const v = arrayItemAt(a, i);
        defer rt.drop(v);
        to.* = rt.box(v);
    }
    return arrayFrom(A, items);
}

/// `[| a; b; c |]`
pub fn arrayOf(comptime A: type, values: anytype) A {
    const items = arrayItems(A, values.len);
    inline for (values, 0..) |v, i| items[i] = dup(@as(ItemOf(A), v));
    return arrayFrom(A, items);
}

/// Is all-zero memory a value of this type? (It is .NET's null, zero, false and None.)
pub fn hasZero(comptime T: type) bool {
    if (T == String) return true;
    return switch (@typeInfo(T)) {
        .int, .float, .bool, .void, .optional => true,
        .@"struct" => |s| blk: {
            if (@hasDecl(T, "fable_func") or @hasDecl(T, "fable_iface")) break :blk false;
            for (s.field_types) |F| {
                if (!hasZero(F)) break :blk false;
            }
            break :blk true;
        },
        else => false,
    };
}

/// `Array.zeroCreate n`. .NET fills the array with null where the items are records, unions
/// or functions: here with `rt.nullOf` of the item type (a reference record's null cell, a
/// union's first case, a function that raises NullReferenceException).
pub fn arrayZero(comptime A: type, n: i32) Raised!A {
    if (n < 0) return countNegative(n);
    const items = try arrayItemsOrRaise(A, @intCast(n));
    fillDefault(A, items) catch |e| {
        rt.alloc().free(items);
        return e;
    };
    return arrayFrom(A, items);
}

/// Items set to .NET's default of their type: zero, null (an array's null for arrays, a
/// record's null cell for reference records, see `rt.nullOf`)
fn fillDefault(comptime A: type, items: []ItemOf(A)) Raised!void {
    const T = ItemOf(A);
    if (comptime hasZero(T)) {
        @memset(items, comptime std.mem.zeroes(T));
    } else if (comptime rt.hasNull(T)) {
        for (items) |*x| x.* = rt.nullOf(T);
    } else if (items.len != 0) {
        return raise(NotSupportedException, str("Array.zeroCreate of a type without a null value: use Array.create or Array.init"));
    }
}

/// `Array.Resize(&a, n)`: a new array of the first items, then defaults (a null array is
/// one of no items)
pub fn arrayResize(place: anytype, n: i32) Raised!void {
    const A = @TypeOf(place.*);
    if (n < 0) return raise(rt.ArgumentOutOfRangeException, str("Non-negative number required. (Parameter 'newSize')"));
    const old = place.*;
    const kept = @min(old.items.len, @as(usize, @intCast(n)));
    const items = try arrayItemsOrRaise(A, @intCast(n));
    for (items[0..kept], 0..) |*x, i| x.* = arrayItemAt(old, i);
    fillDefault(A, items[kept..]) catch |e| {
        for (items[0..kept]) |x| rt.drop(x);
        rt.alloc().free(items);
        return e;
    };
    place.* = arrayFrom(A, items);
    rt.drop(old);
}

/// `Array.create n x`
pub fn arrayCreate(comptime A: type, n: i32, x: ItemOf(A)) Raised!A {
    if (n < 0) return countNegative(n);
    const items = try arrayItemsOrRaise(A, @intCast(n));
    for (items) |*item| item.* = dup(x);
    return arrayFrom(A, items);
}

/// Give up the first `n` of the items that were being made for an array.
pub fn arrayAbandon(items: anytype, n: usize) void {
    for (items[0..n]) |item| drop(item);
    rt.alloc().free(items);
}

/// `Array.init n f`
pub fn arrayInit(comptime A: type, n: i32, f: anytype) Raised!A {
    if (n < 0) return countNegative(n);
    const items = try arrayItemsOrRaise(A, @intCast(n));
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

pub fn indexOutside() Raised {
    return raise(IndexOutOfRangeException, str("Index was outside the bounds of the array."));
}

/// (an index of an array that is outside it, or of the array's null: NullReferenceException)
pub fn indexOutsideOf(a: anytype) Raised {
    if (arrayIsNull(a)) return rt.nullRef();
    return indexOutside();
}

/// `a.[i]`: a reference of its own to the item.
pub inline fn arrayGet(a: anytype, i: i32) Raised!ItemOf(@TypeOf(a)) {
    if (i < 0 or i >= a.items.len) return indexOutsideOf(a);
    return arrayItemAt(a, @intCast(i));
}

/// `a.[i]` where `i` is known to be inside, with its own reference: where the array is shared
/// between threads, under its lock, as a store swaps an item in (Koka's protocol, see `loadIn`)
pub inline fn arrayItemAt(a: anytype, i: usize) ItemOf(@TypeOf(a)) {
    if (comptime !rt.isManaged(ItemOf(@TypeOf(a)))) return a.items[i];
    if (!rt.isShared(a)) return dup(a.items[i]);
    const l = rt.fieldLock(a);
    rt.lockField(l);
    const v = dup(a.items[i]);
    rt.unlockField(l);
    return v;
}

/// `a.[i] <- value`. The collector is told what the array no longer points at and what it
/// points at now: this is where a cycle can be closed.
pub inline fn arraySet(a: anytype, i: i32, value: ItemOf(@TypeOf(a))) Raised!void {
    if (i < 0 or i >= a.items.len) return indexOutsideOf(a);
    arrayPut(a, @intCast(i), dup(value));
}

/// `a.[i] <- value` where `i` is known to be inside bounds.
pub inline fn arraySetAt(a: anytype, i: usize, value: ItemOf(@TypeOf(a))) void {
    arrayPut(a, i, dup(value));
}

pub inline fn arrayPut(a: anytype, i: usize, value: @typeInfo(@TypeOf(a.items)).pointer.child) void {
    if (comptime !rt.isManaged(@TypeOf(value))) {
        a.items[i] = value;
        return;
    }
    if (rt.isShared(a)) {
        // (shared before another thread can read it, swapped in under the array's lock, the
        // old item given up after)
        rt.shareStored(value);
        const l = rt.fieldLock(a);
        rt.lockField(l);
        const prev = a.items[i];
        a.items[i] = value;
        rt.unlockField(l);
        drop(prev);
        return;
    }
    const old = a.items[i];
    a.items[i] = value;
    if (gcOf(a)) |h| {
        eachHdr(old, h, unstored);
        storeValue(h, value);
    } else {
        touch(value);
    }
    drop(old);
}

/// A new array of the items of `a` from `from` that are `n`: they are known to be inside.
pub fn arrayPart(a: anytype, from: usize, n: usize) @TypeOf(a) {
    const A = @TypeOf(a);
    const items = arrayItems(A, n);
    for (items, 0..) |*to, k| to.* = arrayItemAt(a, from + k);
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
    for (0..a.items.len) |i| items[i] = arrayItemAt(a, i);
    for (0..b.items.len) |i| items[a.items.len + i] = arrayItemAt(b, i);
    return arrayFrom(A, items);
}

/// `Array.rev a`
pub fn arrayRev(a: anytype) @TypeOf(a) {
    const A = @TypeOf(a);
    const n = a.items.len;
    const items = arrayItems(A, n);
    for (items, 0..) |*to, i| to.* = arrayItemAt(a, n - 1 - i);
    return arrayFrom(A, items);
}

/// `Array.fill a start count x`
pub fn arrayFill(a: anytype, start: i32, count: i32, x: ItemOf(@TypeOf(a))) Raised!void {
    if (start < 0) return raise(ArgumentException, format(.{ "The input must be non-negative.\nstartIndex = ", start, " (Parameter 'startIndex')" }));
    if (count < 0) return countNegative(count);
    var i = start;
    while (i < start + count) : (i += 1) {
        if (i >= a.items.len) return indexOutsideOf(a);
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
pub fn listOf(comptime T: type, items: []const T) List(T) {
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
    const T = ItemOf(@TypeOf(a));
    if (comptime !rt.isManaged(T)) return listOf(T, a.items);
    if (!rt.isShared(a)) return listOf(T, a.items);
    var all: List(T) = .Empty;
    var i = a.items.len;
    while (i > 0) {
        i -= 1;
        const tail = all;
        all = .{ .Cons = cell(List(T), .Cons, .{ .Head = arrayItemAt(a, i), .Tail = tail }) };
    }
    return all;
}

/// `Array.contains x a`
pub fn arrayContains(x: anytype, a: Array(@TypeOf(x))) bool {
    if (comptime rt.isManaged(@TypeOf(x))) {
        if (rt.isShared(a)) {
            for (0..a.items.len) |i| {
                const item = arrayItemAt(a, i);
                defer rt.drop(item);
                if (eql(item, x)) return true;
            }
            return false;
        }
    }
    for (a.items) |item| {
        if (eql(item, x)) return true;
    }
    return false;
}

/// `Array.map f a`
pub fn arrayMap(comptime A: type, f: anytype, a: anytype) Raised!A {
    const items = arrayItems(A, a.items.len);
    for (items, 0..) |*to, i| {
        to.* = f.code(f.env, arrayItemAt(a, i)) catch |e| {
            arrayAbandon(items, i);
            return e;
        };
    }
    return arrayFrom(A, items);
}

/// Whether two array types have identical element size, element alignment, cyclic status,
/// and cell header layout so an in-place map can reuse the source array cell and slice.
pub fn canReuseArrayMap(comptime A_in: type, comptime A_out: type) bool {
    const C_in = @typeInfo(A_in).pointer.child;
    const C_out = @typeInfo(A_out).pointer.child;
    const T_in = ItemOf(A_in);
    const T_out = ItemOf(A_out);
    return @sizeOf(T_in) == @sizeOf(T_out) and
        @alignOf(T_in) == @alignOf(T_out) and
        holdsCyclic(T_in) == holdsCyclic(T_out) and
        @sizeOf(C_in) == @sizeOf(C_out) and
        @alignOf(C_in) == @alignOf(C_out);
}

/// Progressive fill buffer for specialized `Array.map` / `Array.mapi` loops:
/// reuses a uniquely owned, unshaped input array cell and buffer in place when layouts match,
/// falling back to fresh allocation and clean unwinding on error otherwise.
pub fn MapBuf(comptime A_in: type, comptime A_out: type) type {
    return struct {
        src: A_in,
        in_place: bool,
        items: []ItemOf(A_out),
        filled: usize = 0,
        next: usize = 0,
    };
}

pub inline fn arrayMapBufNew(a: anytype, comptime A_out: type) MapBuf(@TypeOf(a), A_out) {
    const A_in = @TypeOf(a);
    const C_in = @typeInfo(A_in).pointer.child;
    const T_out = ItemOf(A_out);
    if (comptime canReuseArrayMap(A_in, A_out)) {
        if (rt.isUnique(a) and a.shape == null) {
            if (comptime hasGc(C_in)) rt.forget(a);
            if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(a));
            const out_ptr: [*]T_out = @ptrCast(@alignCast(a.items.ptr));
            return .{ .src = a, .in_place = true, .items = out_ptr[0..a.items.len], .filled = 0, .next = 0 };
        }
    }
    return .{ .src = a, .in_place = false, .items = arrayItems(A_out, a.items.len), .filled = 0, .next = 0 };
}

pub inline fn arrayMapBufLen(b: anytype) i32 {
    return @intCast(b.items.len);
}

pub inline fn arrayMapBufTake(b: anytype, i: usize) ItemOf(@TypeOf(b.src)) {
    const MB = @typeInfo(@TypeOf(b)).pointer.child;
    const A_in = @FieldType(MB, "src");
    const T_out = @typeInfo(@FieldType(MB, "items")).pointer.child;
    const T_in = ItemOf(A_in);
    if (comptime canReuseArrayMap(A_in, Array(T_out))) {
        if (b.in_place) {
            b.next = i + 1;
            const x = b.src.items[i];
            if (comptime holdsCyclic(T_in)) rt.touch(x);
            return x;
        }
    }
    return arrayItemAt(b.src, i);
}

pub inline fn arrayMapBufPush(x: anytype, b: anytype) void {
    b.items[b.filled] = x;
    b.filled += 1;
}

pub fn arrayMapBufFinish(comptime A_out: type, b: anytype) A_out {
    const MB = @typeInfo(@TypeOf(b)).pointer.child;
    const A_in = @FieldType(MB, "src");
    const C_out = @typeInfo(A_out).pointer.child;
    if (comptime canReuseArrayMap(A_in, A_out)) {
        if (b.in_place) {
            const out: A_out = @ptrCast(@alignCast(b.src));
            const cap = b.src.capacity;
            out.* = .{ .items = b.items, .capacity = cap };
            if (comptime hasGc(C_out)) {
                if (!thread.collector_ready) rt.collectorSetup();
                thread.collector.allocs += 1;
                out.@"$gc" = gcHeader(C_out, out);
            }
            if (track) thread.stats.reuses += 1;
            return out;
        }
    }
    drop(b.src);
    return arrayFrom(A_out, b.items);
}

pub fn arrayMapBufAbandon(b: anytype) void {
    const MB = @typeInfo(@TypeOf(b)).pointer.child;
    const A_in = @FieldType(MB, "src");
    const T_out = @typeInfo(@FieldType(MB, "items")).pointer.child;
    if (comptime canReuseArrayMap(A_in, Array(T_out))) {
        if (b.in_place) {
            for (b.items[0..b.filled]) |x| drop(x);
            for (b.src.items[b.next..b.src.items.len]) |x| drop(x);
            if (b.src.capacity != 0) rt.alloc().free(b.src.items.ptr[0..b.src.capacity]);
            b.src.capacity = 0;
            b.src.items = &.{};
            rt.free(b.src);
            return;
        }
    }
    arrayAbandon(b.items, b.filled);
    drop(b.src);
}

/// Owned-input `Array.map`: reuses a uniquely owned, unshaped input array in place when layouts match.
pub fn arrayMapInPlace(comptime A_out: type, a: anytype, f: anytype) Raised!A_out {
    const A_in = @TypeOf(a);
    const C_in = @typeInfo(A_in).pointer.child;
    const C_out = @typeInfo(A_out).pointer.child;
    const T_in = ItemOf(A_in);
    const T_out = ItemOf(A_out);
    if (comptime canReuseArrayMap(A_in, A_out)) {
        if (rt.isUnique(a) and a.shape == null) {
            if (comptime hasGc(C_in)) rt.forget(a);
            if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(a));
            const n = a.items.len;
            const out_ptr: [*]T_out = @ptrCast(@alignCast(a.items.ptr));
            const out_items = out_ptr[0..n];
            for (0..n) |i| {
                const x = a.items[i];
                if (comptime holdsCyclic(T_in)) rt.touch(x);
                out_items[i] = f.code(f.env, x) catch |e| {
                    for (out_items[0..i]) |oy| drop(oy);
                    for (a.items[i + 1 .. n]) |rem| drop(rem);
                    if (a.capacity != 0) rt.alloc().free(a.items.ptr[0..a.capacity]);
                    a.capacity = 0;
                    a.items = &.{};
                    rt.free(a);
                    return e;
                };
            }
            const out: A_out = @ptrCast(@alignCast(a));
            const cap = a.capacity;
            out.* = .{ .items = out_items, .capacity = cap };
            if (comptime hasGc(C_out)) {
                if (!thread.collector_ready) rt.collectorSetup();
                thread.collector.allocs += 1;
                out.@"$gc" = gcHeader(C_out, out);
            }
            if (track) thread.stats.reuses += 1;
            return out;
        }
    }
    defer drop(a);
    return arrayMap(A_out, f, a);
}

/// Owned-input `Array.mapi`: reuses a uniquely owned, unshaped input array in place when layouts match.
pub fn arrayMapiInPlace(comptime A_out: type, a: anytype, f: anytype) Raised!A_out {
    const A_in = @TypeOf(a);
    const C_in = @typeInfo(A_in).pointer.child;
    const C_out = @typeInfo(A_out).pointer.child;
    const T_in = ItemOf(A_in);
    const T_out = ItemOf(A_out);
    if (comptime canReuseArrayMap(A_in, A_out)) {
        if (rt.isUnique(a) and a.shape == null) {
            if (comptime hasGc(C_in)) rt.forget(a);
            if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(a));
            const n = a.items.len;
            const out_ptr: [*]T_out = @ptrCast(@alignCast(a.items.ptr));
            const out_items = out_ptr[0..n];
            for (0..n) |i| {
                const x = a.items[i];
                if (comptime holdsCyclic(T_in)) rt.touch(x);
                out_items[i] = apply2(T_out, f, @as(i32, @intCast(i)), x) catch |e| {
                    for (out_items[0..i]) |oy| drop(oy);
                    for (a.items[i + 1 .. n]) |rem| drop(rem);
                    if (a.capacity != 0) rt.alloc().free(a.items.ptr[0..a.capacity]);
                    a.capacity = 0;
                    a.items = &.{};
                    rt.free(a);
                    return e;
                };
            }
            const out: A_out = @ptrCast(@alignCast(a));
            const cap = a.capacity;
            out.* = .{ .items = out_items, .capacity = cap };
            if (comptime hasGc(C_out)) {
                if (!thread.collector_ready) rt.collectorSetup();
                thread.collector.allocs += 1;
                out.@"$gc" = gcHeader(C_out, out);
            }
            if (track) thread.stats.reuses += 1;
            return out;
        }
    }
    defer drop(a);
    return arrayMapi(A_out, f, a);
}

/// Filter buffer for specialized `Array.filter` / `Array.where` loops:
/// compacts a uniquely owned, unshaped array in place using `capacity` to free safely,
/// falling back to a `keep` bitmap otherwise.
pub fn FilterReuseBuf(comptime A: type) type {
    return struct {
        src: A,
        in_place: bool,
        keep: []bool,
        out_len: usize = 0,
        next: usize = 0,
    };
}

pub inline fn arrayFilterBufNew(a: anytype) FilterReuseBuf(@TypeOf(a)) {
    const A = @TypeOf(a);
    const C = @typeInfo(A).pointer.child;
    if (rt.isUnique(a) and a.shape == null) {
        if (comptime hasGc(C)) rt.forget(a);
        if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(a));
        return .{ .src = a, .in_place = true, .keep = &.{}, .out_len = 0, .next = 0 };
    }
    return .{
        .src = a,
        .in_place = false,
        .keep = rt.alloc().alloc(bool, a.items.len) catch rt.oom(),
        .out_len = 0,
        .next = 0,
    };
}

pub inline fn arrayFilterBufLen(b: anytype) i32 {
    return @intCast(b.src.items.len);
}

pub inline fn arrayFilterBufItem(b: anytype, i: usize) ItemOf(@TypeOf(b.src)) {
    const T = ItemOf(@TypeOf(b.src));
    if (b.in_place) {
        const x = b.src.items[i];
        if (comptime holdsCyclic(T)) rt.touch(x);
        return dup(x);
    }
    return arrayItemAt(b.src, i);
}

pub inline fn arrayFilterBufStep(b: anytype, i: usize, keep: bool) void {
    if (b.in_place) {
        const item = b.src.items[i];
        b.next = i + 1;
        if (keep) {
            b.src.items[b.out_len] = item;
            b.out_len += 1;
        } else {
            drop(item);
        }
    } else {
        b.keep[i] = keep;
        b.out_len += @intFromBool(keep);
    }
}

pub fn arrayFilterBufFinish(b: anytype) @TypeOf(b.src) {
    const A = @TypeOf(b.src);
    const C = @typeInfo(A).pointer.child;
    if (b.in_place) {
        const a = b.src;
        const cap = a.capacity;
        a.* = .{ .items = a.items.ptr[0..b.out_len], .capacity = cap };
        if (comptime hasGc(C)) {
            if (!thread.collector_ready) rt.collectorSetup();
            thread.collector.allocs += 1;
            a.@"$gc" = gcHeader(C, a);
        }
        if (track) thread.stats.reuses += 1;
        return a;
    }
    defer rt.alloc().free(b.keep);
    defer drop(b.src);
    const items = arrayItems(A, b.out_len);
    var at: usize = 0;
    for (b.keep, 0..) |k, i| {
        if (k and i < b.src.items.len and at < b.out_len) {
            items[at] = arrayItemAt(b.src, i);
            at += 1;
        }
    }
    return arrayFrom(A, items);
}

pub fn arrayFilterBufAbandon(b: anytype) void {
    if (b.in_place) {
        for (b.src.items[0..b.out_len]) |x| drop(x);
        for (b.src.items[b.next..b.src.items.len]) |x| drop(x);
        if (b.src.capacity != 0) rt.alloc().free(b.src.items.ptr[0..b.src.capacity]);
        b.src.capacity = 0;
        b.src.items = &.{};
        rt.free(b.src);
        return;
    }
    rt.alloc().free(b.keep);
    drop(b.src);
}

/// Owned-input `Array.filter`: compacts a uniquely owned, unshaped array in place.
pub fn arrayFilterInPlace(a: anytype, f: anytype) Raised!@TypeOf(a) {
    const A = @TypeOf(a);
    const C = @typeInfo(A).pointer.child;
    if (rt.isUnique(a) and a.shape == null) {
        if (comptime hasGc(C)) rt.forget(a);
        if (thread.stamps.count() != 0) _ = thread.stamps.remove(@intFromPtr(a));
        const n = a.items.len;
        var out_len: usize = 0;
        for (0..n) |i| {
            const cur = a.items[i];
            if (comptime holdsCyclic(ItemOf(A))) rt.touch(cur);
            const k = f.code(f.env, dup(cur)) catch |e| {
                for (a.items[0..out_len]) |x| drop(x);
                for (a.items[i..n]) |x| drop(x);
                if (a.capacity != 0) rt.alloc().free(a.items.ptr[0..a.capacity]);
                a.capacity = 0;
                a.items = &.{};
                rt.free(a);
                return e;
            };
            if (k) {
                a.items[out_len] = cur;
                out_len += 1;
            } else {
                drop(cur);
            }
        }
        const cap = a.capacity;
        a.* = .{ .items = a.items.ptr[0..out_len], .capacity = cap };
        if (comptime hasGc(C)) {
            if (!thread.collector_ready) rt.collectorSetup();
            thread.collector.allocs += 1;
            a.@"$gc" = gcHeader(C, a);
        }
        if (track) thread.stats.reuses += 1;
        return a;
    }
    defer drop(a);
    return arrayFilter(f, a);
}

/// Progressive fill buffer used by specialized `Array.init` / `map` / `mapi` loops.
pub fn ArrayBuf(comptime A: type) type {
    return struct {
        items: []ItemOf(A),
        filled: usize = 0,
    };
}

pub inline fn arrayBufNew(comptime A: type, n: usize) ArrayBuf(A) {
    return .{ .items = arrayItems(A, n), .filled = 0 };
}

pub inline fn arrayBufPush(x: anytype, b: anytype) void {
    b.items[b.filled] = x;
    b.filled += 1;
}

pub inline fn arrayBufFinish(comptime A: type, b: ArrayBuf(A)) A {
    return arrayFrom(A, b.items);
}

pub inline fn arrayBufAbandon(b: anytype) void {
    arrayAbandon(b.items, b.filled);
}

/// Bitmask buffer used by specialized `Array.filter` / `where` loops.
pub const FilterBuf = struct {
    keep: []bool,
    count: usize = 0,
};

pub inline fn arrayFilterNew(n: usize) FilterBuf {
    return .{
        .keep = rt.alloc().alloc(bool, n) catch rt.oom(),
        .count = 0,
    };
}

pub inline fn arrayFilterSet(b: *FilterBuf, i: usize, keep: bool) void {
    b.keep[i] = keep;
    b.count += @intFromBool(keep);
}

pub fn arrayFilterFinish(a: anytype, b: FilterBuf) @TypeOf(a) {
    defer rt.alloc().free(b.keep);
    const A = @TypeOf(a);
    const items = arrayItems(A, b.count);
    var at: usize = 0;
    for (b.keep, 0..) |k, i| {
        if (k and i < a.items.len and at < b.count) {
            items[at] = arrayItemAt(a, i);
            at += 1;
        }
    }
    return arrayFrom(A, items);
}

pub inline fn arrayFilterAbandon(b: *FilterBuf) void {
    rt.alloc().free(b.keep);
}

// ---- `Array.Parallel`: on threads (fable_rt.parallelFor); the function and the array are
// shared first, and so is each item made ----

fn parallelItems(comptime A: type, n: usize, f: anytype, a: anytype, comptime make: fn (@TypeOf(f), @TypeOf(a), usize) Raised!ItemOf(A)) Raised!A {
    try rt.markShared(f);
    try rt.markShared(a);
    const items = arrayItems(A, n);
    const T = ItemOf(A);
    // (an item not made yet is all zero: what an exception leaves is given up as far as made)
    const done = rt.alloc().alloc(bool, n) catch rt.oom();
    defer rt.alloc().free(done);
    @memset(done, false);
    const Ctx = struct { f: @TypeOf(f), a: @TypeOf(a), items: []T, done: []bool };
    const S = struct {
        fn step(c: Ctx, i: usize) Raised!void {
            const x = try make(c.f, c.a, i);
            try rt.markShared(x);
            c.items[i] = x;
            c.done[i] = true;
        }
    };
    rt.parallelFor(n, Ctx{ .f = f, .a = a, .items = items, .done = done }, S.step) catch |e| {
        for (items, done) |x, d| if (d) rt.drop(x);
        rt.alloc().free(items);
        return e;
    };
    return arrayFrom(A, items);
}

/// `Array.Parallel.map f a`
pub fn arrayParallelMap(comptime A: type, f: anytype, a: anytype) Raised!A {
    const S = struct {
        fn make(g: @TypeOf(f), xs: @TypeOf(a), i: usize) Raised!ItemOf(A) {
            return g.code(g.env, arrayItemAt(xs, i));
        }
    };
    return parallelItems(A, a.items.len, f, a, S.make);
}

/// `Array.Parallel.mapi f a`
pub fn arrayParallelMapi(comptime A: type, f: anytype, a: anytype) Raised!A {
    const S = struct {
        fn make(g: @TypeOf(f), xs: @TypeOf(a), i: usize) Raised!ItemOf(A) {
            return apply2(ItemOf(A), g, @as(i32, @intCast(i)), arrayItemAt(xs, i));
        }
    };
    return parallelItems(A, a.items.len, f, a, S.make);
}

/// `Array.Parallel.init n f`
pub fn arrayParallelInit(comptime A: type, n: i32, f: anytype) Raised!A {
    if (n < 0) return countNegative(n);
    const S = struct {
        fn make(g: @TypeOf(f), _: void, i: usize) Raised!ItemOf(A) {
            return g.code(g.env, @as(i32, @intCast(i)));
        }
    };
    return parallelItems(A, @intCast(n), f, {}, S.make);
}

/// `Array.Parallel.iter f a`
pub fn arrayParallelIter(f: anytype, a: anytype) Raised!void {
    try rt.markShared(f);
    try rt.markShared(a);
    const Ctx = struct { f: @TypeOf(f), a: @TypeOf(a) };
    const S = struct {
        fn step(c: Ctx, i: usize) Raised!void {
            return c.f.code(c.f.env, arrayItemAt(c.a, i));
        }
    };
    return rt.parallelFor(c_len(a), Ctx{ .f = f, .a = a }, S.step);
}

inline fn c_len(a: anytype) usize {
    return a.items.len;
}

/// `Array.mapi f a`
pub fn arrayMapi(comptime A: type, f: anytype, a: anytype) Raised!A {
    const items = arrayItems(A, a.items.len);
    for (items, 0..) |*to, i| {
        to.* = apply2(ItemOf(A), f, @as(i32, @intCast(i)), arrayItemAt(a, i)) catch |e| {
            arrayAbandon(items, i);
            return e;
        };
    }
    return arrayFrom(A, items);
}

/// `Array.iter f a`
pub fn arrayIter(f: anytype, a: anytype) Raised!void {
    for (0..a.items.len) |i| try f.code(f.env, arrayItemAt(a, i));
}

/// `Array.iteri f a`
pub fn arrayIteri(f: anytype, a: anytype) Raised!void {
    for (0..a.items.len) |i| try apply2(void, f, @as(i32, @intCast(i)), arrayItemAt(a, i));
}

/// `Array.fold f state a`: `state` is the caller's, the result is a reference of its own.
pub fn arrayFold(f: anytype, state: anytype, a: anytype) Raised!@TypeOf(state) {
    var acc = dup(state);
    for (0..a.items.len) |i| acc = try apply2(@TypeOf(state), f, acc, arrayItemAt(a, i));
    return acc;
}

/// `Array.filter f a`
pub fn arrayFilter(f: anytype, a: anytype) Raised!@TypeOf(a) {
    const A = @TypeOf(a);
    const keep = rt.alloc().alloc(bool, a.items.len) catch rt.oom();
    defer rt.alloc().free(keep);
    var n: usize = 0;
    for (keep, 0..) |*k, i| {
        k.* = try f.code(f.env, arrayItemAt(a, i));
        n += @intFromBool(k.*);
    }
    const items = arrayItems(A, n);
    var at: usize = 0;
    for (keep, 0..) |k, i| {
        if (k and i < a.items.len and at < n) {
            items[at] = arrayItemAt(a, i);
            at += 1;
        }
    }
    return arrayFrom(A, items);
}

/// `Array.exists f a`
pub fn arrayExists(f: anytype, a: anytype) Raised!bool {
    for (0..a.items.len) |i| {
        if (try f.code(f.env, arrayItemAt(a, i))) return true;
    }
    return false;
}

/// `Array.forall f a`
pub fn arrayForall(f: anytype, a: anytype) Raised!bool {
    for (0..a.items.len) |i| {
        if (!try f.code(f.env, arrayItemAt(a, i))) return false;
    }
    return true;
}

fn restoreMergeSlice(comptime T: type, items: []T, src: []const T, dst: []T, i: usize, mid: usize, j: usize, hi: usize, k: usize) void {
    const left_rem = mid - i;
    @memcpy(dst[k .. k + left_rem], src[i..mid]);
    @memcpy(dst[k + left_rem .. hi], src[j..hi]);
    if (dst.ptr == items.ptr) {
        @memcpy(items[hi..], src[hi..]);
    } else {
        @memcpy(items[0..hi], dst[0..hi]);
    }
}

fn sortSliceCore(
    comptime T: type,
    items: []T,
    ctx: anytype,
    comptime leq: fn (@TypeOf(ctx), T, T) Raised!bool,
) Raised!void {
    if (items.len <= 1) return;
    const n = items.len;
    const tmp = rt.alloc().alloc(T, n) catch rt.oom();
    defer rt.alloc().free(tmp);
    var src: []T = items;
    var dst: []T = tmp;
    var width: usize = 1;
    while (width < n) {
        const step = width *| 2;
        var lo: usize = 0;
        while (lo < n) : (lo +|= step) {
            const mid = @min(lo +| width, n);
            const hi = @min(lo +| step, n);
            if (mid == hi) {
                @memcpy(dst[lo..hi], src[lo..hi]);
                continue;
            }
            var i = lo;
            var j = mid;
            var k = lo;
            while (i < mid and j < hi) : (k += 1) {
                const take_left = leq(ctx, src[i], src[j]) catch |e| {
                    restoreMergeSlice(T, items, src, dst, i, mid, j, hi, k);
                    return e;
                };
                if (take_left) {
                    dst[k] = src[i];
                    i += 1;
                } else {
                    dst[k] = src[j];
                    j += 1;
                }
            }
            const rem = mid - i;
            @memcpy(dst[k .. k + rem], src[i..mid]);
            @memcpy(dst[k + rem .. hi], src[j..hi]);
        }
        const prev = src;
        src = dst;
        dst = prev;
        width = step;
    }
    if (src.ptr != items.ptr) @memcpy(items, src);
}

pub fn sortSliceCmp(comptime T: type, items: []T, comptime desc: bool) void {
    const S = struct {
        fn leq(_: void, a: T, b: T) Raised!bool {
            return if (desc) rt.compare(b, a) <= 0 else rt.compare(a, b) <= 0;
        }
    };
    sortSliceCore(T, items, {}, S.leq) catch unreachable;
}

pub fn sortSliceWith(comptime T: type, items: []T, f: anytype) Raised!void {
    const S = struct {
        fn leq(g: @TypeOf(f), a: T, b: T) Raised!bool {
            return (try apply2(i32, g, dup(a), dup(b))) <= 0;
        }
    };
    return sortSliceCore(T, items, f, S.leq);
}

/// `Array.sort a`
pub fn arraySort(a: anytype) @TypeOf(a) {
    const out = arrayCopy(a);
    sortSliceCmp(ItemOf(@TypeOf(a)), out.items, false);
    return out;
}

/// `Array.sortDescending a`
pub fn arraySortDesc(a: anytype) @TypeOf(a) {
    const out = arrayCopy(a);
    sortSliceCmp(ItemOf(@TypeOf(a)), out.items, true);
    return out;
}

/// `Array.sortWith f a`
pub fn arraySortWith(f: anytype, a: anytype) Raised!@TypeOf(a) {
    const out = arrayCopy(a);
    errdefer drop(out);
    try sortSliceWith(ItemOf(@TypeOf(a)), out.items, f);
    return out;
}

/// `Array.sortInPlace a`
pub fn arraySortInPlace(a: anytype) void {
    if (a.items.len <= 1) return;
    const T = ItemOf(@TypeOf(a));
    if (!rt.isShared(a)) {
        sortSliceCmp(T, a.items, false);
        return;
    }
    const n = a.items.len;
    const work = rt.alloc().alloc(T, n) catch rt.oom();
    for (work, 0..) |*to, i| to.* = arrayItemAt(a, i);
    sortSliceCmp(T, work, false);
    for (work, 0..) |x, i| arrayPut(a, i, x);
    rt.alloc().free(work);
}

/// `Array.sortInPlaceWith f a`
pub fn arraySortInPlaceWith(f: anytype, a: anytype) Raised!void {
    if (a.items.len <= 1) return;
    const T = ItemOf(@TypeOf(a));
    if (!rt.isShared(a)) {
        return sortSliceWith(T, a.items, f);
    }
    const n = a.items.len;
    const work = rt.alloc().alloc(T, n) catch rt.oom();
    for (work, 0..) |*to, i| to.* = arrayItemAt(a, i);
    sortSliceWith(T, work, f) catch |e| {
        arrayAbandon(work, n);
        return e;
    };
    for (work, 0..) |x, i| arrayPut(a, i, x);
    rt.alloc().free(work);
}

fn sortSliceByKeys(comptime T: type, comptime K: type, items: []T, keys: []K, comptime desc: bool) void {
    const n = items.len;
    std.debug.assert(keys.len == n);
    if (n <= 1) return;
    const tmp_v = rt.alloc().alloc(T, n) catch rt.oom();
    defer rt.alloc().free(tmp_v);
    const tmp_k = rt.alloc().alloc(K, n) catch rt.oom();
    defer rt.alloc().free(tmp_k);
    var src_v: []T = items;
    var dst_v: []T = tmp_v;
    var src_k: []K = keys;
    var dst_k: []K = tmp_k;
    var width: usize = 1;
    while (width < n) {
        const step = width *| 2;
        var lo: usize = 0;
        while (lo < n) : (lo +|= step) {
            const mid = @min(lo +| width, n);
            const hi = @min(lo +| step, n);
            if (mid == hi) {
                @memcpy(dst_v[lo..hi], src_v[lo..hi]);
                @memcpy(dst_k[lo..hi], src_k[lo..hi]);
                continue;
            }
            var i = lo;
            var j = mid;
            var k = lo;
            while (i < mid and j < hi) : (k += 1) {
                const take_left = if (desc) rt.compare(src_k[j], src_k[i]) <= 0 else rt.compare(src_k[i], src_k[j]) <= 0;
                if (take_left) {
                    dst_v[k] = src_v[i];
                    dst_k[k] = src_k[i];
                    i += 1;
                } else {
                    dst_v[k] = src_v[j];
                    dst_k[k] = src_k[j];
                    j += 1;
                }
            }
            const rem = mid - i;
            @memcpy(dst_v[k .. k + rem], src_v[i..mid]);
            @memcpy(dst_v[k + rem .. hi], src_v[j..hi]);
            @memcpy(dst_k[k .. k + rem], src_k[i..mid]);
            @memcpy(dst_k[k + rem .. hi], src_k[j..hi]);
        }
        const prev_v = src_v;
        src_v = dst_v;
        dst_v = prev_v;
        const prev_k = src_k;
        src_k = dst_k;
        dst_k = prev_k;
        width = step;
    }
    if (src_v.ptr != items.ptr) {
        @memcpy(items, src_v);
        @memcpy(keys, src_k);
    }
}

/// `Array.sortBy` / `Array.sortByDescending` over precomputed `keys`: stable, zero RC moves.
pub fn arraySortByKeys(keys: anytype, a: anytype, comptime desc: bool) @TypeOf(a) {
    const out = arrayCopy(a);
    sortSliceByKeys(ItemOf(@TypeOf(a)), ItemOf(@TypeOf(keys)), out.items, keys.items, desc);
    return out;
}

/// `Array.sortInPlaceBy` over precomputed `keys`: stable, zero RC moves.
pub fn arraySortInPlaceByKeys(keys: anytype, a: anytype, comptime desc: bool) void {
    if (a.items.len <= 1) return;
    const T = ItemOf(@TypeOf(a));
    const K = ItemOf(@TypeOf(keys));
    if (!rt.isShared(a)) {
        sortSliceByKeys(T, K, a.items, keys.items, desc);
        return;
    }
    const n = a.items.len;
    const work = rt.alloc().alloc(T, n) catch rt.oom();
    for (work, 0..) |*to, i| to.* = arrayItemAt(a, i);
    sortSliceByKeys(T, K, work, keys.items, desc);
    for (work, 0..) |x, i| arrayPut(a, i, x);
    rt.alloc().free(work);
}

test "array merge sort: zero RC moves, stable, exception-safe" {
    const A = Array(String);
    const b0 = rt.strConcat(str("beta-"), str("0"));
    const a0 = rt.strConcat(str("alp"), str("ha"));
    const b1 = rt.strConcat(str("beta-"), str("1"));
    const c0 = rt.strConcat(str("char"), str("lie"));
    const arr = arrayFrom(A, blk: {
        const items = arrayItems(A, 4);
        items[0] = b0;
        items[1] = a0;
        items[2] = b1;
        items[3] = c0;
        break :blk items;
    });
    defer drop(arr);

    // Compare by first UTF-16 unit only so beta-0 and beta-1 compare equal (stability check).
    const S = struct {
        const CmpCtx = struct { fail_after: i32, calls: i32 = 0 };
        fn firstChar(_: ?*rt.Env, x: String, y: String) Raised!i32 {
            defer drop(x);
            defer drop(y);
            const ux = rt.unitsOf(x);
            const uy = rt.unitsOf(y);
            if (ux[0] < uy[0]) return -1;
            if (ux[0] > uy[0]) return 1;
            return 0;
        }
        fn failing(env: ?*rt.Env, x: String, y: String) Raised!i32 {
            defer drop(x);
            defer drop(y);
            const c: *CmpCtx = @ptrCast(@alignCast(env.?));
            c.calls += 1;
            if (c.calls >= c.fail_after) return error.Raised;
            return if (rt.strCompare(x, y) < 0) -1 else if (rt.strCompare(x, y) > 0) 1 else 0;
        }
    };

    const F = rt.Func(*const fn (?*rt.Env, String, String) Raised!i32);
    const before = thread.stats;
    const sorted = arraySortWith(F{ .env = null, .code = &S.firstChar }, arr) catch unreachable;
    try std.testing.expect(eql(sorted.items[0], str("alpha")));
    try std.testing.expect(eql(sorted.items[1], str("beta-0")));
    try std.testing.expect(eql(sorted.items[2], str("beta-1")));
    try std.testing.expect(eql(sorted.items[3], str("charlie")));
    // Only the initial copy and comparator calls dup/drop; the merge itself never retains or drops items.
    drop(sorted);
    try std.testing.expectEqual(thread.stats.allocs - before.allocs, thread.stats.frees - before.frees);

    var ctx = S.CmpCtx{ .fail_after = 2 };
    const before_err = thread.stats;
    const err_res = arraySortWith(F{ .env = @ptrCast(@alignCast(&ctx)), .code = &S.failing }, arr);
    try std.testing.expectError(error.Raised, err_res);
    try std.testing.expectEqual(thread.stats.allocs - before_err.allocs, thread.stats.frees - before_err.frees);

    ctx = .{ .fail_after = 3 };
    const before_in_place_err = thread.stats;
    try std.testing.expectError(error.Raised, arraySortInPlaceWith(F{ .env = @ptrCast(@alignCast(&ctx)), .code = &S.failing }, arr));
    try std.testing.expectEqual(thread.stats.allocs - before_in_place_err.allocs, thread.stats.frees - before_in_place_err.frees);

    // Zero RC traffic for in-place default sort.
    const copy = arrayCopy(arr);
    defer drop(copy);
    const before_sort = thread.stats;
    arraySortInPlace(copy);
    try std.testing.expectEqual(@as(i64, 0), thread.stats.dups - before_sort.dups);
    try std.testing.expectEqual(@as(i64, 0), thread.stats.frees - before_sort.frees);
    try std.testing.expectEqual(@as(i64, 0), thread.stats.allocs - before_sort.allocs);
    try std.testing.expect(eql(copy.items[0], str("alpha")));
    try std.testing.expect(eql(copy.items[1], str("beta-0")));
    try std.testing.expect(eql(copy.items[2], str("beta-1")));
    try std.testing.expect(eql(copy.items[3], str("charlie")));
}
