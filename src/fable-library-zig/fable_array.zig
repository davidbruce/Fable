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
const stored = rt.stored;
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
        /// a two-dimensional array: its rows and columns, the items row after row
        shape: ?[2]usize = null,
    };
}

/// The type of the items of the array type `A`.
pub fn ItemOf(comptime A: type) type {
    return @typeInfo(A).pointer.child.fable_array;
}

pub fn arrayItems(comptime A: type, n: usize) []ItemOf(A) {
    return rt.allocator.alloc(ItemOf(A), n) catch @panic("fable: out of memory");
}

/// A new array that owns `items`.
pub fn arrayFrom(comptime A: type, items: []ItemOf(A)) A {
    const C = @typeInfo(A).pointer.child;
    if (comptime hasGc(C)) gcTick();
    const c = rt.allocator.create(C) catch @panic("fable: out of memory");
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
pub fn hasZero(comptime T: type) bool {
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
        rt.allocator.free(items);
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
pub fn arrayAbandon(items: anytype, n: usize) void {
    for (items[0..n]) |item| drop(item);
    rt.allocator.free(items);
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

pub fn indexOutside() Raised {
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

pub fn arrayPut(a: anytype, i: usize, value: @typeInfo(@TypeOf(a.items)).pointer.child) void {
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
pub fn arrayPart(a: anytype, from: usize, n: usize) @TypeOf(a) {
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
    const keep = rt.allocator.alloc(bool, a.items.len) catch @panic("fable: out of memory");
    defer rt.allocator.free(keep);
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
