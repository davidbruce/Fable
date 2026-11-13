//! Two-dimensional arrays: an array whose `shape` says its rows and columns (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");
const ArgumentException = rt.ArgumentException;
const ArgumentOutOfRangeException = rt.ArgumentOutOfRangeException;
const ItemOf = rt.ItemOf;
const Raised = rt.Raised;
const apply2 = rt.apply2;
const apply3 = rt.apply3;
const arrayAbandon = rt.arrayAbandon;
const arrayCopy = rt.arrayCopy;
const arrayCreate = rt.arrayCreate;
const arrayFrom = rt.arrayFrom;
const arrayItems = rt.arrayItems;
const arrayIter = rt.arrayIter;
const arrayMap = rt.arrayMap;
const arrayPut = rt.arrayPut;
const arrayZero = rt.arrayZero;
const dup = rt.dup;
const format = rt.format;
const indexOutside = rt.indexOutside;
const raise = rt.raise;
const str = rt.str;

// ---------------------------------------------------------------------------------------------
// Two-dimensional arrays: an array whose `shape` says its rows and columns
// ---------------------------------------------------------------------------------------------

pub fn dimNegative(n: i32, comptime param: []const u8) Raised {
    return raise(ArgumentException, format(.{ "The input must be non-negative.\n" ++ param ++ " = ", n, " (Parameter '" ++ param ++ "')" }));
}

pub fn shaped(a: anytype, rows: usize, cols: usize) @TypeOf(a) {
    a.shape = .{ rows, cols };
    return a;
}

/// `Array2D.zeroCreate rows cols`
pub fn array2DZero(comptime A: type, rows: i32, cols: i32) Raised!A {
    if (rows < 0) return dimNegative(rows, "length1");
    if (cols < 0) return dimNegative(cols, "length2");
    return shaped(try arrayZero(A, rows * cols), @intCast(rows), @intCast(cols));
}

/// `Array2D.create rows cols x`
pub fn array2DCreate(comptime A: type, rows: i32, cols: i32, x: ItemOf(A)) Raised!A {
    if (rows < 0) return dimNegative(rows, "length1");
    if (cols < 0) return dimNegative(cols, "length2");
    return shaped(try arrayCreate(A, rows * cols, x), @intCast(rows), @intCast(cols));
}

/// `Array2D.init rows cols f`
pub fn array2DInit(comptime A: type, rows: i32, cols: i32, f: anytype) Raised!A {
    if (rows < 0) return dimNegative(rows, "length1");
    if (cols < 0) return dimNegative(cols, "length2");
    const r: usize = @intCast(rows);
    const c: usize = @intCast(cols);
    const items = arrayItems(A, r * c);
    for (0..r) |i| {
        for (0..c) |j| {
            items[i * c + j] = apply2(ItemOf(A), f, @as(i32, @intCast(i)), @as(i32, @intCast(j))) catch |e| {
                arrayAbandon(items, i * c + j);
                return e;
            };
        }
    }
    return shaped(arrayFrom(A, items), r, c);
}

pub fn shapeOf(a: anytype) [2]usize {
    return a.shape orelse .{ a.items.len, 1 };
}

pub fn at2D(a: anytype, i: i32, j: i32) Raised!usize {
    const shape = shapeOf(a);
    if (i < 0 or j < 0 or i >= shape[0] or j >= shape[1]) return indexOutside();
    return @as(usize, @intCast(i)) * shape[1] + @as(usize, @intCast(j));
}

/// `a.[i, j]`: a reference of its own to the item.
pub fn array2DGet(a: anytype, i: i32, j: i32) Raised!ItemOf(@TypeOf(a)) {
    return dup(a.items[try at2D(a, i, j)]);
}

/// `a.[i, j] <- value`
pub fn array2DSet(a: anytype, i: i32, j: i32, value: ItemOf(@TypeOf(a))) Raised!void {
    arrayPut(a, try at2D(a, i, j), dup(value));
}

/// `Array2D.length1 a`, `Array2D.length2 a`
pub fn array2DLength(a: anytype, comptime dim: usize) i32 {
    return @intCast(shapeOf(a)[dim]);
}

/// `a.GetLength d`
pub fn arrayGetLength(a: anytype, dim: i32) Raised!i32 {
    if (a.shape) |shape| {
        if (dim == 0 or dim == 1) return @intCast(shape[@intCast(dim)]);
    } else if (dim == 0) return @intCast(a.items.len);
    return indexOutside();
}

/// `Array2D.copy a`
pub fn array2DCopy(a: anytype) @TypeOf(a) {
    const c = arrayCopy(a);
    c.shape = a.shape;
    return c;
}

/// `Array2D.map f a`
pub fn array2DMap(comptime A: type, f: anytype, a: anytype) Raised!A {
    const m = try arrayMap(A, f, a);
    m.shape = a.shape;
    return m;
}

/// `Array2D.mapi f a`
pub fn array2DMapi(comptime A: type, f: anytype, a: anytype) Raised!A {
    const shape = shapeOf(a);
    const items = arrayItems(A, a.items.len);
    for (items, 0..) |*to, k| {
        to.* = apply3(ItemOf(A), f, @as(i32, @intCast(k / shape[1])), @as(i32, @intCast(k % shape[1])), dup(a.items[k])) catch |e| {
            arrayAbandon(items, k);
            return e;
        };
    }
    return shaped(arrayFrom(A, items), shape[0], shape[1]);
}

pub fn isListType(comptime T: type) bool {
    return @typeInfo(T) == .@"union" and @hasDecl(T, "fable_list");
}

pub fn rowCount(row: anytype) usize {
    const R = @TypeOf(row);
    if (comptime isListType(R)) {
        var n: usize = 0;
        var rest = row;
        while (rest == .Cons) : (rest = rest.Cons.Tail) n += 1;
        return n;
    }
    return row.items.len;
}

pub fn rowFill(row: anytype, to: anytype) void {
    const R = @TypeOf(row);
    if (comptime isListType(R)) {
        var rest = row;
        var i: usize = 0;
        while (rest == .Cons) : (rest = rest.Cons.Tail) {
            to[i] = dup(rest.Cons.Head);
            i += 1;
        }
    } else {
        for (row.items, 0..) |x, i| to[i] = dup(x);
    }
}

/// `array2D rows`: rows given as a list or an array of lists or arrays, all of one length.
pub fn array2DOfRows(comptime A: type, rows: anytype) Raised!A {
    var all: std.ArrayList(RowOf(@TypeOf(rows))) = .empty;
    defer all.deinit(rt.allocator);
    if (comptime isListType(@TypeOf(rows))) {
        var rest = rows;
        while (rest == .Cons) : (rest = rest.Cons.Tail) all.append(rt.allocator, rest.Cons.Head) catch @panic("fable: out of memory");
    } else {
        for (rows.items) |r| all.append(rt.allocator, r) catch @panic("fable: out of memory");
    }
    const cols: usize = if (all.items.len == 0) 0 else rowCount(all.items[0]);
    for (all.items) |r| {
        if (rowCount(r) != cols) return raise(ArgumentException, str("The arrays have different lengths. (Parameter 'vals')"));
    }
    const items = arrayItems(A, all.items.len * cols);
    for (all.items, 0..) |r, i| rowFill(r, items[i * cols ..][0..cols]);
    return shaped(arrayFrom(A, items), all.items.len, cols);
}

pub fn RowOf(comptime Rows: type) type {
    if (isListType(Rows)) return @FieldType(@typeInfo(@FieldType(Rows, "Cons")).pointer.child, "Head");
    return ItemOf(Rows);
}

pub fn blitRange(comptime param: []const u8, value: i32, comptime what: []const u8, bound: i32) Raised {
    return raise(ArgumentOutOfRangeException, format(.{ "The index is outside the legal range.\n" ++ param ++ " = ", value, ", " ++ what ++ " = ", bound, " (Parameter '" ++ param ++ "')" }));
}

/// `Array2D.blit source i1 i2 target j1 j2 count1 count2`: item after item, as FSharp.Core does
pub fn array2DBlit(source: anytype, si: i32, sj: i32, target: @TypeOf(source), ti: i32, tj: i32, n1: i32, n2: i32) Raised!void {
    const ss = shapeOf(source);
    const ts = shapeOf(target);
    const sx: i32 = @intCast(ss[0]);
    const sy: i32 = @intCast(ss[1]);
    const tx: i32 = @intCast(ts[0]);
    const ty: i32 = @intCast(ts[1]);
    if (si < 0) return blitRange("sourceIndex1", si, "source axis-0 lower bound", 0);
    if (sj < 0) return blitRange("sourceIndex2", sj, "source axis-1 lower bound", 0);
    if (ti < 0) return blitRange("targetIndex1", ti, "target axis-0 lower bound", 0);
    if (tj < 0) return blitRange("targetIndex2", tj, "target axis-1 lower bound", 0);
    if (si + n1 > sx) return raise(ArgumentOutOfRangeException, format(.{ "The index is outside the legal range.\ncount1 = ", n1, ", source axis-0 end index = ", si + n1, " source axis-0 upper bound = ", sx, " (Parameter 'count1')" }));
    if (sj + n2 > sy) return raise(ArgumentOutOfRangeException, format(.{ "The index is outside the legal range.\ncount2 = ", n2, ", source axis-1 end index = ", sj + n2, " source axis-1 upper bound = ", sy, " (Parameter 'count2')" }));
    if (ti + n1 > tx) return raise(ArgumentOutOfRangeException, format(.{ "The index is outside the legal range.\ncount1 = ", n1, ", target axis-0 end index = ", ti + n1, " target axis-0 upper bound = ", tx, " (Parameter 'count1')" }));
    if (tj + n2 > ty) return raise(ArgumentOutOfRangeException, format(.{ "The index is outside the legal range.\ncount2 = ", n2, ", target axis-1 end index = ", tj + n2, " target axis-1 upper bound = ", ty, " (Parameter 'count2')" }));
    var i: i32 = 0;
    while (i < n1) : (i += 1) {
        var j: i32 = 0;
        while (j < n2) : (j += 1) {
            const from: usize = @intCast((si + i) * sy + sj + j);
            const to: usize = @intCast((ti + i) * ty + tj + j);
            arrayPut(target, to, dup(source.items[from]));
        }
    }
}

/// `a.[lo1..hi1, lo2..hi2]`: what of it is inside the array
pub fn array2DSlice(a: anytype, lo1: ?i32, hi1: ?i32, lo2: ?i32, hi2: ?i32) @TypeOf(a) {
    const shape = shapeOf(a);
    const r0: i32 = @max(lo1 orelse 0, 0);
    const r1: i32 = @min(hi1 orelse @as(i32, @intCast(shape[0])) - 1, @as(i32, @intCast(shape[0])) - 1);
    const c0: i32 = @max(lo2 orelse 0, 0);
    const c1: i32 = @min(hi2 orelse @as(i32, @intCast(shape[1])) - 1, @as(i32, @intCast(shape[1])) - 1);
    const rows: usize = if (r1 < r0) 0 else @intCast(r1 - r0 + 1);
    const cols: usize = if (c1 < c0) 0 else @intCast(c1 - c0 + 1);
    const A = @TypeOf(a);
    const items = arrayItems(A, rows * cols);
    for (0..rows) |i| {
        for (0..cols) |j| items[i * cols + j] = dup(a.items[(@as(usize, @intCast(r0)) + i) * shape[1] + @as(usize, @intCast(c0)) + j]);
    }
    return shaped(arrayFrom(A, items), rows, cols);
}

/// `Array2D.iter f a`
pub fn array2DIter(f: anytype, a: anytype) Raised!void {
    return arrayIter(f, a);
}

/// `Array2D.iteri f a`
pub fn array2DIteri(f: anytype, a: anytype) Raised!void {
    const shape = shapeOf(a);
    for (0..a.items.len) |k| try apply3(void, f, @as(i32, @intCast(k / shape[1])), @as(i32, @intCast(k % shape[1])), dup(a.items[k]));
}
