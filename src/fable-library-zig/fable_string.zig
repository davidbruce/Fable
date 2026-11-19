//! Strings: .NET's UTF-16 System.String, its members and F#'s String module (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const root = @import("root");
const rt = @import("fable_rt.zig");
const Any = rt.Any;
const ArgumentException = rt.ArgumentException;
const ArgumentNullException = rt.ArgumentNullException;
const ArgumentOutOfRangeException = rt.ArgumentOutOfRangeException;
const Array = rt.Array;
const Exn = rt.Exn;
const IndexOutOfRangeException = rt.IndexOutOfRangeException;
const Layout = rt.Layout;
const List = rt.List;
const NullReferenceException = rt.NullReferenceException;
const Obj = rt.Obj;
const Raised = rt.Raised;
const Shower = rt.Shower;
const anyTextShape = rt.anyTextShape;
const arrayFrom = rt.arrayFrom;
const arrayIsNull = rt.arrayIsNull;
const arrays = rt.arrays;
const bigCompare = rt.bigCompare;
const bigText = rt.bigText;
const box = rt.box;
const byReference = rt.byReference;
const cell = rt.cell;
const counted = rt.counted;
const decCompare = rt.decCompare;
const decHash = rt.decHash;
const decSpecText = rt.decSpecText;
const decimal = rt.decimal;
const drop = rt.drop;
const dup = rt.dup;
const fable_show = rt.fable_show;
const genericText = rt.genericText;
const hookOf = rt.hookOf;
const hookType = rt.hookType;
const ifaceToObjBorrow = rt.ifaceToObjBorrow;
const isBigInt = rt.isBigInt;
const isCellPtr = rt.isCellPtr;
const isCollection = rt.isCollection;
const isCount = rt.isCount;
const isDecimal = rt.isDecimal;
const isFunc = rt.isFunc;
const isIface = rt.isIface;
const isNullOf = rt.isNullOf;
const netText = rt.netText;
const new = rt.new;
const objStamp = rt.objStamp;
const oom = rt.oom;
const raise = rt.raise;
const reflect = rt.reflect;
const roundTo = rt.roundTo;
const shared_bit = rt.shared_bit;
const take = rt.take;
const thread = rt.thread;
const throw = rt.throw;
const time = rt.time;
const track = rt.track;
const treeCompare = rt.treeCompare;
const treeHash = rt.treeHash;
const unicode = rt.unicode;

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
    /// the units there is room for (more than `len` in a string that is appended to)
    cap: u32,

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

pub fn LiteralCell(comptime n: usize) type {
    return extern struct { header: Str, units: [n]u16 };
}

/// A string literal, from UTF-8 text.
pub inline fn str(comptime utf8: []const u8) String {
    const static = comptime blk: {
        // (the conversion is a loop at compile time, and a function with many literals runs it
        // many times: the compiler's guard against endless loops is not for this)
        @setEvalBranchQuota(std.math.maxInt(u32));
        const u = std.unicode.utf8ToUtf16LeStringLiteral(utf8);
        break :blk LiteralCell(u.len){ .header = .{ .rc = Str.literal, .len = u.len, .cap = u.len }, .units = u.* };
    };
    return @constCast(&static.header);
}

/// A string literal that is not well-formed text (F# allows a surrogate on its own).
pub inline fn strOf(comptime u: []const u16) String {
    const static = comptime LiteralCell(u.len){ .header = .{ .rc = Str.literal, .len = u.len, .cap = u.len }, .units = u[0..u.len].* };
    return @constCast(&static.header);
}

pub fn strWords(len: usize) usize {
    return @sizeOf(Str) / 4 + (len + 1) / 2;
}

/// A new string of `len` units, to be filled in by the caller. Its count is one.
pub fn strNew(len: usize) struct { *Str, []u16 } {
    const words = rt.alloc().alloc(u32, strWords(len)) catch oom();
    const s: *Str = @ptrCast(words.ptr);
    s.* = .{ .rc = 1, .len = @intCast(len), .cap = @intCast(len) };
    if (track) thread.stats.allocs += 1;
    const first: [*]u16 = @ptrCast(@as([*]Str, @ptrCast(s)) + 1);
    return .{ s, first[0..len] };
}

/// A new string with these units.
pub fn strFrom(u: []const u16) String {
    if (u.len == 0) return str("");
    const s, const out = strNew(u.len);
    @memcpy(out, u);
    return s;
}

pub inline fn strRetain(s: String) void {
    const p = s orelse return;
    const rc = @atomicLoad(u32, &p.rc, .monotonic);
    if (rc == Str.literal) return;
    if (rc & shared_bit != 0) {
        _ = @atomicRmw(u32, &p.rc, .Add, 1, .monotonic);
        return;
    }
    p.rc = rc + 1;
    if (track) thread.stats.dups += 1;
}

pub inline fn strRelease(s: String) void {
    const p = s orelse return;
    const rc = @atomicLoad(u32, &p.rc, .monotonic);
    if (rc == Str.literal) return;
    const m = p;
    if (rc & shared_bit != 0) {
        if (@atomicRmw(u32, &m.rc, .Sub, 1, .acq_rel) != shared_bit | 1) return;
        if (track) thread.stats.frees += 1;
        const words: [*]u32 = @ptrCast(@alignCast(m));
        rt.alloc().free(words[0..strWords(m.cap)]);
        return;
    }
    if (m.rc != 1) {
        m.rc -= 1;
        if (track) thread.stats.decs += 1;
        return;
    }
    if (track) thread.stats.frees += 1;
    const words: [*]u32 = @ptrCast(@alignCast(m));
    rt.alloc().free(words[0..strWords(m.cap)]);
}

/// Text that grows: what the functions below build a string of unknown length in.
pub const TextBuilder = struct {
    list: std.ArrayList(u16) = .empty,

    pub fn add(b: *TextBuilder, u: []const u16) void {
        b.list.appendSlice(rt.alloc(), u) catch oom();
    }

    pub fn addOne(b: *TextBuilder, c: u16) void {
        b.list.append(rt.alloc(), c) catch oom();
    }

    pub fn addAscii(b: *TextBuilder, text: []const u8) void {
        for (text) |c| b.addOne(c);
    }

    pub fn deinit(b: *TextBuilder) void {
        b.list.deinit(rt.alloc());
    }

    /// The text as a string; the builder is empty afterwards.
    pub fn finish(b: *TextBuilder) String {
        const s = strFrom(b.list.items);
        b.deinit();
        b.* = .{};
        return s;
    }
};

// ---- System.Text.Encoding: UTF-8 and UTF-16 (little-endian, .NET's Encoding.Unicode) ----

pub const TextEncoding = enum(u8) {
    utf8,
    utf16le,
    /// (the name .NET prints for it)
    pub fn fable_show(b: *Shower, x: TextEncoding, depth: i32) *Layout {
        _ = depth;
        return b.word(if (x == .utf8) "System.Text.UTF8Encoding" else "System.Text.UnicodeEncoding");
    }
};

/// (a code unit, or a pair of them, as a code point; a lone surrogate is U+FFFD, as .NET encodes it)
pub fn nextCodePoint(units: []const u16, i: *usize) u21 {
    const u = units[i.*];
    i.* += 1;
    if (u >= 0xD800 and u <= 0xDBFF and i.* < units.len) {
        const lo = units[i.*];
        if (lo >= 0xDC00 and lo <= 0xDFFF) {
            i.* += 1;
            return 0x10000 + ((@as(u21, u) - 0xD800) << 10) + (lo - 0xDC00);
        }
    }
    if (u >= 0xD800 and u <= 0xDFFF) return 0xFFFD;
    return u;
}

pub fn encodeUnits(enc: TextEncoding, units: []const u16) Array(u8) {
    var out: std.ArrayList(u8) = .empty;
    switch (enc) {
        .utf16le => for (units) |u| {
            out.append(rt.alloc(), @truncate(u)) catch oom();
            out.append(rt.alloc(), @truncate(u >> 8)) catch oom();
        },
        .utf8 => {
            var i: usize = 0;
            while (i < units.len) {
                const cp = nextCodePoint(units, &i);
                var buf: [4]u8 = undefined;
                const n = std.unicode.utf8Encode(cp, &buf) catch 0;
                out.appendSlice(rt.alloc(), buf[0..n]) catch oom();
            }
        },
    }
    return arrayFrom(Array(u8), out.toOwnedSlice(rt.alloc()) catch oom());
}

pub fn rangeOf(len: usize, index: i32, count: i32) Raised![2]usize {
    if (index < 0 or count < 0) return raise(ArgumentOutOfRangeException, str("Non-negative number required."));
    if (@as(usize, @intCast(index)) + @as(usize, @intCast(count)) > len) return raise(ArgumentOutOfRangeException, str("Index and count must refer to a location within the buffer."));
    return .{ @intCast(index), @as(usize, @intCast(index)) + @as(usize, @intCast(count)) };
}

/// `enc.GetBytes(s)`
pub fn encodingGetBytes(enc: TextEncoding, s: String) Raised!Array(u8) {
    if (s == null) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 's')"));
    return encodeUnits(enc, unitsOf(s));
}

/// `enc.GetBytes(chars, index, count)`
pub fn encodingGetBytesRange(enc: TextEncoding, chars: Array(u16), index: i32, count: i32) Raised!Array(u8) {
    const r = try rangeOf(chars.items.len, index, count);
    return encodeUnits(enc, chars.items[r[0]..r[1]]);
}

/// `enc.GetString(bytes)`: invalid bytes are U+FFFD, as .NET decodes them
pub fn decodeBytes(enc: TextEncoding, bytes: []const u8) String {
    var b: TextBuilder = .{};
    switch (enc) {
        .utf16le => {
            var i: usize = 0;
            while (i + 1 < bytes.len) : (i += 2) b.addOne(@as(u16, bytes[i]) | (@as(u16, bytes[i + 1]) << 8));
            if (i < bytes.len) b.addOne(0xFFFD);
        },
        .utf8 => {
            var i: usize = 0;
            while (i < bytes.len) {
                const n = std.unicode.utf8ByteSequenceLength(bytes[i]) catch {
                    b.addOne(0xFFFD);
                    i += 1;
                    continue;
                };
                if (i + n > bytes.len) {
                    b.addOne(0xFFFD);
                    i += 1;
                    continue;
                }
                const cp = std.unicode.utf8Decode(bytes[i .. i + n]) catch {
                    b.addOne(0xFFFD);
                    i += 1;
                    continue;
                };
                if (cp >= 0x10000) {
                    const v = cp - 0x10000;
                    b.addOne(@intCast(0xD800 + (v >> 10)));
                    b.addOne(@intCast(0xDC00 + (v & 0x3FF)));
                } else b.addOne(@intCast(cp));
                i += n;
            }
        },
    }
    return b.finish();
}

pub fn encodingGetString(enc: TextEncoding, bytes: Array(u8)) Raised!String {
    if (arrayIsNull(bytes)) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 'bytes')"));
    return decodeBytes(enc, bytes.items);
}

pub fn encodingGetStringRange(enc: TextEncoding, bytes: Array(u8), index: i32, count: i32) Raised!String {
    const r = try rangeOf(bytes.items.len, index, count);
    return decodeBytes(enc, bytes.items[r[0]..r[1]]);
}

/// `enc.GetByteCount(s)`
pub fn encodingGetByteCount(enc: TextEncoding, s: String) Raised!i32 {
    const a = try encodingGetBytes(enc, s);
    defer drop(a);
    return @intCast(a.items.len);
}

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
    if (comptime hookOf(T, "fable_compare")) return hookType(T).fable_compare.call(.{ a, box(b) });
    if (T == Obj) {
        if (a.type.compare) |f| return f(a, b);
        @panic("fable: At least one object must implement IComparable.");
    }
    if (T == String) return strCompare(a, b);
    if (comptime isBigInt(T)) return bigCompare(a, b);
    if (comptime isDecimal(T)) return decCompare(a, b);
    if (T == bool) return @as(i32, @intFromBool(a)) - @as(i32, @intFromBool(b));
    if (T == void) return 0;
    if (T == Exn) @compileError("fable: exceptions cannot be compared");
    if (comptime isIface(T)) {
        if (ifaceToObjBorrow(a)) |oa| {
            if (ifaceToObjBorrow(b)) |ob| {
                if (oa.type.compare) |f| return f(oa, ob);
            }
        }
        @panic("fable: At least one object must implement IComparable.");
    }
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
            if (comptime @hasDecl(p.child, "fable_array")) return compare(a.items, b.items);
            inline for (@typeInfo(p.child).@"struct".field_names) |name| {
                if (comptime !isCount(name) and !std.mem.eql(u8, name, "shape")) {
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
            // (along a last field of its own type in a loop: a long chain does not use the stack)
            var x = a;
            var y = b;
            while (true) {
                const ta = @backingInt(std.meta.activeTag(x));
                const tb = @backingInt(std.meta.activeTag(y));
                if (ta != tb) return if (ta < tb) -1 else 1;
                switch (x) {
                    inline else => |px, tag| {
                        const py = @field(y, @tagName(tag));
                        const P = @TypeOf(px);
                        const last_self: bool = comptime blk: {
                            if (!isCellPtr(P)) break :blk false;
                            const info = @typeInfo(@typeInfo(P).pointer.child).@"struct";
                            break :blk info.field_types.len > 0 and info.field_types[info.field_types.len - 1] == T;
                        };
                        if (comptime !last_self) return compare(px, py);
                        if (px == py) return 0;
                        const names = @typeInfo(@typeInfo(P).pointer.child).@"struct".field_names;
                        inline for (names[0 .. names.len - 1]) |name| {
                            if (comptime !isCount(name)) {
                                const c = compare(@field(px, name), @field(py, name));
                                if (c != 0) return c;
                            }
                        }
                        x = @field(px, names[names.len - 1]);
                        y = @field(py, names[names.len - 1]);
                    },
                }
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

/// `Math.Max(a, b)`: as `max`, but of floats +0.0 is greater than -0.0, as IEEE 754 says
pub fn mathMax(a: anytype, b: @TypeOf(a)) @TypeOf(a) {
    if (comptime @typeInfo(@TypeOf(a)) == .float) {
        if (a == 0 and b == 0) return if (std.math.signbit(a)) b else a;
    }
    return maxOf(a, b);
}

/// `Math.Min(a, b)`: of floats -0.0 is less than +0.0
pub fn mathMin(a: anytype, b: @TypeOf(a)) @TypeOf(a) {
    if (comptime @typeInfo(@TypeOf(a)) == .float) {
        if (a == 0 and b == 0) return if (std.math.signbit(a)) a else b;
    }
    return minOf(a, b);
}

pub fn minOf(a: anytype, b: @TypeOf(a)) @TypeOf(a) {
    if (comptime @typeInfo(@TypeOf(a)) == .float) {
        if (a != a) return a;
        if (b != b) return b;
    }
    // (of two equal values, the second, as F#'s `if a < b then a else b` and .NET's decimal.Min)
    return dup(if (compare(a, b) < 0) a else b);
}

/// F#'s `hash`: equal values have equal hashes. A number is its own hash, as on .NET; the
/// hash of anything else is this library's.
pub fn hash(x: anytype) i32 {
    const T = @TypeOf(x);
    if (T == reflect.Type) return @bitCast(@as(u32, @truncate(std.hash.Wyhash.hash(0, x.full_name))));
    if (comptime byReference(T)) {
        const h = std.hash.Wyhash.hash(0, std.mem.asBytes(&x));
        return @bitCast(@as(u32, @truncate(h)));
    }
    if (comptime hookOf(T, "fable_hash")) return hookType(T).fable_hash.call(.{x});
    // (null hashes to 0, as on .NET; an object by its own hash)
    if (T == Any) return if (x) |o| hash(o) else 0;
    if (T == Obj) {
        if (x.type.hash) |f| return f(x);
    }
    if (comptime isBigInt(T)) {
        const t = bigText(x);
        defer drop(t);
        return hash(t);
    }
    if (T == String) {
        var h: u32 = 5381;
        for (unitsOf(x)) |c| h = (h *% 33) ^ c;
        return @bitCast(h);
    }
    if (T == Exn) {
        if (x.type.hash) |f| return f(x);
    }
    if (T == Obj) return objStamp(x);
    if (T == Exn) return @truncate(@as(isize, @bitCast(@intFromPtr(x))));
    if (comptime isDecimal(T)) return decHash(x);
    if (comptime isFunc(T)) return @truncate(@as(isize, @bitCast(@intFromPtr(x.env) ^ @intFromPtr(x.code))));
    if (comptime isIface(T)) {
        if (ifaceToObjBorrow(x)) |o| return hash(o);
        return @truncate(@as(isize, @bitCast(@intFromPtr(x.data) ^ @intFromPtr(x.vt))));
    }
    switch (@typeInfo(T)) {
        .void => return 0,
        .bool => return @intFromBool(x),
        .int => |info| {
            if (info.bits <= 32) return if (info.signedness == .signed) @as(i32, @intCast(x)) else @bitCast(@as(u32, @intCast(x)));
            // (as .NET folds a 64-bit number)
            const wide: u64 = if (info.signedness == .signed) @bitCast(@as(i64, @intCast(x))) else @as(u64, @intCast(x));
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
            if (comptime p.size != .slice and @hasDecl(p.child, "fable_array")) return hashWith(17, hash(x.items));
            if (comptime p.size == .slice) {
                for (x) |item| h = hashWith(h, hash(item));
                return h;
            }
            inline for (@typeInfo(p.child).@"struct".field_names) |name| {
                if (comptime !isCount(name) and !std.mem.eql(u8, name, "shape")) h = hashWith(h, hash(@field(x, name)));
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

pub fn hashWith(h: i32, next: i32) i32 {
    return (h *% 31) +% next;
}

// ---- what .NET raises for a string that is null or an argument that is out of range ----

pub fn nullRef() Raised {
    return raise(NullReferenceException, str("Object reference not set to an instance of an object."));
}

pub fn argNull(comptime param: []const u8) Raised {
    return raise(ArgumentNullException, str("Value cannot be null. (Parameter '" ++ param ++ "')"));
}

// ---- F#'s nullness operators: a value is null only of a type that has null here (a string,
// `obj`, an option); of any other type it never is ----

pub fn isNullValue(x: anytype) bool {
    const T = @TypeOf(x);
    if (comptime @typeInfo(T) == .optional) return x == null;
    return isNullOf(x);
}

/// Is the type an array's (a cell of `fable_array`)?
pub fn isArrayPtr(comptime T: type) bool {
    return isCellPtr(T) and @hasDecl(@typeInfo(T).pointer.child, "fable_array");
}

/// `nonNull x`, the `NonNull` and `NonNullQuick` patterns
pub fn nonNullValue(x: anytype) Raised!@TypeOf(x) {
    if (isNullValue(x)) return nullRef();
    return dup(x);
}

/// `nullArgCheck name x`
pub fn nullArgCheck(name: String, x: anytype) Raised!@TypeOf(x) {
    if (!isNullValue(x)) return dup(x);
    const head = strConcat(str("Value cannot be null. (Parameter '"), name);
    defer drop(head);
    return raise(ArgumentNullException, strConcat(head, str("')")));
}

/// `nonNull x` when `x` is a Zig optional wrapping a type whose unwrapped F# type has a non-optional Zig type
pub fn nonNullUnwrap(x: anytype) Raised!@typeInfo(@TypeOf(x)).optional.child {
    const inner = x orelse return nullRef();
    return dup(inner);
}

/// `nullArgCheck name x` when `x` is a Zig optional wrapping a type whose unwrapped F# type has a non-optional Zig type
pub fn nullArgCheckUnwrap(name: String, x: anytype) Raised!@typeInfo(@TypeOf(x)).optional.child {
    if (x) |inner| return dup(inner);
    const head = strConcat(str("Value cannot be null. (Parameter '"), name);
    defer drop(head);
    return raise(ArgumentNullException, strConcat(head, str("')")));
}

pub fn argRange(comptime param: []const u8, comptime text: []const u8) Raised {
    throw(ArgumentOutOfRangeException.new(.{ .Message = str(text ++ " (Parameter '" ++ param ++ "')"), .ParamName = str(param) }));
    return error.Raised;
}

/// `e` with the name of the parameter it is about (an ArgumentException's `ParamName`)
pub fn exnWithParam(e: Exn, name: String) Exn {
    if (e.type.set_param) |f| f(e, name);
    return dup(e);
}

/// `e.ParamName`: null when it has none
pub fn exnParamName(e: Exn) String {
    if (e.type.param) |f| return f(e);
    return null;
}

pub fn argNegative(comptime param: []const u8, value: i32) Raised {
    return raise(ArgumentOutOfRangeException, format(.{
        param ++ " ('",                                                                      value,
        "') must be a non-negative value. (Parameter '" ++ param ++ "')\nActual value was ", value,
        ".",
    }));
}

pub fn argAbove(comptime param: []const u8, value: anytype, limit: i32) Raised {
    return raise(ArgumentOutOfRangeException, format(.{
        param ++ " ('",                                        value,
        "') must be less than or equal to '",                  limit,
        "'. (Parameter '" ++ param ++ "')\nActual value was ", value,
        ".",
    }));
}

pub const index_range = "Index was out of range. Must be non-negative and less than or equal to the size of the collection.";

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

/// `a + b` where the caller gives `a` up: a string nothing else refers to grows in place, its
/// room doubling, so that appending in a loop is not quadratic.
pub fn strAppend(a: String, b: String) String {
    const p = a orelse return strConcat(a, b);
    const y = unitsOf(b);
    if (y.len == 0) return a;
    if (p.rc != 1 or b == a) {
        const r = strConcat(a, b);
        strRelease(a);
        return r;
    }
    const need = @as(usize, p.len) + y.len;
    var s = p;
    if (need > p.cap) {
        const cap = @max(need, @as(usize, p.cap) * 2);
        const old: [*]u32 = @ptrCast(@alignCast(p));
        const words = rt.alloc().realloc(old[0..strWords(p.cap)], strWords(cap)) catch oom();
        s = @ptrCast(words.ptr);
        s.cap = @intCast(cap);
    }
    const first: [*]u16 = @ptrCast(@as([*]Str, @ptrCast(s)) + 1);
    @memcpy(first[s.len..need], y);
    s.len = @intCast(need);
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
pub fn strSlice(s: String, start: usize, n: usize) String {
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

/// (do the units match at `at`, case folded if `fold`?)
fn unitsMatchAt(u: []const u16, at: usize, v: []const u16, fold: bool) bool {
    if (at + v.len > u.len) return false;
    for (v, 0..) |c, k| {
        const d = u[at + k];
        if (c == d) continue;
        if (!fold or unicode.toUpper(c) != unicode.toUpper(d)) return false;
    }
    return true;
}

/// `s.IndexOf(value, start, comparison)`: the comparisons that ignore case (odd values) compare
/// case-folded units; the others, by units (the culture is the invariant one here)
pub fn strIndexOfCmp(s: String, value: String, start: i32, comparison: i32) Raised!i32 {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    const u = p.units();
    if (start < 0 or start > u.len) return argRange("startIndex", index_range);
    const fold = @mod(comparison, 2) == 1;
    const vu = v.units();
    if (vu.len == 0) return start;
    var at: usize = @intCast(start);
    while (at + vu.len <= u.len) : (at += 1) {
        if (unitsMatchAt(u, at, vu, fold)) return @intCast(at);
    }
    return -1;
}

/// `s.LastIndexOf(value, comparison)` and `s.LastIndexOf(value, start, comparison)`: the last
/// match that starts at or before `start` and ends at or before `start + 1`
pub fn strLastIndexOfCmp(s: String, value: String, start: ?i32, comparison: i32) Raised!i32 {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    const u = p.units();
    const fold = @mod(comparison, 2) == 1;
    const vu = v.units();
    const from: i32 = start orelse @as(i32, @intCast(u.len)) - 1;
    if (u.len == 0) return if (vu.len == 0) 0 else -1;
    if (from < 0 or from >= u.len) return argRange("startIndex", index_range);
    if (vu.len == 0) return from;
    // (the match ends at `from` at the latest)
    const last_end: usize = @as(usize, @intCast(from)) + 1;
    if (last_end < vu.len) return -1;
    var at: usize = last_end - vu.len;
    while (true) {
        if (unitsMatchAt(u, at, vu, fold)) return @intCast(at);
        if (at == 0) break;
        at -= 1;
    }
    return -1;
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

pub fn countNegative(count: i32) Raised {
    return raise(ArgumentException, format(.{ "The input must be non-negative.\ncount = ", count, " (Parameter 'count')" }));
}

/// Apply a function value to three values, as `apply2` does to two.
pub inline fn apply3(comptime R: type, f: anytype, a: anytype, b: anytype, c: anytype) Raised!R {
    const Code = @typeInfo(@FieldType(@TypeOf(f), "code")).pointer.child;
    const n = @typeInfo(Code).@"fn".param_types.len;
    if (comptime n == 4) return f.code(f.env, a, b, c);
    if (comptime n == 3) {
        const g = f.code(f.env, a, b) catch |err| {
            drop(c);
            return err;
        };
        defer drop(g);
        return g.code(g.env, c);
    }
    if (comptime @hasField(@TypeOf(f), "code2")) {
        if (f.code2) |c2| {
            const g = c2(f.env, a, b) catch |err| {
                drop(c);
                return err;
            };
            defer drop(g);
            return g.code(g.env, c);
        }
    }
    const g = f.code(f.env, a) catch |err| {
        drop(b);
        drop(c);
        return err;
    };
    defer drop(g);
    return apply2(R, g, b, c);
}

/// Apply a function value to two values: at once if it takes both or exposes `code2`, otherwise
/// one after the other.
pub inline fn apply2(comptime R: type, f: anytype, a: anytype, b: anytype) Raised!R {
    const Code = @typeInfo(@FieldType(@TypeOf(f), "code")).pointer.child;
    if (comptime @typeInfo(Code).@"fn".param_types.len == 3) return f.code(f.env, a, b);
    if (comptime @hasField(@TypeOf(f), "code2")) {
        if (f.code2) |c2| return c2(f.env, a, b);
    }
    const g = f.code(f.env, a) catch |err| {
        drop(b);
        return err;
    };
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

/// Comptime type-shape metadata for `%A` and `ToString` when Zig erases F# distinctions
/// (`option` vs `voption`, tuple vs `struct tuple`, `char` vs `uint16`).
pub const ShowNode = struct {
    pub const auto: u16 = 0xFFFF;
    pub const Kind = enum {
        auto,
        u16_num,
        opt,
        vopt,
        tuple,
        struct_tuple,
        seq,
        map,
        record,
        @"union",
    };
    kind: Kind = .auto,
    a: u16 = auto,
    b: u16 = 0,
};

pub const TypeShape = struct {
    nodes: []const ShowNode = &.{},
    refs: []const u16 = &.{},
};

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
    shape: TypeShape = .{},
};

pub fn Arg(comptime T: type, comptime spec: Spec) type {
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
pub const Piece = union(enum) {
    ascii: []const u8,
    units: []const u16,

    pub fn len(p: Piece) usize {
        return switch (p) {
            .ascii => |a| a.len,
            .units => |u| u.len,
        };
    }
};

pub const scratch_len = 640;

/// The decimal digits of a number: 0.d0 d1 d2 ... x 10^point.
pub const Decimal = struct {
    /// (a double has at most 309 digits before the point, or 1074 after it)
    digits: [1100]u8 = undefined,
    len: usize = 0,
    point: i32 = 1,

    /// The exact digits of a finite number that is not negative.
    pub fn exact(x: f64) Decimal {
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
    pub fn shortest(x: anytype) Decimal {
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
    pub fn round(d: *Decimal, n: i32) void {
        d.roundTo(n, true);
    }

    /// Keep `n` digits, rounding to the nearest; a tie goes to the even digit, or up.
    pub fn roundTo(d: *Decimal, n: i32, even: bool) void {
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

    pub inline fn digit(d: *const Decimal, i: i32) u8 {
        return if (i >= 0 and i < d.len) '0' + d.digits[@intCast(i)] else '0';
    }
};

pub const Text = struct {
    buf: []u8,
    len: usize = 0,

    pub inline fn put(t: *Text, c: u8) void {
        t.buf[t.len] = c;
        t.len += 1;
    }

    /// e+005: the exponent with its sign and at least `width` digits
    pub fn exponent(t: *Text, letter: u8, exp: i32, width: usize) void {
        t.put(letter);
        t.put(if (exp < 0) '-' else '+');
        var digits: [8]u8 = undefined;
        const text = std.fmt.bufPrint(&digits, "{d}", .{@abs(exp)}) catch unreachable;
        for (@min(text.len, width)..width) |_| t.put('0');
        for (text) |c| t.put(c);
    }

    /// The digits without the zeros at their end: plainly while the exponent is above -5 and
    /// below `limit`, as d.ddde+xx otherwise.
    pub fn general(t: *Text, d: *const Decimal, limit: i32, letter: u8) void {
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
pub fn floatText(comptime spec: Spec, value: anytype, out: []u8) []const u8 {
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

pub fn pieceOf(comptime spec: Spec, value: anytype, scratch: *[scratch_len]u8) Piece {
    const T = @TypeOf(value);
    if (comptime isDecimal(T)) return .{ .ascii = if (spec.net.len != 0) netText(spec.net, value, scratch) else decSpecText(spec, value, scratch) };
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
            // (the digits of `x`, `X` and `o` are of the unsigned bits: F# writes the sign flag
            // before them whatever the value)
            const flag: []const u8 = if (spec.plus) "+" else if (spec.space) " " else "";
            const text = switch (spec.kind) {
                'x' => std.fmt.bufPrint(scratch, "{s}{x}", .{ flag, @as(Bits, @bitCast(value)) }),
                'X' => std.fmt.bufPrint(scratch, "{s}{X}", .{ flag, @as(Bits, @bitCast(value)) }),
                'o' => std.fmt.bufPrint(scratch, "{s}{o}", .{ flag, @as(Bits, @bitCast(value)) }),
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

pub fn isLiteralText(comptime T: type) bool {
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
        if (comptime isBigInt(T)) {
            written[i] = bigText(part);
            pieces[i] = .{ .units = unitsOf(written[i]) };
        } else if (comptime (@typeInfo(T) == .@"struct" and @hasDecl(T, "fable_spec") and isBigInt(@FieldType(T, "value")))) {
            written[i] = bigText(part.value);
            pieces[i] = .{ .units = unitsOf(written[i]) };
            if (T.fable_spec.width > pieces[i].len()) pad[i] = T.fable_spec.width - pieces[i].len();
        } else if (comptime isLiteralText(T)) {
            pieces[i] = .{ .units = comptime std.unicode.utf8ToUtf16LeStringLiteral(part) };
        } else if (comptime (@typeInfo(T) == .@"struct" and @hasDecl(T, "fable_spec"))) {
            if (comptime T.fable_spec.kind == 'A') {
                written[i] = anyTextShape(T.fable_spec.shape, part.value);
                pieces[i] = .{ .units = unitsOf(written[i]) };
            } else if (comptime T.fable_spec.kind == 'T') {
                // (`%O` and `{x}` of a value whose type is a type parameter: its `ToString`)
                written[i] = genericText(part.value) catch blk: {
                    drop(take());
                    break :blk str("");
                };
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
pub fn writePiece(out: []u16, start: usize, piece: Piece, pad: usize, spec: Spec) usize {
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

pub fn posixWrite(fd: i32, bytes: []const u8) void {
    if (builtin.os.tag == .freestanding) return;
    var done: usize = 0;
    while (done < bytes.len) {
        const n = std.posix.system.write(fd, bytes.ptr + done, bytes.len - done);
        if (n <= 0) return;
        done += @intCast(n);
    }
}

pub fn defaultOut(bytes: []const u8) void {
    posixWrite(1, bytes);
}

pub fn defaultErr(bytes: []const u8) void {
    posixWrite(2, bytes);
}

pub fn writeText(write: *const fn ([]const u8) void, s: String, newline: bool) void {
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
    writeText(rt.write_out, s, newline);
    drop(s);
}

/// `eprintf` / `eprintfn`
pub fn printErr(parts: anytype, comptime newline: bool) void {
    const s = format(parts);
    writeText(rt.write_err, s, newline);
    drop(s);
}
