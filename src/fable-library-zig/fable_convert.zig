//! System.Convert's text in a base, and System.BitConverter, Base64 and hex: of bytes as .NET lays (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");
const ArgumentException = rt.ArgumentException;
const ArgumentNullException = rt.ArgumentNullException;
const ArgumentOutOfRangeException = rt.ArgumentOutOfRangeException;
const Array = rt.Array;
const BigInt = rt.BigInt;
const FormatException = rt.FormatException;
const ItemOf = rt.ItemOf;
const NetDecimal = rt.NetDecimal;
const OverflowException = rt.OverflowException;
const Raised = rt.Raised;
const String = rt.String;
const TextBuilder = rt.TextBuilder;
const argNull = rt.argNull;
const argRange = rt.argRange;
const arrayFrom = rt.arrayFrom;
const arrayPut = rt.arrayPut;
const bigAdd = rt.bigAdd;
const bigOf = rt.bigOf;
const bigParse = rt.bigParse;
const decAdd = rt.decAdd;
const decDiv = rt.decDiv;
const decParse = rt.decParse;
const drop = rt.drop;
const dup = rt.dup;
const eql = rt.eql;
const format = rt.format;
const isBigInt = rt.isBigInt;
const isDecimal = rt.isDecimal;
const raise = rt.raise;
const roundEven = rt.roundEven;
const str = rt.str;
const strEql = rt.strEql;
const take = rt.take;
const unicode = rt.unicode;
const unitsOf = rt.unitsOf;

// ---------------------------------------------------------------------------------------------
// System.Convert's text in a base, and System.BitConverter, Base64 and hex: of bytes as .NET lays
// them out (little-endian)
// ---------------------------------------------------------------------------------------------

pub fn overflowOf(comptime T: type) Raised {
    return raise(OverflowException, str("Value was either too large or too small for " ++ netIntName(T) ++ "."));
}

/// `TryParse` of any type that has a `Parse` here: the value, or null (and what `Parse` raised is
/// dropped)
pub fn tryParseAny(comptime T: type, s: String) ?T {
    const v = (if (T == NetDecimal)
        decParse(s, false)
    else if (T == BigInt)
        bigParse(s)
    else if (T == bool)
        parseBool(s)
    else if (comptime @typeInfo(T) == .float)
        parseFloat(T, s)
    else
        parseInt(T, s)) catch {
        drop(take());
        return null;
    };
    return v;
}

/// `Int32.Parse(s, NumberStyles.HexNumber)`: hex digits (the bits of the number), white space
/// around them
pub fn parseHex(comptime T: type, s: String) Raised!T {
    const u = trimmed(s);
    const bits = @typeInfo(T).int.bits;
    if (u.len == 0) return badFormat(s);
    var v: u128 = 0;
    for (u) |c| {
        const d = std.fmt.charToDigit(@intCast(@min(c, 127)), 16) catch return badFormat(s);
        v = v * 16 + d;
        if (v > std.math.maxInt(@Int(.unsigned, bits))) return overflowOf(T);
    }
    return @bitCast(@as(@Int(.unsigned, bits), @intCast(v)));
}

/// `Convert.ToInt32(x)` of a float: rounded half to even; what does not fit raises
pub fn convFloatToInt(comptime T: type, x: anytype) Raised!T {
    const r = roundEven(@as(f64, x));
    if (!(r >= @as(f64, @floatFromInt(std.math.minInt(T))) and r <= @as(f64, @floatFromInt(std.math.maxInt(T))))) return overflowOf(T);
    return @intFromFloat(r);
}

/// `Convert.ToInt32(s)` and the others: as `Parse`, but null is 0
pub fn convParse(comptime T: type, s: String) Raised!T {
    if (T == bool) return if (s == null) false else parseBool(s);
    if (s == null) return 0;
    if (comptime @typeInfo(T) == .float) return parseFloat(T, s);
    return parseInt(T, s);
}

/// `Convert.ToInt32(s, base)`: base 10 is signed; in base 2, 8 and 16 the digits are the bits of
/// the number (`"ff"` is -1 as an sbyte), and base 16 may start with `0x`
pub fn convParseBase(comptime T: type, s: String, base: i32) Raised!T {
    if (base != 2 and base != 8 and base != 10 and base != 16) return raise(ArgumentException, str("Invalid Base."));
    if (s == null) return 0;
    var u = unitsOf(s);
    const bits = @typeInfo(T).int.bits;
    if (base == 10) {
        var negative = false;
        if (u.len != 0 and u[0] == '-') {
            negative = true;
            u = u[1..];
        }
        var v: i128 = 0;
        var n: usize = 0;
        while (n < u.len and u[n] >= '0' and u[n] <= '9') : (n += 1) {
            v = v * 10 + (u[n] - '0');
            if (v > (1 << 64)) return overflowOf(T);
        }
        if (n == 0) return raise(FormatException, str("Could not find any recognizable digits."));
        if (n != u.len) return raise(FormatException, str("Additional non-parsable characters are at the end of the string."));
        if (negative) v = -v;
        // (a narrower type is read as an Int32 first, as .NET does)
        if (v < std.math.minInt(T) or v > std.math.maxInt(T)) return overflowOf(T);
        return @intCast(v);
    }
    if (base == 16 and u.len >= 2 and u[0] == '0' and (u[1] == 'x' or u[1] == 'X')) u = u[2..];
    var v: u128 = 0;
    var n: usize = 0;
    while (n < u.len) : (n += 1) {
        const d: u32 = std.fmt.charToDigit(@intCast(@min(u[n], 127)), @intCast(base)) catch break;
        v = v * @as(u128, @intCast(base)) + d;
        if (v > std.math.maxInt(@Int(.unsigned, bits))) return overflowOf(T);
    }
    if (n == 0) return raise(FormatException, str("Could not find any recognizable digits."));
    if (n != u.len) return raise(FormatException, str("Additional non-parsable characters are at the end of the string."));
    return @bitCast(@as(@Int(.unsigned, bits), @intCast(v)));
}

/// `Convert.ToString(x, base)`: in base 2, 8 and 16 the bits of the number (two's complement)
pub fn convToStringBase(x: anytype, base: i32) Raised!String {
    const T = @TypeOf(x);
    if (base != 2 and base != 8 and base != 10 and base != 16) return raise(ArgumentException, str("Invalid Base."));
    if (base == 10) return format(.{x});
    const U = @Int(.unsigned, @typeInfo(T).int.bits);
    var v: U = @bitCast(x);
    var buf: [130]u8 = undefined;
    var i: usize = buf.len;
    if (v == 0) {
        i -= 1;
        buf[i] = '0';
    }
    while (v != 0) {
        i -= 1;
        buf[i] = "0123456789abcdef"[@intCast(v % @as(U, @intCast(base)))];
        v /= @as(U, @intCast(base));
    }
    var b: TextBuilder = .{};
    b.addAscii(buf[i..]);
    return b.finish();
}

/// `BitConverter.GetBytes x`
pub fn bitGetBytes(x: anytype) Array(u8) {
    const T = @TypeOf(x);
    const bytes: []const u8 = if (T == bool) &.{@intFromBool(x)} else std.mem.asBytes(&x);
    const items = rt.allocator.alloc(u8, bytes.len) catch rt.oom();
    @memcpy(items, bytes);
    return arrayFrom(Array(u8), items);
}

/// `BitConverter.ToInt32(bytes, index)` and the others
pub fn bitTo(comptime T: type, bytes: Array(u8), index: i32) Raised!T {
    const b = bytes.items;
    if (index < 0 or index >= b.len) return argRange("startIndex", "Index was out of range. Must be non-negative and less than the size of the collection.");
    const size = if (T == bool) 1 else @sizeOf(T);
    const at: usize = @intCast(index);
    if (at + size > b.len) return raise(ArgumentException, str("The array starting from the specified index is not long enough to read a value of the specified type. (Parameter 'value')"));
    if (T == bool) return b[at] != 0;
    var v: T = undefined;
    @memcpy(std.mem.asBytes(&v), b[at..][0..size]);
    return v;
}

/// `BitConverter.ToString(bytes, start, length)`: `01-AB-FF`
pub fn bitToString(bytes: Array(u8), start: ?i32, length: ?i32) Raised!String {
    const b = bytes.items;
    const from = start orelse 0;
    if (from < 0 or (from >= b.len and b.len != 0)) return argRange("startIndex", "Index was out of range. Must be non-negative and less than the size of the collection.");
    const n = length orelse @as(i32, @intCast(b.len)) - from;
    if (n < 0 or from + n > b.len) return raise(ArgumentException, str("Destination array is not long enough to copy all the items in the collection. Check array index and length."));
    var t: TextBuilder = .{};
    for (b[@intCast(from)..][0..@intCast(n)], 0..) |byte, i| {
        if (i > 0) t.addOne('-');
        var hex: [2]u8 = undefined;
        _ = std.fmt.bufPrint(&hex, "{X:0>2}", .{byte}) catch unreachable;
        t.addAscii(&hex);
    }
    return t.finish();
}

/// `Convert.ToHexString(bytes, offset, length)` (`lower`: `ToHexStringLower`)
pub fn hexOf(bytes: Array(u8), offset: ?i32, length: ?i32, comptime lower: bool) Raised!String {
    if (rt.arrayIsNull(bytes)) return argNull("inArray");
    const b = bytes.items;
    const off = offset orelse 0;
    const n = length orelse @as(i32, @intCast(b.len));
    if (n < 0) return raise(ArgumentOutOfRangeException, format(.{ "length ('", n, "') must be a non-negative value. (Parameter 'length')\nActual value was ", n, "." }));
    if (off < 0) return raise(ArgumentOutOfRangeException, format(.{ "offset ('", off, "') must be a non-negative value. (Parameter 'offset')\nActual value was ", off, "." }));
    const most = @as(i32, @intCast(b.len)) - n;
    if (off > most) return raise(ArgumentOutOfRangeException, format(.{ "offset ('", off, "') must be less than or equal to '", most, "'. (Parameter 'offset')\nActual value was ", off, "." }));
    var t: TextBuilder = .{};
    for (b[@intCast(off)..][0..@intCast(n)]) |byte| {
        var hex: [2]u8 = undefined;
        _ = (if (lower) std.fmt.bufPrint(&hex, "{x:0>2}", .{byte}) else std.fmt.bufPrint(&hex, "{X:0>2}", .{byte})) catch unreachable;
        t.addAscii(&hex);
    }
    return t.finish();
}

/// `Convert.FromHexString s`
pub fn hexParse(s: String) Raised!Array(u8) {
    if (s == null) return argNull("s");
    const u = unitsOf(s);
    if (u.len % 2 != 0) return raise(FormatException, str("The input is not a valid hex string as its length is not a multiple of 2."));
    const items = rt.allocator.alloc(u8, u.len / 2) catch rt.oom();
    for (items, 0..) |*o, i| {
        const hi = std.fmt.charToDigit(@intCast(@min(u[2 * i], 127)), 16) catch {
            rt.allocator.free(items);
            return raise(FormatException, str("The input is not a valid hex string as it contains a non-hex character."));
        };
        const lo = std.fmt.charToDigit(@intCast(@min(u[2 * i + 1], 127)), 16) catch {
            rt.allocator.free(items);
            return raise(FormatException, str("The input is not a valid hex string as it contains a non-hex character."));
        };
        o.* = hi * 16 + lo;
    }
    return arrayFrom(Array(u8), items);
}

/// `Convert.ToBase64String bytes`
pub fn base64Of(bytes: Array(u8)) String {
    const enc = std.base64.standard.Encoder;
    const buf = rt.allocator.alloc(u8, enc.calcSize(bytes.items.len)) catch rt.oom();
    defer rt.allocator.free(buf);
    const text = enc.encode(buf, bytes.items);
    var t: TextBuilder = .{};
    t.addAscii(text);
    return t.finish();
}

/// `Convert.FromBase64String s` (white space is skipped, as .NET does)
pub fn base64Parse(s: String) Raised!Array(u8) {
    if (s == null) return argNull("s");
    const u = unitsOf(s);
    var ascii: std.ArrayList(u8) = .empty;
    defer ascii.deinit(rt.allocator);
    for (u) |c| {
        if (c == ' ' or c == '\t' or c == '\r' or c == '\n') continue;
        if (c > 127) return badBase64();
        ascii.append(rt.allocator, @intCast(c)) catch rt.oom();
    }
    const dec = std.base64.standard.Decoder;
    const n = dec.calcSizeForSlice(ascii.items) catch return badBase64();
    const items = rt.allocator.alloc(u8, n) catch rt.oom();
    dec.decode(items, ascii.items) catch {
        rt.allocator.free(items);
        return badBase64();
    };
    return arrayFrom(Array(u8), items);
}

pub fn badBase64() Raised {
    return raise(FormatException, str("The input is not a valid Base-64 string as it contains a non-base 64 character, more than two padding characters, or an illegal character among the padding characters."));
}

test "Convert and BitConverter" {
    try std.testing.expectEqual(@as(i8, -1), try convParseBase(i8, str("ff"), 16));
    try std.testing.expectEqual(@as(i32, 31), try convParseBase(i32, str("0x1f"), 16));
    const t = try convToStringBase(@as(i32, -5), 16);
    defer drop(t);
    try std.testing.expect(strEql(t, str("fffffffb")));
    const b = bitGetBytes(@as(i32, 258));
    defer drop(b);
    try std.testing.expectEqual(@as(i32, 258), try bitTo(i32, b, 0));
    const h = try bitToString(b, null, null);
    defer drop(h);
    try std.testing.expect(strEql(h, str("02-01-00-00")));
    const e = base64Of(b);
    defer drop(e);
    const back = try base64Parse(e);
    defer drop(back);
    try std.testing.expectEqualSlices(u8, b.items, back.items);
}

pub fn netIntName(comptime T: type) []const u8 {
    return switch (T) {
        i8 => "a signed byte",
        u8 => "an unsigned byte",
        i16 => "an Int16",
        u16, c_ushort => "a UInt16",
        i32 => "an Int32",
        u32 => "a UInt32",
        i64 => "an Int64",
        u64 => "a UInt64",
        else => @typeName(T),
    };
}

pub fn trimmed(s: String) []const u16 {
    var u = unitsOf(s);
    while (u.len != 0 and unicode.isWhiteSpace(u[0])) u = u[1..];
    while (u.len != 0 and unicode.isWhiteSpace(u[u.len - 1])) u = u[0 .. u.len - 1];
    return u;
}

/// The text of a number as .NET's parsers read it: trailing NULs left out, then ASCII white space
/// (tab to carriage return, space) at both ends; other white space is part of the text
pub fn numberText(s: String) []const u16 {
    var u = unitsOf(s);
    while (u.len != 0 and u[u.len - 1] == 0) u = u[0 .. u.len - 1];
    while (u.len != 0 and isNumberWhite(u[0])) u = u[1..];
    while (u.len != 0 and isNumberWhite(u[u.len - 1])) u = u[0 .. u.len - 1];
    return u;
}

fn isNumberWhite(c: u16) bool {
    return c == ' ' or (c >= 0x09 and c <= 0x0D);
}

pub fn badFormat(s: String) Raised {
    return raise(FormatException, format(.{ "The input string '", s, "' was not in a correct format." }));
}

pub const ParseStyle = enum {
    /// `Int32.Parse`: white space, a sign, decimal digits
    dotnet,
    /// F#'s `int s`: also `0x`, `0o` and `0b` and `_` between digits
    fsharp,
};

/// A whole number from text, or null if the text is not one; error.Overflow if it is one
/// that does not fit in 64 bits (or in `T`, for which the caller says what to raise).
pub fn parseWhole(comptime T: type, u: []const u16, comptime style: ParseStyle) error{ Format, Overflow }!T {
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

pub fn parseReal(comptime T: type, u: []const u16) ?T {
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
    _ = negative;
    for (body) |c| {
        if (std.ascii.isAlphabetic(c) and c != 'e' and c != 'E') return null;
    }
    return std.fmt.parseFloat(T, text) catch null;
}

/// .NET's symbols of a float, `NaN` and `Infinity`, in any case, with a sign, white space of
/// any kind around them (but no NUL)
fn floatSymbol(comptime T: type, units: []const u16) ?T {
    var u = units;
    while (u.len != 0 and unicode.isWhiteSpace(u[0])) u = u[1..];
    while (u.len != 0 and unicode.isWhiteSpace(u[u.len - 1])) u = u[0 .. u.len - 1];
    var negative = false;
    if (u.len != 0 and (u[0] == '-' or u[0] == '+')) {
        negative = u[0] == '-';
        u = u[1..];
    }
    var buf: [8]u8 = undefined;
    if (u.len > buf.len) return null;
    for (u, 0..) |c, i| {
        if (c > 0x7F) return null;
        buf[i] = @intCast(c);
    }
    const body = buf[0..u.len];
    if (std.ascii.eqlIgnoreCase(body, "NaN")) return std.math.nan(T);
    if (std.ascii.eqlIgnoreCase(body, "Infinity")) return if (negative) -std.math.inf(T) else std.math.inf(T);
    return null;
}

/// (a float's symbol, or its digits with .NET's white space and trailing NULs around them)
fn readFloat(comptime T: type, units: []const u16) ?T {
    if (floatSymbol(T, units)) |x| return x;
    var u = units;
    while (u.len != 0 and u[u.len - 1] == 0) u = u[0 .. u.len - 1];
    while (u.len != 0 and isNumberWhite(u[0])) u = u[1..];
    while (u.len != 0 and isNumberWhite(u[u.len - 1])) u = u[0 .. u.len - 1];
    return parseReal(T, u);
}

/// `Double.Parse s`
pub fn parseFloat(comptime T: type, s: String) Raised!T {
    if (s == null) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 's')"));
    return readFloat(T, unitsOf(s)) orelse badFormat(s);
}

/// F#'s `float s` and `float32 s`: as FSharp.Core reads them, without the underscores
pub fn parseFloatFs(comptime T: type, s: String) Raised!T {
    if (s == null) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 's')"));
    var buf: [128]u16 = undefined;
    var n: usize = 0;
    for (unitsOf(s)) |c| {
        if (c == '_') continue;
        if (n == buf.len) return badFormat(s);
        buf[n] = c;
        n += 1;
    }
    return readFloat(T, buf[0..n]) orelse badFormat(s);
}

pub fn tryParseFloat(comptime T: type, s: String) ?T {
    if (s == null) return null;
    return readFloat(T, unitsOf(s));
}

/// `Boolean.Parse s`
pub fn parseBool(s: String) Raised!bool {
    const u = trimmed(s);
    if (u.len == 4 and unicode.toLower(u[0]) == 't' and unicode.toLower(u[1]) == 'r' and unicode.toLower(u[2]) == 'u' and unicode.toLower(u[3]) == 'e') return true;
    if (u.len == 5 and unicode.toLower(u[0]) == 'f' and unicode.toLower(u[1]) == 'a' and unicode.toLower(u[2]) == 'l' and unicode.toLower(u[3]) == 's' and unicode.toLower(u[4]) == 'e') return false;
    return raise(FormatException, format(.{ "String '", s, "' was not recognized as a valid Boolean." }));
}

/// `a + b` of a running total: `a` is owned (a bigint total is replaced), `b` borrowed
pub fn addOf(a: anytype, b: @TypeOf(a)) @TypeOf(a) {
    if (comptime isBigInt(@TypeOf(a))) {
        const r = bigAdd(a, b);
        drop(a);
        return r;
    }
    return if (comptime @typeInfo(@TypeOf(a)) == .float) a + b else a +% b;
}

/// the zero a sum starts from
pub fn zeroOf(comptime T: type) T {
    if (comptime isBigInt(T)) return bigOf(@as(i32, 0));
    if (comptime isDecimal(T)) return .{};
    return 0;
}

/// `List.sum xs`
pub fn listSum(xs: anytype) @FieldType(@typeInfo(@FieldType(@TypeOf(xs), "Cons")).pointer.child, "Head") {
    var total = zeroOf(@TypeOf(xs.Cons.Head));
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) total = addOf(total, rest.Cons.Head);
    return total;
}

/// `List.sumBy f xs`
pub fn listSumBy(comptime R: type, f: anytype, xs: anytype) Raised!R {
    var total = zeroOf(R);
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        const v = f.code(f.env, dup(rest.Cons.Head)) catch |e| {
            drop(total);
            return e;
        };
        total = accumulate(total, v) catch |e| {
            drop(v);
            return e;
        };
        drop(v);
    }
    return total;
}

pub fn emptyInput(comptime what: []const u8) Raised {
    return raise(ArgumentException, str("The input " ++ what ++ " was empty. (Parameter 'source')"));
}

/// `List.average xs`
pub fn listAverage(xs: anytype) Raised!@TypeOf(xs.Cons.Head) {
    var total = zeroOf(@TypeOf(xs.Cons.Head));
    var n: usize = 0;
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        total = try accumulate(total, rest.Cons.Head);
        n += 1;
    }
    if (n == 0) return emptyInput("sequence");
    return averageOf(total, n);
}

/// `total + x` of a sum that may raise (a decimal's)
pub fn accumulate(total: anytype, x: @TypeOf(total)) Raised!@TypeOf(total) {
    if (comptime isDecimal(@TypeOf(total))) return decAdd(total, x);
    return addOf(total, x);
}

pub fn averageOf(total: anytype, n: usize) Raised!@TypeOf(total) {
    if (comptime isDecimal(@TypeOf(total))) return decDiv(total, .{ .m = @intCast(n) });
    return total / @as(@TypeOf(total), @floatFromInt(n));
}

/// `List.sum xs` of decimals, which can raise
pub fn listSumDec(xs: anytype) Raised!NetDecimal {
    var total: NetDecimal = .{};
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) total = try decAdd(total, rest.Cons.Head);
    return total;
}

/// `Array.sum a` of decimals
pub fn arraySumDec(a: anytype) Raised!NetDecimal {
    var total: NetDecimal = .{};
    for (a.items) |x| total = try decAdd(total, x);
    return total;
}

/// `List.averageBy f xs`
pub fn listAverageBy(comptime R: type, f: anytype, xs: anytype) Raised!R {
    var total = zeroOf(R);
    var n: usize = 0;
    var rest = xs;
    while (rest == .Cons) : (rest = rest.Cons.Tail) {
        total = try accumulate(total, try f.code(f.env, dup(rest.Cons.Head)));
        n += 1;
    }
    if (n == 0) return emptyInput("sequence");
    return averageOf(total, n);
}

/// `Array.sum a`
pub fn arraySum(a: anytype) ItemOf(@TypeOf(a)) {
    var total = zeroOf(ItemOf(@TypeOf(a)));
    for (a.items) |x| total = addOf(total, x);
    return total;
}

/// `Array.sumBy f a`
pub fn arraySumBy(comptime R: type, f: anytype, a: anytype) Raised!R {
    var total = zeroOf(R);
    for (a.items) |x| {
        const v = f.code(f.env, dup(x)) catch |e| {
            drop(total);
            return e;
        };
        total = accumulate(total, v) catch |e| {
            drop(v);
            return e;
        };
        drop(v);
    }
    return total;
}

/// `Array.averageBy f a`
pub fn arrayAverageBy(comptime R: type, f: anytype, a: anytype) Raised!R {
    if (a.items.len == 0) return raise(ArgumentException, str("The input array was empty. (Parameter 'array')"));
    var total = zeroOf(R);
    for (a.items) |x| total = try accumulate(total, try f.code(f.env, dup(x)));
    return averageOf(total, a.items.len);
}

/// `Array.Copy(source, sourceIndex, target, targetIndex, length)`
pub fn arrayCopyRange(source: anytype, si: i32, target: @TypeOf(source), ti: i32, n: i32) Raised!void {
    // (.NET's Array.Copy: a negative count or index is out of range; a range past an end, an
    // argument error)
    if (n < 0) return raise(ArgumentOutOfRangeException, str("Non-negative number required. (Parameter 'length')"));
    if (si < 0) return raise(ArgumentOutOfRangeException, str("Index was less than the array's lower bound in the first dimension. (Parameter 'sourceIndex')"));
    if (ti < 0) return raise(ArgumentOutOfRangeException, str("Index was less than the array's lower bound in the first dimension. (Parameter 'destinationIndex')"));
    if (si + n > source.items.len) return raise(ArgumentException, str("Source array was not long enough. Check the source index, length, and the array's lower bounds. (Parameter 'sourceArray')"));
    if (ti < 0 or ti + n > target.items.len) return raise(ArgumentException, str("Destination array was not long enough. Check the destination index, length, and the array's lower bounds. (Parameter 'destinationArray')"));
    const from: usize = @intCast(si);
    const to: usize = @intCast(ti);
    const count: usize = @intCast(n);
    if (source == target and to > from) {
        var k = count;
        while (k > 0) : (k -= 1) arrayPut(target, to + k - 1, dup(source.items[from + k - 1]));
    } else {
        for (0..count) |k| arrayPut(target, to + k, dup(source.items[from + k]));
    }
}

/// `target.[lo..hi] <- source`
pub fn arraySetSlice(target: anytype, lo: ?i32, hi: ?i32, source: @TypeOf(target)) Raised!void {
    const start = lo orelse 0;
    const finish = hi orelse @as(i32, @intCast(target.items.len)) - 1;
    return arrayCopyRange(source, 0, target, start, finish - start + 1);
}

/// `Array.IndexOf(a, x, start, count)`: items are compared with `Equals`
pub fn arrayIndexOf(a: anytype, x: ItemOf(@TypeOf(a)), start: i32, count: ?i32) Raised!i32 {
    const len: i32 = @intCast(a.items.len);
    if (start < 0 or start > len) return argRange("startIndex", "Index was out of range. Must be non-negative and less than or equal to the size of the collection.");
    const n = count orelse len - start;
    if (n < 0 or start + n > len) return argRange("count", "Count must be positive and count must refer to a location within the string/array/collection.");
    for (a.items[@intCast(start)..][0..@intCast(n)], 0..) |item, i| {
        if (eql(item, x)) return start + @as(i32, @intCast(i));
    }
    return -1;
}

/// `Array.average a`
pub fn arrayAverage(a: anytype) Raised!ItemOf(@TypeOf(a)) {
    if (a.items.len == 0) return raise(ArgumentException, str("The input array was empty. (Parameter 'array')"));
    var total = zeroOf(ItemOf(@TypeOf(a)));
    for (a.items) |x| total = try accumulate(total, x);
    return averageOf(total, a.items.len);
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
                const truncated: @Int(to.signedness, to.bits) = @truncate(@as(WideTo, @bitCast(@as(WideFrom, @intCast(x)))));
                return @intCast(truncated);
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
