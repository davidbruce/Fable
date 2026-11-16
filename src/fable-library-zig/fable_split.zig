//! Split, Join, characters, comparison that ignores case (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");
const ArgumentException = rt.ArgumentException;
const ArgumentNullException = rt.ArgumentNullException;
const ArgumentOutOfRangeException = rt.ArgumentOutOfRangeException;
const Array = rt.Array;
const FormatException = rt.FormatException;
const IndexOutOfRangeException = rt.IndexOutOfRangeException;
const Raised = rt.Raised;
const String = rt.String;
const StringBuilder = rt.StringBuilder;
const TextBuilder = rt.TextBuilder;
const argNull = rt.argNull;
const argRange = rt.argRange;
const arrayFrom = rt.arrayFrom;
const arrayItems = rt.arrayItems;
const dup = rt.dup;
const index_range = rt.index_range;
const nullRef = rt.nullRef;
const raise = rt.raise;
const str = rt.str;
const strFrom = rt.strFrom;
const strSlice = rt.strSlice;
const unicode = rt.unicode;
const unitsOf = rt.unitsOf;

// ---------------------------------------------------------------------------------------------
// Split, Join, characters, comparison that ignores case
// ---------------------------------------------------------------------------------------------

pub fn splitPush(parts: *std.ArrayList(String), piece: []const u16, remove_empty: bool, trim: bool) void {
    var p = piece;
    if (trim) {
        while (p.len != 0 and unicode.isWhiteSpace(p[0])) p = p[1..];
        while (p.len != 0 and unicode.isWhiteSpace(p[p.len - 1])) p = p[0 .. p.len - 1];
    }
    if (remove_empty and p.len == 0) return;
    parts.append(rt.allocator, strFrom(p)) catch rt.oom();
}

pub fn splitDone(parts: *std.ArrayList(String)) Array(String) {
    const A = Array(String);
    const items = arrayItems(A, parts.items.len);
    @memcpy(items, parts.items);
    parts.deinit(rt.allocator);
    return arrayFrom(A, items);
}

/// (is a part empty, once trimmed if the options trim parts?)
fn pieceEmpty(piece: []const u16, trim: bool) bool {
    if (!trim) return piece.len == 0;
    for (piece) |c| {
        if (!unicode.isWhiteSpace(c)) return false;
    }
    return true;
}

/// (where the next separator is from `from`, and its length)
fn nextSeparator(u: []const u16, from: usize, separators: []const String) ?struct { pos: usize, len: usize } {
    var i = from;
    while (i < u.len) : (i += 1) {
        for (separators) |sepStr| {
            const sep = unitsOf(sepStr);
            if (sep.len != 0 and std.mem.startsWith(u16, u[i..], sep)) return .{ .pos = i, .len = sep.len };
        }
    }
    return null;
}

/// `s.Split(chars, options)`: by any of the chars (white space if there are none). `options`
/// is .NET's StringSplitOptions: 1 removes empty parts, 2 trims each part.
pub fn strSplitChars(s: String, chars: []const u16, count: i32, options: i32) Raised!Array(String) {
    const p = s orelse return nullRef();
    const u = p.units();
    var parts: std.ArrayList(String) = .empty;
    if (count < 0) return raise(ArgumentOutOfRangeException, str("Count cannot be less than zero. (Parameter 'count')"));
    if (count == 0) return splitDone(&parts);
    var start: usize = 0;
    for (u, 0..) |c, i| {
        // (`count` parts at most: the last is the rest of the string)
        if (parts.items.len + 1 == count) break;
        const sep = if (chars.len == 0) unicode.isWhiteSpace(c) else std.mem.indexOfScalar(u16, chars, c) != null;
        if (i < start) continue;
        if (sep) {
            splitPush(&parts, u[start..i], options & 1 != 0, options & 2 != 0);
            start = i + 1;
            // (.NET's: with the parts but the last made, empty ones after are skipped before the
            // last one is taken, when empty parts are removed)
            if (options & 1 != 0 and parts.items.len + 1 == count) {
                while (true) {
                    var j = start;
                    while (j < u.len) : (j += 1) {
                        const d = u[j];
                        const is_sep = if (chars.len == 0) unicode.isWhiteSpace(d) else std.mem.indexOfScalar(u16, chars, d) != null;
                        if (is_sep) break;
                    }
                    if (j >= u.len or !pieceEmpty(u[start..j], options & 2 != 0)) break;
                    start = j + 1;
                }
                break;
            }
        }
    }
    splitPush(&parts, u[start..], options & 1 != 0, options & 2 != 0);
    return splitDone(&parts);
}

/// `s.Split(separators, options)` by strings (the first that matches at each place).
pub fn strSplitStrings(s: String, separators: []const String, count: i32, options: i32) Raised!Array(String) {
    const p = s orelse return nullRef();
    const u = p.units();
    var parts: std.ArrayList(String) = .empty;
    if (count < 0) return raise(ArgumentOutOfRangeException, str("Count cannot be less than zero. (Parameter 'count')"));
    if (count == 0) return splitDone(&parts);
    var start: usize = 0;
    var i: usize = 0;
    outer: while (i < u.len) {
        if (parts.items.len + 1 == count) break;
        for (separators) |sepStr| {
            const sep = unitsOf(sepStr);
            if (sep.len != 0 and std.mem.startsWith(u16, u[i..], sep)) {
                splitPush(&parts, u[start..i], options & 1 != 0, options & 2 != 0);
                i += sep.len;
                start = i;
                // (.NET's: with the parts but the last made, empty ones after are skipped)
                if (options & 1 != 0 and parts.items.len + 1 == count) {
                    while (nextSeparator(u, start, separators)) |at| {
                        if (!pieceEmpty(u[start..at.pos], options & 2 != 0)) break;
                        start = at.pos + at.len;
                    }
                    break :outer;
                }
                continue :outer;
            }
        }
        i += 1;
    }
    splitPush(&parts, u[start..], options & 1 != 0, options & 2 != 0);
    return splitDone(&parts);
}

pub fn strSplitString(s: String, separator: String, count: i32, options: i32) Raised!Array(String) {
    return strSplitStrings(s, &.{separator}, count, options);
}

/// `Char.IsLetter(s, i)` and the other classes: of the char at `i`
pub fn strCharIs(s: String, i: i32, comptime class: fn (u16) bool) Raised!bool {
    const p = s orelse return argNull("s");
    if (i < 0 or i >= p.len) return argRange("index", "Index was out of range. Must be non-negative and less than the size of the collection.");
    return class(p.units()[@intCast(i)]);
}

/// `Char.GetUnicodeCategory c`: .NET's number of the category
pub fn charCategory(c: u16) i32 {
    return @intCast(@backingInt(unicode.category(c)));
}

pub fn strCharCategory(s: String, i: i32) Raised!i32 {
    const p = s orelse return argNull("s");
    if (i < 0 or i >= p.len) return argRange("index", "Index was out of range. Must be non-negative and less than the size of the collection.");
    return charCategory(p.units()[@intCast(i)]);
}

/// `char s` and `Char.Parse s`: a string of exactly one char
pub fn strToChar(s: String) Raised!u16 {
    const p = s orelse return raise(ArgumentNullException, str("Value cannot be null. (Parameter 's')"));
    if (p.len != 1) return raise(FormatException, str("String must be exactly one character long."));
    return p.units()[0];
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

// ---- more of System.String and StringBuilder ----

pub const last_range = "Index was out of range. Must be non-negative and less than the size of the collection.";

/// `s.LastIndexOf(c, start)`: the last at or before `start`
pub fn strLastIndexOfCharFrom(s: String, c: u16, start: i32) Raised!i32 {
    const p = s orelse return nullRef();
    const u = p.units();
    if (u.len == 0) return -1;
    if (start < 0 or start >= u.len) return argRange("startIndex", last_range);
    const at = std.mem.lastIndexOfScalar(u16, u[0 .. @as(usize, @intCast(start)) + 1], c) orelse return -1;
    return @intCast(at);
}

/// `s.LastIndexOf(value, start)`: the last that ends at or before `start`
pub fn strLastIndexOfFrom(s: String, value: String, start: i32) Raised!i32 {
    const p = s orelse return nullRef();
    const v = value orelse return argNull("value");
    const u = p.units();
    if (v.len == 0) return @min(start + 1, @as(i32, @intCast(u.len)));
    if (u.len == 0) return -1;
    if (start < 0 or start >= u.len) return argRange("startIndex", last_range);
    const at = std.mem.lastIndexOf(u16, u[0 .. @as(usize, @intCast(start)) + 1], v.units()) orelse return -1;
    return @intCast(at);
}

/// `s.IndexOfAny(chars, start, count)`
pub fn strIndexOfAny(s: String, chars: Array(u16), start: i32, count: ?i32) Raised!i32 {
    const p = s orelse return nullRef();
    const u = p.units();
    if (start < 0 or start > u.len) return argRange("startIndex", index_range);
    const n = count orelse @as(i32, @intCast(u.len)) - start;
    if (n < 0 or start + n > u.len) return argRange("count", "Count must be positive and count must refer to a location within the string/array/collection.");
    for (u[@intCast(start)..][0..@intCast(n)], 0..) |c, i| {
        if (std.mem.indexOfScalar(u16, chars.items, c) != null) return start + @as(i32, @intCast(i));
    }
    return -1;
}

/// `s.Trim(chars)`, `TrimStart(chars)`, `TrimEnd(chars)`: no chars is white space
pub fn strTrimAny(s: String, comptime start: bool, comptime end: bool, chars: Array(u16)) Raised!String {
    const p = s orelse return nullRef();
    const u = p.units();
    const set = chars.items;
    var from: usize = 0;
    var to: usize = u.len;
    const trimmed_ = struct {
        pub fn is(c: u16, cs: []const u16) bool {
            return if (cs.len == 0) unicode.isWhiteSpace(c) else std.mem.indexOfScalar(u16, cs, c) != null;
        }
    };
    if (start) {
        while (from < to and trimmed_.is(u[from], set)) from += 1;
    }
    if (end) {
        while (to > from and trimmed_.is(u[to - 1], set)) to -= 1;
    }
    return strSlice(s, from, to - from);
}

/// `s.ToCharArray(start, length)`
pub fn strToCharsRange(s: String, start: i32, n: i32) Raised!Array(u16) {
    const p = s orelse return nullRef();
    const u = p.units();
    if (start < 0 or n < 0 or start + n > u.len) return argRange("startIndex", index_range);
    const items = rt.allocator.alloc(u16, @intCast(n)) catch rt.oom();
    @memcpy(items, u[@intCast(start)..][0..@intCast(n)]);
    return arrayFrom(Array(u16), items);
}

/// `String(chars, start, length)`
pub fn strOfCharsRange(chars: Array(u16), start: i32, n: i32) Raised!String {
    if (start < 0 or n < 0 or start + n > chars.items.len) return argRange("startIndex", index_range);
    return strFrom(chars.items[@intCast(start)..][0..@intCast(n)]);
}

/// `String.Join(separator, values, start, count)`
pub fn strJoinRange(sep: String, values: Array(String), start: i32, n: i32) Raised!String {
    if (start < 0 or n < 0 or start + n > values.items.len) return argRange("startIndex", index_range);
    var b: TextBuilder = .{};
    for (values.items[@intCast(start)..][0..@intCast(n)], 0..) |v, i| {
        if (i > 0) b.add(unitsOf(sep));
        b.add(unitsOf(v));
    }
    return b.finish();
}

fn strRangeSlices(a: String, ia: i32, b: String, ib: i32, length: i32) Raised!struct { xs: []const u16, ys: []const u16 } {
    if (ia < 0 or ib < 0 or length < 0) return argRange("length", "Value must be positive.");
    const x = unitsOf(a);
    const y = unitsOf(b);
    if ((a == null or b == null) and length != 0) return argRange("strA", "Specified argument was out of the range of valid values.");
    if (ia > x.len or ib > y.len) return argRange("indexA", "Specified argument was out of the range of valid values.");
    const xs = x[@intCast(ia)..];
    const ys = y[@intCast(ib)..];
    const n: usize = @intCast(length);
    return .{ .xs = xs[0..@min(xs.len, n)], .ys = ys[0..@min(ys.len, n)] };
}

/// `String.Compare(a, ia, b, ib, length, comparison)`: by code unit (and case), as .NET's
/// ordinal comparisons, which give the difference of the first units that differ
pub fn strCompareRange(a: String, ia: i32, b: String, ib: i32, length: i32, ignore_case: bool) Raised!i32 {
    if (a == null or b == null) {
        if (ia < 0 or ib < 0 or length < 0) return argRange("length", "Value must be positive.");
        if (length != 0) return argRange("strA", "Specified argument was out of the range of valid values.");
        return @as(i32, @intFromBool(a != null)) - @as(i32, @intFromBool(b != null));
    }
    const r = try strRangeSlices(a, ia, b, ib, length);
    for (r.xs[0..@min(r.xs.len, r.ys.len)], r.ys[0..@min(r.xs.len, r.ys.len)]) |c0, d0| {
        const c = if (ignore_case) unicode.toUpper(c0) else c0;
        const d = if (ignore_case) unicode.toUpper(d0) else d0;
        if (c != d) return @as(i32, c) - @as(i32, d);
    }
    return @as(i32, @intCast(r.xs.len)) - @as(i32, @intCast(r.ys.len));
}

pub fn strCompareCultureRange(a: String, ia: i32, b: String, ib: i32, length: i32, ignore_case: bool) Raised!i32 {
    if (a == null or b == null) {
        if (ia < 0 or ib < 0 or length < 0) return argRange("length", "Value must be positive.");
        if (length != 0) return argRange("strA", "Specified argument was out of the range of valid values.");
        return @as(i32, @intFromBool(a != null)) - @as(i32, @intFromBool(b != null));
    }
    const r = try strRangeSlices(a, ia, b, ib, length);
    return strCompareCultureUnits(r.xs, r.ys, ignore_case);
}

pub fn strCompareRangeWith(a: String, ia: i32, b: String, ib: i32, length: i32, how: i32) Raised!i32 {
    return switch (how) {
        0, 2 => strCompareCultureRange(a, ia, b, ib, length, false),
        1, 3 => strCompareCultureRange(a, ia, b, ib, length, true),
        4 => strCompareRange(a, ia, b, ib, length, false),
        5 => strCompareRange(a, ia, b, ib, length, true),
        else => argRange("comparisonType", "The string comparison type passed in is currently not supported."),
    };
}

/// `s.[lo..hi]`: what of it is inside the string
pub fn strSliceRange(s: String, lo: ?i32, hi: ?i32) Raised!String {
    const p = s orelse return nullRef();
    const len: i32 = @intCast(p.len);
    const from: i32 = @max(lo orelse 0, 0);
    const to: i32 = @min(hi orelse len - 1, len - 1);
    if (to < from) return str("");
    return strSlice(s, @intCast(from), @intCast(to - from + 1));
}

/// `Environment.NewLine`
pub fn newLine() String {
    return if (builtin.os.tag == .windows) str("\r\n") else str("\n");
}

pub fn isUnreserved(c: u8) bool {
    return std.ascii.isAlphanumeric(c) or c == '-' or c == '_' or c == '.' or c == '~';
}

/// `Uri.EscapeDataString s` (`uri`: `EscapeUriString`, which keeps what a URI uses as syntax)
pub fn uriEscape(s: String, comptime uri: bool) Raised!String {
    const p = s orelse return argNull("stringToEscape");
    var utf8: std.ArrayList(u8) = .empty;
    defer utf8.deinit(rt.allocator);
    var it = std.unicode.Utf16LeIterator.init(p.units());
    while (it.nextCodepoint() catch null) |cp| {
        var buf: [4]u8 = undefined;
        const n = std.unicode.utf8Encode(cp, &buf) catch 0;
        utf8.appendSlice(rt.allocator, buf[0..n]) catch rt.oom();
    }
    var b: TextBuilder = .{};
    for (utf8.items) |c| {
        const keep = isUnreserved(c) or (uri and std.mem.indexOfScalar(u8, ":/?#[]@!$&'()*+,;=", c) != null);
        if (keep) {
            b.addOne(c);
        } else {
            var hex: [3]u8 = undefined;
            _ = std.fmt.bufPrint(&hex, "%{X:0>2}", .{c}) catch unreachable;
            b.addAscii(&hex);
        }
    }
    return b.finish();
}

/// `Uri.UnescapeDataString s`: %XX sequences of UTF-8 decoded; anything else kept
pub fn uriUnescape(s: String) Raised!String {
    const p = s orelse return argNull("stringToUnescape");
    const u = p.units();
    var b: TextBuilder = .{};
    var i: usize = 0;
    while (i < u.len) {
        if (u[i] == '%') {
            var bytes: std.ArrayList(u8) = .empty;
            defer bytes.deinit(rt.allocator);
            var j = i;
            while (j + 2 < u.len + 0 and u[j] == '%' and j + 2 < u.len + 1) {
                if (j + 2 >= u.len) break;
                const hi = std.fmt.charToDigit(@intCast(@min(u[j + 1], 127)), 16) catch break;
                const lo = std.fmt.charToDigit(@intCast(@min(u[j + 2], 127)), 16) catch break;
                bytes.append(rt.allocator, hi * 16 + lo) catch rt.oom();
                j += 3;
            }
            if (bytes.items.len == 0) {
                b.addOne(u[i]);
                i += 1;
                continue;
            }
            if (std.unicode.utf8ValidateSlice(bytes.items)) {
                var view = std.unicode.Utf8View.initUnchecked(bytes.items).iterator();
                while (view.nextCodepoint()) |cp| {
                    if (cp >= 0x10000) {
                        const v = cp - 0x10000;
                        b.addOne(@intCast(0xD800 + (v >> 10)));
                        b.addOne(@intCast(0xDC00 + (v & 0x3FF)));
                    } else b.addOne(@intCast(cp));
                }
            } else {
                for (u[i..j]) |c| b.addOne(c);
            }
            i = j;
        } else {
            b.addOne(u[i]);
            i += 1;
        }
    }
    return b.finish();
}

/// `sb.[i]` / `sb.Chars(i)`
pub fn sbCharAt(sb: StringBuilder, i: i32) Raised!u16 {
    if (i < 0 or i >= sb.units.items.len) return raise(IndexOutOfRangeException, str("Index was outside the bounds of the array."));
    return sb.units.items[@intCast(i)];
}

/// `sb.[i] <- c`
pub fn sbSetChar(sb: StringBuilder, i: i32, c: u16) Raised!void {
    if (i < 0 or i >= sb.units.items.len) return raise(ArgumentOutOfRangeException, str("Index was out of range. Must be non-negative and less than the size of the collection. (Parameter 'index')"));
    sb.units.items[@intCast(i)] = c;
}

/// `sb.ToString(start, length)`
pub fn sbToStringRange(sb: StringBuilder, start: i32, n: i32) Raised!String {
    const u = sb.units.items;
    if (start < 0 or n < 0 or start + n > u.len) return argRange("startIndex", index_range);
    return strFrom(u[@intCast(start)..][0..@intCast(n)]);
}

/// `sb.Append(c, count)`
pub fn sbAppendRepeat(sb: StringBuilder, c: u16, n: i32) Raised!StringBuilder {
    if (n < 0) return argRange("repeatCount", "Count cannot be less than zero.");
    sb.units.appendNTimes(rt.allocator, c, @intCast(n)) catch rt.oom();
    return dup(sb);
}

/// `sb.Remove(start, length)`
pub fn sbRemove(sb: StringBuilder, start: i32, n: i32) Raised!StringBuilder {
    if (start < 0) return argRange("startIndex", "StartIndex cannot be less than zero.");
    if (n < 0) return argRange("length", "Length cannot be less than zero.");
    if (start + n > sb.units.items.len) return argRange("length", "Index was out of range. Must be non-negative and less than the size of the collection.");
    sb.units.replaceRangeAssumeCapacity(@intCast(start), @intCast(n), &.{});
    return dup(sb);
}

/// `sb.Length <- n`: cut, or padded with '\0'
pub fn sbSetLength(sb: StringBuilder, n: i32) Raised!void {
    if (n < 0) return argRange("value", "Length cannot be less than zero.");
    const len: usize = @intCast(n);
    if (len <= sb.units.items.len) {
        sb.units.shrinkRetainingCapacity(len);
    } else {
        sb.units.appendNTimes(rt.allocator, 0, len - sb.units.items.len) catch rt.oom();
    }
}

/// `sb.Replace(oldChar, newChar)`
pub fn sbReplaceChar(sb: StringBuilder, old: u16, new_: u16) StringBuilder {
    for (sb.units.items) |*c| {
        if (c.* == old) c.* = new_;
    }
    return dup(sb);
}

/// `sb.Replace(old, new)`
pub fn sbReplace(sb: StringBuilder, old: String, new_: String) Raised!StringBuilder {
    const o = unitsOf(old);
    if (o.len == 0) return raise(ArgumentException, str("String cannot be of zero length. (Parameter 'oldValue')"));
    var out: std.ArrayList(u16) = .empty;
    const u = sb.units.items;
    var i: usize = 0;
    while (i < u.len) {
        if (i + o.len <= u.len and std.mem.eql(u16, u[i..][0..o.len], o)) {
            out.appendSlice(rt.allocator, unitsOf(new_)) catch rt.oom();
            i += o.len;
        } else {
            out.append(rt.allocator, u[i]) catch rt.oom();
            i += 1;
        }
    }
    sb.units.deinit(rt.allocator);
    sb.units = out;
    return dup(sb);
}

pub fn foldUnits(a: []const u16, b: []const u16) bool {
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

pub fn strIndexOfCharIgnoreCase(s: String, c: u16) Raised!i32 {
    const p = s orelse return nullRef();
    const cu = unicode.toUpper(c);
    for (p.units(), 0..) |u, i| {
        if (unicode.toUpper(u) == cu) return @intCast(i);
    }
    return -1;
}

pub fn strStartsWithOpt(s: String, value: String, ignore_case: bool) Raised!bool {
    return if (ignore_case) strStartsWithIgnoreCase(s, value) else rt.strStartsWith(s, value);
}

pub fn strEndsWithOpt(s: String, value: String, ignore_case: bool) Raised!bool {
    return if (ignore_case) strEndsWithIgnoreCase(s, value) else rt.strEndsWith(s, value);
}

// The base weights of ASCII in .NET's InvariantCulture order (punctuation and symbols <
// digits < letters, case folded).
const ascii_primary: [128]u8 = blk: {
    @setEvalBranchQuota(10000);
    var tbl: [128]u8 = @splat(0);
    var w: u8 = 0;
    for (0..32) |i| {
        tbl[i] = w;
        w += 1;
    }
    tbl[127] = w;
    w += 1;
    const order = " _-,;:!?.'\"()[]{}@*/\\&#%`^+<=>|~$0123456789";
    for (order) |c| {
        tbl[c] = w;
        w += 1;
    }
    for ('a'..'z' + 1) |c| {
        tbl[c] = w;
        tbl[c - 'a' + 'A'] = w;
        w += 1;
    }
    break :blk tbl;
};

const collation = @import("fable_collation.zig");

/// One collation element: its base weight, its accent rank, its case (lower before upper)
const CollElem = struct { primary: u32, secondary: u8, tertiary: u8 };

/// The collation elements of a string, one by one: ignorable chars give none, a char like Æ
/// gives two (A, E)
/// the base weight of an ASCII char (room after each for the letters sorted after it)
fn base(c: u8) u32 {
    return @as(u32, ascii_primary[c]) * 256;
}

const CollIter = struct {
    units: []const u16,
    i: usize = 0,
    pending: ?CollElem = null,

    fn next(it: *CollIter) ?CollElem {
        if (it.pending) |e| {
            it.pending = null;
            return e;
        }
        while (it.i < it.units.len) {
            const c = it.units[it.i];
            it.i += 1;
            if (c < collation.latin_coll.len) {
                const e = collation.latin_coll[c];
                const t: u8 = e.ter;
                switch (e.kind) {
                    1 => continue,
                    2 => {
                        if (e.b1 != 0) it.pending = .{ .primary = base(e.b1), .secondary = 0, .tertiary = t };
                        return .{ .primary = base(e.b0), .secondary = e.sec, .tertiary = t };
                    },
                    3 => return .{ .primary = base(e.b0) + e.sec, .secondary = 0, .tertiary = t },
                    else => if (c < 128) return .{ .primary = base(@intCast(c)), .secondary = 0, .tertiary = 0 },
                }
            }
            // (other scripts: by the code point of the upper case, after the Latin letters)
            const upper = unicode.toUpper(c);
            return .{ .primary = 0x10000 + @as(u32, upper), .secondary = 0, .tertiary = @intFromBool(upper == c and unicode.toLower(c) != c) };
        }
        return null;
    }
};

fn collLevel(x: []const u16, y: []const u16, comptime level: u2) i32 {
    var a: CollIter = .{ .units = x };
    var b: CollIter = .{ .units = y };
    while (true) {
        const ea = a.next();
        const eb = b.next();
        if (ea == null and eb == null) return 0;
        if (ea == null) return -1;
        if (eb == null) return 1;
        const wa: u32 = switch (level) {
            0 => ea.?.primary,
            1 => ea.?.secondary,
            else => ea.?.tertiary,
        };
        const wb: u32 = switch (level) {
            0 => eb.?.primary,
            1 => eb.?.secondary,
            else => eb.?.tertiary,
        };
        if (wa != wb) return if (wa < wb) -1 else 1;
    }
}

/// InvariantCulture ordering of two UTF-16 unit slices, as .NET's: the base letters first
/// (punctuation < digits < letters, control chars ignored), then accents, then case (lower
/// before upper) unless it is ignored. Latin (U+0000..U+024F) is .NET's, from a table made
/// with .NET; other scripts are ordered by code point.
pub fn strCompareCultureUnits(x: []const u16, y: []const u16, ignore_case: bool) i32 {
    const p = collLevel(x, y, 0);
    if (p != 0) return p;
    const s = collLevel(x, y, 1);
    if (s != 0 or ignore_case) return s;
    return collLevel(x, y, 2);
}

pub fn strCompareCulture(a: String, b: String, ignore_case: bool) i32 {
    if (a == null or b == null) return @as(i32, @intFromBool(a != null)) - @as(i32, @intFromBool(b != null));
    return strCompareCultureUnits(unitsOf(a), unitsOf(b), ignore_case);
}

pub fn strCompareTo(a: String, b: String) Raised!i32 {
    const p = a orelse return nullRef();
    if (b == null) return 1;
    return strCompareCultureUnits(p.units(), unitsOf(b), false);
}

pub fn strCompareWith(a: String, b: String, how: i32) Raised!i32 {
    return switch (how) {
        0, 2 => strCompareCulture(a, b, false),
        1, 3 => strCompareCulture(a, b, true),
        4 => rt.strCompare(a, b),
        5 => strCompareIgnoreCase(a, b),
        else => argRange("comparisonType", "The string comparison type passed in is currently not supported."),
    };
}

/// `Path.GetFileName path`: what follows the last directory separator (`/`, and `\\` on Windows).
pub fn pathFileName(path: String) String {
    const u = unitsOf(path);
    var i = u.len;
    while (i > 0) : (i -= 1) {
        const c = u[i - 1];
        if (c == '/' or (builtin.os.tag == .windows and c == '\\')) break;
    }
    if (path == null) return null;
    return strSlice(path, i, u.len - i);
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
