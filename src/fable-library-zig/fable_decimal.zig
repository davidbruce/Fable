//! decimal: .NET's System.Decimal, a value: a whole number below 2^96 and a scale of 0 to 28 (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");
const ArgumentException = rt.ArgumentException;
const ArgumentNullException = rt.ArgumentNullException;
const ArgumentOutOfRangeException = rt.ArgumentOutOfRangeException;
const Array = rt.Array;
const Decimal = rt.Decimal;
const DivideByZeroException = rt.DivideByZeroException;
const OverflowException = rt.OverflowException;
const Raised = rt.Raised;
const Spec = rt.Spec;
const String = rt.String;
const Text = rt.Text;
const arrayFrom = rt.arrayFrom;
const badFormat = rt.badFormat;
const isBigInt = rt.isBigInt;
const netIntName = rt.netIntName;
const raise = rt.raise;
const str = rt.str;
const strNew = rt.strNew;
const trimmed = rt.trimmed;
const numberText = rt.numberText;

// ---------------------------------------------------------------------------------------------
// decimal: .NET's System.Decimal, a value: a whole number below 2^96 and a scale of 0 to 28
// (the number of digits after the point). Results are rounded to fit, a tie to the even digit,
// as .NET does; a result too large raises OverflowException.
// ---------------------------------------------------------------------------------------------

pub const NetDecimal = struct {
    pub const fable_decimal = {};
    /// the value times 10^scale; its magnitude is below 2^96
    m: i128 = 0,
    scale: u8 = 0,
};

pub const dec_max: u256 = (1 << 96) - 1;

pub fn isDecimal(comptime T: type) bool {
    return T == NetDecimal;
}

/// Does a value that holds no cell hold a decimal (so that it is compared by value, not bits)?
pub fn holdsDecimal(comptime T: type) bool {
    if (T == NetDecimal) return true;
    switch (@typeInfo(T)) {
        .optional => |o| return holdsDecimal(o.child),
        .@"struct" => |s| {
            inline for (s.field_types) |F| {
                if (holdsDecimal(F)) return true;
            }
            return false;
        },
        .@"union" => |u| {
            inline for (u.field_types) |F| {
                if (holdsDecimal(F)) return true;
            }
            return false;
        },
        .array => |a| return holdsDecimal(a.child),
        else => return false,
    }
}

pub fn decOverflow() Raised {
    return raise(OverflowException, str("Value was either too large or too small for a Decimal."));
}

pub fn pow10(n: u32) u256 {
    var r: u256 = 1;
    var i: u32 = 0;
    while (i < n) : (i += 1) r *= 10;
    return r;
}

/// m / 10^k rounded to the nearest; a tie goes to the even number, or away from zero
pub fn divRound(m: u256, k: u32, even: bool) u256 {
    if (k == 0) return m;
    if (k > 76) return 0;
    const p = pow10(k);
    var q = m / p;
    const r = m % p;
    const half = p / 2;
    if (r > half or (r == half and (!even or q & 1 == 1))) q += 1;
    return q;
}

pub fn decMake(negative: bool, mag: u256, scale: u32) NetDecimal {
    const m: i128 = @intCast(mag);
    return .{ .m = if (negative) -m else m, .scale = @intCast(scale) };
}

/// The decimal of a sign, a magnitude and a scale of any size: digits are dropped from the end,
/// rounding, until it fits.
pub fn decFit(negative: bool, mag: u256, scale: u32) Raised!NetDecimal {
    var k: u32 = if (scale > 28) scale - 28 else 0;
    while (true) : (k += 1) {
        const q = divRound(mag, k, true);
        if (q <= dec_max) {
            if (k > scale) return decOverflow();
            return decMake(negative, q, scale - k);
        }
        if (k >= scale) return decOverflow();
    }
}

pub fn decMag(d: NetDecimal) u256 {
    return @intCast(@abs(d.m));
}

/// both values at the larger scale, signed
pub fn decAligned(a: NetDecimal, b: NetDecimal) struct { i256, i256, u32 } {
    const s: u32 = @max(a.scale, b.scale);
    const x: i256 = @as(i256, a.m) * @as(i256, @intCast(pow10(s - a.scale)));
    const y: i256 = @as(i256, b.m) * @as(i256, @intCast(pow10(s - b.scale)));
    return .{ x, y, s };
}

/// a decimal literal
/// `Decimal(lo, mid, hi, isNegative, scale)`
pub fn decOfParts(lo: i32, mid: i32, hi: i32, negative: bool, scale: u8) Raised!NetDecimal {
    if (scale > 28) return raise(ArgumentOutOfRangeException, str("Decimal's scale value must be between 0 and 28, inclusive. (Parameter 'scale')"));
    const mag: i128 = (@as(i128, @as(u32, @bitCast(hi))) << 64) | (@as(i128, @as(u32, @bitCast(mid))) << 32) | @as(i128, @as(u32, @bitCast(lo)));
    return .{ .m = if (negative) -mag else mag, .scale = scale };
}

/// `Decimal(bits)`: the four ints of `Decimal.GetBits`
pub fn decOfBits(bits: Array(i32)) Raised!NetDecimal {
    const b = bits.items;
    if (b.len != 4 or b[3] & 0x7F00FFFF != 0) return raise(ArgumentException, str("Decimal constructor requires an array or span of four valid decimal bytes."));
    const flags: u32 = @bitCast(b[3]);
    return decOfParts(b[0], b[1], b[2], flags & 0x80000000 != 0, @intCast((flags >> 16) & 0xFF));
}

/// `Decimal.GetBits d`: the 96 bits of the magnitude, then the sign and the scale
pub fn decGetBits(d: NetDecimal) Array(i32) {
    const mag: u128 = @intCast(@abs(d.m));
    const items = rt.alloc().alloc(i32, 4) catch rt.oom();
    items[0] = @bitCast(@as(u32, @truncate(mag)));
    items[1] = @bitCast(@as(u32, @truncate(mag >> 32)));
    items[2] = @bitCast(@as(u32, @truncate(mag >> 64)));
    const sign: u32 = if (d.m < 0) 0x80000000 else 0;
    items[3] = @bitCast(sign | (@as(u32, d.scale) << 16));
    return arrayFrom(Array(i32), items);
}

test "decimal bits" {
    const d = try decOfParts(-1, -1, -2, true, 0);
    const bits = decGetBits(d);
    try std.testing.expectEqual(@as(i32, -1), bits.items[0]);
    try std.testing.expectEqual(@as(i32, -2), bits.items[2]);
    try std.testing.expectEqual(@as(i32, @bitCast(@as(u32, 0x80000000))), bits.items[3]);
    try std.testing.expect(std.meta.eql(d, try decOfBits(bits)));
}

pub fn decLit(comptime m: i128, comptime scale: u8) NetDecimal {
    return .{ .m = m, .scale = scale };
}

pub fn decAdd(a: NetDecimal, b: NetDecimal) Raised!NetDecimal {
    const x, const y, const s = decAligned(a, b);
    const sum = x + y;
    return decFit(sum < 0, @intCast(@abs(sum)), s);
}

pub fn decSub(a: NetDecimal, b: NetDecimal) Raised!NetDecimal {
    return decAdd(a, .{ .m = -b.m, .scale = b.scale });
}

pub fn decMul(a: NetDecimal, b: NetDecimal) Raised!NetDecimal {
    return decFit((a.m < 0) != (b.m < 0), decMag(a) * decMag(b), @as(u32, a.scale) + b.scale);
}

pub fn decDiv(a: NetDecimal, b: NetDecimal) Raised!NetDecimal {
    if (b.m == 0) return raise(DivideByZeroException, str("Attempted to divide by zero."));
    const negative = (a.m < 0) != (b.m < 0);
    var num = decMag(a);
    const den = decMag(b);
    var scale: i32 = @as(i32, a.scale) - @as(i32, b.scale);
    if (scale < 0) {
        num *= pow10(@intCast(-scale));
        scale = 0;
    }
    var q = num / den;
    var r = num % den;
    if (q > dec_max) return decOverflow();
    // (as many digits as fit)
    while (r != 0 and scale < 28) {
        const next = q * 10 + (r * 10) / den;
        if (next > dec_max) break;
        q = next;
        r = (r * 10) % den;
        scale += 1;
    }
    if (r != 0 and (2 * r > den or (2 * r == den and q & 1 == 1))) {
        q += 1;
        if (q > dec_max) return decFit(negative, q, @intCast(scale));
    }
    // (a quotient that rounds to nothing is .NET's plain 0)
    if (q == 0 and decMag(a) != 0) return decMake(false, 0, 0);
    return decMake(negative, q, @intCast(scale));
}

/// `a % b`: what is left after a whole number of `b`, with the sign of `a`
pub fn decRem(a: NetDecimal, b: NetDecimal) Raised!NetDecimal {
    if (b.m == 0) return raise(DivideByZeroException, str("Attempted to divide by zero."));
    // (.NET's: a dividend smaller than the divisor is the remainder as it is, its scale kept)
    if (decMag(a) * pow10(b.scale) < decMag(b) * pow10(a.scale)) return a;
    const x, const y, const s = decAligned(a, b);
    const r = @rem(x, y);
    return decFit(r < 0, @intCast(@abs(r)), s);
}

pub fn decNeg(a: NetDecimal) NetDecimal {
    return .{ .m = -a.m, .scale = a.scale };
}

pub fn decAbs(a: NetDecimal) NetDecimal {
    return .{ .m = @intCast(@abs(a.m)), .scale = a.scale };
}

pub fn decSign(a: NetDecimal) i32 {
    return if (a.m > 0) 1 else if (a.m < 0) -1 else 0;
}

pub fn decCompare(a: NetDecimal, b: NetDecimal) i32 {
    const x, const y, _ = decAligned(a, b);
    return if (x < y) -1 else if (x > y) 1 else 0;
}

pub fn decNormal(a: NetDecimal) NetDecimal {
    var d = a;
    while (d.scale > 0 and @rem(d.m, 10) == 0) {
        d.m = @divTrunc(d.m, 10);
        d.scale -= 1;
    }
    if (d.m == 0) d.scale = 0;
    return d;
}

pub fn decHash(a: NetDecimal) i32 {
    const d = decNormal(a);
    const u: u128 = @bitCast(d.m);
    return @bitCast(@as(u32, @truncate(u)) ^ @as(u32, @truncate(u >> 32)) ^ @as(u32, @truncate(u >> 64)) ^ (@as(u32, d.scale) << 24));
}

/// `decimal x` of a whole number
pub fn decOf(x: anytype) Raised!NetDecimal {
    const T = @TypeOf(x);
    if (comptime @typeInfo(T) == .float or @typeInfo(T) == .comptime_float) return decOfFloat(x);
    if (comptime isBigInt(T)) {
        const v = x.value.toInt(i128) catch return decOverflow();
        if (@abs(v) > dec_max) return decOverflow();
        return .{ .m = v };
    }
    if (@abs(@as(i256, x)) > dec_max) return decOverflow();
    return .{ .m = @intCast(x) };
}

/// `decimal x` of a float: rounded to 15 significant digits (7 for a float32), as .NET does
pub fn decOfFloat(x: anytype) Raised!NetDecimal {
    const f: f64 = x;
    if (std.math.isNan(f) or std.math.isInf(f) or @abs(f) >= 7.9228162514264338e28) return decOverflow();
    if (f == 0) return .{};
    var d = Decimal.exact(@abs(f));
    d.round(if (@TypeOf(x) == f32) 7 else 15);
    var mag: u256 = 0;
    for (d.digits[0..d.len]) |c| mag = mag * 10 + c;
    const exp: i32 = d.point - @as(i32, @intCast(d.len));
    var r: NetDecimal = undefined;
    if (exp >= 0) {
        r = try decFit(false, mag * pow10(@intCast(exp)), 0);
    } else {
        r = try decFit(false, mag, @intCast(-exp));
    }
    r = decNormal(r);
    if (f < 0) r.m = -r.m;
    return r;
}

/// `int x` of a decimal: the whole part; one that does not fit raises
pub fn decToInt(comptime T: type, a: NetDecimal) Raised!T {
    const w = @divTrunc(a.m, @as(i128, @intCast(pow10(a.scale))));
    if (w < std.math.minInt(T) or w > std.math.maxInt(T)) return raise(OverflowException, str("Value was either too large or too small for " ++ netIntName(T) ++ "."));
    return @intCast(w);
}

pub fn decToFloat(comptime T: type, a: NetDecimal) T {
    var buf: [40]u8 = undefined;
    const text = decAscii(a, &buf);
    return std.fmt.parseFloat(T, text) catch unreachable;
}

/// `pown d n`: by repeated multiplication, as FSharp.Core's; a negative power divides 1 by it
pub fn decPown(a: NetDecimal, n: i32) Raised!NetDecimal {
    var result = decLit(1, 0);
    var k: i32 = if (n < 0) -n else n;
    while (k > 0) : (k -= 1) result = try decMul(result, a);
    if (n < 0) return decDiv(decLit(1, 0), result);
    return result;
}

/// `Math.Round(d, digits)`: a tie to the even digit, or away from zero
pub fn decRound(a: NetDecimal, digits: i32, even: bool) NetDecimal {
    if (digits < 0 or a.scale <= digits) return a;
    const k: u32 = a.scale - @as(u32, @intCast(digits));
    return decMake(a.m < 0, divRound(decMag(a), k, even), @intCast(digits));
}

/// `Math.Round(d, digits, mode)` with .NET's MidpointRounding: ToEven (0), AwayFromZero (1),
/// ToZero (2), ToNegativeInfinity (3), ToPositiveInfinity (4)
pub fn decRoundMode(a: NetDecimal, digits: i32, mode: i32) Raised!NetDecimal {
    if (digits < 0 or digits > 28) return raise(rt.ArgumentOutOfRangeException, str("Decimal can only round to between 0 and 28 digits of precision. (Parameter 'decimals')"));
    if (mode < 0 or mode > 4) return raise(rt.ArgumentException, rt.format(.{ "The value '", mode, "' is not valid for this usage of the type MidpointRounding. (Parameter 'mode')" }));
    if (mode <= 1) return decRound(a, digits, mode == 0);
    if (a.scale <= digits) return a;
    const k: u32 = a.scale - @as(u32, @intCast(digits));
    const p = pow10(k);
    var q = decMag(a) / p;
    const exact = decMag(a) % p == 0;
    if (!exact) {
        if ((mode == 3 and a.m < 0) or (mode == 4 and a.m > 0)) q += 1;
    }
    return decMake(a.m < 0, q, @intCast(digits));
}

/// `floor`, `ceil` (`up`) and `truncate` (neither)
pub fn decWhole(a: NetDecimal, comptime how: enum { down, up, toward_zero }) NetDecimal {
    const p = pow10(a.scale);
    var q = decMag(a) / p;
    const exact = decMag(a) % p == 0;
    if (!exact) switch (how) {
        .down => if (a.m < 0) {
            q += 1;
        },
        .up => if (a.m > 0) {
            q += 1;
        },
        .toward_zero => {},
    };
    return decMake(a.m < 0, q, 0);
}

/// The text of a decimal, as `ToString()` writes it: every digit of its scale.
pub fn decAscii(a: NetDecimal, out: []u8) []const u8 {
    var digits: [40]u8 = undefined;
    const ds = std.fmt.bufPrint(&digits, "{d}", .{@abs(a.m)}) catch unreachable;
    var n: usize = 0;
    if (a.m < 0) {
        out[n] = '-';
        n += 1;
    }
    if (ds.len <= a.scale) {
        out[n] = '0';
        n += 1;
        if (a.scale > 0) {
            out[n] = '.';
            n += 1;
            var z = a.scale - ds.len;
            while (z > 0) : (z -= 1) {
                out[n] = '0';
                n += 1;
            }
            @memcpy(out[n .. n + ds.len], ds);
            n += ds.len;
        }
    } else {
        const whole = ds.len - a.scale;
        @memcpy(out[n .. n + whole], ds[0..whole]);
        n += whole;
        if (a.scale > 0) {
            out[n] = '.';
            n += 1;
            @memcpy(out[n .. n + a.scale], ds[whole..]);
            n += a.scale;
        }
    }
    return out[0..n];
}

pub fn decText(a: NetDecimal) String {
    var buf: [40]u8 = undefined;
    const t = decAscii(a, &buf);
    const s, const u = strNew(t.len);
    for (t, u) |c, *o| o.* = c;
    return s;
}

/// the digits of a decimal for .NET's formats: 0.d0 d1 ... x 10^point
pub fn decDigits(a: NetDecimal) Decimal {
    var d: Decimal = .{};
    if (a.m == 0) return d;
    const text = std.fmt.bufPrint(&d.digits, "{d}", .{@abs(a.m)}) catch unreachable;
    for (d.digits[0..text.len]) |*c| c.* -= '0';
    d.len = text.len;
    d.point = @as(i32, @intCast(text.len)) - a.scale;
    // (without the zeros at the end)
    while (d.len > 0 and d.digits[d.len - 1] == 0) d.len -= 1;
    return d;
}

/// The text of a decimal for an F# format specifier (`%M`, `%f`, `%g`, `string d`).
pub fn decSpecText(comptime spec: Spec, a: NetDecimal, out: []u8) []const u8 {
    switch (spec.kind) {
        'f', 'F', 'e', 'E' => {
            const precision: i32 = @min(spec.precision orelse 6, 80);
            var t: Text = .{ .buf = out };
            if (a.m < 0) t.put('-') else if (spec.plus) t.put('+') else if (spec.space) t.put(' ');
            var d = decDigits(a);
            if (spec.kind == 'f' or spec.kind == 'F') {
                d.roundTo(d.point + precision, false);
                var i: i32 = @min(d.point, 1) - 1;
                while (i < d.point) : (i += 1) t.put(d.digit(i));
                if (precision > 0) {
                    t.put('.');
                    var k: i32 = 0;
                    while (k < precision) : (k += 1) t.put(d.digit(d.point + k));
                }
            } else {
                d.roundTo(precision + 1, false);
                t.put(d.digit(0));
                if (precision > 0) {
                    t.put('.');
                    var k: i32 = 1;
                    while (k <= precision) : (k += 1) t.put(d.digit(k));
                }
                t.exponent(spec.kind, d.point - 1, 3);
            }
            return out[0..t.len];
        },
        'g', 'G' => {
            var t: Text = .{ .buf = out };
            if (a.m < 0) t.put('-') else if (spec.plus) t.put('+') else if (spec.space) t.put(' ');
            var d = decDigits(a);
            if (spec.precision) |p| d.roundTo(@max(p, 1), false);
            if (d.len == 0) t.put('0') else t.general(&d, 29, if (spec.kind == 'g') 'e' else 'E');
            return out[0..t.len];
        },
        else => {
            if (spec.plus and a.m >= 0) {
                out[0] = '+';
                return out[0 .. 1 + decAscii(a, out[1..]).len];
            }
            return decAscii(a, out);
        },
    }
}

/// `Decimal.Parse s` (`fsharp`: F#'s `decimal s`, which also reads an exponent)
pub fn decParse(s: String, comptime fsharp: bool) Raised!NetDecimal {
    if (s == null) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 's')"));
    return decRead(numberText(s), fsharp) catch |e| switch (e) {
        error.Format => badFormat(s),
        error.Raised => error.Raised,
    };
}

/// `Decimal.Parse(s, style)` and `Decimal.TryParse(s, style, provider, &v)`
pub fn decParseStyle(s: String, style: i32) Raised!NetDecimal {
    if (s == null) return raise(ArgumentNullException, str("Value cannot be null. (Parameter 's')"));
    return decReadStyle(s, style) catch |e| switch (e) {
        error.Format => badFormat(s),
        error.Raised => error.Raised,
    };
}

pub fn decTryParseStyle(s: String, style: i32) ?NetDecimal {
    if (s == null) return null;
    return decReadStyle(s, style) catch |e| {
        if (e == error.Raised) rt.drop(rt.take());
        return null;
    };
}

fn decReadStyle(s: String, style: i32) (error{Format} || Raised)!NetDecimal {
    var buf: [400]u8 = undefined;
    const text = rt.numberStyled(rt.unitsOf(s), style, &buf) orelse return error.Format;
    var units: [400]u16 = undefined;
    for (text, 0..) |c, i| units[i] = c;
    return decRead(units[0..text.len], true);
}

pub fn decRead(u: []const u16, comptime fsharp: bool) (error{Format} || Raised)!NetDecimal {
    var i: usize = 0;
    var negative = false;
    if (i < u.len and (u[i] == '-' or u[i] == '+')) {
        negative = u[i] == '-';
        i += 1;
    }
    var mag: u256 = 0;
    var significant: u32 = 0;
    var exp: i32 = 0;
    var any = false;
    var seen_point = false;
    while (i < u.len) : (i += 1) {
        const c = u[i];
        if (c >= '0' and c <= '9') {
            any = true;
            if (significant < 60) {
                mag = mag * 10 + (c - '0');
                if (mag != 0) significant += 1;
                if (seen_point) exp -= 1;
            } else {
                if (!seen_point) exp += 1;
            }
        } else if (c == '.' and !seen_point) {
            seen_point = true;
        } else if (c == ',' and !fsharp and !seen_point and any) {
            // (a group separator)
        } else break;
    }
    if (!any) return error.Format;
    // (.NET's NumberStyles.Number: a sign after the digits, where none came before)
    if (!fsharp and i < u.len and (u[i] == '-' or u[i] == '+') and !(u.len > 0 and (u[0] == '-' or u[0] == '+'))) {
        negative = u[i] == '-';
        i += 1;
    }
    if (fsharp and i < u.len and (u[i] == 'e' or u[i] == 'E')) {
        i += 1;
        var eneg = false;
        if (i < u.len and (u[i] == '-' or u[i] == '+')) {
            eneg = u[i] == '-';
            i += 1;
        }
        var e: i32 = 0;
        var digits = false;
        while (i < u.len and u[i] >= '0' and u[i] <= '9') : (i += 1) {
            e = @min(e * 10 + @as(i32, u[i] - '0'), 10000);
            digits = true;
        }
        if (!digits) return error.Format;
        exp += if (eneg) -e else e;
    }
    if (i != u.len) return error.Format;
    // (zero keeps the digits written after its point)
    if (mag == 0) return .{ .scale = if (exp < 0) @intCast(@min(-exp, 28)) else 0 };
    if (exp >= 0) {
        if (exp > 29) return decOverflow();
        const big = mag * pow10(@intCast(exp));
        if (big > dec_max) return decOverflow();
        return decMake(negative, big, 0);
    }
    if (-exp > 76) return .{};
    return decFit(negative, mag, @intCast(-exp));
}
