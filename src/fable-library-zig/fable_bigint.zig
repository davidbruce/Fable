//! bigint: F#'s arbitrary-precision integer, a counted cell of Zig's big integer (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const rt = @import("fable_rt.zig");
const ArgumentOutOfRangeException = rt.ArgumentOutOfRangeException;
const DivideByZeroException = rt.DivideByZeroException;
const FormatException = rt.FormatException;
const OverflowException = rt.OverflowException;
const Raised = rt.Raised;
const String = rt.String;
const expectAny = rt.expectAny;
const isDecimal = rt.isDecimal;
const netIntName = rt.netIntName;
const raise = rt.raise;
const str = rt.str;
const strNew = rt.strNew;
const thread = rt.thread;
const track = rt.track;
const trimmed = rt.trimmed;

// ---------------------------------------------------------------------------------------------
// bigint: F#'s arbitrary-precision integer, a counted cell of Zig's big integer
// ---------------------------------------------------------------------------------------------

pub const Big = std.math.big.int.Managed;

pub const BigInt = *struct {
    pub const fable_bigint = {};
    @"$rc": u32 = 1,
    value: Big,

    pub fn fable_free(c: anytype) void {
        c.value.deinit();
    }
};

pub fn isBigInt(comptime T: type) bool {
    return T == BigInt;
}

pub fn bigOom(_: anyerror) noreturn {
    rt.oom();
}

pub fn bigEmpty() Big {
    return Big.init(rt.allocator) catch |e| bigOom(e);
}

pub fn bigFrom(m: Big) BigInt {
    const c = rt.allocator.create(@typeInfo(BigInt).pointer.child) catch rt.oom();
    c.* = .{ .value = m };
    if (track) thread.stats.allocs += 1;
    return c;
}

/// `bigint x` of a whole number
pub fn bigOf(x: anytype) BigInt {
    var m = bigEmpty();
    const T = @TypeOf(x);
    if (comptime isDecimal(T)) {
        // (a decimal: its whole part)
        var whole = x.m;
        var i: u8 = 0;
        while (i < x.scale) : (i += 1) whole = @divTrunc(whole, 10);
        m.set(whole) catch |e| bigOom(e);
        return bigFrom(m);
    }
    switch (@typeInfo(T)) {
        .float, .comptime_float => {
            // (its whole part: the bits of the mantissa, shifted by the exponent)
            const t: f64 = @trunc(@as(f64, x));
            if (@abs(t) < 1.0e18) {
                m.set(@as(i64, @intFromFloat(t))) catch |e| bigOom(e);
            } else {
                const bits: u64 = @bitCast(t);
                const exp: i32 = @as(i32, @intCast((bits >> 52) & 0x7ff)) - 1075;
                const mant: u64 = (bits & ((1 << 52) - 1)) | (1 << 52);
                m.set(mant) catch |e| bigOom(e);
                if (exp > 0) m.shiftLeft(&m, @intCast(exp)) catch |e| bigOom(e);
                if (t < 0) m.negate();
            }
        },
        else => m.set(x) catch |e| bigOom(e),
    }
    return bigFrom(m);
}

/// `123456789012345678901234567890I`
pub fn bigLit(comptime digits: []const u8) BigInt {
    var m = bigEmpty();
    m.setString(10, digits) catch |e| bigOom(e);
    return bigFrom(m);
}

pub fn bigAdd(a: BigInt, b: BigInt) BigInt {
    var m = bigEmpty();
    m.add(&a.value, &b.value) catch |e| bigOom(e);
    return bigFrom(m);
}

pub fn bigSub(a: BigInt, b: BigInt) BigInt {
    var m = bigEmpty();
    m.sub(&a.value, &b.value) catch |e| bigOom(e);
    return bigFrom(m);
}

pub fn bigMul(a: BigInt, b: BigInt) BigInt {
    var m = bigEmpty();
    m.mul(&a.value, &b.value) catch |e| bigOom(e);
    return bigFrom(m);
}

/// `a / b` (`quotient`) and `a % b`: truncated, as .NET
pub fn bigDivRem(a: BigInt, b: BigInt, comptime quotient: bool) Raised!BigInt {
    if (b.value.eqlZero()) return raise(DivideByZeroException, str("Attempted to divide by zero."));
    var q = bigEmpty();
    var r = bigEmpty();
    Big.divTrunc(&q, &r, &a.value, &b.value) catch |e| bigOom(e);
    if (quotient) {
        r.deinit();
        return bigFrom(q);
    }
    q.deinit();
    return bigFrom(r);
}

pub fn bigAnd(a: BigInt, b: BigInt) BigInt {
    var m = bigEmpty();
    m.bitAnd(&a.value, &b.value) catch |e| bigOom(e);
    return bigFrom(m);
}

pub fn bigOr(a: BigInt, b: BigInt) BigInt {
    var m = bigEmpty();
    m.bitOr(&a.value, &b.value) catch |e| bigOom(e);
    return bigFrom(m);
}

pub fn bigXor(a: BigInt, b: BigInt) BigInt {
    var m = bigEmpty();
    m.bitXor(&a.value, &b.value) catch |e| bigOom(e);
    return bigFrom(m);
}

/// `a <<< n` (a negative `n` shifts right, as .NET)
pub fn bigShl(a: BigInt, n: i32) BigInt {
    if (n < 0) return bigShr(a, -n);
    var m = bigEmpty();
    m.shiftLeft(&a.value, @intCast(n)) catch |e| bigOom(e);
    return bigFrom(m);
}

/// `a >>> n`: arithmetic, rounding toward negative infinity as .NET
pub fn bigShr(a: BigInt, n: i32) BigInt {
    if (n < 0) return bigShl(a, -n);
    var m = bigEmpty();
    m.shiftRight(&a.value, @intCast(n)) catch |e| bigOom(e);
    return bigFrom(m);
}

test "bigint bitwise" {
    try expectAny("2", bigAnd(bigOf(@as(i32, 6)), bigOf(@as(i32, 2))));
    try expectAny("6", bigOr(bigOf(@as(i32, 4)), bigOf(@as(i32, 2))));
    try expectAny("4", bigXor(bigOf(@as(i32, 6)), bigOf(@as(i32, 2))));
    try expectAny("16", bigShl(bigOf(@as(i32, 4)), 2));
    try expectAny("-3", bigShr(bigOf(@as(i32, -5)), 1));
    try expectAny("-6", bigAnd(bigOf(@as(i32, -5)), bigOf(@as(i32, -2))));
}

pub fn bigNeg(a: BigInt) BigInt {
    var m = a.value.clone() catch |e| bigOom(e);
    m.negate();
    return bigFrom(m);
}

pub fn bigAbs(a: BigInt) BigInt {
    var m = a.value.clone() catch |e| bigOom(e);
    m.abs();
    return bigFrom(m);
}

/// `BigInteger.Pow(a, n)` and `pown a n`
pub fn bigPow(a: BigInt, n: i32) Raised!BigInt {
    if (n < 0) return raise(ArgumentOutOfRangeException, str("The number must be greater than or equal to zero. (Parameter 'exponent')"));
    var m = bigEmpty();
    m.pow(&a.value, @intCast(n)) catch |e| bigOom(e);
    return bigFrom(m);
}

pub fn bigCompare(a: BigInt, b: BigInt) i32 {
    return switch (a.value.order(b.value)) {
        .lt => -1,
        .eq => 0,
        .gt => 1,
    };
}

pub fn bigSign(a: BigInt) i32 {
    if (a.value.eqlZero()) return 0;
    return if (a.value.isPositive()) 1 else -1;
}

/// `int x` of a bigint: a value that does not fit raises, as on .NET
pub fn bigToInt(comptime T: type, a: BigInt) Raised!T {
    return a.value.toInt(T) catch raise(OverflowException, str("Value was either too large or too small for " ++ netIntName(T) ++ "."));
}

pub fn bigToFloat(comptime T: type, a: BigInt) T {
    return a.value.toFloat(T, .nearest_even)[0];
}

pub fn bigDigits(a: BigInt) []u8 {
    return a.value.toString(rt.allocator, 10, .lower) catch |e| bigOom(e);
}

/// `string x` of a bigint: its digits
pub fn bigText(a: BigInt) String {
    const d = bigDigits(a);
    defer rt.allocator.free(d);
    const s, const u = strNew(d.len);
    for (d, u) |c, *o| o.* = c;
    return s;
}

/// `BigInteger.Parse s`
pub fn bigParse(s: String) Raised!BigInt {
    const u = trimmed(s);
    var buf = rt.allocator.alloc(u8, u.len) catch rt.oom();
    defer rt.allocator.free(buf);
    var n: usize = 0;
    for (u, 0..) |c, i| {
        const ok = (c >= '0' and c <= '9') or (i == 0 and (c == '-' or c == '+'));
        if (!ok) return raise(FormatException, str("The value could not be parsed."));
        if (c != '+') {
            buf[n] = @intCast(c);
            n += 1;
        }
    }
    if (n == 0 or (n == 1 and buf[0] == '-')) return raise(FormatException, str("The value could not be parsed."));
    var m = bigEmpty();
    m.setString(10, buf[0..n]) catch return raise(FormatException, str("The value could not be parsed."));
    return bigFrom(m);
}
