//! Numbers: what F#'s operators and System.Math do, raising what they raise on .NET (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const root = @import("root");
const rt = @import("fable_rt.zig");
const ArgumentException = rt.ArgumentException;
const ArgumentOutOfRangeException = rt.ArgumentOutOfRangeException;
const ArithmeticException = rt.ArithmeticException;
const OverflowException = rt.OverflowException;
const Raised = rt.Raised;
const compare = rt.compare;
const decRoundMode = rt.decRoundMode;
const format = rt.format;
const fraction = rt.fraction;
const raise = rt.raise;
const str = rt.str;

// Numbers: what F#'s operators and System.Math do, raising what they raise on .NET
// ---------------------------------------------------------------------------------------------

pub fn overflow() Raised {
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
/// `Math.Round(x, mode)`: the mode checked first, whatever the value (.NET's)
pub fn roundModeOnly(x: anytype, mode: i32) Raised!@TypeOf(x) {
    if (mode < 0 or mode > 4) return raise(ArgumentException, format(.{ "The value '", mode, "' is not valid for this usage of the type MidpointRounding. (Parameter 'mode')" }));
    return roundMode(x, 0, mode);
}

pub fn roundTo(x: anytype, digits: i32) Raised!@TypeOf(x) {
    return roundMode(x, digits, 0);
}

/// `Math.Round(x, digits, mode)` with .NET's MidpointRounding (see `decRoundMode`)
pub fn roundMode(x: anytype, digits: i32, mode: i32) Raised!@TypeOf(x) {
    const T = @TypeOf(x);
    // (.NET's: 15 digits of a double, 6 of a float32; a value with no fraction to round, or not
    // finite, is given back before the mode is looked at)
    const max_digits: i32 = if (T == f32) 6 else 15;
    if (digits < 0 or digits > max_digits) return raise(ArgumentOutOfRangeException, format(.{ "Rounding digits must be between 0 and ", max_digits, ", inclusive. (Parameter 'digits')" }));
    const limit: T = if (T == f32) 1e8 else 1e16;
    if (!std.math.isFinite(x) or @abs(x) >= limit) return x;
    if (mode < 0 or mode > 4) return raise(ArgumentException, format(.{ "The value '", mode, "' is not valid for this usage of the type MidpointRounding. (Parameter 'mode')" }));
    const scale = std.math.pow(T, 10, @floatFromInt(digits));
    const y = x * scale;
    const r = switch (mode) {
        0 => roundEven(y),
        1 => @round(y),
        2 => @trunc(y),
        3 => @floor(y),
        else => @ceil(y),
    };
    return r / scale;
}

/// `Math.MaxMagnitude(x, y)` and `MinMagnitude`: by absolute value (NaN wins; of equal
/// magnitudes, the larger value, or for MinMagnitude the smaller), as .NET
pub fn maxMagnitude(x: anytype, y: @TypeOf(x)) @TypeOf(x) {
    const ax = @abs(x);
    const ay = @abs(y);
    if (ax > ay or std.math.isNan(ax)) return x;
    if (ax == ay) return if (std.math.signbit(x)) y else x;
    return y;
}

pub fn minMagnitude(x: anytype, y: @TypeOf(x)) @TypeOf(x) {
    const ax = @abs(x);
    const ay = @abs(y);
    if (ax < ay or std.math.isNan(ax)) return x;
    if (ax == ay) return if (std.math.signbit(x)) x else y;
    return y;
}

/// `Math.Log(x, b)`
pub fn logBase(x: f64, b: f64) f64 {
    return @log(x) / @log(b);
}

/// `Math.Clamp(x, lo, hi)`
pub fn clamp(x: anytype, lo: @TypeOf(x), hi: @TypeOf(x)) Raised!@TypeOf(x) {
    if (compare(lo, hi) > 0) return raise(ArgumentException, format(.{ "'", lo, "' cannot be greater than ", hi, "." }));
    return if (compare(x, lo) < 0) lo else if (compare(x, hi) > 0) hi else x;
}

/// The name .NET gives a whole-number type in an overflow message.
pub const convert = @import("fable_convert.zig");
pub const arrayAverage = convert.arrayAverage;
pub const arrayAverageBy = convert.arrayAverageBy;
pub const arrayCopyRange = convert.arrayCopyRange;
pub const arrayIndexOf = convert.arrayIndexOf;
pub const arraySetSlice = convert.arraySetSlice;
pub const arraySum = convert.arraySum;
pub const arraySumBy = convert.arraySumBy;
pub const arraySumDec = convert.arraySumDec;
pub const badFormat = convert.badFormat;
pub const base64Of = convert.base64Of;
pub const base64Parse = convert.base64Parse;
pub const bitGetBytes = convert.bitGetBytes;
pub const bitTo = convert.bitTo;
pub const bitToString = convert.bitToString;
pub const conv = convert.conv;
pub const convFloatToInt = convert.convFloatToInt;
pub const convParse = convert.convParse;
pub const convParseBase = convert.convParseBase;
pub const convToStringBase = convert.convToStringBase;
pub const hexOf = convert.hexOf;
pub const hexParse = convert.hexParse;
pub const listAverage = convert.listAverage;
pub const listAverageBy = convert.listAverageBy;
pub const listSum = convert.listSum;
pub const listSumBy = convert.listSumBy;
pub const listSumDec = convert.listSumDec;
pub const netIntName = convert.netIntName;
pub const parseBool = convert.parseBool;
pub const parseFloat = convert.parseFloat;
pub const parseHex = convert.parseHex;
pub const parseInt = convert.parseInt;
pub const parseIntFs = convert.parseIntFs;
pub const parseWhole = convert.parseWhole;
pub const trimmed = convert.trimmed;
pub const numberText = convert.numberText;
pub const parseFloatFs = convert.parseFloatFs;
pub const tryParseAny = convert.tryParseAny;
pub const tryParseFloat = convert.tryParseFloat;
pub const tryParseInt = convert.tryParseInt;
test {
    _ = convert;
}

// ---------------------------------------------------------------------------------------------
