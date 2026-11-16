//! .NET's standard numeric formats: what {x:N2} in an interpolated string asks for (part of fable_rt.zig, which re-exports it)
const std = @import("std");
const builtin = @import("builtin");
const root = @import("root");
const rt = @import("fable_rt.zig");
const Decimal = rt.Decimal;
const Text = rt.Text;
const decAscii = rt.decAscii;
const decDigits = rt.decDigits;
const decimal = rt.decimal;
const format = rt.format;
const isDecimal = rt.isDecimal;

// .NET's standard numeric formats: what `{x:N2}` in an interpolated string asks for
// ---------------------------------------------------------------------------------------------

/// The digits before the point, in groups of three if `grouped`.
pub fn wholeDigits(t: *Text, d: *const Decimal, comptime grouped: bool) void {
    const count: i32 = @max(d.point, 1);
    var i: i32 = 0;
    while (i < count) : (i += 1) {
        if (grouped and i != 0 and @mod(count - i, 3) == 0) t.put(',');
        t.put(d.digit(i + d.point - count));
    }
}

pub fn fraction(t: *Text, d: *const Decimal, places: i32) void {
    if (places <= 0) return;
    t.put('.');
    var k: i32 = 0;
    while (k < places) : (k += 1) t.put(d.digit(d.point + k));
}

/// A number as .NET's `ToString(format)` writes it in the invariant culture, for the
/// standard formats: D, X, B, N, F, E, G, R, P and C with an optional precision.
/// The `n`-th section of a custom format (`positive;negative;zero`), or null.
pub fn customSection(fmt: []const u8, n: usize) ?[]const u8 {
    var start: usize = 0;
    var k: usize = 0;
    var i: usize = 0;
    while (i < fmt.len) : (i += 1) {
        const c = fmt[i];
        if (c == '\\') {
            i += 1;
        } else if (c == '\'' or c == '"') {
            i += 1;
            while (i < fmt.len and fmt[i] != c) i += 1;
        } else if (c == ';') {
            if (k == n) return fmt[start..i];
            k += 1;
            start = i + 1;
        }
    }
    if (k == n) return fmt[start..];
    return null;
}

/// .NET's `FindSection`: the section for a negative number (1) or a zero (2), or the first
/// when the format has no such section or it is empty.
pub fn customFind(fmt: []const u8, n: usize) usize {
    if (n == 0) return 0;
    const s = customSection(fmt, n) orelse return 0;
    return if (s.len == 0) 0 else n;
}

/// A number in one of .NET's custom formats (`0.00`, `#,##0`, `0%`, `0.0;(0.0);zero`,
/// `0.00E+0`, quoted text), as .NET's `NumberToStringFormat` writes it: a double keeps 15
/// significant digits (a float32 7), digits are rounded half away from zero, and digits beyond
/// the placeholders before the point all go where the first placeholder is.
pub fn customText(fmt: []const u8, value: anytype, out: []u8) []const u8 {
    const T = @TypeOf(value);
    const is_dec = comptime isDecimal(T);
    const is_float = comptime !is_dec and @typeInfo(T) == .float;
    var t: Text = .{ .buf = out };
    var negative: bool = undefined;
    var number: Decimal = .{};
    if (is_dec) {
        number = decDigits(value);
        negative = value.m < 0;
    } else if (is_float) {
        if (std.math.isNan(value)) return "NaN";
        if (std.math.isInf(value)) return if (value > 0) "Infinity" else "-Infinity";
        negative = std.math.signbit(value);
        number = Decimal.exact(@abs(@as(f64, value)));
        number.roundTo(if (T == f32) 7 else 15, false);
    } else {
        negative = value < 0;
        if (value != 0) {
            const text = std.fmt.bufPrint(&number.digits, "{d}", .{@abs(@as(i128, value))}) catch unreachable;
            for (number.digits[0..text.len]) |*c| c.* -= '0';
            number.len = text.len;
            number.point = @intCast(text.len);
        }
    }
    while (number.len > 0 and number.digits[number.len - 1] == 0) number.len -= 1;

    var section: usize = if (number.len == 0) customFind(fmt, 2) else if (negative) customFind(fmt, 1) else 0;
    while (true) {
        const sec = customSection(fmt, section).?;
        // what the section asks for
        var digit_count: i32 = 0;
        var decimal_pos: i32 = -1;
        var first_digit: i32 = std.math.maxInt(i32);
        var last_digit: i32 = 0;
        var scientific = false;
        var thousand_pos: i32 = -1;
        var thousand_count: i32 = 0;
        var thousand_seps = false;
        var scale_adjust: i32 = 0;
        var i: usize = 0;
        while (i < sec.len) : (i += 1) {
            const c = sec[i];
            switch (c) {
                '#' => digit_count += 1,
                '0' => {
                    if (first_digit == std.math.maxInt(i32)) first_digit = digit_count;
                    digit_count += 1;
                    last_digit = digit_count;
                },
                '.' => {
                    if (decimal_pos < 0) decimal_pos = digit_count;
                },
                ',' => {
                    if (digit_count > 0 and decimal_pos < 0) {
                        if (thousand_pos >= 0) {
                            if (thousand_pos == digit_count) {
                                thousand_count += 1;
                                continue;
                            }
                            thousand_seps = true;
                        }
                        thousand_pos = digit_count;
                        thousand_count = 1;
                    }
                },
                '%' => scale_adjust += 2,
                '\'', '"' => {
                    i += 1;
                    while (i < sec.len and sec[i] != c) i += 1;
                },
                '\\' => i += 1,
                'E', 'e' => {
                    if ((i + 1 < sec.len and sec[i + 1] == '0') or (i + 2 < sec.len and (sec[i + 1] == '+' or sec[i + 1] == '-') and sec[i + 2] == '0')) {
                        scientific = true;
                        i += 1;
                        if (sec[i] == '+' or sec[i] == '-') i += 1;
                        while (i + 1 < sec.len and sec[i + 1] == '0') i += 1;
                    }
                },
                else => {},
            }
        }
        if (decimal_pos < 0) decimal_pos = digit_count;
        if (thousand_pos >= 0) {
            if (thousand_pos == decimal_pos) {
                scale_adjust -= thousand_count * 3;
            } else {
                thousand_seps = true;
            }
        }

        var d = number;
        if (d.len != 0) {
            d.point += scale_adjust;
            const pos = if (scientific) digit_count else d.point + digit_count - decimal_pos;
            d.roundTo(pos, false);
            while (d.len > 0 and d.digits[d.len - 1] == 0) d.len -= 1;
            if (d.len == 0) {
                d.point = 0;
                if (!is_float) negative = false;
                const z = customFind(fmt, 2);
                if (z != section) {
                    section = z;
                    continue;
                }
            }
        } else {
            if (!is_float) negative = false;
            d.point = 0;
        }

        const first: i32 = if (first_digit < decimal_pos) decimal_pos - first_digit else 0;
        const last: i32 = if (last_digit > decimal_pos) decimal_pos - last_digit else 0;
        var dig_pos: i32 = undefined;
        var adjust: i32 = undefined;
        if (scientific) {
            dig_pos = decimal_pos;
            adjust = 0;
        } else {
            dig_pos = @max(d.point, decimal_pos);
            adjust = d.point - decimal_pos;
        }
        var di: usize = 0;
        if (negative and section == 0 and d.point != 0) t.put('-');
        var decimal_written = false;
        const sep = struct {
            pub fn at(seps: bool, pos: i32) bool {
                return seps and pos > 1 and @mod(pos - 1, 3) == 0;
            }
        };
        var exponent_done = false;
        i = 0;
        while (i < sec.len) : (i += 1) {
            const c = sec[i];
            switch (c) {
                '#', '0' => {
                    var ch: u8 = 0;
                    if (adjust < 0) {
                        adjust += 1;
                        ch = if (dig_pos <= first) '0' else 0;
                    } else {
                        while (adjust > 0) : (adjust -= 1) {
                            if (di < d.len) {
                                t.put('0' + d.digits[di]);
                                di += 1;
                            } else t.put('0');
                            if (sep.at(thousand_seps, dig_pos)) t.put(',');
                            dig_pos -= 1;
                        }
                        if (di < d.len) {
                            ch = '0' + d.digits[di];
                            di += 1;
                        } else {
                            ch = if (dig_pos > last) '0' else 0;
                        }
                    }
                    if (ch != 0) {
                        t.put(ch);
                        if (sep.at(thousand_seps, dig_pos)) t.put(',');
                    }
                    dig_pos -= 1;
                },
                '.' => {
                    if (dig_pos == 0 and !decimal_written and (last < 0 or (decimal_pos < digit_count and di < d.len))) {
                        t.put('.');
                        decimal_written = true;
                    }
                },
                ',' => {},
                '\'', '"' => {
                    i += 1;
                    while (i < sec.len and sec[i] != c) : (i += 1) t.put(sec[i]);
                },
                '\\' => {
                    i += 1;
                    if (i < sec.len) t.put(sec[i]);
                },
                'E', 'e' => {
                    var positive_sign = false;
                    var zeros: u8 = 0;
                    if (scientific and !exponent_done and i + 1 < sec.len and (sec[i + 1] == '0' or (i + 2 < sec.len and (sec[i + 1] == '+' or sec[i + 1] == '-') and sec[i + 2] == '0'))) {
                        var j = i + 1;
                        if (sec[j] == '+') positive_sign = true;
                        if (sec[j] == '+' or sec[j] == '-') j += 1;
                        while (j < sec.len and sec[j] == '0') : (j += 1) zeros += 1;
                        i = j - 1;
                        const e: i32 = if (d.len == 0) 0 else d.point - decimal_pos;
                        t.put(c);
                        if (e < 0) t.put('-') else if (positive_sign) t.put('+');
                        var buf: [12]u8 = undefined;
                        const digits = std.fmt.bufPrint(&buf, "{d}", .{@abs(e)}) catch unreachable;
                        var pad: i32 = @as(i32, @min(zeros, 10)) - @as(i32, @intCast(digits.len));
                        while (pad > 0) : (pad -= 1) t.put('0');
                        for (digits) |x| t.put(x);
                        exponent_done = true;
                    } else {
                        t.put(c);
                    }
                },
                else => t.put(c),
            }
        }
        if (negative and section == 0 and d.point == 0 and t.len > 0) {
            std.mem.copyBackwards(u8, out[1 .. t.len + 1], out[0..t.len]);
            out[0] = '-';
            t.len += 1;
        }
        return out[0..t.len];
    }
}

pub fn isStandardFormat(comptime fmt: []const u8) bool {
    if (fmt.len == 0 or fmt.len > 3 or !std.ascii.isAlphabetic(fmt[0])) return false;
    for (fmt[1..]) |c| {
        if (!std.ascii.isDigit(c)) return false;
    }
    return true;
}

pub fn netText(comptime fmt: []const u8, value: anytype, out: []u8) []const u8 {
    if (comptime !isStandardFormat(fmt)) return customText(fmt, value, out);
    const T = @TypeOf(value);
    const isDec = comptime isDecimal(T);
    const whole = !isDec and @typeInfo(T) == .int;
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
    // (`G` of a decimal: every digit of its scale)
    if (isDec and (letter == 'G' or letter == 'g') and given == null) return decAscii(value, out);
    if (!whole and !isDec) {
        if (std.math.isNan(value)) return "NaN";
        if (std.math.isInf(value)) return if (value > 0) "Infinity" else "-Infinity";
    }

    const negative = if (isDec) value.m < 0 else if (whole) value < 0 else std.math.signbit(value);
    const shortest = !whole and !isDec and (letter == 'R' or letter == 'r' or ((letter == 'G' or letter == 'g') and (given orelse 0) == 0));
    var d: Decimal = .{};
    if (isDec) {
        d = decDigits(value);
    } else if (whole) {
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
    // (and neither does .NET's formatting of a decimal)
    const even = !whole and !isDec;

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
            // (a decimal that rounds to zero is written without its sign; a float keeps it)
            var zero = true;
            for (d.digits[0..d.len]) |c| {
                if (c != 0) zero = false;
            }
            const signed = negative and !(isDec and zero);
            if (signed) t.put(if (currency) '(' else '-');
            if (currency) t.put(0xA4);
            wholeDigits(&t, &d, !(letter == 'F' or letter == 'f'));
            fraction(&t, &d, places);
            if (percent) {
                t.put(' ');
                t.put('%');
            }
            if (signed and currency) t.put(')');
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
