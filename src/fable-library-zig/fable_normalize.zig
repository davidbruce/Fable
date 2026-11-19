//! `String.Normalize` and `String.IsNormalized`: Unicode's normalization forms (UAX #15), by the
//! tables of fable_normalize_data.zig (generated from the Unicode data) and Hangul's arithmetic.

const std = @import("std");
const rt = @import("fable_rt.zig");
const data = @import("fable_normalize_data.zig");

const String = rt.String;
const Raised = rt.Raised;

/// .NET's `NormalizationForm`: its values
pub const form_c: i32 = 1;
pub const form_d: i32 = 2;
pub const form_kc: i32 = 5;
pub const form_kd: i32 = 6;

const s_base: u21 = 0xAC00;
const l_base: u21 = 0x1100;
const v_base: u21 = 0x1161;
const t_base: u21 = 0x11A7;
const l_count: u21 = 19;
const v_count: u21 = 21;
const t_count: u21 = 28;
const n_count: u21 = v_count * t_count;
const s_count: u21 = l_count * n_count;

fn find(keys: []const u21, cp: u21) ?usize {
    var lo: usize = 0;
    var hi: usize = keys.len;
    while (lo < hi) {
        const mid = lo + (hi - lo) / 2;
        if (keys[mid] < cp) lo = mid + 1 else hi = mid;
    }
    return if (lo < keys.len and keys[lo] == cp) lo else null;
}

fn combiningClass(cp: u21) u8 {
    if (cp < 0x300) return 0;
    return if (find(&data.ccc_keys, cp)) |i| data.ccc_values[i] else 0;
}

fn spanOf(spans: []const u32, items: []const u21, i: usize) []const u21 {
    const span = spans[i];
    const start = span >> 5;
    return items[start .. start + (span & 31)];
}

fn decompose(out: *std.ArrayList(u21), cp: u21, compat: bool) void {
    if (cp >= s_base and cp < s_base + s_count) {
        const s = cp - s_base;
        out.append(rt.alloc(), l_base + s / n_count) catch rt.oom();
        out.append(rt.alloc(), v_base + (s % n_count) / t_count) catch rt.oom();
        const t = s % t_count;
        if (t != 0) out.append(rt.alloc(), t_base + t) catch rt.oom();
        return;
    }
    if (compat) {
        if (find(&data.compat_keys, cp)) |i| {
            out.appendSlice(rt.alloc(), spanOf(&data.compat_spans, &data.compat_items, i)) catch rt.oom();
            return;
        }
    }
    if (find(&data.canon_keys, cp)) |i| {
        out.appendSlice(rt.alloc(), spanOf(&data.canon_spans, &data.canon_items, i)) catch rt.oom();
        return;
    }
    out.append(rt.alloc(), cp) catch rt.oom();
}

/// (the canonical order: the marks after a starter sorted by their class, stably)
fn reorder(cps: []u21) void {
    var i: usize = 1;
    while (i < cps.len) : (i += 1) {
        const c = combiningClass(cps[i]);
        if (c == 0) continue;
        var j = i;
        while (j > 0) {
            const p = combiningClass(cps[j - 1]);
            if (p == 0 or p <= c) break;
            std.mem.swap(u21, &cps[j - 1], &cps[j]);
            j -= 1;
        }
    }
}

fn composePair(a: u21, b: u21) ?u21 {
    // (Hangul: a leading and a vowel jamo, or a syllable of those and a trailing one)
    if (a >= l_base and a < l_base + l_count and b >= v_base and b < v_base + v_count) {
        return s_base + ((a - l_base) * v_count + (b - v_base)) * t_count;
    }
    if (a >= s_base and a < s_base + s_count and (a - s_base) % t_count == 0 and b > t_base and b < t_base + t_count) {
        return a + (b - t_base);
    }
    var lo: usize = 0;
    var hi: usize = data.pair_firsts.len;
    while (lo < hi) {
        const mid = lo + (hi - lo) / 2;
        const f = data.pair_firsts[mid];
        if (f < a or (f == a and data.pair_seconds[mid] < b)) lo = mid + 1 else hi = mid;
    }
    if (lo < data.pair_firsts.len and data.pair_firsts[lo] == a and data.pair_seconds[lo] == b) return data.pair_composites[lo];
    return null;
}

/// (the canonical composition of a decomposed, reordered sequence, in place: its new length)
fn compose(cps: []u21) usize {
    if (cps.len == 0) return 0;
    var starter_pos: usize = 0;
    var starter = cps[0];
    var last_class: u16 = combiningClass(starter);
    if (last_class != 0) last_class = 256;
    var out: usize = 1;
    var i: usize = 1;
    while (i < cps.len) : (i += 1) {
        const ch = cps[i];
        const class: u16 = combiningClass(ch);
        if (composePair(starter, ch)) |composite| {
            if (last_class < class or last_class == 0) {
                cps[starter_pos] = composite;
                starter = composite;
                continue;
            }
        }
        if (class == 0) {
            starter_pos = out;
            starter = ch;
        }
        last_class = class;
        cps[out] = ch;
        out += 1;
    }
    return out;
}

/// (below this unit, text is already in the form)
fn quickLimit(form: i32) u16 {
    return switch (form) {
        form_c => 0x300,
        form_d => 0xC0,
        else => 0xA0,
    };
}

/// (a lone surrogate: U+FFFD in what `Normalize` gives, as ICU writes it; left as it is where
/// `IsNormalized` compares)
fn normalized(units: []const u16, form: i32, replace_lone: bool) []u21 {
    const compat = form == form_kc or form == form_kd;
    var cps: std.ArrayList(u21) = .empty;
    var i: usize = 0;
    while (i < units.len) {
        const u = units[i];
        var cp: u21 = u;
        if (u >= 0xD800 and u < 0xDC00 and i + 1 < units.len and units[i + 1] >= 0xDC00 and units[i + 1] < 0xE000) {
            cp = 0x10000 + ((@as(u21, u) - 0xD800) << 10) + (units[i + 1] - 0xDC00);
            i += 2;
        } else {
            i += 1;
            if (replace_lone and u >= 0xD800 and u < 0xE000) cp = 0xFFFD;
        }
        decompose(&cps, cp, compat);
    }
    reorder(cps.items);
    if (form == form_c or form == form_kc) cps.items.len = compose(cps.items);
    return cps.toOwnedSlice(rt.alloc()) catch rt.oom();
}

fn checkForm(form: i32) Raised!void {
    if (form != form_c and form != form_d and form != form_kc and form != form_kd) {
        return rt.raise(rt.ArgumentException, rt.str("Invalid normalization form. (Parameter 'normalizationForm')"));
    }
}

/// (U+FFFE, which ICU refuses)
fn checkUnits(units: []const u16, comptime param: []const u8) Raised!void {
    if (std.mem.indexOfScalar(u16, units, 0xFFFE) != null) {
        return rt.raise(rt.ArgumentException, rt.str("String contains invalid Unicode code points. (Parameter '" ++ param ++ "')"));
    }
}

/// `s.Normalize(form)`
pub fn strNormalize(s: String, form: i32) Raised!String {
    return normalizeWith(s, form, true, "strInput");
}

fn normalizeWith(s: String, form: i32, replace_lone: bool, comptime param: []const u8) Raised!String {
    try checkForm(form);
    const units = rt.unitsOf(s);
    const limit = quickLimit(form);
    for (units) |u| {
        if (u >= limit) break;
    } else return rt.dup(s);
    try checkUnits(units, param);
    const cps = normalized(units, form, replace_lone);
    defer rt.alloc().free(cps);
    var b: rt.TextBuilder = .{};
    for (cps) |cp| {
        if (cp >= 0x10000) {
            const v = cp - 0x10000;
            b.add(&[_]u16{ @intCast(0xD800 + (v >> 10)), @intCast(0xDC00 + (v & 0x3FF)) });
        } else {
            b.add(&[_]u16{@intCast(cp)});
        }
    }
    return b.finish();
}

/// `s.IsNormalized(form)`
pub fn strIsNormalized(s: String, form: i32) Raised!bool {
    const n = try normalizeWith(s, form, false, "source");
    defer rt.drop(n);
    return std.mem.eql(u16, rt.unitsOf(n), rt.unitsOf(s));
}

test "normalization forms" {
    const e_acute = rt.str("\u{e9}");
    defer rt.drop(e_acute);
    const d = try strNormalize(e_acute, form_d);
    defer rt.drop(d);
    try std.testing.expectEqualSlices(u16, &.{ 'e', 0x301 }, rt.unitsOf(d));
    const c = try strNormalize(d, form_c);
    defer rt.drop(c);
    try std.testing.expectEqualSlices(u16, &.{0xE9}, rt.unitsOf(c));
    const hangul = rt.str("\u{d55c}");
    defer rt.drop(hangul);
    const hd = try strNormalize(hangul, form_d);
    defer rt.drop(hd);
    try std.testing.expectEqualSlices(u16, &.{ 0x1112, 0x1161, 0x11AB }, rt.unitsOf(hd));
    const hc = try strNormalize(hd, form_c);
    defer rt.drop(hc);
    try std.testing.expectEqualSlices(u16, &.{0xD55C}, rt.unitsOf(hc));
    const lig = rt.str("\u{fb01}");
    defer rt.drop(lig);
    const kc = try strNormalize(lig, form_kc);
    defer rt.drop(kc);
    try std.testing.expectEqualSlices(u16, &.{ 'f', 'i' }, rt.unitsOf(kc));
}
