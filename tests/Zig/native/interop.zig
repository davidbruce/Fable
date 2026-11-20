//! Hand-written Zig that InteropTests.fs imports (`[<Import>]`, `[<ImportMember>]`).
const std = @import("std");
const fable_rt = @import("../fable_modules/fable-library-zig/fable_rt.zig");

pub fn add(a: i32, b: i32) i32 {
    return a + b;
}

pub const answer: i32 = 42;

/// The length of an F# string, borrowed for the call
pub fn units(s: fable_rt.String) i32 {
    return @intCast(fable_rt.unitsOf(s).len);
}

/// A new string, which the caller owns
pub fn greet(name: fable_rt.String) fable_rt.String {
    return fable_rt.strConcat(fable_rt.str("hello "), name);
}

/// A string kept past the call: dup'ed, as an argument is borrowed
var kept: fable_rt.String = null;

pub fn keep(s: fable_rt.String) void {
    fable_rt.drop(kept);
    kept = fable_rt.dup(s);
}

pub fn kept_len() i32 {
    return @intCast(fable_rt.unitsOf(kept).len);
}

pub fn release_kept() void {
    fable_rt.drop(kept);
    kept = null;
}

/// Calls of F# functions that InteropTests.fs gives to C, by their C names
pub fn call_twice(x: i32) i32 {
    const f = @extern(*const fn (i32) callconv(.c) i32, .{ .name = "fable_test_twice" });
    return f(x);
}

pub fn call_len(s: [*:0]const u8) i32 {
    const f = @extern(*const fn (?[*:0]const u8) callconv(.c) i32, .{ .name = "fable_test_len" });
    return f(s);
}

/// A Zig struct that InteropTests.fs uses through an `[<Erase; Import>]` interface
pub const Counter = struct {
    n: i32,

    pub fn add(self: *Counter, x: i32) i32 {
        self.n += x;
        return self.n;
    }
};

var live_counters: i32 = 0;

pub fn counter_new(start: i32) *Counter {
    const c = fable_rt.allocator.create(Counter) catch fable_rt.oom();
    c.* = .{ .n = start };
    live_counters += 1;
    return c;
}

pub fn counter_free(c: *Counter) void {
    fable_rt.allocator.destroy(c);
    live_counters -= 1;
}

pub fn counters_live() i32 {
    return live_counters;
}

/// A call of an F# function of InteropTests.fs from Zig
pub fn call_twice_text(s: fable_rt.String) fable_rt.String {
    const app = @import("../InteropTests.zig");
    return fable_rt.callFSharp(app, "twiceText", .{s}) catch fable_rt.str("raised");
}

/// C functions that take and give structs by value (InteropTests.fs: DllImport and `c:`)
const CVec2 = extern struct { x: f32, y: f32 };
const CRect = extern struct { pos: CVec2, width: f32, height: f32, solid: bool };

export fn fable_test_vadd(a: CVec2, b: CVec2) CVec2 {
    return .{ .x = a.x + b.x, .y = a.y + b.y };
}

export fn fable_test_area(r: CRect) f32 {
    return if (r.solid) r.width * r.height + r.pos.x else 0;
}

/// For InteropTests.fs's byrefs, bools, wide strings and callbacks
export fn fable_test_scale(v: *CVec2, k: f32) void {
    v.x *= k;
    v.y *= k;
}

export fn fable_test_bool4(b: i32) i32 {
    return if (b != 0) 7 else 3;
}

export fn fable_test_bool1(b: bool) bool {
    return !b;
}

export fn fable_test_is_positive(x: i32) i32 {
    return @intFromBool(x > 0);
}

export fn fable_test_wlen(s: [*:0]const u16) i32 {
    return @intCast(std.mem.len(s));
}

export fn fable_test_whello() [*:0]const u16 {
    return std.unicode.utf8ToUtf16LeStringLiteral("h\u{e9}llo");
}

export fn fable_test_out_flag(x: i32, flag: *i32) void {
    flag.* = @intFromBool(x > 10);
}

var stored_callback: ?*const fn (i32) callconv(.c) i32 = null;

export fn fable_test_register(cb: *const fn (i32) callconv(.c) i32) void {
    stored_callback = cb;
}

export fn fable_test_fire(x: i32) i32 {
    return stored_callback.?(x);
}

export fn fable_test_each_name(cb: *const fn (?[*:0]const u8, i32) callconv(.c) void) void {
    cb("one", 1);
    cb("two", 2);
}

pub const PackedRec = extern struct {
    tag: u8 align(@min(1, @alignOf(u8))),
    val: i64 align(@min(1, @alignOf(i64))),
    tail: u16 align(@min(1, @alignOf(u16))),
};

export fn fable_test_packed_sum(p: PackedRec) i64 {
    return @as(i64, p.tag) + p.val + @as(i64, p.tail);
}

export fn fable_test_packed_ptr(p: *const PackedRec) i64 {
    return @as(i64, p.tag) + p.val * 2 + @as(i64, p.tail);
}

pub const IntFloatUnion = extern union {
    i: i32,
    f: f32,
};

export fn fable_test_union_as_bits(u: IntFloatUnion) i32 {
    return u.i;
}

export fn fable_test_9args(a1: i32, a2: i32, a3: i32, a4: i32, a5: i32, a6: i32, a7: i32, a8: i32, a9: i32) i32 {
    return a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9;
}

export fn fable_test_inref_vec(v: *const CVec2) f32 {
    return v.x * 10.0 + v.y;
}

export fn fable_test_byref_bool_ptr(flag: *bool, ptr: ?[*]i32, idx: i32) bool {
    const prev = flag.*;
    flag.* = !prev;
    if (ptr) |p| p[@intCast(idx)] += 5;
    return prev;
}

export fn fable_test_null_array_span(arr: ?[*]const i32, sp: ?[*]const i32, n: i32) i32 {
    var sum: i32 = 0;
    if (arr != null) sum += 1000;
    if (sp) |p| {
        var i: usize = 0;
        while (i < @as(usize, @intCast(n))) : (i += 1) sum += p[i];
    }
    return sum;
}

export fn fable_test_opt_callback(x: i32, cb: ?*const fn (i32) callconv(.c) i32) i32 {
    return if (cb) |f| f(x) else -x;
}

export fn fable_test_callback6(cb: *const fn (i32, i32, i32, i32, i32, i32) callconv(.c) i32) i32 {
    return cb(1, 2, 3, 4, 5, 6);
}

extern fn fable_test_uco_struct(v: CVec2, p: ?[*]i32, r: *const i32) CVec2;

pub export fn fable_test_call_uco_struct(x: f32, y: f32, factor: i32) f32 {
    var buf: [2]i32 = .{ 10, 20 };
    const res = fable_test_uco_struct(.{ .x = x, .y = y }, &buf, &factor);
    return res.x + res.y + @as(f32, @floatFromInt(buf[0]));
}
