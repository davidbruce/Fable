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
