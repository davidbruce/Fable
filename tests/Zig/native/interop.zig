//! Hand-written Zig that InteropTests.fs imports (`[<Import>]`, `[<ImportMember>]`).
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
