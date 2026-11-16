//! C functions that InteropTests.fs imports with `c:` (as a module translated from a header
//! by the build would declare them)
pub extern "c" fn strlen(s: [*:0]const u8) usize;
pub extern "c" fn strchr(s: [*:0]const u8, c: c_int) ?[*:0]const u8;
pub extern "c" fn abs(x: c_int) c_int;
