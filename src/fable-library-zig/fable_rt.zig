//! The hand-written part of the Zig runtime library: reference-counted cells, reuse tokens and
//! the cycle collector will live here. Nothing in generated code depends on it yet.
const std = @import("std");

pub const interface_version: i32 = 1;
