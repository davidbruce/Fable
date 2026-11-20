//! `zig build` of a program that Fable compiled to Zig. In the program's `build.zig`:
//!
//!     const fable = @import("fable_modules/fable-library-zig/fable_build.zig");
//!
//!     pub fn build(b: *std.Build) void {
//!         const exe = fable.addExecutable(b, .{
//!             .name = "app",
//!             .target = b.standardTargetOptions(.{}),
//!             .optimize = b.standardOptimizeOption(.{}),
//!             .system_libraries = &.{"sqlite3"},
//!             .c_headers = &.{.{ .name = "sqlite", .header = "sqlite.h" }},
//!         });
//!         b.installArtifact(exe);
//!     }
//!
//! The Zig that Fable writes finds the runtime by relative paths (`fable_modules/...`), so the
//! root file is all a build needs; this adds what C interop asks for.
const std = @import("std");

/// A C header translated into a module (`b.addTranslateC`), which `[<Import("f", "c:name")>]`
/// imports. `header`: a file of the project, which may `#include` system headers.
pub const CHeader = struct {
    name: []const u8,
    header: []const u8,
};

pub const Options = struct {
    name: []const u8,
    /// the Zig of the file with the `[<EntryPoint>]` (or, for `addTests`, of the tests)
    root: []const u8 = "Program.zig",
    target: std.Build.ResolvedTarget,
    /// what `b.standardOptimizeOption(.{})` gives (null: Debug)
    optimize: ?std.builtin.Optimize = null,
    /// C's library: what `[<DllImport>]` and C functions need. Linked also for system
    /// libraries and C headers. (The runtime then allocates with C's allocator.)
    link_libc: bool = false,
    /// system libraries linked: `&.{"sqlite3"}`
    system_libraries: []const []const u8 = &.{},
    /// library search directories (`-L`)
    library_paths: []const []const u8 = &.{},
    /// C header search directories (`-I`, applied to both the module and `c_headers`)
    include_paths: []const []const u8 = &.{},
    /// macOS/Darwin frameworks (`&.{"CoreVideo", "IOKit"}`)
    frameworks: []const []const u8 = &.{},
    /// macOS/Darwin framework search directories (`-F`)
    framework_paths: []const []const u8 = &.{},
    c_headers: []const CHeader = &.{},
};

fn buildLazyPath(b: *std.Build, p: []const u8) std.Build.LazyPath {
    return if (std.fs.path.isAbsolute(p)) .{ .cwd_relative = p } else b.path(p);
}

/// The program's module, with what the options ask for
pub fn addModule(b: *std.Build, o: Options) *std.Build.Module {
    const libc = o.link_libc or o.system_libraries.len > 0 or o.c_headers.len > 0 or o.frameworks.len > 0;
    const m = b.createModule(.{
        .root_source_file = b.path(o.root),
        .target = o.target,
        .optimize = o.optimize,
        .link_libc = if (libc) true else null,
    });
    for (o.library_paths) |p| m.addLibraryPath(buildLazyPath(b, p));
    for (o.include_paths) |p| m.addIncludePath(buildLazyPath(b, p));
    for (o.framework_paths) |p| m.addFrameworkPath(buildLazyPath(b, p));
    for (o.system_libraries) |lib| m.linkSystemLibrary(lib, .{});
    for (o.frameworks) |fw| m.linkFramework(fw, .{});
    for (o.c_headers) |h| {
        const tc = b.addTranslateC(.{
            .root_source_file = b.path(h.header),
            .target = o.target,
            .optimize = o.optimize orelse .Debug,
        });
        for (o.include_paths) |p| tc.addIncludePath(buildLazyPath(b, p));
        m.addImport(h.name, tc.createModule());
    }
    return m;
}

pub fn addExecutable(b: *std.Build, o: Options) *std.Build.Step.Compile {
    return b.addExecutable(.{ .name = o.name, .root_module = addModule(b, o) });
}

/// `zig build test` of a file of `[<Fact>]` tests
pub fn addTests(b: *std.Build, o: Options) *std.Build.Step.Compile {
    return b.addTest(.{ .name = o.name, .root_module = addModule(b, o) });
}
