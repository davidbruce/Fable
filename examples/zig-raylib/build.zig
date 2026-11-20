const std = @import("std");
const fable = @import("fable_modules/fable-library-zig/fable_build.zig");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const exe = fable.addExecutable(b, .{
        .name = "raylib_examples",
        .root = "Program.zig",
        .target = target,
        .optimize = optimize,
        .system_libraries = &.{"raylib"},
        .library_paths = &.{ "/opt/homebrew/Cellar/raylib/6.2/lib", "/opt/homebrew/lib" },
    });
    b.installArtifact(exe);

    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.option([]const u8, "example", "Example name or flag to pass")) |arg| {
        run_cmd.addArg(arg);
    }

    const run_step = b.step("run", "Run raylib_examples");
    run_step.dependOn(&run_cmd.step);

    const verify_cmd = b.addRunArtifact(exe);
    verify_cmd.step.dependOn(b.getInstallStep());
    verify_cmd.addArg("--verify");
    const verify_step = b.step("verify", "Run headless parity verification");
    verify_step.dependOn(&verify_cmd.step);

    const bench_cmd = b.addRunArtifact(exe);
    bench_cmd.step.dependOn(b.getInstallStep());
    bench_cmd.addArg("--bench");
    const bench_step = b.step("bench", "Run steady-state FFI benchmarks");
    bench_step.dependOn(&bench_cmd.step);
}
