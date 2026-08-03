const std = @import("std");
const builtin = @import("builtin");

pub fn build(b: *std.Build) void {
    const exe = b.addExecutable(.{
        .name = "mond",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = b.standardTargetOptions(.{}),
            .optimize = b.standardOptimizeOption(.{}),
        }),
    });

    exe.use_llvm = true;
    exe.use_lld = true;

    const i = b.addInstallArtifact(exe, .{ .dest_dir = .{ .override = .{ .custom = "../" } } });
    b.getInstallStep().dependOn(&i.step);

    const run_exe = b.addRunArtifact(exe);
    const run_step = b.step("run", "Run the application.");
    run_step.dependOn(&run_exe.step);

    { // https://zigtools.org/zls/guides/build-on-save/
        const exe_check = b.addExecutable(.{
            .name = "mond",
            .root_module = exe.root_module,
        });
        const check = b.step("check", "Check if mond compiles.");
        check.dependOn(&exe_check.step);
    }
}
