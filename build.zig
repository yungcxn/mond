const std = @import("std");
const builtin = @import("builtin");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const exe = b.addExecutable(.{
        .name = "mond",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = .ReleaseFast,
        }),
    });

    exe.use_llvm = true;
    exe.use_lld = true;

    const i = b.addInstallArtifact(exe, .{ .dest_dir = .{ .override = .{ .custom = "../" } } });
    b.getInstallStep().dependOn(&i.step);

    const run_exe = b.addRunArtifact(exe);
    const run_step = b.step("run", "Run the application.");
    run_step.dependOn(&run_exe.step);

    const tests = b.addExecutable(.{ .name = "mond-test", .root_module = b.createModule(.{ .root_source_file = b.path("src/test.zig"), .target = b.graph.host }) });
    const run_tests = b.addRunArtifact(tests);
    run_tests.setCwd(b.path("."));
    if (b.args) |args| run_tests.addArgs(args);
    b.step("test", "Run the positive and negative example tests.").dependOn(&run_tests.step);

    { // https://zigtools.org/zls/guides/build-on-save/
        const exe_check = b.addExecutable(.{
            .name = "mond",
            .root_module = exe.root_module,
        });
        const check = b.step("check", "Check if mond compiles.");
        check.dependOn(&exe_check.step);
    }

    { // the language server, every editor plugin in lsp/ gets its own copy
        const lsp = b.addExecutable(.{
            .name = "mond-lsp",
            .root_module = b.createModule(.{
                .root_source_file = b.path("lsp/main.zig"),
                .target = target,
                .optimize = .ReleaseFast,
            }),
        });
        const step = b.step("lsp", "Build the language server into the editor plugins in lsp/.");
        for ([_][]const u8{ "../lsp/vscode", "../lsp/vim" }) |dir| {
            step.dependOn(&b.addInstallArtifact(lsp, .{ .dest_dir = .{ .override = .{ .custom = dir } } }).step);
        }
    }
}
