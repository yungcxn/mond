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
    // lld cannot link mach-o, darwin keeps the system linker
    exe.use_lld = !target.result.os.tag.isDarwin();

    const i = b.addInstallArtifact(exe, .{ .dest_dir = .{ .override = .{ .custom = "../" } } });
    b.getInstallStep().dependOn(&i.step);

    const run_exe = b.addRunArtifact(exe);
    const run_step = b.step("run", "Run the application.");
    run_step.dependOn(&run_exe.step);

    const tests = b.addExecutable(.{ .name = "mond-test", .root_module = b.createModule(.{ .root_source_file = b.path("src/test.zig"), .target = b.graph.host }) });
    const run_tests = b.addRunArtifact(tests);
    run_tests.setCwd(b.path("."));
    if (b.args) |args| run_tests.addArgs(args);
    const test_step = b.step("test", "Run the positive and negative example tests and the lsp tests.");
    test_step.dependOn(&run_tests.step);

    { // the whole pipeline over every compiling example, `zig build bench -- <rounds>`
        const bench = b.addExecutable(.{ .name = "mond-bench", .root_module = b.createModule(.{
            .root_source_file = b.path("stats/bench.zig"),
            .target = target,
            .optimize = .ReleaseFast,
            .imports = &.{.{ .name = "mond", .module = exe.root_module }},
        }) });
        const run_bench = b.addRunArtifact(bench);
        run_bench.setCwd(b.path("."));
        if (b.args) |args| run_bench.addArgs(args);
        b.step("bench", "Time lexing, parsing, resolving and lowering of all examples.").dependOn(&run_bench.step);
    }

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
                .imports = &.{.{ .name = "mond", .module = exe.root_module }},
            }),
        });
        const lsp_tests = b.addTest(.{ .root_module = b.createModule(.{
            .root_source_file = b.path("lsp/Analysis.zig"),
            .target = target,
            .imports = &.{.{ .name = "mond", .module = exe.root_module }},
        }) });
        test_step.dependOn(&b.addRunArtifact(lsp_tests).step);
        const step = b.step("lsp", "Build the language server into the editor plugins in lsp/.");
        // `mond-lsp` for this machine, and one per platform (`mond-lsp-linux-aarch64`) for an editor reaching the plugins
        // from another one (a remote host sharing the folder): the plugins take the one of the machine they run on
        const host = b.graph.host.result;
        for ([_][]const u8{ "../lsp/vscode", "../lsp/vim" }) |dir| {
            step.dependOn(&b.addInstallArtifact(lsp, .{ .dest_dir = .{ .override = .{ .custom = dir } } }).step);
        }
        for ([_]std.Target.Os.Tag{ .linux, .macos }) |os| for ([_]std.Target.Cpu.Arch{ .aarch64, .x86_64 }) |arch| {
            const name = b.fmt("mond-lsp-{t}-{t}", .{ os, arch });
            const native = os == host.os.tag and arch == host.cpu.arch;
            const t = if (native) target else b.resolveTargetQuery(.{ .os_tag = os, .cpu_arch = arch });
            const mond = if (native) exe.root_module else b.createModule(.{ .root_source_file = b.path("src/main.zig"), .target = t, .optimize = .ReleaseFast });
            const built = if (native) lsp else b.addExecutable(.{ .name = name, .root_module = b.createModule(.{
                .root_source_file = b.path("lsp/main.zig"),
                .target = t,
                .optimize = .ReleaseFast,
                .imports = &.{.{ .name = "mond", .module = mond }},
            }) });
            for ([_][]const u8{ "../lsp/vscode", "../lsp/vim" }) |dir| {
                step.dependOn(&b.addInstallArtifact(built, .{ .dest_dir = .{ .override = .{ .custom = dir } }, .dest_sub_path = name }).step);
            }
        };
    }
}
