const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    // `-Doptimize=Debug` gives a compiler bug a stack trace
    const optimize = b.option(std.builtin.OptimizeMode, "optimize", "how mond is built") orelse
        .ReleaseFast;

    // the front end, from lexing to `HighIr`: all that the language server and the example tests
    // need, so they build without llvm
    const front = b.createModule(.{
        .root_source_file = b.path("src/mond.zig"),
        .target = target,
        .optimize = optimize,
    });

    const exe = b.addExecutable(.{
        .name = "mond",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{.{ .name = "mond", .module = front }},
        }),
    });
    add_backend(b, exe.root_module);

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
    const test_step = b.step("test", "Run the example, lsp and backend tests.");
    test_step.dependOn(&run_tests.step);

    { // programs built by `mond` and run: in `test` after the front end passed its tests
        const backend_tests = b.addExecutable(.{
            .name = "mond-test-backend",
            .root_module = b.createModule(.{
                .root_source_file = b.path("src/test_backend.zig"),
                .target = b.graph.host,
            }),
        });
        const backend_step = b.step("test-backend", "Build and run the programs of examples/backend.");
        for ([_]*std.Build.Step{ test_step, backend_step }) |step| {
            const run_backend_tests = b.addRunArtifact(backend_tests);
            run_backend_tests.setCwd(b.path("."));
            run_backend_tests.addArtifactArg(exe);
            if (b.args) |args| run_backend_tests.addArgs(args);
            if (step == test_step) run_backend_tests.step.dependOn(&run_tests.step);
            step.dependOn(&run_backend_tests.step);
        }
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
                .optimize = optimize,
                .imports = &.{.{ .name = "mond", .module = front }},
            }),
        });
        const lsp_tests = b.addTest(.{ .root_module = b.createModule(.{
            .root_source_file = b.path("lsp/Analysis.zig"),
            .target = target,
            .imports = &.{.{ .name = "mond", .module = front }},
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
            const mond = if (native) front else b.createModule(.{ .root_source_file = b.path("src/mond.zig"), .target = t, .optimize = optimize });
            const built = if (native) lsp else b.addExecutable(.{ .name = name, .root_module = b.createModule(.{
                .root_source_file = b.path("lsp/main.zig"),
                .target = t,
                .optimize = optimize,
                .imports = &.{.{ .name = "mond", .module = mond }},
            }) });
            for ([_][]const u8{ "../lsp/vscode", "../lsp/vim" }) |dir| {
                step.dependOn(&b.addInstallArtifact(built, .{ .dest_dir = .{ .override = .{ .custom = dir } }, .dest_sub_path = name }).step);
            }
        };
    }
}

// the llvm c api as the module `llvm_c`, lld through a small c++ shim, and where the linker finds
// the system's libraries (`link_paths`). `-Dllvm-config=..` picks the llvm installation, else the
// first llvm-config in PATH or in a package manager's place; lld is looked for next to it
fn add_backend(b: *std.Build, module: *std.Build.Module) void {
    const target = module.resolved_target.?;
    const darwin = target.result.os.tag.isDarwin();
    const llvm_config = b.option([]const u8, "llvm-config", "the llvm-config to use") orelse
        b.findProgram(&llvm_config_names, &llvm_config_places) catch
        std.process.fatal("llvm-config not found, pass -Dllvm-config=/path/to/it", .{});
    const llvm_prefix = ask(b, llvm_config, "--prefix");
    const llvm_include = ask(b, llvm_config, "--includedir");
    const llvm_lib = ask(b, llvm_config, "--libdir");
    const lld_prefix = b.option([]const u8, "lld-prefix", "where lld's include/, lib/ are") orelse
        find_lld(b, llvm_prefix);
    const lld_include = b.pathJoin(&.{ lld_prefix, "include" });
    const lib = if (exists(b, lld_prefix, "lib64")) "lib64" else "lib";
    const lld_lib = b.pathJoin(&.{ lld_prefix, lib });

    // not `llvm.h`: what is translated from it would be named `llvm.*`, which llvm reserves
    const llvm_c = b.addTranslateC(.{
        .root_source_file = b.path("src/llvm_lowerer/llvm_c.h"),
        .target = target,
        .optimize = .ReleaseFast,
        .link_libc = true,
    });
    llvm_c.addIncludePath(.{ .cwd_relative = llvm_include });
    module.addImport("llvm_c", llvm_c.createModule());

    // the linker of the host only, its flavor told to the shim
    module.addCSourceFile(.{
        .file = b.path("src/llvm_lowerer/lld.cpp"),
        .flags = &.{
            "-std=c++17",
            "-fno-exceptions",
            "-fno-rtti",
            if (darwin) "-DMOND_LLD_macho" else "-DMOND_LLD_elf",
        },
    });
    module.link_libc = true;
    // the headers of lld and llvm are c++, the shim compiles against libc++
    module.link_libcpp = true;
    for ([_][]const u8{ llvm_include, lld_include }) |dir| {
        module.addSystemIncludePath(.{ .cwd_relative = dir });
    }
    for ([_][]const u8{ llvm_lib, lld_lib }) |dir| {
        module.addLibraryPath(.{ .cwd_relative = dir });
        module.addRPath(.{ .cwd_relative = dir });
    }
    module.linkSystemLibrary("LLVM", .{});
    module.linkSystemLibrary("lldCommon", .{});
    module.linkSystemLibrary(if (darwin) "lldMachO" else "lldELF", .{});

    const link_paths = b.addOptions();
    link_paths.addOption([]const u8, "sdk_root", if (darwin) xcrun(b, "--show-sdk-path") else "");
    const sdk_version = if (darwin) xcrun(b, "--show-sdk-version") else "";
    link_paths.addOption([]const u8, "sdk_version", sdk_version);
    const crt_dir = if (target.result.os.tag != .linux)
        ""
    else
        b.option([]const u8, "crt-dir", "where Scrt1.o and libc are") orelse find_crt_dir(b);
    link_paths.addOption([]const u8, "crt_dir", crt_dir);
    // zig knows the loader of the target, `-Ddynamic-linker=..` overrides it
    const dynamic_linker = target.result.dynamic_linker.get() orelse "";
    link_paths.addOption([]const u8, "dynamic_linker", dynamic_linker);
    module.addOptions("link_paths", link_paths);
}

fn find_lld(b: *std.Build, llvm_prefix: []const u8) []const u8 {
    const candidates = [_][]const u8{
        llvm_prefix,
        // homebrew keeps lld apart: <brew>/Cellar/llvm/<version> next to <brew>/opt/lld
        b.pathResolve(&.{ llvm_prefix, "../../../opt/lld" }),
        "/opt/homebrew/opt/lld",
        "/usr/local/opt/lld",
    };
    for (candidates) |candidate| {
        if (exists(b, candidate, "include/lld/Common/Driver.h")) return candidate;
    }
    std.process.fatal("lld headers not found, pass -Dlld-prefix=/path/to/lld", .{});
}

fn find_crt_dir(b: *std.Build) []const u8 {
    for (linux_crt_places) |candidate| if (exists(b, candidate, "Scrt1.o")) return candidate;
    std.process.fatal("crt files not found, pass -Dcrt-dir=/path/with/Scrt1.o", .{});
}

// llvm 19 or newer: the backend uses `LLVMConstStringInContext2`
const llvm_config_names = [_][]const u8{
    "llvm-config",    "llvm-config-22", "llvm-config-21",
    "llvm-config-20", "llvm-config-19",
};

// homebrew (arm, intel), debian and ubuntu (llvm-N), fedora (llvmN)
const llvm_config_places = [_][]const u8{
    "/opt/homebrew/opt/llvm/bin", "/usr/local/opt/llvm/bin",
    "/usr/lib/llvm-22/bin",       "/usr/lib/llvm-21/bin",
    "/usr/lib/llvm-20/bin",       "/usr/lib/llvm-19/bin",
    "/usr/lib64/llvm22/bin",      "/usr/lib64/llvm21/bin",
    "/usr/lib64/llvm20/bin",      "/usr/lib64/llvm19/bin",
};

const linux_crt_places = [_][]const u8{
    "/usr/lib/x86_64-linux-gnu", "/usr/lib/aarch64-linux-gnu",
    "/usr/lib64",                "/usr/lib",
};

fn ask(b: *std.Build, llvm_config: []const u8, question: []const u8) []const u8 {
    return std.mem.trim(u8, b.run(&.{ llvm_config, question }), " \n\r");
}

fn xcrun(b: *std.Build, question: []const u8) []const u8 {
    return std.mem.trim(u8, b.run(&.{ "xcrun", question }), " \n\r");
}

fn exists(b: *std.Build, directory: []const u8, file: []const u8) bool {
    std.Io.Dir.accessAbsolute(b.graph.io, b.pathJoin(&.{ directory, file }), .{}) catch {
        return false;
    };
    return true;
}
