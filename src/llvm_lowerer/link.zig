// links an object file into an executable of this machine with the lld built into mond, against the
// system's c library (found by build.zig and baked in as `link_paths`)
const std = @import("std");
const builtin = @import("builtin");
const llvm = @import("llvm_c");
const link_paths = @import("link_paths");

// joined at compile time, which zero-terminates them for lld
const sdk_root = link_paths.sdk_root ++ "";
const sdk_version = link_paths.sdk_version ++ "";
const crt_dir = link_paths.crt_dir ++ "";
const dynamic_linker = link_paths.dynamic_linker ++ "";
// the objects are built for the macos mond runs on, see `Machine` in emit.zig
const macos_version = if (builtin.os.tag == .macos) std.fmt.comptimePrint("{d}.{d}", .{
    builtin.os.version_range.semver.min.major,
    builtin.os.version_range.semver.min.minor,
}) else "";

// `inputs`: further object files and libraries (`foo.o`, `libbar.a`, `-lm`), the c code mond calls.
// with `libc` the c library starts the program and is linked, else mond's `_start` does and
// nothing is: a static executable on linux, on macos only libSystem, which dyld requires
pub fn executable(
    arena: std.mem.Allocator,
    object: [:0]const u8,
    output: [:0]const u8,
    inputs: []const [:0]const u8,
    libc: bool,
) bool {
    const arch = switch (builtin.cpu.arch) {
        .aarch64 => "arm64",
        else => @tagName(builtin.cpu.arch),
    };
    const macos = [_][*:0]const u8{
        "ld64.lld",
        "-arch",
        arch,
        "-platform_version",
        "macos",
        macos_version,
        sdk_version,
        "-syslibroot",
        sdk_root,
        "-lSystem",
        "-o",
        output,
        object,
    };
    const system: []const [*:0]const u8 = switch (builtin.os.tag) {
        .macos => if (libc) &macos else &(macos ++ [_][*:0]const u8{ "-e", "__start" }),
        .linux => if (libc) &.{
            "ld.lld",
            "-pie",
            "--dynamic-linker",
            dynamic_linker,
            in_crt_dir(arena, "Scrt1.o"),
            in_crt_dir(arena, "crti.o"),
            object,
            "-L",
            crt_dir,
            "-lc",
            in_crt_dir(arena, "crtn.o"),
            "-o",
            output,
        } else &.{ "ld.lld", "-static", "-e", "_start", object, "-o", output },
        else => @compileError("mond links only on macos and linux"),
    };
    var arguments: std.ArrayList([*:0]const u8) = .empty;
    arguments.appendSlice(arena, system) catch @panic("OOM");
    for (inputs) |input| arguments.append(arena, input.ptr) catch @panic("OOM");
    const count: c_int = @intCast(arguments.items.len);
    return llvm.mond_lld_link(count, @ptrCast(arguments.items.ptr));
}

fn in_crt_dir(arena: std.mem.Allocator, file: []const u8) [*:0]const u8 {
    const path = std.fs.path.joinZ(arena, &.{ crt_dir, file }) catch @panic("OOM");
    return path.ptr;
}
