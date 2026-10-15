// from a lowered llvm module to an object file: the host as the target, the optimization passes,
// the machine code
const std = @import("std");
const llvm = @import("llvm_c");

// `--mode`: the pass pipeline, how hard instruction selection tries, and whether the runtime checks
// the lowerer emits stay
pub const Mode = enum {
    none,
    safe,
    less,
    default,
    aggressive,
    size,
    minsize,

    pub fn description(mode: Mode) []const u8 {
        return switch (mode) {
            .none => "no optimization, runtime checks (the default)",
            .safe => "optimized like default, runtime checks",
            .less => "light optimization",
            .default => "full optimization",
            .aggressive => "more inlining and unrolling, larger code",
            .size => "optimized, small code",
            .minsize => "smallest code",
        };
    }

    // the level as llvm and c compilers name it, `-O2` for clang
    pub fn optimization(mode: Mode) []const u8 {
        return switch (mode) {
            .none => "O0",
            .less => "O1",
            .default, .safe => "O2",
            .aggressive => "O3",
            .size => "Os",
            .minsize => "Oz",
        };
    }

    pub fn has_checks(mode: Mode) bool {
        return mode == .none or mode == .safe;
    }

    fn pipeline(mode: Mode) [:0]const u8 {
        return switch (mode) {
            inline else => |known| "default<" ++ comptime known.optimization() ++ ">",
        };
    }

    fn codegen(mode: Mode) llvm.LLVMCodeGenOptLevel {
        return switch (mode) {
            .none => llvm.LLVMCodeGenLevelNone,
            .less => llvm.LLVMCodeGenLevelLess,
            .default, .safe, .size, .minsize => llvm.LLVMCodeGenLevelDefault,
            .aggressive => llvm.LLVMCodeGenLevelAggressive,
        };
    }
};

// the executable runs where it is built, so it may use every feature of this cpu
pub const Machine = struct {
    mode: Mode,
    triple: [*c]u8,
    target_machine: llvm.LLVMTargetMachineRef,

    pub fn init(mode: Mode) Machine {
        if (llvm.LLVMInitializeNativeTarget() != 0) @panic("llvm has no backend for this machine");
        if (llvm.LLVMInitializeNativeAsmPrinter() != 0) {
            @panic("llvm can't print this machine's code");
        }

        const triple = llvm.LLVMGetDefaultTargetTriple();
        var target: llvm.LLVMTargetRef = null;
        var message: [*c]u8 = null;
        if (llvm.LLVMGetTargetFromTriple(triple, &target, &message) != 0) {
            std.debug.panic("no llvm target for {s}: {s}", .{ triple, message });
        }
        const cpu = llvm.LLVMGetHostCPUName();
        defer llvm.LLVMDisposeMessage(cpu);
        const features = llvm.LLVMGetHostCPUFeatures();
        defer llvm.LLVMDisposeMessage(features);
        return .{
            .mode = mode,
            .triple = triple,
            .target_machine = llvm.LLVMCreateTargetMachine(
                target,
                triple,
                cpu,
                features,
                mode.codegen(),
                llvm.LLVMRelocPIC,
                llvm.LLVMCodeModelDefault,
            ),
        };
    }

    pub fn deinit(machine: Machine) void {
        llvm.LLVMDisposeTargetMachine(machine.target_machine);
        llvm.LLVMDisposeMessage(machine.triple);
    }

    pub fn optimize(machine: Machine, module: llvm.LLVMModuleRef) void {
        llvm.LLVMSetTarget(module, machine.triple);
        const data_layout = llvm.LLVMCreateTargetDataLayout(machine.target_machine);
        defer llvm.LLVMDisposeTargetData(data_layout);
        llvm.LLVMSetModuleDataLayout(module, data_layout);

        const options = llvm.LLVMCreatePassBuilderOptions();
        defer llvm.LLVMDisposePassBuilderOptions(options);
        const failure = llvm.LLVMRunPasses(
            module,
            machine.mode.pipeline(),
            machine.target_machine,
            options,
        );
        if (failure != null) {
            const message = llvm.LLVMGetErrorMessage(failure);
            std.debug.panic("llvm passes failed: {s}", .{message});
        }
    }

    pub fn write_object(machine: Machine, module: llvm.LLVMModuleRef, path: [:0]const u8) void {
        var message: [*c]u8 = null;
        const failed = llvm.LLVMTargetMachineEmitToFile(
            machine.target_machine,
            module,
            path.ptr,
            llvm.LLVMObjectFile,
            &message,
        );
        if (failed != 0) std.debug.panic("writing {s} failed: {s}", .{ path, message });
    }
};

pub fn print(io: std.Io, module: llvm.LLVMModuleRef) !void {
    const text = llvm.LLVMPrintModuleToString(module);
    defer llvm.LLVMDisposeMessage(text);
    try std.Io.File.stdout().writeStreamingAll(io, std.mem.span(text));
}
