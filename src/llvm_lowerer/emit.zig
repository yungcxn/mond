// from a lowered llvm module to an object file: the host as the target, the optimization passes,
// the machine code
const std = @import("std");
const llvm = @import("llvm_c");

// `--level`: the pass pipeline and how hard instruction selection tries.
// level 0 also keeps the runtime checks the lowerer emits
pub const Level = enum {
    @"0",
    @"1",
    @"2",
    @"3",
    s,
    z,

    pub const usage = "levels: 0, 1, 2, 3, s (small), z (smallest)\n";

    pub fn parse(text: []const u8) ?Level {
        return std.meta.stringToEnum(Level, text);
    }

    fn pipeline(level: Level) [:0]const u8 {
        return switch (level) {
            .@"0" => "default<O0>",
            .@"1" => "default<O1>",
            .@"2" => "default<O2>",
            .@"3" => "default<O3>",
            .s => "default<Os>",
            .z => "default<Oz>",
        };
    }

    fn codegen(level: Level) llvm.LLVMCodeGenOptLevel {
        return switch (level) {
            .@"0" => llvm.LLVMCodeGenLevelNone,
            .@"1" => llvm.LLVMCodeGenLevelLess,
            .@"2", .s, .z => llvm.LLVMCodeGenLevelDefault,
            .@"3" => llvm.LLVMCodeGenLevelAggressive,
        };
    }
};

// the executable runs where it is built, so it may use every feature of this cpu
pub const Machine = struct {
    level: Level,
    triple: [*c]u8,
    target_machine: llvm.LLVMTargetMachineRef,

    pub fn init(level: Level) Machine {
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
            .level = level,
            .triple = triple,
            .target_machine = llvm.LLVMCreateTargetMachine(
                target,
                triple,
                cpu,
                features,
                level.codegen(),
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
            machine.level.pipeline(),
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
