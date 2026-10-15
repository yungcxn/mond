const std = @import("std");
const builtin = @import("builtin");
const llvm = @import("llvm_c");
const mond = @import("mond");
const Types = @import("llvm_lowerer/Types.zig");
const DebugInfo = @import("llvm_lowerer/DebugInfo.zig");
const c_abi = @import("llvm_lowerer/c_abi.zig");
const constants = @import("llvm_lowerer/constants.zig");
const values = @import("llvm_lowerer/values.zig");
const runtime = @import("llvm_lowerer/runtime.zig");
const HighIr = mond.HighIr;
const HighLowerer = mond.HighLowerer;
const StaticPool = mond.StaticPool;
const DeclPool = mond.DeclPool;
const Ref = HighIr.Ref;
const Op = HighIr.Op;
const Index = StaticPool.Index;
pub const Value = llvm.LLVMValueRef;
pub const Type = llvm.LLVMTypeRef;
pub const Block = llvm.LLVMBasicBlockRef;

// lowers `HighIr` into an llvm module: an llvm function per ir function, an llvm value per
// instruction. the ir is in ssa form already, so this translates; llvm optimizes (emit.zig).
// records, arrays and variants live in memory like in c: such a value is the address of an
// immutable copy, passed by that address and returned through a pointer the caller gives
// (sret). the conversions, casts and variants are in llvm_lowerer/values.zig, constants in
// constants.zig, dwarf in DebugInfo.zig, calls of c functions follow c_abi.zig
const LLVMLowerer = @This();
pub const no_function = std.math.maxInt(u32);

pub const Options = struct {
    // traps on division by zero, oversized shifts, indices past an array's end and reached
    // `unreachable`s
    checks: bool,
    // the absolute path of the source to emit dwarf for, null for none
    debug_source: ?[]const u8 = null,
    // the module will be optimized, debug info marks itself so
    optimized: bool = false,
    // linked with the c library, started by its startup, else by mond's own `_start`
    libc: bool = false,
};

// a phi waits for its operands until all blocks of its function are lowered. a value in memory
// has no phi but a slot of its own, each predecessor copies its value into it
const PendingPhi = struct { phi: Value, block: u32, instruction: HighIr.Inst };

allocator: std.mem.Allocator,
options: Options,
high: *HighLowerer,
ir: *const HighIr,
pool: *StaticPool,
context: llvm.LLVMContextRef,
module: llvm.LLVMModuleRef,
builder: llvm.LLVMBuilderRef,
types: Types,
debug: ?DebugInfo,
// per ir function: its llvm function and that function's type
functions: []Value,
function_types: []Type,
// per ir function: the function as a function value, taking the environment first
thunks: []Value,
// per ir function: declared without a body, called with the c library's conventions
externals: std.DynamicBitSetUnmanaged,
// per ir function: returns through the pointer in its first parameter
results_in_memory: std.DynamicBitSetUnmanaged,
// per ir function: of a variadic c function, how many parameters are fixed; `no_function` else
fixed_parameters: []u32,
globals: []Value,
// per declaration: its ir function, `no_function` for others
function_of_declaration: []u32,
// per pool value, null until needed: its constant global. a string's holds its bytes with a zero
// behind, so c functions can read it, a record's, array's or variant's the value
value_globals: []Value,
// per pool type, null until needed: zero bytes in a constant global, `zeroed` in memory
zero_globals: []Value,
// the operands and types of what is built now, as stacks: a user takes its part from a mark
// on, reads it once it pushed everything (a nested user may grow the buffer meanwhile), and
// truncates back to its mark
value_stack: std.ArrayList(Value) = .empty,
type_stack: std.ArrayList(Type) = .empty,
name_buffer: [256:0]u8 = undefined,

// the function being lowered
function: HighIr.Function = undefined,
function_index: u32 = 0,
// the index in `ir.insts` of the instruction being lowered
instruction_index: u32 = 0,
llvm_function: Value = null,
instruction_values: std.ArrayList(Value) = .empty,
// per ir block: where it starts, and where it ends once checks split it
blocks: std.ArrayList(Block) = .empty,
block_exits: std.ArrayList(Block) = .empty,
reachable: std.DynamicBitSetUnmanaged = .{},
block_order: std.ArrayList(u32) = .empty,
// blocks being walked, and how many of their successors are walked already
walk: std.ArrayList([2]u32) = .empty,
pending_phis: std.ArrayList(PendingPhi) = .empty,
// the entry block holding the function's allocas, in front of the ir's first block
alloca_builder: llvm.LLVMBuilderRef,
trap_block: Block = null,

pub fn init(
    allocator: std.mem.Allocator,
    high: *HighLowerer,
    name: [:0]const u8,
    options: Options,
) LLVMLowerer {
    const context = llvm.LLVMContextCreate();
    const module = llvm.LLVMModuleCreateWithNameInContext(name, context);
    const ir = &high.ir;
    const function_count = ir.functions.len();
    const declaration_count = high.resolver.decl_pool.entries.len();
    const pool_count = high.static_pool.items.len();
    const debug: ?DebugInfo = if (options.debug_source) |path| .init(
        allocator,
        module,
        high.resolver.tree,
        high.resolver.src_bytes,
        path,
        options.optimized,
    ) else null;
    return .{
        .allocator = allocator,
        .options = options,
        .high = high,
        .ir = ir,
        .pool = high.static_pool,
        .context = context,
        .module = module,
        .builder = llvm.LLVMCreateBuilderInContext(context),
        .alloca_builder = llvm.LLVMCreateBuilderInContext(context),
        .types = .init(allocator, context, high.static_pool, &high.resolver.name_pool),
        .debug = debug,
        .functions = filled(allocator, Value, function_count, null),
        .function_types = filled(allocator, Type, function_count, null),
        .thunks = filled(allocator, Value, function_count, null),
        .externals = bits(allocator, function_count),
        .results_in_memory = bits(allocator, function_count),
        .fixed_parameters = filled(allocator, u32, function_count, no_function),
        .globals = filled(allocator, Value, ir.globals.len(), null),
        .function_of_declaration = filled(allocator, u32, declaration_count, no_function),
        .value_globals = filled(allocator, Value, pool_count, null),
        .zero_globals = filled(allocator, Value, pool_count, null),
    };
}

fn filled(allocator: std.mem.Allocator, T: type, count: usize, value: T) []T {
    const items = allocator.alloc(T, count) catch @panic("OOM");
    @memset(items, value);
    return items;
}

fn bits(allocator: std.mem.Allocator, count: usize) std.DynamicBitSetUnmanaged {
    return std.DynamicBitSetUnmanaged.initEmpty(allocator, count) catch @panic("OOM");
}

pub fn deinit(self: *LLVMLowerer) void {
    const allocator = self.allocator;
    self.types.deinit();
    if (self.debug) |*debug| debug.deinit();
    allocator.free(self.functions);
    allocator.free(self.function_types);
    allocator.free(self.thunks);
    self.externals.deinit(allocator);
    self.results_in_memory.deinit(allocator);
    allocator.free(self.fixed_parameters);
    allocator.free(self.globals);
    allocator.free(self.function_of_declaration);
    allocator.free(self.value_globals);
    allocator.free(self.zero_globals);
    self.value_stack.deinit(allocator);
    self.type_stack.deinit(allocator);
    self.instruction_values.deinit(allocator);
    self.blocks.deinit(allocator);
    self.block_exits.deinit(allocator);
    self.reachable.deinit(allocator);
    self.block_order.deinit(allocator);
    self.walk.deinit(allocator);
    self.pending_phis.deinit(allocator);
    llvm.LLVMDisposeBuilder(self.builder);
    llvm.LLVMDisposeBuilder(self.alloca_builder);
    llvm.LLVMDisposeModule(self.module);
    llvm.LLVMContextDispose(self.context);
}

pub fn lower(self: *LLVMLowerer) void {
    const function_count = self.ir.functions.len();
    // an external function declared with several parameter lists is one variadic c function
    // (`printf`), the parameters all of its lists share are fixed
    const resolver = self.high.resolver;
    for (self.ir.functions.column(.decl), 0..) |declaration, i| {
        if (declaration == .none or self.ir.functions.column(.blocks)[i] != 0) continue;
        const name = resolver.decl_pool.get(declaration, .name);
        const these = self.pool.get(self.ir.functions.column(.ty)[i]).function_type.parameters;
        var shared = these.len;
        var lists: u32 = 0;
        var overload = resolver.scopes.globals.get(name) orelse continue;
        while (overload != .none) : (overload = resolver.decl_pool.get(overload, .next_overload)) {
            if (resolver.bodies.body_index_of.contains(overload)) continue;
            const value_type = resolver.decl_pool.get(overload, .value_type);
            if (value_type == .none or self.pool.tag(value_type) != .function_type) continue;
            lists += 1;
            const others = self.pool.get(value_type).function_type.parameters;
            shared = @min(shared, others.len);
            for (0..shared) |k| if (these[k] != others[k]) {
                shared = k;
                break;
            };
        }
        if (lists > 1) self.fixed_parameters[i] = @intCast(shared);
    }
    for (0..function_count) |i| self.declare_function(@intCast(i));
    for (self.ir.globals.column(.decl), 0..) |declaration, i| self.declare_global(declaration, i);
    for (0..function_count) |i| self.lower_function(@intCast(i));
    if (self.debug) |*debug| debug.leave_function(self.builder);
    self.define_main();
    if (!self.options.libc and builtin.os.tag == .linux) runtime.define(self);
    if (self.debug) |*debug| debug.finish();

    var message: [*c]u8 = null;
    if (llvm.LLVMVerifyModule(self.module, llvm.LLVMReturnStatusAction, &message) != 0) {
        llvm.LLVMDumpModule(self.module);
        std.debug.panic("the lowered llvm module is invalid:\n{s}", .{message});
    }
}

// declarations

fn declare_function(self: *LLVMLowerer, function_index: u32) void {
    const function = self.ir.functions.get(function_index).?;
    if (function.decl != .none) {
        self.function_of_declaration[@intFromEnum(function.decl)] = function_index;
    }
    const is_external = function.blocks == 0 and function.decl != .none;
    const function_type = self.pool.get(function.ty).function_type;
    const has_result = Types.has_value(function_type.return_type);
    const result_passing: c_abi.Passing = if (has_result)
        c_abi.classify(self, function_type.return_type)
    else
        .{ .how = .direct, .lowered = self.types.unit };
    const in_memory = if (is_external)
        has_result and result_passing.how == .indirect
    else
        self.types.is_in_memory(function_type.return_type);
    self.externals.setValue(function_index, is_external);
    self.results_in_memory.setValue(function_index, in_memory);

    // the result slot, the captures (their types only the params of the body know), the
    // parameters; of a variadic c function only the fixed ones
    const mark = self.type_stack.items.len;
    defer self.type_stack.shrinkRetainingCapacity(mark);
    const first = @intFromBool(in_memory);
    const fixed = @min(function_type.parameters.len, self.fixed_parameters[function_index]);
    const count = first + function.captures + fixed;
    self.type_stack.appendNTimes(self.allocator, self.types.pointer, count) catch @panic("OOM");
    const parameters = self.type_stack.items[mark..];
    const declared = parameters[first + function.captures ..];
    for (function_type.parameters[0..fixed], declared) |parameter, *lowered| {
        lowered.* = if (is_external)
            c_abi.classify(self, parameter).lowered
        else
            self.types.value_of(parameter);
    }
    const instructions = self.ir.insts.columns();
    for (function.first_inst..function.first_inst + function.insts) |i| {
        if (instructions.op[i] != .param or instructions.a[i] >= function.captures) continue;
        parameters[first + instructions.a[i]] = self.types.value_of(instructions.ty[i]);
    }
    const result = if (in_memory or !has_result)
        llvm.LLVMVoidTypeInContext(self.context)
    else if (is_external)
        result_passing.lowered
    else
        self.types.value_of(function_type.return_type);
    const variadic: c_int = @intFromBool(self.fixed_parameters[function_index] != no_function);
    const lowered_type = llvm.LLVMFunctionType(result, parameters.ptr, @intCast(count), variadic);
    self.function_types[function_index] = lowered_type;

    const name = self.name_of(function.decl, "$init");
    // the lists of a variadic c function are one symbol of one type
    if (is_external) if (llvm.LLVMGetNamedFunction(self.module, name)) |existing| {
        self.functions[function_index] = existing;
        self.function_types[function_index] = llvm.LLVMGlobalGetValueType(existing);
        return;
    };
    const lowered = llvm.LLVMAddFunction(self.module, name, lowered_type);
    self.functions[function_index] = lowered;
    if (in_memory) self.add_result_attributes(lowered, function_type.return_type);
    if (is_external) {
        self.add_c_attributes(lowered, llvm.LLVMAttributeReturnIndex, function_type.return_type);
        for (function_type.parameters[0..fixed], 0..) |parameter, i| {
            self.add_c_attributes(lowered, @intCast(first + i + 1), parameter);
        }
        return;
    }
    llvm.LLVMSetLinkage(lowered, llvm.LLVMInternalLinkage);
    self.add_function_attributes(lowered);
    for (0..function_type.parameters.len) |i| {
        const parameter = self.pool.get(function.ty).function_type.parameters[i];
        const position: c_uint = @intCast(first + function.captures + i);
        self.add_value_attributes(lowered, position, parameter);
    }
}

fn declare_global(self: *LLVMLowerer, declaration: DeclPool.Index, global_index: usize) void {
    const global = self.ir.globals.get(@intCast(global_index)).?;
    const initializer = if (global.init == .none)
        llvm.LLVMConstNull(self.types.of(global.ty))
    else
        constants.lower(self, global.init, global.ty);
    const lowered = llvm.LLVMAddGlobal(
        self.module,
        llvm.LLVMTypeOf(initializer),
        self.name_of(declaration, "global"),
    );
    llvm.LLVMSetInitializer(lowered, initializer);
    llvm.LLVMSetLinkage(lowered, llvm.LLVMInternalLinkage);
    llvm.LLVMSetAlignment(lowered, self.alignment_of(global.ty));
    self.globals[global_index] = lowered;
}

// the entry: the global initializers, then `$main` with the arguments it asks for. with the c
// library its `main`, which its startup calls. without it `_start`: linux jumps there with
// argc and argv on the stack and takes the exit code by a system call, macos' dyld calls it
// like `main`
fn define_main(self: *LLVMLowerer) void {
    const main_function = for (self.ir.functions.column(.decl), 0..) |declaration, i| {
        if (declaration == .none) continue;
        if (self.high.resolver.decl_pool.get(declaration, .name) == .main) break i;
    } else return;

    const int = llvm.LLVMInt32TypeInContext(self.context);
    const is_bare_linux = !self.options.libc and builtin.os.tag == .linux;
    const argument_count, const argument_vector = if (is_bare_linux) blk: {
        // the stack is aligned for the call of `mond_start`, which gets its address
        llvm.LLVMAppendModuleInlineAsm(self.module, start_assembly.ptr, start_assembly.len);
        var parameters = [_]Type{self.types.pointer};
        const void_type = llvm.LLVMVoidTypeInContext(self.context);
        const start_type = llvm.LLVMFunctionType(void_type, &parameters, 1, 0);
        const start = llvm.LLVMAddFunction(self.module, "mond_start", start_type);
        llvm.LLVMSetVisibility(start, llvm.LLVMHiddenVisibility);
        self.add_function_attributes(start);
        llvm.LLVMPositionBuilderAtEnd(
            self.builder,
            llvm.LLVMAppendBasicBlockInContext(self.context, start, "entry"),
        );
        const stack = llvm.LLVMGetParam(start, 0);
        const count = llvm.LLVMBuildLoad2(self.builder, self.types.length, stack, "");
        var offset = [_]Value{llvm.LLVMConstInt(self.types.length, 1, 0)};
        const vector =
            llvm.LLVMBuildInBoundsGEP2(self.builder, self.types.pointer, stack, &offset, 1, "");
        break :blk .{ llvm.LLVMBuildTrunc(self.builder, count, int, ""), vector };
    } else blk: {
        var parameters = [_]Type{ int, self.types.pointer };
        const main_type = llvm.LLVMFunctionType(int, &parameters, parameters.len, 0);
        const name = if (self.options.libc) "main" else "_start";
        const main = llvm.LLVMAddFunction(self.module, name, main_type);
        self.add_function_attributes(main);
        llvm.LLVMPositionBuilderAtEnd(
            self.builder,
            llvm.LLVMAppendBasicBlockInContext(self.context, main, "entry"),
        );
        break :blk .{ llvm.LLVMGetParam(main, 0), llvm.LLVMGetParam(main, 1) };
    };
    const init_function = self.ir.init_fn;
    _ = self.build_call(self.function_types[init_function], self.functions[init_function], &.{});

    // `()` or `(argc, argv)`
    const main_type_index = self.ir.functions.column(.ty)[main_function];
    const parameters = self.pool.get(main_type_index).function_type.parameters;
    const mark = self.value_stack.items.len;
    defer self.value_stack.shrinkRetainingCapacity(mark);
    if (parameters.len == 2) {
        const count_type = self.types.of(parameters[0]);
        const signed: c_int = @intFromBool(self.is_signed(parameters[0]));
        const count = llvm.LLVMBuildIntCast2(self.builder, argument_count, count_type, signed, "");
        self.value_stack.append(self.allocator, count) catch @panic("OOM");
        self.value_stack.append(self.allocator, argument_vector) catch @panic("OOM");
    }
    const result = self.build_call(
        self.function_types[main_function],
        self.functions[main_function],
        self.value_stack.items[mark..],
    );

    const return_type = self.pool.get(main_type_index).function_type.return_type;
    const signed: c_int = @intFromBool(self.is_signed(return_type));
    const exit_code = if (!Types.has_value(return_type))
        llvm.LLVMConstInt(int, 0, 0)
    else
        llvm.LLVMBuildIntCast2(self.builder, result, int, signed, "");
    if (!is_bare_linux) {
        _ = llvm.LLVMBuildRet(self.builder, exit_code);
        return;
    }
    // exit_group(exit code)
    const length = self.types.length;
    var exit_parameters = [_]Type{ length, length };
    const void_type = llvm.LLVMVoidTypeInContext(self.context);
    const exit_type = llvm.LLVMFunctionType(void_type, &exit_parameters, 2, 0);
    const exit_assembly, const constraints, const exit_number = switch (builtin.cpu.arch) {
        .x86_64 => .{ "syscall", "{ax},{di},~{rcx},~{r11},~{memory}", 231 },
        .aarch64 => .{ "svc #0", "{x8},{x0},~{memory}", 94 },
        else => @compileError("mond starts programs only on aarch64 and x86-64"),
    };
    const exit = llvm.LLVMGetInlineAsm(
        exit_type,
        @constCast(exit_assembly.ptr),
        exit_assembly.len,
        @constCast(constraints.ptr),
        constraints.len,
        1,
        0,
        llvm.LLVMInlineAsmDialectATT,
        0,
    );
    const code = llvm.LLVMBuildSExt(self.builder, exit_code, length, "");
    _ = self.build_call(exit_type, exit, &.{ llvm.LLVMConstInt(length, exit_number, 0), code });
    _ = llvm.LLVMBuildUnreachable(self.builder);
}

// a call of the kernel. linux gives -errno itself, macos sets the carry flag and gives errno
const system_call = switch (builtin.os.tag) {
    .linux => switch (builtin.cpu.arch) {
        .x86_64 => "syscall",
        .aarch64 => "svc #0",
        else => @compileError("mond calls the kernel only on aarch64 and x86-64"),
    },
    .macos => switch (builtin.cpu.arch) {
        .x86_64 => "syscall\n\tjnc 1f\n\tneg %rax\n1:",
        .aarch64 => "svc #0x80\n\tcneg x0, x0, cs",
        else => @compileError("mond calls the kernel only on aarch64 and x86-64"),
    },
    else => @compileError("mond calls the kernel only on linux and macos"),
};

// per argument count: the result's register, the number's, the arguments', and what the kernel
// changes besides (macos may give a second result)
const system_call_constraints = blk: {
    const Registers = struct {
        result: []const u8,
        number: []const u8,
        arguments: [6][]const u8,
        clobbers: []const u8,
    };
    const registers: Registers = switch (builtin.cpu.arch) {
        .x86_64 => .{
            .result = "={rax}",
            .number = "{rax}",
            .arguments = .{ "{rdi}", "{rsi}", "{rdx}", "{r10}", "{r8}", "{r9}" },
            .clobbers = ",~{rcx},~{r11},~{rdx},~{memory},~{flags}",
        },
        .aarch64 => .{
            .result = "={x0}",
            .number = if (builtin.os.tag == .macos) "{x16}" else "{x8}",
            .arguments = .{ "{x0}", "{x1}", "{x2}", "{x3}", "{x4}", "{x5}" },
            .clobbers = ",~{memory},~{cc}",
        },
        else => @compileError("mond calls the kernel only on aarch64 and x86-64"),
    };
    var all: [7][]const u8 = undefined;
    for (&all, 0..) |*constraints, count| {
        var text: []const u8 = registers.result ++ "," ++ registers.number;
        for (registers.arguments[0..count]) |argument| text = text ++ "," ++ argument;
        constraints.* = text ++ registers.clobbers;
    }
    break :blk all;
};

// what `$asm` may change: every register llvm allocates (the frame pointer and on aarch64 the
// platform register aside), the flags and memory
const assembly_clobbers = blk: {
    @setEvalBranchQuota(100_000);
    var clobbers: []const u8 = "~{memory}";
    const registers: []const []const u8 = switch (builtin.cpu.arch) {
        .x86_64 => &.{ "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "dirflag", "fpsr", "flags" },
        .aarch64 => &.{ "x30", "cc" },
        else => @compileError("mond builds code only for aarch64 and x86-64"),
    };
    for (registers) |register| clobbers = clobbers ++ ",~{" ++ register ++ "}";
    const numbered: []const [3]u8 = switch (builtin.cpu.arch) {
        .x86_64 => &.{ .{ 'r', 8, 15 }, .{ 'x', 0, 15 } },
        .aarch64 => &.{ .{ 'x', 0, 17 }, .{ 'x', 19, 28 }, .{ 'q', 0, 31 } },
        else => unreachable,
    };
    for (numbered) |range| for (range[1]..range[2] + 1) |n| {
        const is_vector = range[0] == 'x' and builtin.cpu.arch == .x86_64;
        const prefix = if (is_vector) "xmm" else &[_]u8{range[0]};
        clobbers = clobbers ++ std.fmt.comptimePrint(",~{{{s}{d}}}", .{ prefix, n });
    };
    break :blk clobbers;
};

// `_start` on linux: the stack holds argc, then argv; `mond_start` gets its address
const start_assembly = switch (builtin.cpu.arch) {
    .x86_64 =>
    \\.text
    \\.globl _start
    \\.type _start,@function
    \\_start:
    \\  xor %ebp, %ebp
    \\  mov %rsp, %rdi
    \\  and $-16, %rsp
    \\  call mond_start
    \\  ud2
    ,
    .aarch64 =>
    \\.text
    \\.globl _start
    \\.type _start,%function
    \\_start:
    \\  mov x29, #0
    \\  mov x30, #0
    \\  mov x0, sp
    \\  bl mond_start
    \\  brk #0
    ,
    else => "",
};

// a function value of a function: called with the environment first, which holds its captures
pub fn thunk(self: *LLVMLowerer, function_index: u32) Value {
    if (self.thunks[function_index]) |known| return known;
    const function = self.ir.functions.get(function_index).?;
    const pool_type = self.pool.get(function.ty).function_type;
    const in_memory = self.types.is_in_memory(pool_type.return_type);
    const lowered = llvm.LLVMAddFunction(
        self.module,
        self.name_of(function.decl, "$init"),
        self.closure_function_type(function.ty),
    );
    llvm.LLVMSetLinkage(lowered, llvm.LLVMInternalLinkage);
    self.add_function_attributes(lowered);
    self.thunks[function_index] = lowered;

    // built between instructions of another function: its place and location come back after
    const saved_block = llvm.LLVMGetInsertBlock(self.builder);
    const saved_location = llvm.LLVMGetCurrentDebugLocation2(self.builder);
    defer {
        if (saved_block != null) llvm.LLVMPositionBuilderAtEnd(self.builder, saved_block);
        llvm.LLVMSetCurrentDebugLocation2(self.builder, saved_location);
    }
    llvm.LLVMSetCurrentDebugLocation2(self.builder, null);
    const entry = llvm.LLVMAppendBasicBlockInContext(self.context, lowered, "entry");
    llvm.LLVMPositionBuilderAtEnd(self.builder, entry);

    // (result slot, environment, parameters) to (result slot, captures, parameters)
    const first: c_uint = @intFromBool(in_memory);
    const captures_at: usize = @intFromBool(self.results_in_memory.isSet(function_index));
    const target_type = self.function_types[function_index];
    const type_mark = self.type_stack.items.len;
    defer self.type_stack.shrinkRetainingCapacity(type_mark);
    const target_parameter_count = llvm.LLVMCountParamTypes(target_type);
    self.type_stack.appendNTimes(self.allocator, null, target_parameter_count) catch {
        @panic("OOM");
    };
    llvm.LLVMGetParamTypes(target_type, self.type_stack.items[type_mark..].ptr);
    const environment_type = llvm.LLVMStructTypeInContext(
        self.context,
        self.type_stack.items[type_mark + captures_at ..].ptr,
        function.captures,
        0,
    );

    const mark = self.value_stack.items.len;
    defer self.value_stack.shrinkRetainingCapacity(mark);
    const environment = llvm.LLVMGetParam(lowered, first);
    for (0..function.captures) |i| {
        const position: c_uint = @intCast(i);
        const field =
            llvm.LLVMBuildStructGEP2(self.builder, environment_type, environment, position, "");
        const field_type = llvm.LLVMStructGetTypeAtIndex(environment_type, position);
        const capture = llvm.LLVMBuildLoad2(self.builder, field_type, field, "");
        self.value_stack.append(self.allocator, capture) catch @panic("OOM");
    }
    for (0..pool_type.parameters.len) |i| {
        const parameter = llvm.LLVMGetParam(lowered, first + 1 + @as(c_uint, @intCast(i)));
        self.value_stack.append(self.allocator, parameter) catch @panic("OOM");
    }
    const result_slot = if (in_memory) llvm.LLVMGetParam(lowered, 0) else null;
    const result = self.call_function(function_index, mark, result_slot);
    if (in_memory or !Types.has_value(pool_type.return_type)) {
        _ = llvm.LLVMBuildRetVoid(self.builder);
    } else {
        _ = llvm.LLVMBuildRet(self.builder, result);
    }
    return lowered;
}

// `(ptr result?, ptr env, parameters..) -> result`, how a function value is called
pub fn closure_function_type(self: *LLVMLowerer, function_type_index: Index) Type {
    const function_type = self.pool.get(function_type_index).function_type;
    const in_memory = self.types.is_in_memory(function_type.return_type);
    const mark = self.type_stack.items.len;
    defer self.type_stack.shrinkRetainingCapacity(mark);
    const prefix: usize = 1 + @as(usize, @intFromBool(in_memory));
    self.type_stack.appendNTimes(self.allocator, self.types.pointer, prefix) catch @panic("OOM");
    for (0..function_type.parameters.len) |i| {
        const parameter = self.pool.get(function_type_index).function_type.parameters[i];
        self.type_stack.append(self.allocator, self.types.value_of(parameter)) catch {
            @panic("OOM");
        };
    }
    const result = if (in_memory or !Types.has_value(function_type.return_type))
        llvm.LLVMVoidTypeInContext(self.context)
    else
        self.types.value_of(function_type.return_type);
    const parameters = self.type_stack.items[mark..];
    return llvm.LLVMFunctionType(result, parameters.ptr, @intCast(parameters.len), 0);
}

// zero-terminated in `name_buffer` until the next call, llvm copies names
fn name_of(self: *LLVMLowerer, declaration: DeclPool.Index, fallback: [:0]const u8) [*c]const u8 {
    if (declaration == .none) return fallback;
    const name = self.high.resolver.decl_pool.get(declaration, .name);
    if (name == .empty or name == .none) return fallback;
    const text = self.high.resolver.name_pool.text_of(name);
    const length = @min(text.len, self.name_buffer.len);
    @memcpy(self.name_buffer[0..length], text[0..length]);
    self.name_buffer[length] = 0;
    return &self.name_buffer;
}

// attributes

// nothing unwinds, and with debug info frames keep their pointer for the debugger's backtraces
fn add_function_attributes(self: *LLVMLowerer, function: Value) void {
    const index: c_uint = @bitCast(@as(c_int, llvm.LLVMAttributeFunctionIndex));
    self.add_attribute(function, index, "nounwind", 0);
    if (self.debug == null) return;
    const key = "frame-pointer";
    const value = "all";
    const attribute = llvm.LLVMCreateStringAttribute(self.context, key, key.len, value, value.len);
    llvm.LLVMAddAttributeAtIndex(function, index, attribute);
}

// the result slot is the caller's own memory, only written by the callee
fn add_result_attributes(self: *LLVMLowerer, function: Value, result_type: Index) void {
    const kind = llvm.LLVMGetEnumAttributeKindForName("sret", "sret".len);
    const sret = llvm.LLVMCreateTypeAttribute(self.context, kind, self.types.of(result_type));
    llvm.LLVMAddAttributeAtIndex(function, 1, sret);
    self.add_attribute(function, 1, "noalias", 0);
    self.add_memory_attributes(function, 1, result_type);
}

// a value in memory is an immutable copy nobody writes during the call, and the callee copies
// it before keeping it: llvm may read it at will and keep it in registers
fn add_value_attributes(
    self: *LLVMLowerer,
    function: Value,
    position: c_uint,
    value_type: Index,
) void {
    if (!self.types.is_in_memory(value_type)) return;
    const index = position + 1;
    self.add_attribute(function, index, "noalias", 0);
    self.add_attribute(function, index, "readonly", 0);
    // `captures(none)` since llvm 21, before that `nocapture`
    self.add_attribute(function, index, "captures", 0);
    self.add_attribute(function, index, "nocapture", 0);
    self.add_memory_attributes(function, index, value_type);
}

fn add_memory_attributes(
    self: *LLVMLowerer,
    function: Value,
    index: c_uint,
    value_type: Index,
) void {
    self.add_attribute(function, index, "nonnull", 0);
    self.add_attribute(function, index, "align", self.alignment_of(value_type));
    const size = self.pool.layout(value_type).size;
    if (size > 0) self.add_attribute(function, index, "dereferenceable", size);
}

// how c widens a small int, and a record x86-64 copies itself (`byval`)
fn add_c_attributes(self: *LLVMLowerer, function: Value, index: c_uint, value_type: Index) void {
    if (!Types.has_value(value_type)) return;
    switch (c_abi.classify(self, value_type).how) {
        .sign_extended => self.add_attribute(function, index, "signext", 0),
        .zero_extended => self.add_attribute(function, index, "zeroext", 0),
        .indirect => if (builtin.cpu.arch == .x86_64 and index != llvm.LLVMAttributeReturnIndex) {
            const kind = llvm.LLVMGetEnumAttributeKindForName("byval", "byval".len);
            const memory_type = self.types.of(value_type);
            const byval = llvm.LLVMCreateTypeAttribute(self.context, kind, memory_type);
            llvm.LLVMAddAttributeAtIndex(function, index, byval);
            self.add_attribute(function, index, "align", self.alignment_of(value_type));
        },
        .direct, .coerced, .function => {},
    }
}

// skipped when this llvm doesn't know the attribute
fn add_attribute(
    self: *LLVMLowerer,
    function: Value,
    index: c_uint,
    name: []const u8,
    value: u64,
) void {
    const kind = llvm.LLVMGetEnumAttributeKindForName(name.ptr, name.len);
    if (kind == 0) return;
    const attribute = llvm.LLVMCreateEnumAttribute(self.context, kind, value);
    llvm.LLVMAddAttributeAtIndex(function, index, attribute);
}

// functions

fn lower_function(self: *LLVMLowerer, function_index: u32) void {
    const function = self.ir.functions.get(function_index).?;
    if (function.blocks == 0) return;
    self.function = function;
    self.function_index = function_index;
    self.llvm_function = self.functions[function_index];
    self.trap_block = null;
    self.pending_phis.clearRetainingCapacity();
    self.instruction_values.clearRetainingCapacity();
    self.instruction_values.appendNTimes(self.allocator, null, function.insts) catch @panic("OOM");
    if (self.debug) |*debug| {
        const name = std.mem.span(self.name_of(function.decl, "$init"));
        const origin = if (function.decl == .none)
            0
        else
            self.high.resolver.decl_pool.get(function.decl, .node);
        debug.enter_function(self.llvm_function, name, origin, self.options.optimized);
    }

    const allocas = llvm.LLVMAppendBasicBlockInContext(self.context, self.llvm_function, "entry");
    self.blocks.clearRetainingCapacity();
    for (0..function.blocks) |_| {
        const block = llvm.LLVMAppendBasicBlockInContext(self.context, self.llvm_function, "");
        self.blocks.append(self.allocator, block) catch @panic("OOM");
    }
    self.block_exits.clearRetainingCapacity();
    self.block_exits.appendSlice(self.allocator, self.blocks.items) catch @panic("OOM");
    llvm.LLVMPositionBuilderAtEnd(self.alloca_builder, allocas);
    const into_first = llvm.LLVMBuildBr(self.alloca_builder, self.blocks.items[0]);
    llvm.LLVMPositionBuilderBefore(self.alloca_builder, into_first);

    // in reverse postorder every value is lowered before its uses, phis aside
    self.order_blocks();
    for (self.block_order.items) |block| self.lower_block(block);
    for (self.blocks.items, 0..) |block, i| {
        if (self.reachable.isSet(i)) continue;
        llvm.LLVMPositionBuilderAtEnd(self.builder, block);
        _ = llvm.LLVMBuildUnreachable(self.builder);
    }

    // an operand pairs with the predecessor at its position, unreachable ones branch nowhere
    for (self.pending_phis.items) |pending| {
        const block = self.ir.blocks.get(self.function.first_block + pending.block).?;
        const predecessors = self.ir.list(block.preds);
        const phi_type = pending.instruction.ty;
        const in_memory = self.types.is_in_memory(phi_type);
        for (predecessors, self.ir.list(pending.instruction.b)) |predecessor, operand_ref| {
            if (!self.reachable.isSet(predecessor)) continue;
            const exit = self.block_exits.items[predecessor];
            const incoming = self.operand(@enumFromInt(operand_ref));
            if (in_memory) {
                const terminator = llvm.LLVMGetBasicBlockTerminator(exit);
                llvm.LLVMPositionBuilderBefore(self.builder, terminator);
                self.copy(pending.phi, incoming, phi_type);
                continue;
            }
            var incoming_value = [_]Value{incoming};
            var incoming_block = [_]Block{exit};
            llvm.LLVMAddIncoming(pending.phi, &incoming_value, &incoming_block, 1);
        }
    }
}

fn lower_block(self: *LLVMLowerer, block_index: u32) void {
    const block = self.ir.blocks.get(self.function.first_block + block_index).?;
    llvm.LLVMPositionBuilderAtEnd(self.builder, self.blocks.items[block_index]);
    const first = self.function.first_inst + block.start;
    for (first..first + block.len) |i| {
        const instruction = self.ir.insts.get(@intCast(i)).?;
        if (self.debug) |*debug| debug.locate(self.builder, instruction.origin);
        self.instruction_index = @intCast(i);
        const local: u32 = @intCast(i - self.function.first_inst);
        self.instruction_values.items[local] = self.lower_instruction(instruction, block_index);
    }
    self.block_exits.items[block_index] = llvm.LLVMGetInsertBlock(self.builder);
}

// the reachable blocks in reverse postorder into `block_order`
fn order_blocks(self: *LLVMLowerer) void {
    self.reachable.resize(self.allocator, self.function.blocks, false) catch @panic("OOM");
    self.reachable.unsetAll();
    self.block_order.clearRetainingCapacity();
    self.walk.clearRetainingCapacity();
    self.walk.append(self.allocator, .{ 0, 0 }) catch @panic("OOM");
    self.reachable.set(0);
    while (self.walk.items.len > 0) {
        const top = &self.walk.items[self.walk.items.len - 1];
        const following = self.successors(top[0]);
        if (top[1] == following.count) {
            self.block_order.append(self.allocator, top[0]) catch @panic("OOM");
            _ = self.walk.pop();
            continue;
        }
        const successor = following.at(self, top[1]);
        top[1] += 1;
        if (self.reachable.isSet(successor)) continue;
        self.reachable.set(successor);
        self.walk.append(self.allocator, .{ successor, 0 }) catch @panic("OOM");
    }
    std.mem.reverse(u32, self.block_order.items);
}

// the blocks a block's terminator may continue in
const Successors = struct {
    terminator: HighIr.Inst,
    count: u32,

    fn at(self: Successors, lowerer: *LLVMLowerer, position: u32) u32 {
        const terminator = self.terminator;
        return switch (terminator.op) {
            .br => terminator.a,
            .cond_br => lowerer.ir.list(terminator.b)[position],
            // the default, then pairs of a key and its block
            .@"switch" => lowerer.ir.list(terminator.b)[position * 2],
            else => unreachable,
        };
    }
};

fn successors(self: *LLVMLowerer, block_index: u32) Successors {
    const block = self.ir.blocks.get(self.function.first_block + block_index).?;
    const terminator = self.ir.insts.get(self.function.first_inst + block.start + block.len - 1).?;
    const count: u32 = switch (terminator.op) {
        .br => 1,
        .cond_br => 2,
        .@"switch" => @intCast((self.ir.list(terminator.b).len + 1) / 2),
        else => 0,
    };
    return .{ .terminator = terminator, .count = count };
}

// instructions

fn lower_instruction(self: *LLVMLowerer, instruction: HighIr.Inst, block: u32) Value {
    const builder = self.builder;
    const result_type = instruction.ty;
    const a: Ref = @enumFromInt(instruction.a);
    const b: Ref = @enumFromInt(instruction.b);
    return switch (instruction.op) {
        .param => {
            const result_slots = @intFromBool(self.results_in_memory.isSet(self.function_index));
            return llvm.LLVMGetParam(self.llvm_function, instruction.a + result_slots);
        },
        .phi => {
            const phi = if (self.types.is_in_memory(result_type))
                self.entry_alloca(self.types.of(result_type))
            else
                llvm.LLVMBuildPhi(builder, self.types.value_of(result_type), "");
            const pending: PendingPhi = .{ .phi = phi, .block = block, .instruction = instruction };
            self.pending_phis.append(self.allocator, pending) catch @panic("OOM");
            return phi;
        },
        .undef => if (self.types.is_in_memory(result_type))
            self.entry_alloca(self.types.of(result_type))
        else
            llvm.LLVMGetUndef(self.types.of(result_type)),
        .zeroed => if (self.types.is_in_memory(result_type))
            constants.zeros(self, result_type)
        else
            llvm.LLVMConstNull(self.types.of(result_type)),
        .add, .sub, .mul, .div, .rem, .shl, .shr, .bit_and, .bit_or, .bit_xor => {
            return self.arithmetic(instruction.op, result_type, self.operand(a), self.operand(b));
        },
        .eq, .ne, .lt, .gt, .le, .ge => {
            const left = self.operand(a);
            const right = self.operand(b);
            return values.compare(self, instruction.op, self.type_of_ref(a), left, right);
        },
        .bytes_eq => {
            const left = self.operand(a);
            const right = self.operand(b);
            return values.bytes_equal(self, self.type_of_ref(a), left, right);
        },
        .neg => if (self.pool.properties(result_type).is_float)
            llvm.LLVMBuildFNeg(builder, self.operand(a), "")
        else
            llvm.LLVMBuildNeg(builder, self.operand(a), ""),
        .not => llvm.LLVMBuildNot(builder, self.operand(a), ""),
        .convert => values.convert(self, @enumFromInt(instruction.b), result_type, a),
        .cast => values.cast(self, @enumFromInt(instruction.b), result_type, a),
        .alloca => {
            const pointee = self.types.of(self.pool.pointee(result_type));
            // with a length: the elements of a runtime-length array, allocated where it is made
            if (a == .none) return self.entry_alloca(pointee);
            return llvm.LLVMBuildArrayAlloca(builder, pointee, self.operand(a), "");
        },
        .load => {
            const pointer = self.operand(a);
            // a runtime-length array is the address its pointer holds
            if (self.types.is_runtime_array(result_type)) return pointer;
            // a value in memory is a copy, the memory loaded from may change later
            if (self.types.is_in_memory(result_type)) {
                const copied = self.entry_alloca(self.types.of(result_type));
                self.copy(copied, pointer, result_type);
                return copied;
            }
            const loaded = llvm.LLVMBuildLoad2(builder, self.types.of(result_type), pointer, "");
            if (self.is_packed_field(a)) llvm.LLVMSetAlignment(loaded, 1);
            return loaded;
        },
        .store => {
            const stored_type = self.type_of_ref(b);
            if (!self.types.is_in_memory(stored_type)) {
                const stored = self.operand(b);
                const store = llvm.LLVMBuildStore(builder, stored, self.operand(a));
                if (self.is_packed_field(a)) llvm.LLVMSetAlignment(store, 1);
            } else if (self.is_zeroed(b)) {
                // a zeroed value is cleared in place rather than copied from zeros
                const zero = llvm.LLVMConstInt(llvm.LLVMInt8TypeInContext(self.context), 0, 0);
                const size = self.pool.layout(stored_type).size;
                const length = llvm.LLVMConstInt(self.types.length, size, 0);
                const alignment = self.alignment_of(stored_type);
                _ = llvm.LLVMBuildMemSet(builder, self.operand(a), zero, length, alignment);
            } else {
                self.copy(self.operand(a), self.operand(b), stored_type);
            }
            return null;
        },
        .field_ptr => values.field_pointer(self, a, instruction.b),
        .index_ptr => values.index_pointer(self, result_type, a, b),
        .dyn => {
            const bounds = self.ir.list(instruction.b);
            const element = self.pool.get(result_type).array_type.element;
            const start = self.index_value(@enumFromInt(bounds[0]));
            var offset = [_]Value{start};
            const element_type = self.types.of(element);
            const base = self.operand(a);
            return llvm.LLVMBuildInBoundsGEP2(builder, element_type, base, &offset, 1, "");
        },
        .aggregate => values.aggregate(self, result_type, self.ir.list(instruction.b)),
        .select => {
            const choices = self.ir.list(instruction.b);
            const then_value = self.operand(@enumFromInt(choices[0]));
            const else_value = self.operand(@enumFromInt(choices[1]));
            return llvm.LLVMBuildSelect(builder, self.operand(a), then_value, else_value, "");
        },
        .extract => values.extract(self, result_type, a, instruction.b),
        .variant_make => values.variant_make(self, result_type, instruction.a, b),
        .variant_tag => values.variant_tag(self, self.type_of_ref(a), self.operand(a)),
        .variant_payload => {
            const variant_type = self.type_of_ref(a);
            return values.variant_payload(self, result_type, variant_type, self.operand(a));
        },
        .call => self.call(result_type, a, self.ir.list(instruction.b)),
        .closure => self.closure(instruction.a, self.ir.list(instruction.b)),
        .syscall => {
            // every argument one 64-bit register, the result the kernel's or -errno
            const length = self.types.length;
            const mark = self.value_stack.items.len;
            defer self.value_stack.shrinkRetainingCapacity(mark);
            const operands = self.ir.list(instruction.b);
            for (operands, 0..) |operand_ref, i| {
                const ref: Ref = @enumFromInt(operand_ref);
                const value_type = self.type_of_ref(ref);
                const value = self.operand(ref);
                const signed: c_int = @intFromBool(self.is_signed(value_type));
                var widened = if (llvm.LLVMTypeOf(value) == self.types.pointer)
                    llvm.LLVMBuildPtrToInt(builder, value, length, "")
                else
                    llvm.LLVMBuildIntCast2(builder, value, length, signed, "");
                // macos on x86-64 takes the class of its calls in the number
                if (i == 0 and builtin.os.tag == .macos and builtin.cpu.arch == .x86_64) {
                    const unix_class = llvm.LLVMConstInt(length, 0x2000000, 0);
                    widened = llvm.LLVMBuildOr(builder, widened, unix_class, "");
                }
                self.value_stack.append(self.allocator, widened) catch @panic("OOM");
            }
            const arguments = self.value_stack.items[mark..];
            const constraints = system_call_constraints[arguments.len - 1];
            var parameter_types: [7]Type = @splat(length);
            const count: c_uint = @intCast(arguments.len);
            const call_type = llvm.LLVMFunctionType(length, &parameter_types, count, 0);
            const code = llvm.LLVMGetInlineAsm(
                call_type,
                @constCast(system_call.ptr),
                system_call.len,
                @constCast(constraints.ptr),
                constraints.len,
                1,
                0,
                llvm.LLVMInlineAsmDialectATT,
                0,
            );
            return self.build_call(call_type, code, arguments);
        },
        .inline_asm => {
            // what it touches is unknown: all memory, the flags and every register llvm may
            // allocate. it is kept where it stands
            const text = self.pool.get(a.value()).string_value;
            const void_type = llvm.LLVMVoidTypeInContext(self.context);
            const asm_type = llvm.LLVMFunctionType(void_type, null, 0, 0);
            const code = llvm.LLVMGetInlineAsm(
                asm_type,
                @constCast(text.ptr),
                text.len,
                @constCast(assembly_clobbers.ptr),
                assembly_clobbers.len,
                1,
                0,
                llvm.LLVMInlineAsmDialectATT,
                0,
            );
            _ = self.build_call(asm_type, code, &.{});
            return null;
        },
        .br => {
            _ = llvm.LLVMBuildBr(builder, self.blocks.items[instruction.a]);
            return null;
        },
        .cond_br => {
            const targets = self.ir.list(instruction.b);
            const then_block = self.blocks.items[targets[0]];
            const else_block = self.blocks.items[targets[1]];
            _ = llvm.LLVMBuildCondBr(builder, self.operand(a), then_block, else_block);
            return null;
        },
        .@"switch" => {
            const cases = self.ir.list(instruction.b);
            const key_count: c_uint = @intCast(cases.len / 2);
            const default = self.blocks.items[cases[0]];
            const lowered = llvm.LLVMBuildSwitch(builder, self.operand(a), default, key_count);
            var i: usize = 1;
            while (i < cases.len) : (i += 2) {
                const key = self.operand(@enumFromInt(cases[i]));
                llvm.LLVMAddCase(lowered, key, self.blocks.items[cases[i + 1]]);
            }
            return null;
        },
        .ret => {
            const result = self.pool.get(self.function.ty).function_type.return_type;
            if (self.types.is_in_memory(result)) {
                if (a != .none) {
                    self.copy(llvm.LLVMGetParam(self.llvm_function, 0), self.operand(a), result);
                }
                _ = llvm.LLVMBuildRetVoid(builder);
            } else if (a == .none or !Types.has_value(result)) {
                _ = llvm.LLVMBuildRetVoid(builder);
            } else {
                _ = llvm.LLVMBuildRet(builder, self.operand(a));
            }
            return null;
        },
        // a failed `??` or a case no arm matched: with checks the program stops right there
        .@"unreachable" => {
            if (self.options.checks) {
                _ = llvm.LLVMBuildBr(builder, self.trap());
            } else {
                _ = llvm.LLVMBuildUnreachable(builder);
            }
            return null;
        },
    };
}

fn arithmetic(self: *LLVMLowerer, op: Op, result_type: Index, left: Value, right: Value) Value {
    const builder = self.builder;
    if (self.pool.properties(result_type).is_float) return switch (op) {
        .add => llvm.LLVMBuildFAdd(builder, left, right, ""),
        .sub => llvm.LLVMBuildFSub(builder, left, right, ""),
        .mul => llvm.LLVMBuildFMul(builder, left, right, ""),
        .div => llvm.LLVMBuildFDiv(builder, left, right, ""),
        .rem => llvm.LLVMBuildFRem(builder, left, right, ""),
        else => unreachable,
    };

    const signed = self.is_signed(result_type);
    const lowered_type = llvm.LLVMTypeOf(right);
    switch (op) {
        .div, .rem => if (self.options.checks) {
            const zero = llvm.LLVMConstNull(lowered_type);
            var failed = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, right, zero, "");
            // the one quotient a signed type can't hold: its minimum divided by -1
            if (signed) {
                const width = llvm.LLVMGetIntTypeWidth(lowered_type);
                const sign_bit = @as(u64, 1) << @intCast(width - 1);
                const minimum = llvm.LLVMConstInt(lowered_type, sign_bit, 0);
                const minus_one = llvm.LLVMConstAllOnes(lowered_type);
                const is_minimum = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left, minimum, "");
                const by_minus_one =
                    llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, right, minus_one, "");
                const overflows = llvm.LLVMBuildAnd(builder, is_minimum, by_minus_one, "");
                failed = llvm.LLVMBuildOr(builder, failed, overflows, "");
            }
            self.trap_if(failed);
        },
        .shl, .shr => if (self.options.checks) {
            const bit_count = llvm.LLVMGetIntTypeWidth(lowered_type);
            const width = llvm.LLVMConstInt(lowered_type, bit_count, 0);
            self.trap_if(llvm.LLVMBuildICmp(builder, llvm.LLVMIntUGE, right, width, ""));
        },
        else => {},
    }
    return switch (op) {
        .add => llvm.LLVMBuildAdd(builder, left, right, ""),
        .sub => llvm.LLVMBuildSub(builder, left, right, ""),
        .mul => llvm.LLVMBuildMul(builder, left, right, ""),
        .div => if (signed)
            llvm.LLVMBuildSDiv(builder, left, right, "")
        else
            llvm.LLVMBuildUDiv(builder, left, right, ""),
        .rem => if (signed)
            llvm.LLVMBuildSRem(builder, left, right, "")
        else
            llvm.LLVMBuildURem(builder, left, right, ""),
        .shl => llvm.LLVMBuildShl(builder, left, right, ""),
        .shr => if (signed)
            llvm.LLVMBuildAShr(builder, left, right, "")
        else
            llvm.LLVMBuildLShr(builder, left, right, ""),
        .bit_and => llvm.LLVMBuildAnd(builder, left, right, ""),
        .bit_or => llvm.LLVMBuildOr(builder, left, right, ""),
        .bit_xor => llvm.LLVMBuildXor(builder, left, right, ""),
        else => unreachable,
    };
}

// a constant function is called directly, any other function value through its pointer
fn call(self: *LLVMLowerer, result_type: Index, callee: Ref, arguments: []const u32) Value {
    const in_memory = self.types.is_in_memory(result_type);
    const result_slot = if (in_memory) self.entry_alloca(self.types.of(result_type)) else null;
    const is_direct = callee.is_const() and self.pool.tag(callee.value()) == .function_value;
    const direct_function = if (is_direct)
        self.function_of_declaration[@intFromEnum(self.pool.get(callee.value()).function_value)]
    else
        no_function;
    const callee_type = if (is_direct)
        self.ir.functions.column(.ty)[direct_function]
    else
        self.type_of_ref(callee);

    // a direct call takes the captures first, a function value its result slot and environment
    const mark = self.value_stack.items.len;
    defer self.value_stack.shrinkRetainingCapacity(mark);
    const closure_value = if (is_direct) null else self.operand(callee);
    if (!is_direct) {
        if (in_memory) self.value_stack.append(self.allocator, result_slot) catch @panic("OOM");
        const environment = llvm.LLVMBuildExtractValue(self.builder, closure_value, 1, "");
        self.value_stack.append(self.allocator, environment) catch @panic("OOM");
    }
    for (arguments) |argument| {
        const argument_ref: Ref = @enumFromInt(argument);
        // a capture by reference of a variable that never lived in memory is passed as nothing
        const lowered = if (argument_ref == .none)
            llvm.LLVMConstNull(self.types.pointer)
        else
            self.operand(argument_ref);
        self.value_stack.append(self.allocator, lowered) catch @panic("OOM");
    }

    const result = if (is_direct)
        self.call_function(direct_function, mark, result_slot)
    else blk: {
        const target = llvm.LLVMBuildExtractValue(self.builder, closure_value, 0, "");
        const function_type = self.closure_function_type(callee_type);
        const called = self.build_call(function_type, target, self.value_stack.items[mark..]);
        break :blk if (in_memory) result_slot else called;
    };
    if (!Types.has_value(result_type)) return llvm.LLVMConstNull(self.types.unit);
    return result;
}

// calls an ir function with the arguments on `value_stack` from `mark` on: its captures, then its
// parameters. a result in memory goes to `result_slot`. a c function gets its arguments as
// c_abi.zig says, those of a variadic one past the fixed ones promoted as c promotes them
fn call_function(self: *LLVMLowerer, function_index: u32, mark: usize, result_slot: Value) Value {
    const function_type = self.function_types[function_index];
    const target = self.functions[function_index];
    if (self.externals.isSet(function_index)) {
        const pool_type = self.ir.functions.column(.ty)[function_index];
        const fixed = self.fixed_parameters[function_index];
        const context = self.context;
        // records go to c through a scratch slot of the registers' size, 16 bytes fit them all
        const scratch_type = llvm.LLVMArrayType2(llvm.LLVMInt8TypeInContext(context), 16);
        for (self.value_stack.items[mark..], 0..) |*argument, i| {
            const parameter = self.pool.get(pool_type).function_type.parameters[i];
            const passing = c_abi.classify(self, parameter);
            argument.* = switch (passing.how) {
                .direct, .sign_extended, .zero_extended => argument.*,
                .coerced => blk: {
                    const scratch = self.entry_alloca(scratch_type);
                    llvm.LLVMSetAlignment(scratch, 16);
                    self.copy(scratch, argument.*, parameter);
                    break :blk llvm.LLVMBuildLoad2(self.builder, passing.lowered, scratch, "");
                },
                // aarch64 lets the callee change the copy, x86-64 copies itself (`byval`)
                .indirect => if (builtin.cpu.arch == .aarch64) blk: {
                    const copied = self.entry_alloca(self.types.of(parameter));
                    self.copy(copied, argument.*, parameter);
                    break :blk copied;
                } else argument.*,
                .function => self.c_function_pointer(argument.*),
            };
            if (i < fixed) continue;
            // c's default promotions for variadic arguments
            const lowered_type = llvm.LLVMTypeOf(argument.*);
            const int = llvm.LLVMInt32TypeInContext(context);
            if (passing.how == .sign_extended or passing.how == .zero_extended) {
                const signed: c_int = @intFromBool(passing.how == .sign_extended);
                argument.* = llvm.LLVMBuildIntCast2(self.builder, argument.*, int, signed, "");
            } else if (lowered_type == llvm.LLVMFloatTypeInContext(context) or
                lowered_type == llvm.LLVMHalfTypeInContext(context))
            {
                const double = llvm.LLVMDoubleTypeInContext(context);
                argument.* = llvm.LLVMBuildFPExt(self.builder, argument.*, double, "");
            }
        }
        if (self.results_in_memory.isSet(function_index)) {
            self.value_stack.insert(self.allocator, mark, result_slot) catch @panic("OOM");
        }
        const result = self.build_call(function_type, target, self.value_stack.items[mark..]);
        if (result_slot == null or self.results_in_memory.isSet(function_index)) {
            return result_slot orelse result;
        }
        // a record c gives back in registers
        const result_type = self.pool.get(pool_type).function_type.return_type;
        const scratch = self.entry_alloca(scratch_type);
        llvm.LLVMSetAlignment(scratch, 16);
        _ = llvm.LLVMBuildStore(self.builder, result, scratch);
        self.copy(result_slot, scratch, result_type);
        return result_slot;
    }
    if (!self.results_in_memory.isSet(function_index)) {
        return self.build_call(function_type, target, self.value_stack.items[mark..]);
    }
    self.value_stack.insert(self.allocator, mark, result_slot) catch @panic("OOM");
    _ = self.build_call(function_type, target, self.value_stack.items[mark..]);
    return result_slot;
}

// a function value c can call: a function without captures, taken itself rather than its
// thunk, which expects an environment first
fn c_function_pointer(self: *LLVMLowerer, closure_value: Value) Value {
    if (llvm.LLVMIsConstant(closure_value) != 0) {
        const thunk_of_value = llvm.LLVMGetOperand(closure_value, 0);
        for (self.thunks, 0..) |known, i| {
            if (known == thunk_of_value) return self.functions[i];
        }
    }
    std.debug.panic("c takes only functions without captures, named directly", .{});
}

pub fn build_call(
    self: *LLVMLowerer,
    function_type: Type,
    target: Value,
    arguments: []const Value,
) Value {
    const count: c_uint = @intCast(arguments.len);
    const pointer = @constCast(arguments.ptr);
    return llvm.LLVMBuildCall2(self.builder, function_type, target, pointer, count, "");
}

// the environment of a closure is a slot of the frame making it: a closure never outlives that
// frame (`escaping_closure`), and one made in a loop fills the slot anew on each pass
fn closure(self: *LLVMLowerer, function_index: u32, captured: []const u32) Value {
    const function = self.thunk(function_index);
    const mark = self.value_stack.items.len;
    defer self.value_stack.shrinkRetainingCapacity(mark);
    const type_mark = self.type_stack.items.len;
    defer self.type_stack.shrinkRetainingCapacity(type_mark);
    for (captured) |capture| {
        const capture_ref: Ref = @enumFromInt(capture);
        const capture_value = if (capture_ref == .none)
            llvm.LLVMConstNull(self.types.pointer)
        else
            self.operand(capture_ref);
        self.value_stack.append(self.allocator, capture_value) catch @panic("OOM");
        self.type_stack.append(self.allocator, llvm.LLVMTypeOf(capture_value)) catch @panic("OOM");
    }
    const field_types = self.type_stack.items[type_mark..];
    const environment_type = llvm.LLVMStructTypeInContext(
        self.context,
        field_types.ptr,
        @intCast(field_types.len),
        0,
    );
    const environment = self.entry_alloca(environment_type);
    for (self.value_stack.items[mark..], 0..) |capture_value, i| {
        const position: c_uint = @intCast(i);
        const field =
            llvm.LLVMBuildStructGEP2(self.builder, environment_type, environment, position, "");
        _ = llvm.LLVMBuildStore(self.builder, capture_value, field);
    }
    return self.pair(self.types.closure, function, environment);
}

// operands and helpers shared with values.zig and constants.zig

pub fn operand(self: *LLVMLowerer, ref: Ref) Value {
    if (ref.is_global()) return self.globals[ref.index()];
    if (ref.is_const()) return constants.operand(self, ref.value());
    return self.instruction_values.items[@intFromEnum(ref)] orelse
        std.debug.panic("%{d} is used before it is lowered", .{@intFromEnum(ref)});
}

// the pool type of an operand, a global's is the type of what it holds
pub fn type_of_ref(self: *LLVMLowerer, ref: Ref) Index {
    if (ref.is_global()) return self.ir.globals.column(.ty)[ref.index()];
    if (ref.is_const()) return self.pool.type_of(ref.value());
    return self.ir.insts.column(.ty)[self.function.first_inst + @intFromEnum(ref)];
}

// what an operand points to, also for a global
pub fn pointee_of_ref(self: *LLVMLowerer, ref: Ref) Index {
    if (ref.is_global()) return self.type_of_ref(ref);
    return self.pool.pointee(self.type_of_ref(ref));
}

pub fn instruction_of(self: *LLVMLowerer, ref: Ref) ?HighIr.Inst {
    if (ref == .none or ref.is_const() or ref.is_global()) return null;
    return self.ir.insts.get(self.function.first_inst + @intFromEnum(ref)).?;
}

fn is_zeroed(self: *LLVMLowerer, ref: Ref) bool {
    const instruction = self.instruction_of(ref) orelse return false;
    return instruction.op == .zeroed;
}

// a field of a packed record may sit at any address
fn is_packed_field(self: *LLVMLowerer, pointer: Ref) bool {
    const instruction = self.instruction_of(pointer) orelse return false;
    if (instruction.op != .field_ptr) return false;
    const record = self.pointee_of_ref(@enumFromInt(instruction.a));
    return self.pool.tag(record) == .record_type and self.pool.get(record).record_type.is_packed;
}

pub fn is_signed(self: *LLVMLowerer, type_index: Index) bool {
    return switch (self.pool.get(type_index)) {
        .int_type => |int| int.signedness == .signed,
        else => false,
    };
}

pub fn alignment_of(self: *LLVMLowerer, type_index: Index) c_uint {
    return @as(c_uint, 1) << @intCast(self.pool.layout(type_index).align_log2);
}

// an index widened to 64 bits by its signedness, as getelementptr and lengths take it
pub fn index_value(self: *LLVMLowerer, index: Ref) Value {
    const signed: c_int = @intFromBool(self.is_signed(self.type_of_ref(index)));
    return llvm.LLVMBuildIntCast2(self.builder, self.operand(index), self.types.length, signed, "");
}

pub fn pair(self: *LLVMLowerer, pair_type: Type, first: Value, second: Value) Value {
    const empty = llvm.LLVMGetUndef(pair_type);
    const with_first = llvm.LLVMBuildInsertValue(self.builder, empty, first, 0, "");
    return llvm.LLVMBuildInsertValue(self.builder, with_first, second, 1, "");
}

// allocas in the entry block are allocated once per call, and promoted to registers by llvm
pub fn entry_alloca(self: *LLVMLowerer, allocated: Type) Value {
    return llvm.LLVMBuildAlloca(self.alloca_builder, allocated, "");
}

// copies a value in memory of `copied_type` from `source` to `destination`
pub fn copy(self: *LLVMLowerer, destination: Value, source: Value, copied_type: Index) void {
    const size = llvm.LLVMConstInt(self.types.length, self.pool.layout(copied_type).size, 0);
    const alignment = self.alignment_of(copied_type);
    _ = llvm.LLVMBuildMemCpy(self.builder, destination, alignment, source, alignment, size);
}

// with checks on, continues only when `failed` is false
pub fn trap_if(self: *LLVMLowerer, failed: Value) void {
    if (!self.options.checks) return;
    const passed = llvm.LLVMAppendBasicBlockInContext(self.context, self.llvm_function, "");
    _ = llvm.LLVMBuildCondBr(self.builder, failed, self.trap(), passed);
    llvm.LLVMPositionBuilderAtEnd(self.builder, passed);
}

// the block of the current function stopping the program
fn trap(self: *LLVMLowerer) Block {
    if (self.trap_block) |known| return known;
    const block = llvm.LLVMAppendBasicBlockInContext(self.context, self.llvm_function, "trap");
    const builder = llvm.LLVMCreateBuilderInContext(self.context);
    defer llvm.LLVMDisposeBuilder(builder);
    llvm.LLVMPositionBuilderAtEnd(builder, block);
    const name = "llvm.trap";
    const id = llvm.LLVMLookupIntrinsicID(name, name.len);
    const declaration = llvm.LLVMGetIntrinsicDeclaration(self.module, id, null, 0);
    const trap_type = llvm.LLVMIntrinsicGetType(self.context, id, null, 0);
    _ = llvm.LLVMBuildCall2(builder, trap_type, declaration, null, 0, "");
    _ = llvm.LLVMBuildUnreachable(builder);
    self.trap_block = block;
    return block;
}

// a function of the c library, declared on first use
pub fn runtime_function(self: *LLVMLowerer, name: [:0]const u8, function_type: Type) Value {
    return llvm.LLVMGetNamedFunction(self.module, name) orelse
        llvm.LLVMAddFunction(self.module, name, function_type);
}
