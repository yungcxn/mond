const std = @import("std");
const llvm = @import("llvm_c");
const mond = @import("mond");
const Types = @import("llvm_lowerer/Types.zig");
const constants = @import("llvm_lowerer/constants.zig");
const values = @import("llvm_lowerer/values.zig");
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
// constants.zig
const LLVMLowerer = @This();

pub const Options = struct {
    // traps on division by zero, oversized shifts and indices past an array's end
    checks: bool,
};

// a phi waits for its operands until all blocks of its function are lowered
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
// per ir function: its llvm function and that function's type
functions: []Value,
function_types: []Type,
// per ir function: the function as a function value, taking the environment first
thunks: []Value,
// per ir function: declared without a body, called with the c library's conventions
externals: std.DynamicBitSetUnmanaged,
// per ir function: returns through the pointer in its first parameter
results_in_memory: std.DynamicBitSetUnmanaged,
globals: []Value,
function_of_declaration: std.AutoHashMapUnmanaged(DeclPool.Index, u32) = .empty,
// string constants as zero-terminated bytes, so c functions can read them
strings: std.AutoHashMapUnmanaged(Index, Value) = .empty,
// constants in memory, as constant globals
constant_globals: std.AutoHashMapUnmanaged(Index, Value) = .empty,
// a constant global of zero bytes per type, the value of `zeroed` in memory
zeros: std.AutoHashMapUnmanaged(Index, Value) = .empty,
runtime_functions: std.StringHashMapUnmanaged(Value) = .empty,
name_buffer: [256:0]u8 = undefined,

// the function being lowered
function: HighIr.Function = undefined,
function_index: u32 = 0,
llvm_function: Value = null,
instruction_values: std.ArrayList(Value) = .empty,
// per ir block: where it starts, and where it ends once checks split it
blocks: std.ArrayList(Block) = .empty,
block_exits: std.ArrayList(Block) = .empty,
reachable: std.DynamicBitSetUnmanaged = .{},
pending_phis: std.ArrayList(PendingPhi) = .empty,
// the entry block holding the function's allocas, in front of the ir's first block
alloca_builder: llvm.LLVMBuilderRef,
trap_block: Block = null,
scratch: std.ArrayList(Value) = .empty,

pub fn init(
    allocator: std.mem.Allocator,
    high: *HighLowerer,
    name: [:0]const u8,
    options: Options,
) LLVMLowerer {
    const context = llvm.LLVMContextCreate();
    const ir = &high.ir;
    const function_count = ir.functions.len();
    return .{
        .allocator = allocator,
        .options = options,
        .high = high,
        .ir = ir,
        .pool = high.static_pool,
        .context = context,
        .module = llvm.LLVMModuleCreateWithNameInContext(name, context),
        .builder = llvm.LLVMCreateBuilderInContext(context),
        .alloca_builder = llvm.LLVMCreateBuilderInContext(context),
        .types = .init(allocator, context, high.static_pool, &high.resolver.name_pool),
        .functions = allocator.alloc(Value, function_count) catch @panic("OOM"),
        .function_types = allocator.alloc(Type, function_count) catch @panic("OOM"),
        .thunks = allocator.alloc(Value, function_count) catch @panic("OOM"),
        .externals = std.DynamicBitSetUnmanaged.initEmpty(allocator, function_count) catch {
            @panic("OOM");
        },
        .results_in_memory = std.DynamicBitSetUnmanaged.initEmpty(allocator, function_count) catch {
            @panic("OOM");
        },
        .globals = allocator.alloc(Value, ir.globals.len()) catch @panic("OOM"),
    };
}

pub fn deinit(self: *LLVMLowerer) void {
    const allocator = self.allocator;
    self.types.deinit();
    allocator.free(self.functions);
    allocator.free(self.function_types);
    allocator.free(self.thunks);
    self.externals.deinit(allocator);
    self.results_in_memory.deinit(allocator);
    self.zeros.deinit(allocator);
    allocator.free(self.globals);
    self.function_of_declaration.deinit(allocator);
    self.strings.deinit(allocator);
    self.constant_globals.deinit(allocator);
    self.runtime_functions.deinit(allocator);
    self.instruction_values.deinit(allocator);
    self.blocks.deinit(allocator);
    self.block_exits.deinit(allocator);
    self.reachable.deinit(allocator);
    self.pending_phis.deinit(allocator);
    self.scratch.deinit(allocator);
    llvm.LLVMDisposeBuilder(self.builder);
    llvm.LLVMDisposeBuilder(self.alloca_builder);
    llvm.LLVMDisposeModule(self.module);
    llvm.LLVMContextDispose(self.context);
}

pub fn lower(self: *LLVMLowerer) void {
    const function_count = self.ir.functions.len();
    @memset(self.thunks, null);
    for (0..function_count) |i| self.declare_function(@intCast(i));
    for (self.ir.globals.column(.decl), 0..) |declaration, i| self.declare_global(declaration, i);
    for (0..function_count) |i| self.lower_function(@intCast(i));
    self.define_main();

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
        self.function_of_declaration.put(self.allocator, function.decl, function_index) catch {
            @panic("OOM");
        };
    }
    const is_external = function.blocks == 0 and function.decl != .none;
    const function_type = self.pool.get(function.ty).function_type;
    const in_memory = !is_external and self.types.is_in_memory(function_type.return_type);
    self.externals.setValue(function_index, is_external);
    self.results_in_memory.setValue(function_index, in_memory);

    const first: usize = @intFromBool(in_memory);
    const parameter_count = first + function.captures + function_type.parameters.len;
    const parameters = self.allocator.alloc(Type, parameter_count) catch @panic("OOM");
    defer self.allocator.free(parameters);
    if (in_memory) parameters[0] = self.types.pointer;
    for (function_type.parameters, parameters[first + function.captures ..]) |parameter, *lowered| {
        lowered.* = if (is_external) self.types.of(parameter) else self.types.value_of(parameter);
    }
    // the captures come first, their types only the params of the body know
    const instructions = self.ir.insts.columns();
    for (function.first_inst..function.first_inst + function.insts) |i| {
        if (instructions.op[i] != .param or instructions.a[i] >= function.captures) continue;
        parameters[first + instructions.a[i]] = self.types.value_of(instructions.ty[i]);
    }
    const result = if (in_memory)
        llvm.LLVMVoidTypeInContext(self.context)
    else if (is_external)
        self.c_return_type(function_type.return_type)
    else
        self.lowered_return_type(function_type.return_type);
    const lowered_type = llvm.LLVMFunctionType(
        result,
        parameters.ptr,
        @intCast(parameter_count),
        0,
    );
    self.function_types[function_index] = lowered_type;

    const name = self.name_of(function.decl, "$init");
    // overloads of an external function are one symbol, called with each overload's type
    if (is_external) if (llvm.LLVMGetNamedFunction(self.module, name)) |existing| {
        self.functions[function_index] = existing;
        return;
    };
    const lowered = llvm.LLVMAddFunction(self.module, name, lowered_type);
    if (!is_external) {
        llvm.LLVMSetLinkage(lowered, llvm.LLVMInternalLinkage);
        self.add_attribute(lowered, "nounwind");
    }
    self.functions[function_index] = lowered;
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

// `main` of c: the global initializers, then `$main` with the arguments it asks for
fn define_main(self: *LLVMLowerer) void {
    const main_function = for (self.ir.functions.column(.decl), 0..) |declaration, i| {
        if (declaration == .none) continue;
        if (self.high.resolver.decl_pool.get(declaration, .name) == .main) break i;
    } else return;

    const int = llvm.LLVMInt32TypeInContext(self.context);
    var parameters = [_]Type{ int, self.types.pointer };
    const main_type = llvm.LLVMFunctionType(int, &parameters, parameters.len, 0);
    const entry = llvm.LLVMAddFunction(self.module, "main", main_type);
    const argument_count = llvm.LLVMGetParam(entry, 0);
    const argument_vector = llvm.LLVMGetParam(entry, 1);
    llvm.LLVMPositionBuilderAtEnd(
        self.builder,
        llvm.LLVMAppendBasicBlockInContext(self.context, entry, "entry"),
    );
    const init_function = self.ir.init_fn;
    _ = self.build_call(self.function_types[init_function], self.functions[init_function], &.{});

    // `(argc, argv)` in the shapes `$main` takes them: ints, a pointer, or `[]&u8` with its length
    const main_type_index = self.ir.functions.column(.ty)[main_function];
    const main_parameters = self.pool.get(main_type_index).function_type.parameters;
    self.scratch.clearRetainingCapacity();
    for (main_parameters, 0..) |parameter, i| {
        const lowered = self.types.of(parameter);
        const given = if (i == 0) argument_count else argument_vector;
        const argument = if (i > 1)
            llvm.LLVMConstNull(lowered)
        else if (lowered == self.types.slice) blk: {
            const count = llvm.LLVMBuildZExt(self.builder, argument_count, self.types.length, "");
            break :blk self.pair(self.types.slice, argument_vector, count);
        } else if (lowered == self.types.pointer)
            given
        else if (i == 0)
            llvm.LLVMBuildIntCast2(self.builder, given, lowered, 1, "")
        else
            llvm.LLVMBuildPtrToInt(self.builder, given, lowered, "");
        self.scratch.append(self.allocator, argument) catch @panic("OOM");
    }
    const result = self.build_call(
        self.function_types[main_function],
        self.functions[main_function],
        self.scratch.items,
    );

    const return_type = self.pool.get(main_type_index).function_type.return_type;
    const exit_code = if (!Types.has_value(return_type))
        llvm.LLVMConstInt(int, 0, 0)
    else
        llvm.LLVMBuildIntCast2(
            self.builder,
            result,
            int,
            @intFromBool(self.is_signed(return_type)),
            "",
        );
    _ = llvm.LLVMBuildRet(self.builder, exit_code);
}

// a function value of a function: called with the environment first, which holds its captures
pub fn thunk(self: *LLVMLowerer, function_index: u32) Value {
    if (self.thunks[function_index]) |known| return known;
    const function = self.ir.functions.get(function_index).?;
    const thunk_type = self.closure_function_type(function.ty);
    const lowered = llvm.LLVMAddFunction(
        self.module,
        self.name_of(function.decl, "$init"),
        thunk_type,
    );
    llvm.LLVMSetLinkage(lowered, llvm.LLVMInternalLinkage);
    self.add_attribute(lowered, "nounwind");
    self.thunks[function_index] = lowered;

    const saved_block = llvm.LLVMGetInsertBlock(self.builder);
    defer if (saved_block != null) llvm.LLVMPositionBuilderAtEnd(self.builder, saved_block);
    const entry = llvm.LLVMAppendBasicBlockInContext(self.context, lowered, "entry");
    llvm.LLVMPositionBuilderAtEnd(self.builder, entry);

    // (result slot, environment, parameters) to (result slot, captures, parameters)
    const pool_type = self.pool.get(function.ty).function_type;
    const in_memory = self.types.is_in_memory(pool_type.return_type);
    const first: c_uint = @intFromBool(in_memory);
    const target_type = self.function_types[function_index];
    const target_parameters = self.allocator.alloc(
        Type,
        llvm.LLVMCountParamTypes(target_type),
    ) catch {
        @panic("OOM");
    };
    defer self.allocator.free(target_parameters);
    llvm.LLVMGetParamTypes(target_type, target_parameters.ptr);
    const captures_at: usize = @intFromBool(self.results_in_memory.isSet(function_index));
    const environment_type = llvm.LLVMStructTypeInContext(
        self.context,
        target_parameters[captures_at..].ptr,
        function.captures,
        0,
    );
    self.scratch.clearRetainingCapacity();
    const environment = llvm.LLVMGetParam(lowered, first);
    for (0..function.captures) |i| {
        const field = llvm.LLVMBuildStructGEP2(
            self.builder,
            environment_type,
            environment,
            @intCast(i),
            "",
        );
        const field_type = llvm.LLVMStructGetTypeAtIndex(environment_type, @intCast(i));
        const capture = llvm.LLVMBuildLoad2(self.builder, field_type, field, "");
        self.scratch.append(self.allocator, capture) catch @panic("OOM");
    }
    for (0..pool_type.parameters.len) |i| {
        const parameter = llvm.LLVMGetParam(lowered, first + 1 + @as(c_uint, @intCast(i)));
        self.scratch.append(self.allocator, parameter) catch @panic("OOM");
    }
    const result_slot = if (in_memory) llvm.LLVMGetParam(lowered, 0) else null;
    const result = self.call_function(function_index, self.scratch.items, result_slot);
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
    const first: usize = @intFromBool(in_memory);
    const parameters = self.allocator.alloc(Type, first + 1 + function_type.parameters.len) catch {
        @panic("OOM");
    };
    defer self.allocator.free(parameters);
    @memset(parameters[0 .. first + 1], self.types.pointer);
    for (function_type.parameters, parameters[first + 1 ..]) |parameter, *lowered| {
        lowered.* = self.types.value_of(parameter);
    }
    const result = if (in_memory)
        llvm.LLVMVoidTypeInContext(self.context)
    else
        self.lowered_return_type(function_type.return_type);
    return llvm.LLVMFunctionType(result, parameters.ptr, @intCast(parameters.len), 0);
}

fn lowered_return_type(self: *LLVMLowerer, result_type: Index) Type {
    if (!Types.has_value(result_type)) return llvm.LLVMVoidTypeInContext(self.context);
    return self.types.value_of(result_type);
}

// a c function returns a struct by value
fn c_return_type(self: *LLVMLowerer, result_type: Index) Type {
    if (!Types.has_value(result_type)) return llvm.LLVMVoidTypeInContext(self.context);
    return self.types.of(result_type);
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

fn add_attribute(self: *LLVMLowerer, function: Value, name: []const u8) void {
    const kind = llvm.LLVMGetEnumAttributeKindForName(name.ptr, name.len);
    const attribute = llvm.LLVMCreateEnumAttribute(self.context, kind, 0);
    const function_index: c_uint = @bitCast(@as(c_int, llvm.LLVMAttributeFunctionIndex));
    llvm.LLVMAddAttributeAtIndex(function, function_index, attribute);
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
    const order = self.reverse_postorder();
    defer self.allocator.free(order);
    for (order) |block| self.lower_block(block);
    for (self.blocks.items, 0..) |block, i| {
        if (self.reachable.isSet(i)) continue;
        llvm.LLVMPositionBuilderAtEnd(self.builder, block);
        _ = llvm.LLVMBuildUnreachable(self.builder);
    }

    // an operand pairs with the predecessor at its position, unreachable ones branch nowhere
    for (self.pending_phis.items) |pending| {
        const block = self.ir.blocks.get(self.function.first_block + pending.block).?;
        const predecessors = self.ir.list(block.preds);
        for (predecessors, self.ir.list(pending.instruction.b)) |predecessor, operand_ref| {
            if (!self.reachable.isSet(predecessor)) continue;
            const phi_type = llvm.LLVMTypeOf(pending.phi);
            var incoming_value = [_]Value{self.operand_as(@enumFromInt(operand_ref), phi_type)};
            var incoming_block = [_]Block{self.block_exits.items[predecessor]};
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
        const local: u32 = @intCast(i - self.function.first_inst);
        self.instruction_values.items[local] = self.lower_instruction(instruction, block_index);
    }
    self.block_exits.items[block_index] = llvm.LLVMGetInsertBlock(self.builder);
}

fn reverse_postorder(self: *LLVMLowerer) []u32 {
    const block_count = self.function.blocks;
    self.reachable.resize(self.allocator, block_count, false) catch @panic("OOM");
    self.reachable.unsetAll();
    var order: std.ArrayList(u32) = .empty;
    // a block, and how many of its successors are walked already
    var stack: std.ArrayList(struct { u32, u32 }) = .empty;
    defer stack.deinit(self.allocator);
    stack.append(self.allocator, .{ 0, 0 }) catch @panic("OOM");
    self.reachable.set(0);
    while (stack.items.len > 0) {
        const top = &stack.items[stack.items.len - 1];
        const following = self.successors(top[0]);
        if (top[1] == following.count) {
            order.append(self.allocator, top[0]) catch @panic("OOM");
            _ = stack.pop();
            continue;
        }
        const successor = following.at(self, top[1]);
        top[1] += 1;
        if (self.reachable.isSet(successor)) continue;
        self.reachable.set(successor);
        stack.append(self.allocator, .{ successor, 0 }) catch @panic("OOM");
    }
    std.mem.reverse(u32, order.items);
    return order.toOwnedSlice(self.allocator) catch @panic("OOM");
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
            const phi = llvm.LLVMBuildPhi(builder, self.types.value_of(result_type), "");
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
            const right = self.operand_as(b, llvm.LLVMTypeOf(left));
            return values.compare(self, instruction.op, self.type_of_ref(a), left, right);
        },
        .bytes_eq => {
            const left = self.operand(a);
            const right = self.operand_as(b, llvm.LLVMTypeOf(left));
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
            const pointee = self.pool.pointee(result_type);
            // with a length: the elements of a runtime-length array, allocated where it is made
            if (a == .none) return self.entry_alloca(self.types.of(pointee));
            return llvm.LLVMBuildArrayAlloca(builder, self.types.of(pointee), self.operand(a), "");
        },
        .load => {
            const pointer = self.operand(a);
            // a pointer to a runtime-length array is the same pair as the array it points to
            if (llvm.LLVMTypeOf(pointer) == self.types.slice) return pointer;
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
            if (self.types.is_in_memory(stored_type)) {
                // a zeroed value is cleared in place rather than copied from zeros
                if (self.is_zeroed(b)) {
                    const zero = llvm.LLVMConstInt(llvm.LLVMInt8TypeInContext(self.context), 0, 0);
                    const length = llvm.LLVMConstInt(
                        self.types.length,
                        self.pool.layout(stored_type).size,
                        0,
                    );
                    _ = llvm.LLVMBuildMemSet(
                        builder,
                        self.operand(a),
                        zero,
                        length,
                        self.alignment_of(stored_type),
                    );
                } else {
                    self.copy(self.operand(a), self.operand(b), stored_type);
                }
                return null;
            }
            const stored = self.operand_as(b, self.types.of(self.pointee_of_ref(a)));
            const store = llvm.LLVMBuildStore(builder, stored, self.operand(a));
            if (self.is_packed_field(a)) llvm.LLVMSetAlignment(store, 1);
            return null;
        },
        .field_ptr => values.field_pointer(self, a, instruction.b),
        .index_ptr => values.index_pointer(self, result_type, a, b),
        .dyn => {
            const bounds = self.ir.list(instruction.b);
            const element = self.pool.get(result_type).array_type.element;
            const start = self.index_value(@enumFromInt(bounds[0]));
            const end = self.index_value(@enumFromInt(bounds[1]));
            var offset = [_]Value{start};
            const first = llvm.LLVMBuildInBoundsGEP2(
                builder,
                self.types.of(element),
                self.operand(a),
                &offset,
                1,
                "",
            );
            return self.pair(self.types.slice, first, llvm.LLVMBuildSub(builder, end, start, ""));
        },
        .len => llvm.LLVMBuildExtractValue(builder, self.operand(a), 1, ""),
        .aggregate => values.aggregate(self, result_type, self.ir.list(instruction.b)),
        .select => {
            const choices = self.ir.list(instruction.b);
            const choice_type = self.types.value_of(result_type);
            const then_value = self.operand_as(@enumFromInt(choices[0]), choice_type);
            const else_value = self.operand_as(@enumFromInt(choices[1]), choice_type);
            return llvm.LLVMBuildSelect(builder, self.operand(a), then_value, else_value, "");
        },
        .extract => values.extract(self, result_type, a, instruction.b),
        .variant_make => values.variant_make(self, result_type, instruction.a, b),
        .variant_tag => values.variant_tag(self, self.type_of_ref(a), self.operand(a)),
        .variant_payload => values.variant_payload(
            self,
            result_type,
            self.type_of_ref(a),
            self.operand(a),
        ),
        .call => self.call(result_type, a, self.ir.list(instruction.b)),
        .closure => self.closure(instruction.a, self.ir.list(instruction.b), block),
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
            const lowered = llvm.LLVMBuildSwitch(
                builder,
                self.operand(a),
                self.blocks.items[cases[0]],
                key_count,
            );
            var i: usize = 1;
            while (i < cases.len) : (i += 2) {
                const key = self.operand(@enumFromInt(cases[i]));
                llvm.LLVMAddCase(lowered, key, self.blocks.items[cases[i + 1]]);
            }
            return null;
        },
        .ret => {
            const function_type = self.pool.get(self.function.ty).function_type;
            if (self.types.is_in_memory(function_type.return_type)) {
                if (a != .none) {
                    const result_slot = llvm.LLVMGetParam(self.llvm_function, 0);
                    self.copy(result_slot, self.operand(a), function_type.return_type);
                }
                _ = llvm.LLVMBuildRetVoid(builder);
            } else if (a == .none or !Types.has_value(function_type.return_type)) {
                _ = llvm.LLVMBuildRetVoid(builder);
            } else {
                const returned_type = self.types.value_of(function_type.return_type);
                _ = llvm.LLVMBuildRet(builder, self.operand_as(a, returned_type));
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
    switch (op) {
        .div, .rem => if (self.options.checks) {
            const lowered_type = llvm.LLVMTypeOf(right);
            const zero = llvm.LLVMConstNull(lowered_type);
            var failed = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, right, zero, "");
            // the one quotient a signed type can't hold: its minimum divided by -1
            if (signed) {
                const bits: u6 = @intCast(llvm.LLVMGetIntTypeWidth(lowered_type) - 1);
                const minimum = llvm.LLVMConstInt(lowered_type, @as(u64, 1) << bits, 0);
                const minus_one = llvm.LLVMConstAllOnes(lowered_type);
                const is_minimum = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left, minimum, "");
                const by_minus_one = llvm.LLVMBuildICmp(
                    builder,
                    llvm.LLVMIntEQ,
                    right,
                    minus_one,
                    "",
                );
                const overflows = llvm.LLVMBuildAnd(builder, is_minimum, by_minus_one, "");
                failed = llvm.LLVMBuildOr(builder, failed, overflows, "");
            }
            self.trap_if(failed);
        },
        .shl, .shr => if (self.options.checks) {
            const lowered_type = llvm.LLVMTypeOf(right);
            const width = llvm.LLVMConstInt(
                lowered_type,
                llvm.LLVMGetIntTypeWidth(lowered_type),
                0,
            );
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
    const callee_type = if (is_direct) blk: {
        const declaration = self.pool.get(callee.value()).function_value;
        const function_index = self.function_of_declaration.get(declaration).?;
        break :blk self.ir.functions.column(.ty)[function_index];
    } else self.type_of_ref(callee);
    const parameter_count = self.pool.get(callee_type).function_type.parameters.len;

    // a direct call passes the captures first, a function value its environment
    const lowered = self.allocator.alloc(Value, arguments.len + 2) catch @panic("OOM");
    defer self.allocator.free(lowered);
    const first: usize = if (is_direct) 0 else 1 + @as(usize, @intFromBool(in_memory));
    const capture_count = arguments.len - parameter_count;
    for (arguments, lowered[first..][0..arguments.len], 0..) |argument, *value, i| {
        const argument_ref: Ref = @enumFromInt(argument);
        const parameters = self.pool.get(callee_type).function_type.parameters;
        const expected = if (i < capture_count)
            llvm.LLVMTypeOf(self.operand(argument_ref))
        else
            self.types.value_of(parameters[i - capture_count]);
        // a capture by reference of a variable that never lived in memory is passed as nothing
        value.* = if (argument_ref == .none)
            llvm.LLVMGetUndef(expected)
        else
            self.operand_as(argument_ref, expected);
    }

    const result = if (is_direct) blk: {
        const declaration = self.pool.get(callee.value()).function_value;
        const function_index = self.function_of_declaration.get(declaration).?;
        break :blk self.call_function(function_index, lowered[0..arguments.len], result_slot);
    } else blk: {
        const closure_value = self.operand(callee);
        if (in_memory) lowered[0] = result_slot;
        lowered[first - 1] = llvm.LLVMBuildExtractValue(self.builder, closure_value, 1, "");
        const target = llvm.LLVMBuildExtractValue(self.builder, closure_value, 0, "");
        const called = self.build_call(
            self.closure_function_type(callee_type),
            target,
            lowered[0 .. first + arguments.len],
        );
        break :blk if (in_memory) result_slot else called;
    };
    if (!Types.has_value(result_type)) return llvm.LLVMConstNull(self.types.unit);
    return result;
}

// calls an ir function with `arguments`, its captures then its parameters. a result in memory
// goes to `result_slot`, and a c function takes and gives structs by value
fn call_function(
    self: *LLVMLowerer,
    function_index: u32,
    arguments: []const Value,
    result_slot: Value,
) Value {
    const function_type = self.function_types[function_index];
    const target = self.functions[function_index];
    if (self.externals.isSet(function_index)) {
        const pool_type = self.ir.functions.column(.ty)[function_index];
        const by_value = self.allocator.alloc(Value, arguments.len) catch @panic("OOM");
        defer self.allocator.free(by_value);
        for (arguments, by_value, 0..) |argument, *value, i| {
            const parameter = self.pool.get(pool_type).function_type.parameters[i];
            value.* = if (self.types.is_in_memory(parameter))
                llvm.LLVMBuildLoad2(self.builder, self.types.of(parameter), argument, "")
            else
                argument;
        }
        const result = self.build_call(function_type, target, by_value);
        if (result_slot == null) return result;
        _ = llvm.LLVMBuildStore(self.builder, result, result_slot);
        return result_slot;
    }
    if (!self.results_in_memory.isSet(function_index)) {
        return self.build_call(function_type, target, arguments);
    }
    const with_slot = self.allocator.alloc(Value, arguments.len + 1) catch @panic("OOM");
    defer self.allocator.free(with_slot);
    with_slot[0] = result_slot;
    @memcpy(with_slot[1..], arguments);
    _ = self.build_call(function_type, target, with_slot);
    return result_slot;
}

pub fn build_call(
    self: *LLVMLowerer,
    function_type: Type,
    target: Value,
    arguments: []const Value,
) Value {
    return llvm.LLVMBuildCall2(
        self.builder,
        function_type,
        target,
        @constCast(arguments.ptr),
        @intCast(arguments.len),
        "",
    );
}

// the environment of a closure lives in the frame making it: once per call, or once per pass when
// that happens in a loop, so each closure made there keeps its own captures
fn closure(self: *LLVMLowerer, function_index: u32, captured: []const u32, block: u32) Value {
    self.scratch.clearRetainingCapacity();
    for (captured) |capture| {
        const capture_ref: Ref = @enumFromInt(capture);
        const capture_value = if (capture_ref == .none)
            llvm.LLVMConstNull(self.types.pointer)
        else
            self.operand(capture_ref);
        self.scratch.append(self.allocator, capture_value) catch @panic("OOM");
    }
    const field_types = self.allocator.alloc(Type, captured.len) catch @panic("OOM");
    defer self.allocator.free(field_types);
    for (self.scratch.items, field_types) |capture_value, *field_type| {
        field_type.* = llvm.LLVMTypeOf(capture_value);
    }
    const environment_type = llvm.LLVMStructTypeInContext(
        self.context,
        field_types.ptr,
        @intCast(field_types.len),
        0,
    );
    const environment = if (self.is_in_cycle(block))
        llvm.LLVMBuildAlloca(self.builder, environment_type, "")
    else
        self.entry_alloca(environment_type);
    for (self.scratch.items, 0..) |capture_value, i| {
        const field = llvm.LLVMBuildStructGEP2(
            self.builder,
            environment_type,
            environment,
            @intCast(i),
            "",
        );
        _ = llvm.LLVMBuildStore(self.builder, capture_value, field);
    }
    return self.pair(self.types.closure, self.thunk(function_index), environment);
}

fn is_in_cycle(self: *LLVMLowerer, block: u32) bool {
    var seen = std.DynamicBitSetUnmanaged.initEmpty(self.allocator, self.function.blocks) catch {
        @panic("OOM");
    };
    defer seen.deinit(self.allocator);
    var stack: std.ArrayList(u32) = .empty;
    defer stack.deinit(self.allocator);
    stack.append(self.allocator, block) catch @panic("OOM");
    while (stack.pop()) |current| {
        const following = self.successors(current);
        for (0..following.count) |i| {
            const successor = following.at(self, @intCast(i));
            if (successor == block) return true;
            if (seen.isSet(successor)) continue;
            seen.set(successor);
            stack.append(self.allocator, successor) catch @panic("OOM");
        }
    }
    return false;
}

// operands and helpers shared with values.zig and constants.zig

// a constant shaped for where it is used, see `constants.operand_as`
pub fn operand_as(self: *LLVMLowerer, ref: Ref, expected: Type) Value {
    if (!ref.is_const() or ref.is_global()) return self.operand(ref);
    return constants.operand_as(self, ref.value(), expected);
}

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
    const value = self.operand(index);
    return llvm.LLVMBuildIntCast2(
        self.builder,
        value,
        self.types.length,
        @intFromBool(self.is_signed(self.type_of_ref(index))),
        "",
    );
}

pub fn pair(self: *LLVMLowerer, pair_type: Type, first: Value, second: Value) Value {
    const with_first = llvm.LLVMBuildInsertValue(
        self.builder,
        llvm.LLVMGetUndef(pair_type),
        first,
        0,
        "",
    );
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
    return self.trap_block orelse blk: {
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
        break :blk block;
    };
}

// a function of the c library, declared on first use
pub fn runtime_function(self: *LLVMLowerer, name: [:0]const u8, function_type: Type) Value {
    if (self.runtime_functions.get(name)) |known| return known;
    const declared = llvm.LLVMGetNamedFunction(self.module, name) orelse
        llvm.LLVMAddFunction(self.module, name, function_type);
    self.runtime_functions.put(self.allocator, name, declared) catch @panic("OOM");
    return declared;
}
