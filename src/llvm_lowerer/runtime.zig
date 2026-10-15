// the c functions generated code calls, for a program linked without the c library: llvm turns
// copies and fills into `memcpy`, `memset` and `memmove`, float `%` into `fmod` and `fmodf`,
// comparisons of bytes call `memcmp` and `strcmp`. weak, so a library linked anyway takes over.
// `no-builtins` keeps llvm from turning their loops back into calls of themselves, it still
// vectorizes them
const std = @import("std");
const llvm = @import("llvm_c");
const LLVMLowerer = @import("../LLVMLowerer.zig");
const Value = LLVMLowerer.Value;
const Type = LLVMLowerer.Type;

pub fn define(lowerer: *LLVMLowerer) void {
    const pointer = lowerer.types.pointer;
    const length = lowerer.types.length;
    const int = llvm.LLVMInt32TypeInContext(lowerer.context);
    const byte = llvm.LLVMInt8TypeInContext(lowerer.context);
    const builder = llvm.LLVMCreateBuilderInContext(lowerer.context);
    defer llvm.LLVMDisposeBuilder(builder);
    var loop: Loop = .{ .lowerer = lowerer, .builder = builder };

    // memcpy(to, from, count) and memmove(to, from, count), which copies backwards when `to`
    // lies behind `from`
    for ([_][:0]const u8{ "memcpy", "memmove" }) |name| {
        const function = loop.begin(name, pointer, &.{ pointer, pointer, length });
        const to = llvm.LLVMGetParam(function, 0);
        const from = llvm.LLVMGetParam(function, 1);
        const count = llvm.LLVMGetParam(function, 2);
        const backwards = if (std.mem.eql(u8, name, "memmove")) blk: {
            const to_address = llvm.LLVMBuildPtrToInt(builder, to, length, "");
            const from_address = llvm.LLVMBuildPtrToInt(builder, from, length, "");
            break :blk llvm.LLVMBuildICmp(builder, llvm.LLVMIntUGT, to_address, from_address, "");
        } else llvm.LLVMConstInt(llvm.LLVMInt1TypeInContext(lowerer.context), 0, 0);
        const index = loop.counting(count);
        const last = llvm.LLVMBuildSub(builder, count, llvm.LLVMConstInt(length, 1, 0), "");
        const backward_index = llvm.LLVMBuildSub(builder, last, index, "");
        const at = llvm.LLVMBuildSelect(builder, backwards, backward_index, index, "");
        const loaded = llvm.LLVMBuildLoad2(builder, byte, loop.element(from, at), "");
        _ = llvm.LLVMBuildStore(builder, loaded, loop.element(to, at));
        loop.end(to);
    }

    // memset(to, value, count)
    {
        const function = loop.begin("memset", pointer, &.{ pointer, int, length });
        const to = llvm.LLVMGetParam(function, 0);
        const value = llvm.LLVMBuildTrunc(builder, llvm.LLVMGetParam(function, 1), byte, "");
        const index = loop.counting(llvm.LLVMGetParam(function, 2));
        _ = llvm.LLVMBuildStore(builder, value, loop.element(to, index));
        loop.end(to);
    }

    // memcmp(left, right, count) and strcmp(left, right): the difference of the first bytes that
    // differ, strcmp also stops after a zero byte
    for ([_][:0]const u8{ "memcmp", "strcmp" }) |name| {
        const counted = std.mem.eql(u8, name, "memcmp");
        const parameters: []const Type = if (counted)
            &.{ pointer, pointer, length }
        else
            &.{ pointer, pointer };
        const function = loop.begin(name, int, parameters);
        const left = llvm.LLVMGetParam(function, 0);
        const right = llvm.LLVMGetParam(function, 1);
        const unbounded = llvm.LLVMConstAllOnes(length);
        const index = loop.counting(if (counted) llvm.LLVMGetParam(function, 2) else unbounded);
        const left_byte = llvm.LLVMBuildLoad2(builder, byte, loop.element(left, index), "");
        const right_byte = llvm.LLVMBuildLoad2(builder, byte, loop.element(right, index), "");
        var stops = llvm.LLVMBuildICmp(builder, llvm.LLVMIntNE, left_byte, right_byte, "");
        if (!counted) {
            const zero = llvm.LLVMConstNull(byte);
            const ended = llvm.LLVMBuildICmp(builder, llvm.LLVMIntEQ, left_byte, zero, "");
            stops = llvm.LLVMBuildOr(builder, stops, ended, "");
        }
        const differs = llvm.LLVMAppendBasicBlockInContext(lowerer.context, function, "");
        const next = llvm.LLVMAppendBasicBlockInContext(lowerer.context, function, "");
        _ = llvm.LLVMBuildCondBr(builder, stops, differs, next);
        llvm.LLVMPositionBuilderAtEnd(builder, differs);
        const left_wide = llvm.LLVMBuildZExt(builder, left_byte, int, "");
        const right_wide = llvm.LLVMBuildZExt(builder, right_byte, int, "");
        _ = llvm.LLVMBuildRet(builder, llvm.LLVMBuildSub(builder, left_wide, right_wide, ""));
        llvm.LLVMPositionBuilderAtEnd(builder, next);
        loop.end(llvm.LLVMConstNull(int));
    }

    // fmod(x, y) and fmodf(x, y), exact as c's: binary long division. |y| doubled up to below |x|,
    // then halved back down to |y|, subtracted wherever it fits; each subtraction is exact, as the
    // remainder is below twice what is subtracted. the result has the sign of x
    const context = lowerer.context;
    const floats = [_]struct { [:0]const u8, Type }{
        .{ "fmod", llvm.LLVMDoubleTypeInContext(context) },
        .{ "fmodf", llvm.LLVMFloatTypeInContext(context) },
    };
    for (floats) |entry| {
        const name, const float = entry;
        const function = loop.begin(name, float, &.{ float, float });
        const x = llvm.LLVMGetParam(function, 0);
        const y = llvm.LLVMGetParam(function, 1);
        var types = [_]Type{float};
        const fabs_id = llvm.LLVMLookupIntrinsicID("llvm.fabs", "llvm.fabs".len);
        const fabs = llvm.LLVMGetIntrinsicDeclaration(lowerer.module, fabs_id, &types, 1);
        const fabs_type = llvm.LLVMIntrinsicGetType(context, fabs_id, &types, 1);
        const x_size = call(builder, fabs_type, fabs, &.{x});
        const y_size = call(builder, fabs_type, fabs, &.{y});
        const infinity = llvm.LLVMConstReal(float, std.math.inf(f64));
        const zero = llvm.LLVMConstReal(float, 0);
        // y zero, x infinite, or either not a number: not a number
        const by_zero = llvm.LLVMBuildFCmp(builder, llvm.LLVMRealOEQ, y_size, zero, "");
        const unbounded = llvm.LLVMBuildFCmp(builder, llvm.LLVMRealOEQ, x_size, infinity, "");
        const unordered = llvm.LLVMBuildFCmp(builder, llvm.LLVMRealUNO, x, y, "");
        const invalid = llvm.LLVMBuildOr(
            builder,
            llvm.LLVMBuildOr(builder, by_zero, unbounded, ""),
            unordered,
            "",
        );
        const blocks = [_]llvm.LLVMBasicBlockRef{
            llvm.LLVMAppendBasicBlockInContext(context, function, ""),
            llvm.LLVMAppendBasicBlockInContext(context, function, ""),
            llvm.LLVMAppendBasicBlockInContext(context, function, ""),
            llvm.LLVMAppendBasicBlockInContext(context, function, ""),
            llvm.LLVMAppendBasicBlockInContext(context, function, ""),
            llvm.LLVMAppendBasicBlockInContext(context, function, ""),
        };
        const not_a_number, const check, const unchanged, const grow, const reduce, const done =
            blocks;
        _ = llvm.LLVMBuildCondBr(builder, invalid, not_a_number, check);

        llvm.LLVMPositionBuilderAtEnd(builder, not_a_number);
        const product = llvm.LLVMBuildFMul(builder, x, y, "");
        _ = llvm.LLVMBuildRet(builder, llvm.LLVMBuildFDiv(builder, product, product, ""));

        llvm.LLVMPositionBuilderAtEnd(builder, check);
        const smaller = llvm.LLVMBuildFCmp(builder, llvm.LLVMRealOLT, x_size, y_size, "");
        _ = llvm.LLVMBuildCondBr(builder, smaller, unchanged, grow);
        llvm.LLVMPositionBuilderAtEnd(builder, unchanged);
        _ = llvm.LLVMBuildRet(builder, x);

        // the largest |y| * 2^k not above |x|; a doubling that overflows is not above it
        llvm.LLVMPositionBuilderAtEnd(builder, grow);
        const step = llvm.LLVMBuildPhi(builder, float, "");
        const doubled = llvm.LLVMBuildFMul(builder, step, llvm.LLVMConstReal(float, 2), "");
        const fits = llvm.LLVMBuildFCmp(builder, llvm.LLVMRealOLE, doubled, x_size, "");
        _ = llvm.LLVMBuildCondBr(builder, fits, grow, reduce);
        var step_values = [_]Value{ y_size, doubled };
        var step_blocks = [_]llvm.LLVMBasicBlockRef{ check, grow };
        llvm.LLVMAddIncoming(step, &step_values, &step_blocks, 2);

        llvm.LLVMPositionBuilderAtEnd(builder, reduce);
        const rest = llvm.LLVMBuildPhi(builder, float, "");
        const part = llvm.LLVMBuildPhi(builder, float, "");
        const takes = llvm.LLVMBuildFCmp(builder, llvm.LLVMRealOGE, rest, part, "");
        const taken = llvm.LLVMBuildFSub(builder, rest, part, "");
        const next_rest = llvm.LLVMBuildSelect(builder, takes, taken, rest, "");
        const halved = llvm.LLVMBuildFMul(builder, part, llvm.LLVMConstReal(float, 0.5), "");
        const more = llvm.LLVMBuildFCmp(builder, llvm.LLVMRealOGE, halved, y_size, "");
        _ = llvm.LLVMBuildCondBr(builder, more, reduce, done);
        var rest_values = [_]Value{ x_size, next_rest };
        var part_values = [_]Value{ step, halved };
        var reduce_blocks = [_]llvm.LLVMBasicBlockRef{ grow, reduce };
        llvm.LLVMAddIncoming(rest, &rest_values, &reduce_blocks, 2);
        llvm.LLVMAddIncoming(part, &part_values, &reduce_blocks, 2);

        llvm.LLVMPositionBuilderAtEnd(builder, done);
        const sign_id = llvm.LLVMLookupIntrinsicID("llvm.copysign", "llvm.copysign".len);
        const copysign = llvm.LLVMGetIntrinsicDeclaration(lowerer.module, sign_id, &types, 1);
        const copysign_type = llvm.LLVMIntrinsicGetType(context, sign_id, &types, 1);
        _ = llvm.LLVMBuildRet(builder, call(builder, copysign_type, copysign, &.{ next_rest, x }));
    }
}

fn call(
    builder: llvm.LLVMBuilderRef,
    function_type: Type,
    target: Value,
    arguments: []const Value,
) Value {
    const count: c_uint = @intCast(arguments.len);
    const pointer = @constCast(arguments.ptr);
    return llvm.LLVMBuildCall2(builder, function_type, target, pointer, count, "");
}

// a function made of one loop over `index` from 0 to a count: `begin`, `counting`, the body,
// `end` with what it returns after the last pass
const Loop = struct {
    lowerer: *LLVMLowerer,
    builder: llvm.LLVMBuilderRef,
    function: Value = null,
    head: llvm.LLVMBasicBlockRef = null,
    exit: llvm.LLVMBasicBlockRef = null,
    index: Value = null,

    fn begin(loop: *Loop, name: [:0]const u8, result: Type, parameters: []const Type) Value {
        const lowerer = loop.lowerer;
        const count: c_uint = @intCast(parameters.len);
        const function_type = llvm.LLVMFunctionType(result, @constCast(parameters.ptr), count, 0);
        const function = llvm.LLVMAddFunction(lowerer.module, name, function_type);
        llvm.LLVMSetLinkage(function, llvm.LLVMWeakAnyLinkage);
        const index: c_uint = @bitCast(@as(c_int, llvm.LLVMAttributeFunctionIndex));
        const key = "no-builtins";
        const attribute = llvm.LLVMCreateStringAttribute(lowerer.context, key, key.len, "", 0);
        llvm.LLVMAddAttributeAtIndex(function, index, attribute);
        const entry = llvm.LLVMAppendBasicBlockInContext(lowerer.context, function, "");
        llvm.LLVMPositionBuilderAtEnd(loop.builder, entry);
        loop.function = function;
        return function;
    }

    // the index of this pass, the body follows
    fn counting(loop: *Loop, count: Value) Value {
        const context = loop.lowerer.context;
        const length = loop.lowerer.types.length;
        const builder = loop.builder;
        const entry = llvm.LLVMGetInsertBlock(builder);
        loop.head = llvm.LLVMAppendBasicBlockInContext(context, loop.function, "");
        const body = llvm.LLVMAppendBasicBlockInContext(context, loop.function, "");
        loop.exit = llvm.LLVMAppendBasicBlockInContext(context, loop.function, "");
        _ = llvm.LLVMBuildBr(builder, loop.head);
        llvm.LLVMPositionBuilderAtEnd(builder, loop.head);
        loop.index = llvm.LLVMBuildPhi(builder, length, "");
        var start = [_]Value{llvm.LLVMConstNull(length)};
        var from = [_]llvm.LLVMBasicBlockRef{entry};
        llvm.LLVMAddIncoming(loop.index, &start, &from, 1);
        const done = llvm.LLVMBuildICmp(builder, llvm.LLVMIntUGE, loop.index, count, "");
        _ = llvm.LLVMBuildCondBr(builder, done, loop.exit, body);
        llvm.LLVMPositionBuilderAtEnd(builder, body);
        return loop.index;
    }

    fn element(loop: *Loop, base: Value, at: Value) Value {
        const byte = llvm.LLVMInt8TypeInContext(loop.lowerer.context);
        var offset = [_]Value{at};
        return llvm.LLVMBuildInBoundsGEP2(loop.builder, byte, base, &offset, 1, "");
    }

    fn end(loop: *Loop, result: Value) void {
        const builder = loop.builder;
        const one = llvm.LLVMConstInt(loop.lowerer.types.length, 1, 0);
        var next = [_]Value{llvm.LLVMBuildAdd(builder, loop.index, one, "")};
        var from = [_]llvm.LLVMBasicBlockRef{llvm.LLVMGetInsertBlock(builder)};
        llvm.LLVMAddIncoming(loop.index, &next, &from, 1);
        _ = llvm.LLVMBuildBr(builder, loop.head);
        llvm.LLVMPositionBuilderAtEnd(builder, loop.exit);
        _ = llvm.LLVMBuildRet(builder, result);
    }
};
