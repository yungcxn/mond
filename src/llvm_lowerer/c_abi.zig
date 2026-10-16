const std = @import("std");
const builtin = @import("builtin");
const llvm = @import("llvm_c");
const mond = @import("mond");
const LLVMLowerer = @import("../LLVMLowerer.zig");
const StaticPool = mond.StaticPool;
const Index = StaticPool.Index;
const Type = LLVMLowerer.Type;

// how a value crosses into or out of a c function of this machine: aarch64 (aapcs64, apple's
// too) or x86-64 (system v). llvm leaves this to the front end, as clang does it
pub const Passing = struct {
    how: How,
    // the llvm type c sees: the value's own, or the registers a record goes in
    lowered: Type,

    pub const How = enum {
        direct,
        // a small int, widened by the caller as c expects
        sign_extended,
        zero_extended,
        // a record in memory, read as the registers c takes it in
        coerced,
        // a record too large for registers: by the address of a copy (aarch64), copied by
        // llvm (`byval`, x86-64), or returned through the caller's slot (`sret`)
        indirect,
        // a function value naming a function without captures, as a c function pointer
        function,
    };
};

pub fn classify(lowerer: *LLVMLowerer, value_type: Index) Passing {
    const types = &lowerer.types;
    const pool = lowerer.pool;
    if (pool.tag(value_type) == .function_type) {
        return .{ .how = .function, .lowered = types.pointer };
    }
    if (!types.is_in_memory(value_type)) {
        const how: Passing.How = switch (pool.get(value_type)) {
            .int_type => |int| if (int.bits >= 32)
                .direct
            else if (int.signedness == .signed)
                .sign_extended
            else
                .zero_extended,
            .simple_type => |simple| if (simple == .bool) .zero_extended else .direct,
            else => .direct,
        };
        return .{ .how = how, .lowered = types.of(value_type) };
    }

    const size = pool.layout(value_type).size;
    var shape: Shape = .{};
    collect(pool, value_type, 0, &shape);
    const context = lowerer.context;
    switch (builtin.cpu.arch) {
        .aarch64 => {
            // up to four floats or doubles alone go in float registers
            const float_count = shape.float32_count + shape.float64_count;
            const homogeneous = !shape.has_integer and float_count >= 1 and float_count <= 4 and
                (shape.float32_count == 0 or shape.float64_count == 0);
            if (homogeneous) {
                const float = if (shape.float64_count > 0)
                    llvm.LLVMDoubleTypeInContext(context)
                else
                    llvm.LLVMFloatTypeInContext(context);
                return .{ .how = .coerced, .lowered = llvm.LLVMArrayType2(float, float_count) };
            }
            if (size > 16) return .{ .how = .indirect, .lowered = types.pointer };
            const register = llvm.LLVMInt64TypeInContext(context);
            const lowered = if (size <= 8) register else llvm.LLVMArrayType2(register, 2);
            return .{ .how = .coerced, .lowered = lowered };
        },
        .x86_64 => {
            if (size > 16 or shape.is_unaligned) {
                return .{ .how = .indirect, .lowered = types.pointer };
            }
            // each eightbyte of only floats goes in an sse register, any other in an integer one
            var eightbytes: [2]Type = undefined;
            const count: usize = if (size > 8) 2 else 1;
            for (eightbytes[0..count], 0..) |*eightbyte, k| {
                const bytes: u64 = @min(8, size - 8 * k);
                eightbyte.* = if (shape.integer_in[k] or !shape.float_in[k])
                    llvm.LLVMIntTypeInContext(context, @intCast(bytes * 8))
                else if (bytes <= 4)
                    llvm.LLVMFloatTypeInContext(context)
                else if (shape.float32_in[k] == 2)
                    llvm.LLVMVectorType(llvm.LLVMFloatTypeInContext(context), 2)
                else
                    llvm.LLVMDoubleTypeInContext(context);
            }
            if (count == 1) return .{ .how = .coerced, .lowered = eightbytes[0] };
            const pair = llvm.LLVMStructTypeInContext(context, &eightbytes, 2, 0);
            return .{ .how = .coerced, .lowered = pair };
        },
        else => @compileError("mond calls c only on aarch64 and x86-64"),
    }
}

// what the scalars of a record are and in which eightbyte they sit
const Shape = struct {
    float32_count: u32 = 0,
    float64_count: u32 = 0,
    has_integer: bool = false,
    integer_in: [2]bool = .{ false, false },
    float_in: [2]bool = .{ false, false },
    float32_in: [2]u8 = .{ 0, 0 },
    // a packed field off its alignment, which c only passes in memory
    is_unaligned: bool = false,
};

fn collect(pool: *StaticPool, value_type: Index, offset: u64, shape: *Shape) void {
    const layout = pool.layout(value_type);
    switch (pool.get(value_type)) {
        .record_type => |record| {
            var at = offset;
            for (0..record.field_types.len) |i| {
                const field = pool.field_type(value_type, i);
                const alignment = @as(u64, 1) << @intCast(pool.layout(field).align_log2);
                if (!record.is_packed) at = std.mem.alignForward(u64, at, alignment);
                if (at % alignment != 0) shape.is_unaligned = true;
                collect(pool, field, at, shape);
                at += pool.layout(field).size;
            }
        },
        .array_type => |array| {
            const element_size = pool.layout(array.element).size;
            for (0..pool.static_length(value_type) orelse 0) |i| {
                collect(pool, array.element, offset + i * element_size, shape);
            }
        },
        // a half has no float class of its own here, it counts as an integer
        .float_type => |float| if (float.bits != 16) {
            const eightbyte = @min(offset / 8, 1);
            shape.float_in[eightbyte] = true;
            if (float.bits == 64) shape.float64_count += 1 else shape.float32_count += 1;
            if (float.bits == 32) shape.float32_in[eightbyte] += 1;
            return;
        } else {
            shape.has_integer = true;
            shape.integer_in[@min(offset / 8, 1)] = true;
        },
        else => {
            shape.has_integer = true;
            if (layout.size == 0) return;
            for (offset / 8..(offset + layout.size - 1) / 8 + 1) |eightbyte| {
                shape.integer_in[@min(eightbyte, 1)] = true;
            }
        },
    }
}
