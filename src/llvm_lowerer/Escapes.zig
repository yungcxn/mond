const std = @import("std");
const mond = @import("mond");
const HighIr = mond.HighIr;
const StaticPool = mond.StaticPool;
const Ref = HighIr.Ref;

// which closures outlive the call making them, over the whole program. a closure escapes when
// it is returned, stored, put into an aggregate, captured by an escaping closure, or passed to a
// parameter that escapes (unknown callees: always). an escaping closure gets its environment on
// the heap, and so does each variable it captures by reference; all others stay in the frame,
// where they cost nothing
const Escapes = @This();

allocator: std.mem.Allocator,
// per instruction of the whole ir: its function value outlives the call
escapes: std.DynamicBitSetUnmanaged,
// per instruction of the whole ir: an alloca an escaping closure captures, so it lives on the heap
on_heap: std.DynamicBitSetUnmanaged,
// per param of every function (captures first, `parameter_start` gives a function's first):
// the function value passed there escapes / the pointer passed there is captured by an escaping
// closure
parameter_escapes: std.DynamicBitSetUnmanaged,
parameter_captured: std.DynamicBitSetUnmanaged,
parameter_start: []u32,
pool: *const StaticPool,
// per declaration: its ir function, `no_function` for others
function_of_declaration: []const u32,

pub fn init(
    allocator: std.mem.Allocator,
    ir: *const HighIr,
    pool: *const StaticPool,
    function_of_declaration: []const u32,
) Escapes {
    const function_count = ir.functions.len();
    const parameter_start = allocator.alloc(u32, function_count + 1) catch @panic("OOM");
    var count: u32 = 0;
    const functions = ir.functions.columns();
    for (functions.ty, functions.captures, 0..) |function_type, captures, i| {
        parameter_start[i] = count;
        const parameter_count = pool.get(function_type).function_type.parameters.len;
        count += captures + @as(u32, @intCast(parameter_count));
    }
    parameter_start[function_count] = count;
    const instruction_count = ir.insts.len();
    var self: Escapes = .{
        .allocator = allocator,
        .escapes = empty(allocator, instruction_count),
        .on_heap = empty(allocator, instruction_count),
        .parameter_escapes = empty(allocator, count),
        .parameter_captured = empty(allocator, count),
        .parameter_start = parameter_start,
        .pool = pool,
        .function_of_declaration = function_of_declaration,
    };
    // a summary only grows, so passing over every function until none grows ends
    var changed = true;
    while (changed) {
        changed = false;
        for (0..function_count) |i| changed = self.pass(ir, @intCast(i)) or changed;
    }
    return self;
}

fn empty(allocator: std.mem.Allocator, count: usize) std.DynamicBitSetUnmanaged {
    return std.DynamicBitSetUnmanaged.initEmpty(allocator, count) catch @panic("OOM");
}

pub fn deinit(self: *Escapes) void {
    self.escapes.deinit(self.allocator);
    self.on_heap.deinit(self.allocator);
    self.parameter_escapes.deinit(self.allocator);
    self.parameter_captured.deinit(self.allocator);
    self.allocator.free(self.parameter_start);
}

// the place of one function's facts while it is walked
const Walk = struct {
    escapes: *Escapes,
    ir: *const HighIr,
    function: HighIr.Function,
    function_index: u32,
    changed: bool = false,

    fn set(walk: *Walk, bits: *std.DynamicBitSetUnmanaged, index: usize) void {
        if (bits.isSet(index)) return;
        bits.set(index);
        walk.changed = true;
    }

    fn instruction_of(walk: *Walk, ref: Ref) ?HighIr.Inst {
        if (ref == .none or ref.is_const() or ref.is_global()) return null;
        return walk.ir.insts.get(walk.function.first_inst + @intFromEnum(ref)).?;
    }

    // the value outlives the call: a closure or a function-typed param
    fn escape(walk: *Walk, ref: Ref) void {
        const instruction = walk.instruction_of(ref) orelse return;
        const global_index = walk.function.first_inst + @intFromEnum(ref);
        walk.set(&walk.escapes.escapes, global_index);
        if (instruction.op == .param) {
            const position = walk.escapes.parameter_start[walk.function_index] + instruction.a;
            walk.set(&walk.escapes.parameter_escapes, position);
        }
    }

    // the memory the pointer reaches is captured by an escaping closure
    fn capture(walk: *Walk, ref: Ref) void {
        const instruction = walk.instruction_of(ref) orelse return;
        switch (instruction.op) {
            .alloca => {
                const global_index = walk.function.first_inst + @intFromEnum(ref);
                walk.set(&walk.escapes.on_heap, global_index);
            },
            .param => {
                const position = walk.escapes.parameter_start[walk.function_index] + instruction.a;
                walk.set(&walk.escapes.parameter_captured, position);
            },
            .field_ptr, .index_ptr, .convert, .cast => walk.capture(@enumFromInt(instruction.a)),
            else => {},
        }
    }

    fn escapes_already(walk: *Walk, global_index: usize) bool {
        return walk.escapes.escapes.isSet(global_index);
    }
};

// one walk over the function, true when a fact grew
fn pass(self: *Escapes, ir: *const HighIr, function_index: u32) bool {
    const function = ir.functions.get(function_index).?;
    var walk: Walk = .{
        .escapes = self,
        .ir = ir,
        .function = function,
        .function_index = function_index,
    };
    // backwards, so a use is seen before what it uses, phis aside (the outer loop repeats)
    var local = function.insts;
    while (local > 0) {
        local -= 1;
        const global_index = function.first_inst + local;
        const instruction = ir.insts.get(global_index).?;
        const a: Ref = @enumFromInt(instruction.a);
        const b: Ref = @enumFromInt(instruction.b);
        switch (instruction.op) {
            .ret => walk.escape(a),
            .store => walk.escape(b),
            .aggregate => for (ir.list(instruction.b)) |part| walk.escape(@enumFromInt(part)),
            .variant_make => walk.escape(b),
            .phi => if (walk.escapes_already(global_index)) {
                for (ir.list(instruction.b)) |incoming| walk.escape(@enumFromInt(incoming));
            },
            .select => if (walk.escapes_already(global_index)) {
                for (ir.list(instruction.b)) |choice| walk.escape(@enumFromInt(choice));
            },
            .convert, .cast => if (walk.escapes_already(global_index)) walk.escape(a),
            .call => self.call(&walk, a, ir.list(instruction.b)),
            .closure => {
                const outlives = walk.escapes_already(global_index);
                const start = self.parameter_start[instruction.a];
                for (ir.list(instruction.b), 0..) |captured, k| {
                    const ref: Ref = @enumFromInt(captured);
                    if (outlives or self.parameter_escapes.isSet(start + k)) walk.escape(ref);
                    if (outlives or self.parameter_captured.isSet(start + k)) walk.capture(ref);
                }
            },
            else => {},
        }
    }
    return walk.changed;
}

// a direct call passes on what its callee's params do, an unknown callee may keep anything
fn call(self: *Escapes, walk: *Walk, callee: Ref, arguments: []const u32) void {
    const target = self.function_of(callee) orelse {
        for (arguments) |argument| walk.escape(@enumFromInt(argument));
        return;
    };
    const is_external = walk.ir.functions.column(.blocks)[target] == 0;
    const start = self.parameter_start[target];
    for (arguments, 0..) |argument, k| {
        const ref: Ref = @enumFromInt(argument);
        if (is_external or self.parameter_escapes.isSet(start + k)) walk.escape(ref);
        if (!is_external and self.parameter_captured.isSet(start + k)) walk.capture(ref);
    }
}

// the ir function a constant callee names, null for a function value
fn function_of(self: *Escapes, callee: Ref) ?u32 {
    if (!callee.is_const() or self.pool.tag(callee.value()) != .function_value) return null;
    const declaration = self.pool.get(callee.value()).function_value;
    const function = self.function_of_declaration[@intFromEnum(declaration)];
    return if (function == std.math.maxInt(u32)) null else function;
}
