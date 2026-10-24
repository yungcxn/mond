const std = @import("std");
const builtin = @import("builtin");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;

// types: type values built while evaluating, casts and questions about types
const Types = @This();

pub fn owning_interpreter(self: *Types) *Interpreter {
    return @alignCast(@fieldParentPtr("types", self));
}

pub fn type_of_node(self: *Types, node: NodeId) ?Index {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;

    const value = interpreter.evaluate(node);
    if (value.is(.poison_type)) return null;

    const is_type = value.is_pooled() and
        !value.is(.none) and
        static_pool.properties(value.index()).is_type;
    if (is_type) return value.index();

    _ = interpreter.fail(node, .not_a_type, interpreter.interned(value), .none);
    return null;
}

pub fn admits(self: *Types, value: Value, expected_type: Index) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const value_type = interpreter.value_type(value);

    const value_is_number = Value.is_int(value_type) or Value.is_float(value_type);
    const expects_number = Value.is_int(expected_type) or Value.is_float(expected_type);
    if (value_is_number and expects_number) return true;

    return value_type == expected_type or
        resolver.static_pool.coercion(value_type, expected_type) != .incompatible;
}

// arrays of different lengths join to an array of dynamic length
pub fn joined_type(self: *Types, values: []const Value) Index {
    const interpreter = self.owning_interpreter();
    if (values.len == 0) return .unit_type;

    const static_pool = &interpreter.owning_resolver().static_pool;
    const first_type = interpreter.value_type(values[0]);
    var joined = first_type;
    for (values[1..]) |value| {
        const value_type = interpreter.value_type(value);
        if (value_type == joined) continue;
        // arrays of different lengths make a runtime-length array
        if (static_pool.tag(first_type) == .array_type) {
            const element = static_pool.get(first_type).array_type.element;
            return static_pool.intern(.{
                .array_type = .{ .length = StaticPool.dyn_len, .element = element },
            });
        }
        // other values join like the branches of an `if` (two cases make their variant)
        const join = static_pool.join(joined, value_type).joined_type;
        if (join != .none) joined = join;
    }
    return joined;
}

pub fn static_value(self: *Types, node: NodeId, kind: Kind) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (!interpreter.has_body_frame()) {
        return .pooled(resolver.types.define_static_type(interpreter.function_context, node));
    }

    return switch (kind) {
        .def_fun => interpreter.calls.closure(interpreter.node_info(.declaration, node)),
        .type_array,
        .type_array_unlengthed,
        .type_ptr,
        .type_ptrmut,
        .unify_variants,
        .unify_variants_packed,
        .variant_difference,
        => self.build(node),
        else => .pooled(self.define(node)),
    };
}

// a type expression whose parts are evaluated in the frame: arrays, pointers, unified variants
fn build(self: *Types, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const tree = resolver.tree;
    const kind = tree.kind(node);

    // `A || B`, `A ||| B` (see `StaticPool.unified_of`)
    if (kind == .unify_variants or kind == .unify_variants_packed) {
        const sides = [_]NodeId{ tree.arg(node, 0), tree.arg(node, 1) };
        const types = [_]Index{
            self.type_of_node(sides[0]) orelse return .poison,
            self.type_of_node(sides[1]) orelse return .poison,
        };
        const is_packed = kind == .unify_variants_packed;
        return switch (static_pool.unified_of(types[0], types[1], is_packed)) {
            .unified => |unified| .pooled(unified),
            .sizeless_side => |i| {
                return interpreter.fail(sides[i], .unstorable_outside_parameter, types[i], 0);
            },
        };
    }

    // `A -- B` (see `StaticPool.difference_of`)
    if (kind == .variant_difference) {
        const sides = [_]NodeId{ tree.arg(node, 0), tree.arg(node, 1) };
        const types = [_]Index{
            self.type_of_node(sides[0]) orelse return .poison,
            self.type_of_node(sides[1]) orelse return .poison,
        };
        return switch (static_pool.difference_of(types[0], types[1])) {
            .difference => |difference| .pooled(difference),
            .wrong_side => |i| {
                const expected = if (i == 0) Index.variant_type else types[0];
                return interpreter.fail(sides[i], .type_mismatch, types[i], expected);
            },
        };
    }

    const element_node = tree.arg(node, if (kind == .type_array) 1 else 0);
    const element = self.type_of_node(element_node) orelse return .poison;
    if (tree.props(node).pointer) {
        return .pooled(static_pool.pointer_to(element, kind == .type_ptrmut));
    }
    if (kind == .type_array_unlengthed) {
        return .pooled(static_pool.intern(.{
            .array_type = .{ .length = StaticPool.dyn_len, .element = element },
        }));
    }

    const length_node = tree.arg(node, 0);
    const length = interpreter.evaluate(length_node);
    if (!Value.is_int(length.value_type)) {
        if (length.is(.poison_type)) return length;
        return interpreter.fail(length_node, .not_static, interpreter.interned(length), 0);
    }
    return .pooled(static_pool.array_of(length.bits, element));
}

// a type defined in a frame sees the frame's values of the locals it names as static parameters
fn define(self: *Types, node: NodeId) Index {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const decl_pool = &resolver.decl_pool;
    var context = Resolver.FunctionContext{
        .declaration = .none,
        .return_type = .none,
        .self_type = .none,
        .loop_depth = 0,
        .is_static_context = true,
    };

    resolver.declarations.open_declaration_scope(true, .none, 0);
    defer resolver.scopes.close();

    const subtree = resolver.tree.subtree(node);
    for (subtree[0]..subtree[1]) |i| {
        const id: NodeId = @intCast(i);
        const declaration = interpreter.node_info(.declaration, id);
        const is_local_name = resolver.tree.props(id).name and
            declaration != .none and
            !decl_pool.get(declaration, .flags).is_global;
        if (!is_local_name) continue;

        const value = interpreter.variables.peek(declaration);
        if (value.is(.none)) continue;

        const static_value_index = interpreter.interned(value);
        const parameter = resolver.declarations.declare_local(
            decl_pool.get(declaration, .name),
            id,
            .static_parameter,
            decl_pool.get(declaration, .value_type),
        );
        decl_pool.set(parameter, .static_value, static_value_index);
    }
    return resolver.types.define_static_type(&context, node);
}

pub fn cast(self: *Types, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const operand = resolver.tree.arg(node, 0);
    const target_node = resolver.tree.arg(node, 1);
    const framed = interpreter.has_body_frame();

    const value = interpreter.evaluate(operand);
    if (!framed or interpreter.node_info(.node_type, node) != .poison_type) {
        // the type cast from: the checked one in a frame, else the value's case or type
        const source = blk: {
            if (interpreter.has_body_frame()) {
                const operand_type = interpreter.node_info(.node_type, operand);
                break :blk static_pool.substitute_type_variables(operand_type);
            }
            const case = interpreter.patterns.case_of(value);
            if (case != .none) break :blk case;
            break :blk interpreter.value_type(value);
        };
        const target = if (interpreter.has_body_frame())
            interpreter.node_info(.node_type, node)
        else
            resolver.types.cast_target(
                interpreter.function_context,
                resolver.tree.arg(node, 1),
                source,
            );

        switch (static_pool.cast_kind(source, target)) {
            .bit_reinterpret => {
                const variant_to_int = Value.is_int(target) and
                    static_pool.properties(source).is_variant;
                if (variant_to_int) return self.tag(node, value, target);
                return .cast(value, target);
            },
            .variant_retag => return self.retag(node, value, target),
            .array_narrow, .pointer_relength => return self.shrink(node, value, target),
            .array_to_slice => return interpreter.sliced(value, target, 0, null),
            .slice_to_pointer => return .ref(target, value.cell()),
            .identity,
            .int_resize,
            .int_to_float,
            .float_to_int,
            .float_resize,
            .bit_extend,
            .payload_wrap,
            .trait_narrow,
            => return .cast(value, target),
            // the checker reports invalid casts it can see, this is one only the value shows
            .invalid => return interpreter.fail(node, .invalid_cast, source, target),
        }
    }

    // the checker could not type the target, so it is a type the frame computes
    if (interpreter.node_info(.static_value, target_node) != .none) return .poison;
    const target = self.type_of_node(target_node) orelse return .poison;

    const value_type = interpreter.value_type(value);
    if (static_pool.cast_kind(value_type, target) == .invalid) {
        return interpreter.fail(node, .invalid_cast, interpreter.value_type(value), target);
    }
    return .cast(value, target);
}

// a variant case without payload reinterpreted as an integer is its tag
fn tag(self: *Types, node: NodeId, value: Value, target: Index) Value {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;

    const case = interpreter.patterns.case_of(value);
    if (case == .none) return interpreter.fail(node, .not_static, 0, 0);

    const case_type = static_pool.get(case).variant_case_type;
    if (case_type.payload != .none) return interpreter.fail(node, .not_static, 0, 0);
    return .int(target, static_pool.get(case_type.tag).int_value.bits);
}

// another case of the same variant keeps the payload's bytes, the target case reads them as at run
// time (bytes past the source's payload are zero)
fn retag(self: *Types, node: NodeId, value: Value, target: Index) Value {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;

    const case = interpreter.patterns.case_of(value);
    if (case == target) return value;

    const target_payload = static_pool.get(target).variant_case_type.payload;
    if (target_payload == .none) return .pooled(target);

    if (case == .none or !value.is_pooled()) return interpreter.fail(node, .not_static, 0, 0);
    if (static_pool.tag(value.index()) != .variant_value) {
        return interpreter.fail(node, .not_static, 0, 0);
    }

    const source_payload = static_pool.get(case).variant_case_type.payload;
    // a case without payload has nothing to give the payload of the target case
    if (source_payload == .none) return interpreter.fail(node, .invalid_cast, case, target);

    const source_size = static_pool.layout(source_payload).size;
    const target_size = static_pool.layout(target_payload).size;
    const bytes = interpreter.owning_resolver().temporary_slice(u8, @max(source_size, target_size));
    @memset(bytes, 0);
    const payload_value: Value = .pooled(static_pool.get(value.index()).variant_value.payload);
    if (!self.store_bytes(payload_value, source_payload, bytes)) {
        return interpreter.fail(node, .not_static, 0, 0);
    }
    const target_value = self.load_bytes(target_payload, bytes) orelse
        return interpreter.fail(node, .not_static, 0, 0);
    const payload = interpreter.interned(target_value);
    const niche = static_pool.niche_case(target, payload);
    if (niche != .none) return .pooled(niche);
    const retagged = static_pool.intern(.{
        .variant_value = .{ .case = target, .payload = payload },
    });
    return .pooled(retagged);
}

extern "c" fn syscall(number: c_long, ...) c_long;

// the kernel's call: on linux directly, elsewhere through the c library. -errno when it failed
fn kernel(at: [7]u64) i64 {
    if (builtin.os.tag != .linux) {
        const c: [7]c_long = @bitCast(at);
        const result = syscall(c[0], c[1], c[2], c[3], c[4], c[5], c[6]);
        return if (result == -1) -@as(i64, std.c._errno().*) else result;
    }
    return switch (builtin.cpu.arch) {
        .x86_64 => asm volatile ("syscall"
            : [ret] "={rax}" (-> i64),
            : [number] "{rax}" (at[0]),
              [arg1] "{rdi}" (at[1]),
              [arg2] "{rsi}" (at[2]),
              [arg3] "{rdx}" (at[3]),
              [arg4] "{r10}" (at[4]),
              [arg5] "{r8}" (at[5]),
              [arg6] "{r9}" (at[6]),
            : .{ .rcx = true, .r11 = true, .memory = true }),
        .aarch64 => asm volatile ("svc #0"
            : [ret] "={x0}" (-> i64),
            : [number] "{x8}" (at[0]),
              [arg1] "{x0}" (at[1]),
              [arg2] "{x1}" (at[2]),
              [arg3] "{x2}" (at[3]),
              [arg4] "{x3}" (at[4]),
              [arg5] "{x4}" (at[5]),
              [arg6] "{x5}" (at[6]),
            : .{ .memory = true }),
        else => @compileError("the kernel's calls are known on x86_64 and aarch64"),
    };
}

// `syscall (n, ..)` while compiling runs as it does in the program: integers and bools go as they
// are, a pointer as the address of what it points to laid out in bytes, which a `*T` gets back
// after the call. a pointer to an element reaches the elements after it. the result is the
// kernel's, or the negated error number
pub fn system_call(self: *Types, node: NodeId, arguments: []const NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    // room after a pointer's bytes, so a length past them does not reach other memory
    const slack = 1 << 16;
    if (arguments.len > 7 or interpreter.speculative > 0) {
        return interpreter.fail(node, .not_static, 0, 0);
    }

    var registers: [7]u64 = @splat(0);
    var buffers: [7][]u8 = @splat(&.{});
    // where the bytes of a `*T` go back to: its first cell, how many there are and their type
    var written: [7]?struct { u32, u32, Index } = @splat(null);
    defer for (buffers) |buffer| resolver.allocator.free(buffer);
    for (arguments, 0..) |argument, i| {
        const value_node = resolver.tree.arg_value(argument);
        const value = interpreter.evaluate(value_node);
        if (value.is(.poison_type) or interpreter.unwind != .none) return value;

        const argument_type = interpreter.checked_type(value_node);
        if (!static_pool.is_pointer(argument_type)) {
            const scalar = if (value.is_pooled()) Value.of(static_pool, value.index()) else value;
            registers[i] = scalar.raw_bits();
            continue;
        }
        const pointer = static_pool.get(argument_type).pointer_type;
        // the cells of what a `*T` points to are written after the call, so they are thawed
        if (pointer.is_mutable and value.is_ref()) _ = interpreter.thaw_cell(value.cell());
        const target = interpreter.dereference(value);
        const element_size = static_pool.layout(pointer.pointee).size;
        // an element is followed by the others of its array, up to the next value of another type
        var run: u32 = 1;
        if (value.is_ref() and !target.is_heap() and !target.is_pooled()) {
            const cells = interpreter.memory.buffer[value.cell()..interpreter.memory.len];
            while (run < cells.len and cells[run].value_type == target.value_type) run += 1;
        }
        // an array without a length in its type has the length of its value
        const size = if (static_pool.tag(pointer.pointee) == .array_type)
            (interpreter.aggregate_length(target) orelse 0) *
                static_pool.layout(static_pool.element_type(pointer.pointee)).size
        else
            run * element_size;
        buffers[i] = resolver.allocator.alloc(u8, size + slack) catch @panic("OOM");
        @memset(buffers[i], 0);
        for (0..run) |r| {
            const part = if (value.is_ref())
                interpreter.memory.buffer[value.cell() + r]
            else
                target;
            if (!self.lay_out(part, pointer.pointee, buffers[i][r * element_size ..])) {
                return interpreter.fail(value_node, .not_static, interpreter.interned(value), 0);
            }
        }
        registers[i] = @intFromPtr(buffers[i].ptr);
        if (pointer.is_mutable and value.is_ref()) {
            written[i] = .{ value.cell(), run, pointer.pointee };
        }
    }

    interpreter.system_calls += 1;
    const returned = kernel(registers);

    for (written, buffers) |back, buffer| {
        const cell, const run, const pointee = back orelse continue;
        const element_size = static_pool.layout(pointee).size;
        for (0..run) |r| {
            self.read_back(cell + @as(u32, @intCast(r)), pointee, buffer[r * element_size ..]);
        }
    }
    return .int(.i64_type, @bitCast(returned));
}

// the bytes of a value: a block by its cells, anything else as `store_bytes` lays it out
fn lay_out(self: *Types, value: Value, value_type: Index, bytes: []u8) bool {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;
    // a bit-packed record is laid out whole, its fields share bytes
    const is_bit_packed = static_pool.tag(value_type) == .record_type and
        static_pool.is_bit_packed(static_pool.get(value_type).record_type);
    if (is_bit_packed and value.is_heap()) {
        return self.store_bytes(.pooled(interpreter.interned(value)), value_type, bytes);
    }
    if (!value.is_heap()) return self.store_bytes(value, value_type, bytes);
    for (0..value.len()) |i| {
        const part_type, const offset = part_at(static_pool, value_type, i) orelse return false;
        const part = interpreter.memory.buffer[value.cell() + i];
        if (!self.lay_out(part, part_type, bytes[offset..])) return false;
    }
    return true;
}

// the cell's value read from the bytes `lay_out` made, a block's cells one by one
fn read_back(self: *Types, cell: u32, value_type: Index, bytes: []const u8) void {
    const interpreter = self.owning_interpreter();
    const value = interpreter.memory.buffer[cell];
    const static_pool = &interpreter.owning_resolver().static_pool;
    const is_bit_packed = static_pool.tag(value_type) == .record_type and
        static_pool.is_bit_packed(static_pool.get(value_type).record_type);
    if (value.is_heap() and !is_bit_packed) {
        for (0..value.len()) |i| {
            const part_type, const offset = part_at(static_pool, value_type, i) orelse return;
            self.read_back(value.cell() + @as(u32, @intCast(i)), part_type, bytes[offset..]);
        }
        return;
    }
    if (self.load_bytes(value_type, bytes)) |loaded| interpreter.store_cell(cell, loaded);
}

// a value laid out in `bytes` as its type lays it out in memory: numbers, bools, arrays, records,
// text. false for anything else (a pointer has no static address)
fn store_bytes(self: *Types, value: Value, value_type: Index, bytes: []u8) bool {
    const static_pool = &self.owning_interpreter().owning_resolver().static_pool;
    const size = static_pool.layout(value_type).size;
    if (Value.is_number(value_type) or value_type == .bool_type) {
        const scalar = if (value.is_pooled()) Value.of(static_pool, value.index()) else value;
        const raw = scalar.raw_bits();
        for (bytes[0..size], 0..) |*byte, i| byte.* = @truncate(raw >> @intCast(i * 8));
        return true;
    }
    if (!value.is_pooled() or value.is(.none)) return false;
    switch (static_pool.get(value.index())) {
        .string_value => |text| @memcpy(bytes[0..text.len], text),
        .aggregate_value => |aggregate| for (aggregate.elements, 0..) |element, i| {
            // a bit field's bits go where they start
            const is_bit_field = static_pool.tag(value_type) == .record_type and
                static_pool.is_bit_field(static_pool.get(value_type).record_type, i);
            if (is_bit_field) {
                const record = static_pool.get(value_type).record_type;
                const offset = static_pool.field_bit_offset(record, i);
                const raw = Value.of(static_pool, element).raw_bits();
                for (0..static_pool.field_bits(record.field_types[i])) |bit| {
                    const at = offset + bit;
                    const mask = @as(u8, 1) << @intCast(at % 8);
                    if (raw >> @intCast(bit) & 1 != 0) {
                        bytes[at / 8] |= mask;
                    } else {
                        bytes[at / 8] &= ~mask;
                    }
                }
                continue;
            }
            const part_type, const offset = part_at(static_pool, value_type, i) orelse return false;
            if (!self.store_bytes(.of(static_pool, element), part_type, bytes[offset..])) {
                return false;
            }
        },
        else => return false,
    }
    return true;
}

// a value of `value_type` read from the bytes `store_bytes` lays out, null for what it cannot
fn load_bytes(self: *Types, value_type: Index, bytes: []const u8) ?Value {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;
    const size = static_pool.layout(value_type).size;
    if (Value.is_number(value_type) or value_type == .bool_type) {
        var raw: u64 = 0;
        for (bytes[0..size], 0..) |byte, i| raw |= @as(u64, byte) << @intCast(i * 8);
        return Value.from_raw(value_type, raw);
    }
    const is_record = static_pool.tag(value_type) == .record_type;
    if (!is_record and static_pool.tag(value_type) != .array_type) return null;

    const mark = interpreter.pool_indices.len;
    defer interpreter.pool_indices.len = mark;
    const count = if (is_record)
        static_pool.get(value_type).record_type.field_types.len
    else
        static_pool.static_length(value_type) orelse return null;
    // by index: interning a part may move the type's lists
    for (0..count) |i| {
        const part_type, const offset = part_at(static_pool, value_type, i).?;
        const is_bit_field = is_record and
            static_pool.is_bit_field(static_pool.get(value_type).record_type, i);
        if (is_bit_field) {
            const start = static_pool.field_bit_offset(static_pool.get(value_type).record_type, i);
            var raw: u64 = 0;
            for (0..static_pool.field_bits(part_type)) |bit| {
                const at = start + bit;
                raw |= @as(u64, bytes[at / 8] >> @intCast(at % 8) & 1) << @intCast(bit);
            }
            interpreter.pool_indices.push(interpreter.interned(Value.from_raw(part_type, raw)));
            continue;
        }
        const part = self.load_bytes(part_type, bytes[offset..]) orelse return null;
        interpreter.pool_indices.push(interpreter.interned(part));
    }
    return .pooled(static_pool.intern(.{ .aggregate_value = .{
        .value_type = value_type,
        .elements = interpreter.pool_indices.buffer[mark..interpreter.pool_indices.len],
    } }));
}

// the type of part `i` of a record or array and where it starts, null for any other type
fn part_at(static_pool: *StaticPool, aggregate_type: Index, i: usize) ?struct { Index, u64 } {
    return switch (static_pool.get(aggregate_type)) {
        .record_type => |record| .{ record.field_types[i], static_pool.field_offset(record, i) },
        .array_type => |array| .{ array.element, i * static_pool.layout(array.element).size },
        else => null,
    };
}

// a narrowed array is a view on the cells of the original, from the start the target names
fn shrink(self: *Types, node: NodeId, value: Value, target: Index) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (value.is(.poison_type) or target == .poison_type) return .poison;

    const to_pointer = static_pool.is_pointer(target);
    const array_type = static_pool.pointee(target);
    const length_index = static_pool.get(array_type).array_type.length;
    if (static_pool.tag(length_index) != .int_value) {
        if (to_pointer and value.is_ref()) return .ref(target, value.cell());
        return value;
    }

    const start_node = resolver.tree.narrowed(resolver.tree.arg(node, 1));
    const start_value: Value = if (start_node != 0)
        interpreter.evaluate(start_node)
    else
        .int(.u64_type, 0);
    if (start_value.is(.poison_type)) return .poison;
    if (!Value.is_int(start_value.value_type)) return interpreter.fail(node, .not_static, 0, 0);

    const held_cell = if (value.is_ref()) value.cell() else interpreter.push_cell(value);
    // a pooled aggregate is thawed into cells first, so the view can point into them
    const source_length = interpreter.aggregate_length(interpreter.memory.buffer[held_cell]);
    const cell = if (source_length != null) interpreter.thaw_cell(held_cell).cell() else held_cell;

    const length = static_pool.get(length_index).int_value.bits;
    // the view stays inside the source: its elements, or the cells behind a reference
    const available: u64 = source_length orelse interpreter.memory.len - cell;
    if (start_value.bits > available or length > available - start_value.bits) {
        const shown_start = interpreter.interned(start_value);
        return interpreter.fail(node, .static_eval_failed, shown_start, available);
    }
    const start: u32 = @intCast(start_value.bits);
    const view: Value = .block(array_type, cell + start, @intCast(length));
    if (to_pointer) return .ref(target, interpreter.push_cell(view));
    return view;
}

pub fn bit_cast(self: *Types, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const operand = resolver.tree.arg(node, 0);

    const evaluated = interpreter.evaluate(operand);
    const value = Value.fit(evaluated, interpreter.node_info(.node_type, operand));
    if (value.is(.poison_type)) return value;

    const target = if (interpreter.has_body_frame())
        interpreter.node_info(.node_type, node)
    else
        resolver.types.type_from_node(interpreter.function_context, resolver.tree.arg(node, 1));
    return Value.reinterpret(value, target) orelse
        interpreter.fail(node, .not_static, interpreter.interned(value), 0);
}

pub fn type_test(self: *Types, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const operand = resolver.tree.arg(node, 0);
    const type_node = resolver.tree.arg(node, 1);
    const framed = interpreter.has_body_frame();

    const static_type = if (framed)
        Index.none
    else
        static_pool.through_pointer(
            resolver.expressions.infer(interpreter.function_context, operand, .none),
        );

    if (resolver.tree.macros) {
        const operand_type = if (framed)
            interpreter.node_info(.node_type, operand)
        else
            static_type;
        if (static_pool.is_tree(operand_type)) {
            const evaluated = interpreter.evaluate(operand);
            const tree = interpreter.trees.node_of(evaluated) orelse return .poison;
            return .boolean(interpreter.trees.has_type(tree, self.tested_type(type_node)));
        }
    }

    // a precise static type answers without evaluating the operand
    const known = static_type != .none and
        static_type != .poison_type and
        static_pool.tag(static_type) != .meta_type and
        static_pool.tag(static_type) != .trait_type and
        static_pool.template_of(static_type) == .none;
    const subject = if (known)
        static_type
    else
        interpreter.interned(interpreter.dereference(interpreter.evaluate(operand)));

    const named = self.tested_type(type_node);
    // a stcfun named as a type stands for the types it makes
    const tested = if (named != .none and static_pool.tag(named) == .static_function)
        static_pool.intern(.{ .template_type = static_pool.get(named).static_function.declaration })
    else
        named;
    const wanted = if (tested != .none) tested else self.type_of_node(type_node) orelse
        return .poison;

    const subject_type = if (static_pool.properties(subject).is_type)
        subject
    else
        static_pool.type_of(subject);
    if (static_pool.tag(wanted) == .template_type) {
        return .boolean(resolver.generics.realizes(subject_type, wanted));
    }
    const matches = subject_type == wanted or
        static_pool.type_of(subject) == wanted or
        static_pool.implements(subject_type, wanted);
    if (matches) return .boolean(true);

    // a value is of the type its case or member is, which may need the value
    const operand_type = static_pool.through_pointer(if (framed)
        interpreter.node_info(.node_type, operand)
    else
        static_type);
    if (operand_type == .none) return .boolean(false);
    switch (static_pool.units_covered(operand_type, wanted)) {
        .all => return .boolean(true),
        .none => return .boolean(false),
        .some => {},
    }
    const value = if (known)
        interpreter.dereference(interpreter.evaluate(operand))
    else
        Value.of(static_pool, subject);
    if (value.is(.poison_type)) return value;
    const case = interpreter.patterns.case_of(value);
    const variant = if (case == .none) Index.none else static_pool.get(case).variant_case_type.variant;
    for ([_]Index{ case, variant, interpreter.value_type(value) }) |unit| {
        if (unit == .none or !static_pool.covers_unit(operand_type, unit)) continue;
        return .boolean(static_pool.covers_unit(wanted, unit));
    }
    return .boolean(false);
}

// the type named on the right of `oftype` as the checker knows it, none when it does not
inline fn tested_type(self: *Types, type_node: NodeId) Index {
    const interpreter = self.owning_interpreter();
    if (interpreter.has_body_frame()) return interpreter.node_info(.static_value, type_node);
    const context = interpreter.function_context;
    return interpreter.owning_resolver().types.type_from_node(context, type_node);
}

// `sizeof` and `alignof` in bytes, of a type or of a value's type
pub fn size_of(self: *Types, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const operand = resolver.tree.arg(node, 0);

    const checked = interpreter.checked_type(operand);
    const measured = if (static_pool.tag(checked) == .meta_type)
        interpreter.interned(interpreter.evaluate(operand))
    else
        static_pool.substitute_type_variables(checked);

    const is_template = resolver.generics.is_template(interpreter.node_info(.declaration, operand));
    const unrealized = is_template or
        measured != .poison_type and static_pool.contains_template(measured);
    if (unrealized) return interpreter.fail(operand, .unrealized_template, measured, 0);

    if (measured == .poison_type) return .poison;
    const layout = static_pool.layout(resolver.types.with_runtime_lengths(measured));
    if (resolver.tree.kind(node) == .alignof) {
        return .int(.u64_type, @as(u64, 1) << @intCast(layout.align_log2));
    }
    return .int(.u64_type, layout.size);
}
