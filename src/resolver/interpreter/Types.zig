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
        => self.build(node),
        else => .pooled(self.define(node)),
    };
}

// a type expression whose parts are evaluated in the frame: arrays, pointers, unions of variants
fn build(self: *Types, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const tree = resolver.tree;
    const kind = tree.kind(node);

    // `A | B`: the variants of both sides, a union on either side contributes its members
    if (kind == .unify_variants) {
        const mark = interpreter.pool_indices.len;
        defer interpreter.pool_indices.len = mark;
        for ([_]NodeId{ tree.arg(node, 0), tree.arg(node, 1) }) |side| {
            const side_type = self.type_of_node(side) orelse return .poison;
            switch (static_pool.tag(side_type)) {
                .variant_union_type => {
                    interpreter.pool_indices.append(static_pool.get(side_type).variant_union_type);
                },
                .variant_type => interpreter.pool_indices.push(side_type),
                else => return interpreter.fail(side, .type_mismatch, side_type, .variant_type),
            }
        }

        const members = interpreter.pool_indices.buffer[mark..interpreter.pool_indices.len];
        return .pooled(static_pool.intern(.{ .variant_union_type = members }));
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

// another case of the same variant keeps the payload bits
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

    const field_count = static_pool.get(target_payload).record_type.field_types.len;
    const source_payload = static_pool.get(case).variant_case_type.payload;
    // a case without payload has nothing to give the payload of the target case
    if (source_payload == .none) return interpreter.fail(node, .invalid_cast, case, target);
    if (static_pool.get(source_payload).record_type.field_types.len != field_count) {
        return interpreter.fail(node, .not_static, 0, 0);
    }

    const mark = interpreter.pool_indices.len;
    defer interpreter.pool_indices.len = mark;
    const payload_value = static_pool.get(value.index()).variant_value.payload;
    interpreter.pool_indices.append(static_pool.get(payload_value).aggregate_value.elements);

    for (0..field_count) |i| {
        const source_field = static_pool.field_type(source_payload, i);
        const target_field = static_pool.field_type(target_payload, i);
        if (source_field == target_field) continue;

        const field: Value = .of(static_pool, interpreter.pool_indices.buffer[mark + i]);
        const reinterpreted = Value.reinterpret(field, target_field) orelse
            return interpreter.fail(node, .not_static, 0, 0);
        interpreter.pool_indices.buffer[mark + i] = interpreter.interned(reinterpreted);
    }

    const payload = static_pool.intern(.{ .aggregate_value = .{
        .value_type = target_payload,
        .elements = interpreter.pool_indices.buffer[mark..interpreter.pool_indices.len],
    } });
    const niche = static_pool.niche_case(target, payload);
    if (niche != .none) return .pooled(niche);
    const retagged = static_pool.intern(.{
        .variant_value = .{ .case = target, .payload = payload },
    });
    return .pooled(retagged);
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
    return .boolean(subject_type == wanted or
        static_pool.type_of(subject) == wanted or
        static_pool.implements(subject_type, wanted));
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
