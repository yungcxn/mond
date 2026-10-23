const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const StaticPool = @import("../StaticPool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;

// match: arms tried in order, patterns tested against values and their binders bound
const Patterns = @This();

pub fn owning_interpreter(self: *Patterns) *Interpreter {
    return @alignCast(@fieldParentPtr("patterns", self));
}

pub fn match(self: *Patterns, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;
    const scrutinee = tree.arg(node, 0);
    const arms = tree.arg(node, 1);

    const evaluated = interpreter.evaluate(scrutinee);
    const scrutinee_type = if (interpreter.has_body_frame())
        interpreter.node_info(.node_type, scrutinee)
    else
        evaluated.value_type;
    const through_reference = evaluated.is_ref() and
        resolver.static_pool.through_pointer(scrutinee_type) != scrutinee_type;
    const value = if (through_reference) interpreter.dereference(evaluated) else evaluated;
    if (value.is(.poison_type) or interpreter.unwind != .none) return value;

    // a body frame already holds the binders of the arms
    const scoped = !interpreter.has_body_frame();
    if (scoped) resolver.scopes.open();
    defer if (scoped) resolver.scopes.close();

    // the checker matched a static scrutinee itself and checked only the arm it took
    if (!scoped) {
        for (tree.manychildren(arms)) |arm| {
            if (interpreter.node_info(.static_value, arm) == .bool_true) {
                return interpreter.evaluate(tree.arg(arm, 1));
            }
        }
    }

    // by index: a value pattern may evaluate a quote, which grows the tree and moves child lists
    for (0..tree.manychildren(arms).len) |arm_index| {
        const arm = tree.manychildren(arms)[arm_index];
        if (self.matches(tree.arg(arm, 0), value)) return interpreter.evaluate(tree.arg(arm, 1));
        // a guard that jumped leaves the arms after it
        if (interpreter.unwind != .none) return .poison;
    }
    return interpreter.fail(node, .non_exhaustive_match, interpreter.interned(value), .none);
}

// a case value is pooled, or a block of its payload fields when they hold references
pub fn case_of(self: *Patterns, value: Value) Index {
    const static_pool = &self.owning_interpreter().owning_resolver().static_pool;
    const is_case_block = value.is_heap() and
        static_pool.tag(value.value_type) == .variant_case_type;
    if (is_case_block) return value.value_type;
    if (!value.is_pooled() or value.is(.none)) return .none;

    return switch (static_pool.tag(value.index())) {
        .variant_value => static_pool.get(value.index()).variant_value.case,
        .variant_case_type => value.index(),
        else => .none,
    };
}

pub fn matches(self: *Patterns, pattern: NodeId, value: Value) bool {
    const interpreter = self.owning_interpreter();
    const tree = interpreter.owning_resolver().tree;
    if (tree.macros and interpreter.trees.node_of(value) != null) {
        return interpreter.trees.matches(pattern, value);
    }

    switch (tree.kind(pattern)) {
        .identifier => {
            self.bind_name(pattern, value);
            return true;
        },
        .partial__match_case_pattern_or => return self.matches_any(pattern, value),
        .partial__match_case_pattern_typecast => return self.matches_typecast(pattern, value),
        .labelarrow => {
            if (!self.matches(tree.arg(pattern, 0), value)) return false;
            self.bind_label(tree.arg(pattern, 1), self.payload_of(value) orelse value);
            return true;
        },
        .fun_call => return self.matches_fields(pattern, value),
        .gen_incl,
        .gen_excl,
        .gen_lowerbound,
        .gen_upperbound_incl,
        .gen_upperbound_excl,
        => return self.matches_range(pattern, value),
        else => return self.matches_value(pattern, value),
    }
}

inline fn matches_any(self: *Patterns, alternatives: NodeId, value: Value) bool {
    const tree = self.owning_interpreter().owning_resolver().tree;
    for (0..tree.manychildren(alternatives).len) |alternative_index| {
        const alternative = tree.manychildren(alternatives)[alternative_index];
        if (self.matches(alternative, value)) return true;
    }
    return false;
}

// `T x`: a case matches its variant and any unified variant of it, other values their type or trait
inline fn matches_typecast(self: *Patterns, pattern: NodeId, value: Value) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const tree = resolver.tree;

    const wanted_type = if (interpreter.has_body_frame())
        interpreter.node_info(.node_type, tree.arg(pattern, 1))
    else
        resolver.types.type_from_node(interpreter.function_context, tree.arg(pattern, 0));
    const case = self.case_of(value);
    const value_type = interpreter.value_type(value);

    // a case belongs to its variant and to every unified variant holding that variant
    const matched = if (case != .none) blk: {
        const variant = static_pool.get(case).variant_case_type.variant;
        if (variant == wanted_type) break :blk true;
        break :blk static_pool.is_member(wanted_type, variant);
    } else value_type == wanted_type or static_pool.implements(value_type, wanted_type);
    if (matched) self.bind_name(tree.arg(pattern, 1), value);
    return matched;
}

// `T(a, b = ..)`: a record or variant case whose fields match the argument patterns
inline fn matches_fields(self: *Patterns, pattern: NodeId, value: Value) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const tree = resolver.tree;

    const checked_target = interpreter.node_info(.node_type, pattern);
    const target = if (checked_target != .none)
        checked_target
    else
        interpreter.interned(interpreter.evaluate(tree.arg(pattern, 0)));

    var record_type = target;
    var fields = value;
    if (static_pool.tag(target) == .variant_case_type) {
        if (self.case_of(value) != target) return false;
        record_type = static_pool.get(target).variant_case_type.payload;
        // the payload fields of a case value as an aggregate of the payload type
        fields = blk: {
            if (value.is_heap()) break :blk .block(record_type, value.cell(), value.len());
            if (static_pool.tag(value.index()) != .variant_value) break :blk .empty;
            break :blk .of(static_pool, static_pool.get(value.index()).variant_value.payload);
        };
    }

    const arguments = tree.arg(pattern, 1);
    for (0..tree.manychildren(arguments).len) |i| {
        const argument = tree.manychildren(arguments)[i];
        const field_index = resolver.calls.field_index_of(record_type, argument, i) orelse
            return false;
        if (field_index >= (interpreter.aggregate_length(fields) orelse 0)) return false;

        const field = interpreter.element(fields, @intCast(field_index));
        if (!self.matches(tree.arg_value(argument), field)) return false;
    }
    return true;
}

inline fn matches_range(self: *Patterns, pattern: NodeId, value: Value) bool {
    const interpreter = self.owning_interpreter();
    const range = ParseTree.Range.from_node(interpreter.owning_resolver().tree, pattern);

    if (!Value.is_int(value.value_type)) return false;
    if (range.lo != 0 and Value.less(value, interpreter.evaluate(range.lo))) return false;
    if (range.hi == 0) return true;

    const end = interpreter.evaluate(range.hi);
    if (range.incl) return !Value.less(end, value);
    return Value.less(value, end);
}

// any other pattern is a value: a case without payload tests the case, the rest equality
inline fn matches_value(self: *Patterns, pattern: NodeId, value: Value) bool {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;

    const expected = interpreter.evaluate(pattern);
    const is_case = expected.is_pooled() and
        !expected.is(.none) and
        static_pool.tag(expected.index()) == .variant_case_type;
    if (is_case) return self.case_of(value) == expected.index();

    if (expected.is(.poison_type)) return false;
    // heap values are compared by their interned form
    const expected_pooled: Value = if (expected.is_heap())
        .pooled(interpreter.interned(expected))
    else
        expected;
    const value_pooled: Value = if (value.is_heap())
        .pooled(interpreter.interned(value))
    else
        value;
    return Value.eql(expected_pooled, value_pooled);
}

pub fn bind_name(self: *Patterns, id: NodeId, value: Value) void {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (interpreter.has_body_frame()) {
        return interpreter.variables.bind(interpreter.node_info(.declaration, id), value);
    }

    const name = resolver.name_pool.name_of_node(id);
    if (name == .underscore) return;

    const binder_type = interpreter.value_type(value);
    const declaration = resolver.declarations.declare_local(name, id, .pattern_binder, binder_type);
    resolver.node_declarations[id] = declaration;
    interpreter.variables.bind(declaration, value);
}

// a destructuring label binds each name to an element, missing elements to poison
pub fn bind_label(self: *Patterns, label: NodeId, value: Value) void {
    const interpreter = self.owning_interpreter();
    const tree = interpreter.owning_resolver().tree;
    if (tree.kind(label) != .partial__destructure) return self.bind_name(label, value);

    for (tree.manychildren(label), 0..) |id, i| {
        const present = i < (interpreter.aggregate_length(value) orelse 0);
        const element = if (present) interpreter.element(value, @intCast(i)) else Value.poison;
        self.bind_name(id, element);
    }
}

// a payload of one field is that field
pub fn payload_of(self: *Patterns, value: Value) ?Value {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;

    if (value.is_heap() and static_pool.tag(value.value_type) == .variant_case_type) {
        if (value.len() == 1) return interpreter.memory.buffer[value.cell()];
        const payload_type = static_pool.get(value.value_type).variant_case_type.payload;
        return .block(payload_type, value.cell(), value.len());
    }

    const is_variant_value = value.is_pooled() and
        !value.is(.none) and
        static_pool.tag(value.index()) == .variant_value;
    if (!is_variant_value) return null;

    const payload = static_pool.get(value.index()).variant_value.payload;
    if (payload == .none) return null;

    const elements = static_pool.get(payload).aggregate_value.elements;
    return .of(static_pool, if (elements.len == 1) elements[0] else payload);
}
