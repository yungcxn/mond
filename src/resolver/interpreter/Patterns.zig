const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const StaticPool = @import("../StaticPool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;

// match: arms tried in order, patterns tested against values and their binders bound
const Patterns = @This();
const none_cell = std.math.maxInt(u32);

// the cell of what the pattern being matched tests, when a label names it
matched_cell: u32 = none_cell,
// the checker declared the binders of the pattern it matches itself, typed by their place
binders_declared: bool = false,

pub fn owning_interpreter(self: *Patterns) *Interpreter {
    return @alignCast(@fieldParentPtr("patterns", self));
}

pub fn match(self: *Patterns, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;
    const scrutinee = tree.arg(node, 0);
    const arms = tree.arg(node, 1);

    // a label in a pattern names the part of the scrutinee's place it matched
    const labelled = interpreter.has_body_frame() and for (tree.manychildren(arms)) |arm| {
        if (tree.holds_label(tree.arg(arm, 0))) break true;
    } else false;
    const cell = if (labelled)
        interpreter.variables.cell_of_operand(scrutinee) orelse return .poison
    else
        none_cell;
    const evaluated = if (labelled)
        interpreter.memory.buffer[cell]
    else
        interpreter.evaluate(scrutinee);
    const scrutinee_type = if (interpreter.has_body_frame())
        interpreter.node_info(.node_type, scrutinee)
    else
        evaluated.value_type;
    const through_reference = evaluated.is_ref() and
        resolver.static_pool.through_pointer(scrutinee_type) != scrutinee_type;
    const value = if (through_reference) interpreter.dereference(evaluated) else evaluated;
    if (value.is(.poison_type) or interpreter.unwind != .none) return value;
    const outer_cell = self.matched_cell;
    defer self.matched_cell = outer_cell;
    self.matched_cell = if (labelled and through_reference) evaluated.cell() else cell;

    // a body frame already holds the binders of the arms
    const scoped = !interpreter.has_body_frame();
    if (scoped) resolver.scopes.open();
    defer if (scoped) resolver.scopes.close();

    // the checker matched a static scrutinee itself and checked only the arm it took, matching it
    // again binds its names
    if (!scoped) {
        for (tree.manychildren(arms)) |arm| {
            if (interpreter.node_info(.static_value, arm) == .bool_true) {
                _ = self.matches(tree.arg(arm, 0), value);
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
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;
    const is_case_block = value.is_heap() and
        static_pool.tag(value.value_type) == .variant_case_type;
    // a payload written where a niche is (`?<-` through a place) makes it the niche's case
    if (is_case_block) {
        const payload_type = static_pool.get(value.value_type).variant_case_type.payload;
        const payload = interpreter.interned(.block(payload_type, value.cell(), value.len()));
        const niche = static_pool.niche_case(value.value_type, payload);
        return if (niche != .none) niche else value.value_type;
    }
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
        .partial__match_case_where => {
            if (!self.matches(tree.arg(pattern, 0), value)) return false;
            const holds = interpreter.evaluate(tree.arg(pattern, 1));
            return holds.value_type == .bool_type and holds.bits != 0;
        },
        .labelarrow => {
            if (!self.matches(tree.arg(pattern, 0), value)) return false;
            if (self.matched_cell == none_cell) {
                self.bind_label(tree.arg(pattern, 1), value);
            } else {
                self.alias_label(tree.arg(pattern, 1), self.matched_cell);
            }
            return true;
        },
        .fun_call => return self.matches_fields(pattern, value),
        .partial__match_case_pattern_bits => return self.matches_bits(pattern, value),
        .gen_incl,
        .gen_excl,
        .gen_lowerbound,
        .gen_upperbound_incl,
        .gen_upperbound_excl,
        => return self.matches_range(pattern, value),
        else => return self.matches_value(pattern, value),
    }
}

// `bits(..)`: each part matches its bits from the lowest up, as its width's type
fn matches_bits(self: *Patterns, pattern: NodeId, value: Value) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;
    const static_pool = &resolver.static_pool;
    const integer = if (value.is_pooled()) Value.of(static_pool, value.index()) else value;
    var offset: u64 = 0;
    // by index: a part's pattern may evaluate a quote, which moves child lists
    const total = static_pool.get(integer.value_type).int_type.bits;
    // the bits of a part live in no cell
    const outer_cell = self.matched_cell;
    defer self.matched_cell = outer_cell;
    self.matched_cell = none_cell;
    for (0..tree.manychildren(pattern).len) |i| {
        const part = tree.manychildren(pattern)[i];
        // a pattern the checker matched itself (a static scrutinee) has no types noted
        const noted = interpreter.node_info(.node_type, part);
        const part_type = if (noted != .none)
            noted
        else if (tree.kind(part) == .partial__bits_rest)
            Index.int_of(.unsigned, @intCast(total - offset))
        else
            resolver.types.type_from_node(interpreter.function_context, tree.arg(part, 0));
        if (static_pool.tag(part_type) != .int_type) return false;
        const bits = static_pool.get(part_type).int_type.bits;
        const raw = if (offset >= 64) 0 else integer.raw_bits() >> @intCast(offset);
        offset += bits;
        const part_value = Value.int(part_type, raw);
        if (tree.kind(part) == .partial__bits_rest) {
            if (tree.arg(part, 0) != 0) self.bind_name(tree.arg(part, 0), part_value);
            continue;
        }
        if (!self.matches(tree.arg(part, 1), part_value)) return false;
    }
    return true;
}

inline fn matches_any(self: *Patterns, alternatives: NodeId, value: Value) bool {
    const tree = self.owning_interpreter().owning_resolver().tree;
    // alternatives share their names, which then are values, not places
    const outer_cell = self.matched_cell;
    defer self.matched_cell = outer_cell;
    self.matched_cell = none_cell;
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
        if (case == wanted_type or variant == wanted_type) break :blk true;
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

    // the cells of the fields, when a label may name one
    const outer_cell = self.matched_cell;
    defer self.matched_cell = outer_cell;
    const field_cells = if (outer_cell == none_cell) none_cell else blk: {
        const holder = if (static_pool.tag(target) == .variant_case_type)
            self.case_block(outer_cell)
        else
            interpreter.thaw_cell(outer_cell);
        break :blk if (holder.is_heap()) holder.cell() else none_cell;
    };
    const arguments = tree.arg(pattern, 1);
    for (0..tree.manychildren(arguments).len) |i| {
        const argument = tree.manychildren(arguments)[i];
        const field_index = resolver.calls.field_index_of(record_type, argument, i) orelse
            return false;
        if (field_index >= (interpreter.aggregate_length(fields) orelse 0)) return false;

        const field = interpreter.element(fields, @intCast(field_index));
        self.matched_cell = if (field_cells == none_cell)
            none_cell
        else
            field_cells + @as(u32, @intCast(field_index));
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
    // as `==` compares: a slice or array by its elements, in whatever form they are
    const equal = interpreter.evaluate_binary(pattern, .equal, value, expected);
    return !equal.is(.poison_type) and equal.bits != 0;
}

pub fn bind_name(self: *Patterns, id: NodeId, value: Value) void {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (interpreter.has_body_frame()) {
        return interpreter.variables.bind(interpreter.node_info(.declaration, id), value);
    }

    const name = resolver.name_pool.name_of_node(id);
    if (name == .underscore) return;

    // a label keeps the declaration the checker gave it, so does a binder the checker typed,
    // another binder of a static match gets a new one
    const labelled = resolver.node_declarations[id];
    const is_label = labelled != .none and resolver.decl_pool.get(labelled, .kind) == .arrow_binder;
    const declaration = if (self.binders_declared and labelled != .none)
        labelled
    else if (is_label) blk: {
        resolver.scopes.bind(name, labelled);
        break :blk labelled;
    } else blk: {
        const binder_type = interpreter.value_type(value);
        const declarations = &resolver.declarations;
        const declared = declarations.declare_local(name, id, .pattern_binder, binder_type);
        resolver.node_declarations[id] = declared;
        break :blk declared;
    };
    interpreter.variables.bind(declaration, value);
    // matched while checking (a static scrutinee): the name is that static value where it is used
    if (!interpreter.escapes(value)) {
        resolver.decl_pool.set(declaration, .static_value, interpreter.interned(value));
    }
}

// a label names the place in `cell`, a destructuring one each field of it
pub fn alias_label(self: *Patterns, label: NodeId, cell: u32) void {
    const interpreter = self.owning_interpreter();
    const tree = interpreter.owning_resolver().tree;
    const held = interpreter.memory.buffer[cell];
    if (!interpreter.has_body_frame()) return self.bind_label(label, held);
    const variables = &interpreter.variables;
    if (tree.kind(label) != .partial__destructure) {
        return variables.alias(interpreter.node_info(.declaration, label), cell, false);
    }
    const fields = interpreter.thaw_cell(cell);
    if (!fields.is_heap()) return;
    for (tree.manychildren(label), 0..) |name, i| {
        if (i >= fields.len()) break;
        const field_cell = fields.cell() + @as(u32, @intCast(i));
        variables.alias(interpreter.node_info(.declaration, name), field_cell, false);
    }
}

// `?<-` names the payload where the variant in `cell` holds it: a single field itself, several
// as a view of their cells
pub fn alias_payload(self: *Patterns, label: NodeId, cell: u32) void {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    if (!interpreter.has_body_frame()) {
        return self.bind_label(label, self.payload_of(interpreter.memory.buffer[cell]).?);
    }
    const case = self.case_block(cell);
    const variables = &interpreter.variables;
    if (resolver.tree.kind(label) == .partial__destructure) {
        for (resolver.tree.manychildren(label), 0..) |name, i| {
            if (i >= case.len()) break;
            const field_cell = case.cell() + @as(u32, @intCast(i));
            variables.alias(interpreter.node_info(.declaration, name), field_cell, false);
        }
        return;
    }
    const declaration = interpreter.node_info(.declaration, label);
    if (case.len() == 1) return variables.alias(declaration, case.cell(), false);
    const payload_type = resolver.static_pool.get(case.value_type).variant_case_type.payload;
    const view = interpreter.push_cell(.block(payload_type, case.cell(), case.len()));
    variables.alias(declaration, view, true);
}

// the variant in `cell` as a case block, its payload in cells of their own
fn case_block(self: *Patterns, cell: u32) Value {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;
    const held = interpreter.memory.buffer[cell];
    if (held.is_heap()) return held;
    const case_value = static_pool.get(held.index()).variant_value;
    const payload: Value = .of(static_pool, case_value.payload);
    const length = interpreter.aggregate_length(payload) orelse 0;
    const first = interpreter.allocate_cells(length);
    for (0..length) |i| {
        interpreter.memory.buffer[first + i] = interpreter.element(payload, @intCast(i));
    }
    interpreter.store_cell(cell, .block(case_value.case, first, length));
    return interpreter.memory.buffer[cell];
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
