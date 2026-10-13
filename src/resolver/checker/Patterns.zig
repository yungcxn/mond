const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const FunctionContext = Resolver.FunctionContext;
const NodeId = ParseTree.NodeId;

// match: arms, patterns and their binders, exhaustiveness and redundancy
const Patterns = @This();

pub fn owning_resolver(self: *Patterns) *Resolver {
    return @alignCast(@fieldParentPtr("patterns", self));
}

pub fn check_match(
    self: *Patterns,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const arms = resolver.tree.manychildren(resolver.tree.arg(node, 1));
    const scrutinee = resolver.tree.arg(node, 0);
    const scrutinee_type = resolver.static_pool.through_pointer(
        resolver.expressions.infer(context, scrutinee, .none),
    );
    const is_stcmatch = resolver.tree.kind(node) == .stcmatch;
    const is_stc = is_stcmatch and !context.is_interpreted and !context.is_abstract;
    for (arms) |arm| resolver.node_static_values[arm] = .none;

    const known = if (context.is_interpreted or context.is_abstract and is_stcmatch)
        resolver.static_values.try_evaluate(context, scrutinee)
    else
        null;
    // a stcmatch needs a static scrutinee, then only the matching arm is checked (as in a stcfun)
    if (is_stc or known != null) {
        const value = known orelse resolver.interpreter.evaluate_static(context, scrutinee);
        return self.check_static_match(context, node, arms, value, expected);
    }
    return self.check_arms(context, node, arms, scrutinee_type, expected);
}

fn check_static_match(
    self: *Patterns,
    context: *FunctionContext,
    node: NodeId,
    arms: []const NodeId,
    value: StaticPool.Index,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    if (value == .poison_type) return value;

    resolver.scopes.open();
    defer resolver.scopes.close();
    for (arms) |arm| {
        const arm_pattern = resolver.tree.arg(arm, 0);
        if (!resolver.interpreter.matches_static(context, arm_pattern, value)) continue;
        resolver.node_static_values[arm] = .bool_true;
        return resolver.flow.check_branch(context, resolver.tree.arg(arm, 1), expected);
    }
    return resolver.report(.non_exhaustive_match, node, value, .none);
}

fn check_arms(
    self: *Patterns,
    context: *FunctionContext,
    node: NodeId,
    arms: []const NodeId,
    scrutinee_type: StaticPool.Index,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    // errors in a template realization were reported for the template already
    var quiet = resolver.generics.is_inside_template_realization(context);
    var has_catch_all = false;
    var result: StaticPool.Index = .none;

    const initialization_mark = resolver.initialization.count;
    defer resolver.initialization.release(initialization_mark);
    const before = resolver.initialization.save(0);
    const after = resolver.initialization.new_set();
    defer resolver.initialization.copy(0, after);

    var patterns: std.ArrayList(NodeId) = .empty;
    defer patterns.deinit(resolver.allocator);
    for (arms) |arm| {
        patterns.append(resolver.allocator, resolver.tree.arg(arm, 0)) catch @panic("OOM");
    }

    // arms checked before `expected` became concrete are settled against it at the end
    var first_settled_arm = arms.len;
    for (arms, 0..) |arm, i| {
        const is_first_concrete = first_settled_arm == arms.len and
            resolver.static_pool.is_concrete(expected);
        if (is_first_concrete) first_settled_arm = i;

        resolver.initialization.copy(0, before);
        resolver.scopes.open();
        const mark = resolver.doctor.diagnostics.len();
        const takes_every_value = self.pattern(context, resolver.tree.arg(arm, 0), scrutinee_type);
        quiet = quiet or resolver.doctor.errors_since(resolver.tree, mark, arm);
        const may_be_redundant = !quiet and scrutinee_type != .poison_type;
        if (may_be_redundant and self.is_redundant(context, scrutinee_type, patterns.items, i)) {
            resolver.doctor.report(.redundant_match_arm, arm, 0, 0);
        }
        has_catch_all = has_catch_all or takes_every_value;

        const body = resolver.tree.arg(arm, 1);
        const body_type = resolver.flow.check_branch(context, body, expected);
        if (body_type != .never_type) resolver.initialization.merge(after, 0);
        resolver.scopes.close();

        // a literal body joins after the others, it takes their type
        const is_adaptable = !resolver.static_pool.is_concrete(expected) and
            resolver.tree.is_literal(body);
        const joined_type: StaticPool.Index = if (is_adaptable) .never_type else body_type;
        result = resolver.flow.merge_branch_types(arm, result, joined_type, expected);
    }

    result = self.join_literal_arms(arms, result, expected);
    self.settle_arms(arms[0..first_settled_arm], expected);

    const needs_exhaustiveness = !has_catch_all and scrutinee_type != .poison_type;
    if (needs_exhaustiveness and !self.is_exhaustive(context, scrutinee_type, patterns.items)) {
        _ = resolver.report(.non_exhaustive_match, node, scrutinee_type, .none);
    }
    return if (result == .none) .unit_type else result;
}

// the arms above already cover every value the pattern of this one takes
fn is_redundant(
    self: *Patterns,
    context: *FunctionContext,
    scrutinee_type: StaticPool.Index,
    patterns: []const NodeId,
    arm_index: usize,
) bool {
    const earlier_rows = patterns[0..arm_index];
    const this_row = patterns[arm_index..][0..1];
    return self.covers(context, &.{scrutinee_type}, earlier_rows, arm_index, this_row);
}

// the arms cover a single wildcard, so every value
fn is_exhaustive(
    self: *Patterns,
    context: *FunctionContext,
    scrutinee_type: StaticPool.Index,
    patterns: []const NodeId,
) bool {
    return self.covers(context, &.{scrutinee_type}, patterns, patterns.len, &.{0});
}

// literal bodies were left out of the join: they take the common type of the arms
fn join_literal_arms(
    self: *Patterns,
    arms: []const NodeId,
    joined_type: StaticPool.Index,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    var result = joined_type;
    const is_unjoined = result == .none or result == .never_type;
    if (!resolver.static_pool.is_concrete(expected) and is_unjoined) {
        const bodies = resolver.temporary_slice(NodeId, arms.len);
        for (arms, 0..) |arm, i| bodies[i] = resolver.tree.arg(arm, 1);
        const literal_type = resolver.flow.common_literal_type(bodies);
        if (literal_type != .none) result = literal_type;
    }

    if (resolver.static_pool.is_concrete(expected)) return result;
    for (arms) |arm| {
        const body = resolver.tree.arg(arm, 1);
        if (!resolver.tree.is_literal(body)) continue;
        const adapted_type = resolver.flow.adapt(body, resolver.node_types[body], result);
        result = resolver.flow.merge_branch_types(arm, result, adapted_type, expected);
    }
    return result;
}

fn settle_arms(self: *Patterns, arms: []const NodeId, expected: StaticPool.Index) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (!static_pool.is_concrete(expected)) return;
    for (arms) |arm| {
        const body = resolver.tree.arg(arm, 1);
        const body_type = static_pool.substitute_type_variables(resolver.node_types[body]);
        _ = resolver.flow.settle(body, body_type, expected);
    }
}

// whether the pattern takes every value of its type
fn pattern(
    self: *Patterns,
    context: *FunctionContext,
    node: NodeId,
    scrutinee_type: StaticPool.Index,
) bool {
    const resolver = self.owning_resolver();
    switch (resolver.tree.kind(node)) {
        .identifier => return self.binder_pattern(node, scrutinee_type),
        .partial__match_case_pattern_or => {
            return self.alternatives_pattern(context, node, scrutinee_type);
        },
        .partial__match_case_pattern_typecast => {
            return self.typecast_pattern(context, node, scrutinee_type);
        },
        .labelarrow => return self.labelled_pattern(context, node, scrutinee_type),
        .fun_call => return self.constructor_pattern(context, node, scrutinee_type),
        .quote => {
            resolver.macros.quote_pattern(resolver.tree.arg(node, 0));
            return false;
        },
        // literals, ranges and constant paths (`Toggle.On`): any expression
        else => return self.value_pattern(context, node, scrutinee_type),
    }
}

fn binder_pattern(self: *Patterns, node: NodeId, scrutinee_type: StaticPool.Index) bool {
    const resolver = self.owning_resolver();
    const name = resolver.name_pool.name_of_node(node);
    resolver.declarations.report_redeclaration(name, node);
    if (name != .underscore) {
        resolver.node_declarations[node] =
            resolver.declarations.declare_local(name, node, .pattern_binder, scrutinee_type);
    }
    _ = resolver.set_node_type(node, scrutinee_type);
    return true;
}

// every alternative binds the same names, sharing the declarations of the first one
fn alternatives_pattern(
    self: *Patterns,
    context: *FunctionContext,
    node: NodeId,
    scrutinee_type: StaticPool.Index,
) bool {
    const resolver = self.owning_resolver();
    const scope_names = &resolver.scopes.local_names;
    const first_start = scope_names.len;
    var first_end = first_start;
    var takes_every_value = false;
    for (resolver.tree.manychildren(node), 0..) |alternative, i| {
        if (i > 0) resolver.scopes.open();
        const alternative_start = scope_names.len;
        const alternative_takes_all = self.pattern(context, alternative, scrutinee_type);
        takes_every_value = takes_every_value or alternative_takes_all;
        if (i == 0) {
            first_end = scope_names.len;
            continue;
        }

        self.report_unbound_names(alternative, first_start, first_end, alternative_start);
        self.share_first_declarations(first_start, first_end, alternative_start);
        resolver.scopes.close();
    }
    return takes_every_value;
}

// the names of the first alternative this one does not bind
fn report_unbound_names(
    self: *Patterns,
    alternative: NodeId,
    first_start: usize,
    first_end: usize,
    alternative_start: usize,
) void {
    const resolver = self.owning_resolver();
    const scope_names = &resolver.scopes.local_names;
    const bound_here = scope_names.buffer[alternative_start..scope_names.len];
    for (scope_names.buffer[first_start..first_end]) |name| {
        if (std.mem.indexOfScalar(NamePool.Index, bound_here, name) != null) continue;
        resolver.doctor.report(.undefined_name, alternative, name, 0);
    }
}

// the binders of a later alternative take the declarations of the first one, which must agree
fn share_first_declarations(
    self: *Patterns,
    first_start: usize,
    first_end: usize,
    alternative_start: usize,
) void {
    const resolver = self.owning_resolver();
    const scopes = &resolver.scopes;
    for (alternative_start..scopes.local_names.len) |j| {
        const binder = resolver.decl_pool.get(scopes.local_declarations.buffer[j], .node);
        const name = scopes.local_names.buffer[j];
        const first_names = scopes.local_names.buffer[first_start..first_end];
        const index_in_first = std.mem.indexOfScalar(NamePool.Index, first_names, name) orelse {
            resolver.doctor.report(.undefined_name, binder, name, 0);
            continue;
        };

        const shared = scopes.local_declarations.buffer[first_start + index_in_first];
        resolver.node_declarations[binder] = shared;
        const shared_type = resolver.decl_pool.get(shared, .value_type);
        const binder_type = resolver.node_types[binder];
        const disagrees = binder_type != shared_type and binder_type != .poison_type and
            shared_type != .poison_type;
        if (disagrees) _ = resolver.report(.type_mismatch, binder, binder_type, shared_type);
    }
}

// `T x`: binds x as a T, every value when the scrutinee always is one
fn typecast_pattern(
    self: *Patterns,
    context: *FunctionContext,
    node: NodeId,
    scrutinee_type: StaticPool.Index,
) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const cast_type = resolver.types.concrete_type_from_node(context, resolver.tree.arg(node, 0));
    const binder = resolver.tree.arg(node, 1);
    const name = resolver.name_pool.name_of_node(binder);
    resolver.declarations.report_redeclaration(name, binder);
    resolver.node_declarations[binder] =
        resolver.declarations.declare_local(name, binder, .pattern_binder, cast_type);
    _ = resolver.set_node_type(binder, cast_type);

    const widens = type_pattern_widens(static_pool, scrutinee_type, cast_type);
    // a variant or trait value may hold a value of a narrower type
    const narrows = switch (static_pool.tag(scrutinee_type)) {
        .variant_type,
        .variant_union_type,
        .trait_type,
        => static_pool.coercion(cast_type, scrutinee_type) != .incompatible,
        else => false,
    };
    const fits = widens or narrows or
        resolver.generics.is_sibling_realization(context, cast_type, scrutinee_type);
    if (!fits) _ = resolver.report(.type_mismatch, node, cast_type, scrutinee_type);
    return widens;
}

// `p <- x`: x is bound to the payload of what p matches, or to all of it
fn labelled_pattern(
    self: *Patterns,
    context: *FunctionContext,
    node: NodeId,
    scrutinee_type: StaticPool.Index,
) bool {
    const resolver = self.owning_resolver();
    const inner = resolver.tree.arg(node, 0);
    const takes_every_value = self.pattern(context, inner, scrutinee_type);
    const inner_type = resolver.node_types[inner];
    const payload_type = resolver.static_pool.payload_of(inner_type);
    const bound_type = if (payload_type == .none) inner_type else payload_type;
    resolver.flow.bind_label(resolver.tree.arg(node, 1), bound_type);
    return takes_every_value;
}

// `Case(a, b)`, `Record(x = p)`: a constructor with a pattern per field
fn constructor_pattern(
    self: *Patterns,
    context: *FunctionContext,
    node: NodeId,
    scrutinee_type: StaticPool.Index,
) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const callee = resolver.tree.arg(node, 0);
    const callee_type = resolver.expressions.infer(context, callee, .none);
    const constructor_type = if (static_pool.tag(callee_type) == .meta_type)
        resolver.interpreter.evaluate_static(context, callee)
    else
        callee_type;
    const target = resolver.set_node_type(node, constructor_type);
    if (target == .poison_type) {
        // binders still exist, as poison
        for (self.argument_nodes(node)) |argument| {
            _ = self.pattern(context, resolver.tree.arg_value(argument), target);
        }
        return false;
    }

    const is_mismatch = target != scrutinee_type and
        static_pool.coercion(target, scrutinee_type) == .incompatible and
        !resolver.generics.is_sibling_realization(context, target, scrutinee_type);
    if (is_mismatch) _ = resolver.report(.type_mismatch, node, target, scrutinee_type);

    // `ast.BinaryAdd(lhs, rhs)`: the children of a root of that kind, by their fields
    if (static_pool.tag(target) == .ast_type) {
        for (self.argument_nodes(node)) |argument| {
            _ = self.pattern(context, resolver.tree.arg_value(argument), .ast_type);
        }
        return false;
    }
    return self.field_patterns(context, node, target);
}

fn argument_nodes(self: *Patterns, call: NodeId) []const NodeId {
    const tree = self.owning_resolver().tree;
    return tree.manychildren(tree.arg(call, 1));
}

// the arguments of a case or record pattern matched against the fields they bind to
fn field_patterns(
    self: *Patterns,
    context: *FunctionContext,
    node: NodeId,
    target: StaticPool.Index,
) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const is_case = static_pool.tag(target) == .variant_case_type;
    const record_type = if (is_case) static_pool.get(target).variant_case_type.payload else target;
    const arguments = self.argument_nodes(node);
    const field_of_argument = resolver.temporary_slice(u32, arguments.len);
    const binds = record_type != .none and static_pool.tag(record_type) == .record_type and
        resolver.calls.bind_arguments(
            resolver.types.field_nodes_of(record_type),
            arguments,
            field_of_argument,
            true,
        );
    if (!binds) {
        if (arguments.len > 0) _ = resolver.report(.wrong_arity, node, arguments.len, 0);
        return false;
    }

    var all_take_every_value = true;
    for (arguments, 0..) |argument, i| {
        const field_type = static_pool.field_type(record_type, field_of_argument[i]);
        const argument_type = resolver.calls.type_named_argument(argument, field_type);
        const argument_pattern = resolver.tree.arg_value(argument);
        all_take_every_value =
            self.pattern(context, argument_pattern, argument_type) and all_take_every_value;
    }
    // a case pattern leaves the other cases of the variant
    return !is_case and all_take_every_value;
}

// literals, ranges and constant paths match by value, so never every value
fn value_pattern(
    self: *Patterns,
    context: *FunctionContext,
    node: NodeId,
    scrutinee_type: StaticPool.Index,
) bool {
    const resolver = self.owning_resolver();
    const pattern_type = resolver.expressions.infer(context, node, scrutinee_type);
    if (resolver.tree.props(node).range) {
        self.check_range_pattern(node, pattern_type, scrutinee_type);
        return false;
    }

    if (!resolver.generics.is_sibling_realization(context, pattern_type, scrutinee_type)) {
        _ = resolver.expressions.expect_type(node, pattern_type, scrutinee_type);
    }
    return false;
}

// a range is an array of its elements, those must fit the scrutinee
fn check_range_pattern(
    self: *Patterns,
    node: NodeId,
    pattern_type: StaticPool.Index,
    scrutinee_type: StaticPool.Index,
) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const range_type = static_pool.substitute_type_variables(pattern_type);
    if (pattern_type == .poison_type or scrutinee_type == .poison_type) return;
    if (static_pool.get(range_type) != .array_type) return;

    const element_type = static_pool.get(range_type).array_type.element;
    if (static_pool.coercion(element_type, scrutinee_type) == .incompatible) {
        _ = resolver.report(.type_mismatch, node, element_type, scrutinee_type);
    }
}

// whether `row_count` rows of patterns over the column types cover the vector `query`
// exhaustiveness asks it for a vector of wildcards (0), redundancy for the pattern of an arm
// the first column splits by the constructors of its type, each split checks the columns after
fn covers(
    self: *Patterns,
    context: *FunctionContext,
    columns: []const StaticPool.Index,
    rows: []const NodeId,
    row_count: usize,
    query: []const NodeId,
) bool {
    const resolver = self.owning_resolver();
    if (row_count == 0) return false;
    if (columns.len == 0) return true;

    const width = columns.len;
    const column_type = columns[0];
    var queries: std.ArrayList(NodeId) = .empty;
    defer queries.deinit(resolver.allocator);
    self.spread(query, query[0], column_type, &queries);
    // a query with alternatives is covered when each of them is
    if (queries.items.len > width) {
        for (0..queries.items.len / width) |query_index| {
            const alternative = queries.items[query_index * width ..][0..width];
            if (!self.covers(context, columns, rows, row_count, alternative)) return false;
        }
        return true;
    }

    var spread_rows: std.ArrayList(NodeId) = .empty;
    defer spread_rows.deinit(resolver.allocator);
    for (0..row_count) |row_index| {
        const row = rows[row_index * width ..][0..width];
        self.spread(row, row[0], column_type, &spread_rows);
    }

    if (column_type == .bool_type) {
        return self.covers_booleans(context, columns, spread_rows.items, queries.items);
    }
    return switch (resolver.static_pool.tag(column_type)) {
        .variant_type,
        .variant_union_type,
        .record_type,
        => self.covers_constructors(context, columns, spread_rows.items, queries.items),
        .int_type => self.covers_integers(context, columns, spread_rows.items, queries.items),
        .float_type,
        .simple_type,
        .meta_type,
        .array_type,
        .pointer_type,
        .mutable_pointer_type,
        .function_type,
        .variant_case_type,
        .trait_type,
        .static_function,
        .template_type,
        .type_variable,
        .ast_type,
        .int_value,
        .float_value,
        .simple_value,
        .string_value,
        .aggregate_value,
        .variant_value,
        .function_value,
        .tree_value,
        => self.covers_by_wildcards(context, columns, spread_rows.items, queries.items),
    };
}

// a bool column splits into `true` and `false`
fn covers_booleans(
    self: *Patterns,
    context: *FunctionContext,
    columns: []const StaticPool.Index,
    rows: []const NodeId,
    query: []const NodeId,
) bool {
    const resolver = self.owning_resolver();
    const width = columns.len;
    var next_rows: std.ArrayList(NodeId) = .empty;
    defer next_rows.deinit(resolver.allocator);
    var next_query: std.ArrayList(NodeId) = .empty;
    defer next_query.deinit(resolver.allocator);
    for ([_]StaticPool.Index{ .bool_true, .bool_false }) |value| {
        next_query.clearRetainingCapacity();
        if (self.specialize(query, width, value, &.{}, &next_query) == 0) continue;

        next_rows.clearRetainingCapacity();
        const next_count = self.specialize(rows, width, value, &.{}, &next_rows);
        const rest_columns = columns[1..];
        if (!self.covers(context, rest_columns, next_rows.items, next_count, next_query.items)) {
            return false;
        }
    }
    return true;
}

// a variant column splits into its cases with their payload fields, a record into its fields
fn covers_constructors(
    self: *Patterns,
    context: *FunctionContext,
    columns: []const StaticPool.Index,
    rows: []const NodeId,
    query: []const NodeId,
) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const width = columns.len;
    const constructors = self.constructors_of(columns[0]);
    var next_rows: std.ArrayList(NodeId) = .empty;
    defer next_rows.deinit(resolver.allocator);
    var next_query: std.ArrayList(NodeId) = .empty;
    defer next_query.deinit(resolver.allocator);
    for (constructors) |constructor| {
        const record_type = if (static_pool.tag(constructor) == .variant_case_type)
            static_pool.get(constructor).variant_case_type.payload
        else
            constructor;
        const fields = if (record_type == .none)
            &[_]NodeId{}
        else
            resolver.types.field_nodes_of(record_type);
        next_query.clearRetainingCapacity();
        if (self.specialize(query, width, constructor, fields, &next_query) == 0) continue;

        const next_columns = resolver.temporary_slice(StaticPool.Index, fields.len + width - 1);
        for (0..fields.len) |i| next_columns[i] = static_pool.field_type(record_type, i);
        @memcpy(next_columns[fields.len..][0 .. width - 1], columns[1..]);
        next_rows.clearRetainingCapacity();
        const next_count = self.specialize(rows, width, constructor, fields, &next_rows);
        if (!self.covers(context, next_columns, next_rows.items, next_count, next_query.items)) {
            return false;
        }
    }
    return true;
}

// the cases of a variant or of every variant of a union, a record is its own constructor
fn constructors_of(self: *Patterns, column_type: StaticPool.Index) []StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const is_union = static_pool.tag(column_type) == .variant_union_type;
    const member_count = if (is_union) static_pool.get(column_type).variant_union_type.len else 1;

    var constructor_count: usize = 0;
    for (0..member_count) |i| {
        constructor_count += self.constructor_count_of_member(column_type, is_union, i);
    }

    const constructors = resolver.temporary_slice(StaticPool.Index, constructor_count);
    var filled: usize = 0;
    for (0..member_count) |i| {
        const member = if (is_union)
            static_pool.get(column_type).variant_union_type[i]
        else
            column_type;
        if (static_pool.tag(member) == .record_type) {
            constructors[filled] = member;
            filled += 1;
            continue;
        }
        for (static_pool.get(member).variant_type.cases) |case| {
            constructors[filled] = case;
            filled += 1;
        }
    }
    return constructors;
}

fn constructor_count_of_member(
    self: *Patterns,
    column_type: StaticPool.Index,
    is_union: bool,
    member_index: usize,
) usize {
    const static_pool = &self.owning_resolver().static_pool;
    if (is_union) {
        const member = static_pool.get(column_type).variant_union_type[member_index];
        return static_pool.get(member).variant_type.cases.len;
    }
    if (static_pool.tag(column_type) == .variant_type) {
        return static_pool.get(column_type).variant_type.cases.len;
    }
    return 1;
}

// an integer column splits into the segments between the bounds of the patterns
fn covers_integers(
    self: *Patterns,
    context: *FunctionContext,
    columns: []const StaticPool.Index,
    rows: []const NodeId,
    query: []const NodeId,
) bool {
    const resolver = self.owning_resolver();
    const width = columns.len;
    const int_type = resolver.static_pool.get(columns[0]).int_type;
    const bits: u7 = @intCast(int_type.bits);
    const one: i128 = 1;
    const is_signed = int_type.signedness == .signed;
    const min: i128 = if (is_signed) -(one << (bits - 1)) else 0;
    const max: i128 = if (is_signed) (one << (bits - 1)) - 1 else (one << bits) - 1;
    const query_pattern = query[0];
    // a query bound that is not static is never covered
    const query_bounds = if (query_pattern == 0)
        null
    else
        self.interval(context, query_pattern) orelse return false;

    var next_rows: std.ArrayList(NodeId) = .empty;
    defer next_rows.deinit(resolver.allocator);
    var cuts: std.ArrayList(i128) = .empty;
    defer cuts.deinit(resolver.allocator);
    self.collect_cuts(context, rows, width, min, query_bounds, &cuts);

    for (cuts.items, 0..) |low, cut_index| {
        const is_repeated = cut_index > 0 and cuts.items[cut_index - 1] == low;
        if (low < min or low > max or is_repeated) continue;
        const high = segment_end(cuts.items[cut_index..], low, max);
        if (query_bounds) |bounds| if (low < bounds[0] or high > bounds[1]) continue;

        next_rows.clearRetainingCapacity();
        const next_count = self.rows_covering_segment(context, rows, width, low, high, &next_rows);
        const rest_columns = columns[1..];
        if (!self.covers(context, rest_columns, next_rows.items, next_count, query[1..width])) {
            return false;
        }
    }
    return true;
}

// the segments start at the type minimum and at each bound of the query and of the rows
fn collect_cuts(
    self: *Patterns,
    context: *FunctionContext,
    rows: []const NodeId,
    width: usize,
    min: i128,
    query_bounds: ?[2]i128,
    cuts: *std.ArrayList(i128),
) void {
    const alloc = self.owning_resolver().allocator;
    cuts.append(alloc, min) catch @panic("OOM");
    if (query_bounds) |bounds| {
        cuts.appendSlice(alloc, &.{ bounds[0], bounds[1] +| 1 }) catch @panic("OOM");
    }
    for (0..rows.len / width) |row_index| {
        const row_pattern = rows[row_index * width];
        if (row_pattern == 0) continue;
        const bounds = self.interval(context, row_pattern) orelse continue;
        cuts.appendSlice(alloc, &.{ bounds[0], bounds[1] +| 1 }) catch @panic("OOM");
    }
    std.mem.sort(i128, cuts.items, {}, std.sort.asc(i128));
}

// a segment ends before the next cut above its start
fn segment_end(cuts_from_start: []const i128, low: i128, max: i128) i128 {
    for (cuts_from_start) |cut| {
        if (cut > low) return @min(cut - 1, max);
    }
    return max;
}

// the rest of the rows whose first pattern takes every value of the segment
fn rows_covering_segment(
    self: *Patterns,
    context: *FunctionContext,
    rows: []const NodeId,
    width: usize,
    low: i128,
    high: i128,
    out: *std.ArrayList(NodeId),
) usize {
    const alloc = self.owning_resolver().allocator;
    var count: usize = 0;
    for (0..rows.len / width) |row_index| {
        const row = rows[row_index * width ..][0..width];
        if (row[0] != 0) {
            const bounds = self.interval(context, row[0]) orelse continue;
            if (bounds[0] > low or bounds[1] < high) continue;
        }
        out.appendSlice(alloc, row[1..]) catch @panic("OOM");
        count += 1;
    }
    return count;
}

// any other type has no constructors to split by, only wildcards cover it
fn covers_by_wildcards(
    self: *Patterns,
    context: *FunctionContext,
    columns: []const StaticPool.Index,
    rows: []const NodeId,
    query: []const NodeId,
) bool {
    const resolver = self.owning_resolver();
    const width = columns.len;
    var next_rows: std.ArrayList(NodeId) = .empty;
    defer next_rows.deinit(resolver.allocator);
    var next_count: usize = 0;
    for (0..rows.len / width) |row_index| {
        const row = rows[row_index * width ..][0..width];
        if (row[0] != 0) continue;
        next_rows.appendSlice(resolver.allocator, row[1..]) catch @panic("OOM");
        next_count += 1;
    }
    return self.covers(context, columns[1..], next_rows.items, next_count, query[1..width]);
}

// a row with its first pattern normalized: binders and widening type patterns are wildcards,
// alternatives are rows of their own
fn spread(
    self: *Patterns,
    row: []const NodeId,
    first: NodeId,
    column_type: StaticPool.Index,
    out: *std.ArrayList(NodeId),
) void {
    const resolver = self.owning_resolver();
    var normalized = first;
    while (normalized != 0) switch (resolver.tree.kind(normalized)) {
        .capture, .labelarrow => normalized = resolver.tree.arg(normalized, 0),
        .identifier => normalized = 0,
        .partial__match_case_pattern_or => {
            for (resolver.tree.manychildren(normalized)) |alternative| {
                self.spread(row, alternative, column_type, out);
            }
            return;
        },
        .partial__match_case_pattern_typecast => {
            const cast_type = resolver.node_types[resolver.tree.arg(normalized, 1)];
            if (!type_pattern_widens(&resolver.static_pool, column_type, cast_type)) break;
            normalized = 0;
        },
        else => break,
    };
    out.append(resolver.allocator, normalized) catch @panic("OOM");
    out.appendSlice(resolver.allocator, row[1..]) catch @panic("OOM");
}

// the rows of a constructor (a case, a record or a bool), the first column replaced by the
// patterns of its fields
fn specialize(
    self: *Patterns,
    rows: []const NodeId,
    width: usize,
    constructor: StaticPool.Index,
    fields: []const NodeId,
    out: *std.ArrayList(NodeId),
) usize {
    const alloc = self.owning_resolver().allocator;
    var count: usize = 0;
    for (0..rows.len / width) |row_index| {
        const row = rows[row_index * width ..][0..width];
        if (!self.is_of_constructor(row[0], constructor)) continue;
        self.append_field_patterns(row[0], fields, out);
        out.appendSlice(alloc, row[1..]) catch @panic("OOM");
        count += 1;
    }
    return count;
}

fn is_of_constructor(self: *Patterns, row_pattern: NodeId, constructor: StaticPool.Index) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (row_pattern == 0) return true;

    const is_typecast = resolver.tree.kind(row_pattern) == .partial__match_case_pattern_typecast;
    const pattern_type = if (is_typecast)
        resolver.node_types[resolver.tree.arg(row_pattern, 1)]
    else
        resolver.node_types[row_pattern];
    return switch (static_pool.tag(constructor)) {
        .variant_case_type => {
            const variant = static_pool.get(constructor).variant_case_type.variant;
            return pattern_type == variant or self.same(pattern_type, constructor);
        },
        .record_type => self.same(pattern_type, constructor),
        else => {
            const boolean_kind: ParseTree.Node.Kind =
                if (constructor == .bool_true) .boolean_true else .boolean_false;
            return resolver.tree.kind(row_pattern) == boolean_kind;
        },
    };
}

// the patterns a constructor pattern gives its fields, by name or position, wildcards for the rest
fn append_field_patterns(
    self: *Patterns,
    row_pattern: NodeId,
    fields: []const NodeId,
    out: *std.ArrayList(NodeId),
) void {
    const resolver = self.owning_resolver();
    const at = out.items.len;
    out.appendNTimes(resolver.allocator, 0, fields.len) catch @panic("OOM");
    const is_call = row_pattern != 0 and resolver.tree.kind(row_pattern) == .fun_call;
    const arguments = if (is_call) self.argument_nodes(row_pattern) else &[_]NodeId{};
    const field_of_argument = resolver.temporary_slice(u32, arguments.len);
    if (!resolver.calls.bind_arguments(fields, arguments, field_of_argument, true)) return;
    for (arguments, 0..) |argument, i| {
        out.items[at + field_of_argument[i]] = resolver.tree.arg_value(argument);
    }
}

// a constructor of another realization of the same template stands for this one
fn same(self: *Patterns, pattern_type: StaticPool.Index, constructor: StaticPool.Index) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (pattern_type == constructor) return true;
    if (pattern_type == .none) return false;
    if (static_pool.tag(pattern_type) != static_pool.tag(constructor)) return false;

    const template = resolver.generics.template_source_of(pattern_type);
    if (template == .none) return false;
    if (template != resolver.generics.template_source_of(constructor)) return false;
    if (static_pool.tag(pattern_type) != .variant_case_type) return true;
    const pattern_case = static_pool.get(pattern_type).variant_case_type.case_index;
    return pattern_case == static_pool.get(constructor).variant_case_type.case_index;
}

// the integer values a literal or range pattern covers, as a closed interval
fn interval(self: *Patterns, context: *FunctionContext, node: NodeId) ?[2]i128 {
    const resolver = self.owning_resolver();
    const static_values = &resolver.static_values;
    if (!resolver.tree.props(node).range) {
        const value = static_values.static_integer(context, node) orelse return null;
        return .{ value, value };
    }

    const range = ParseTree.Range.from_node(resolver.tree, node);
    const low = if (range.lo == 0)
        std.math.minInt(i128)
    else
        static_values.static_integer(context, range.lo) orelse return null;
    if (range.hi == 0) return .{ low, std.math.maxInt(i128) };
    const high = static_values.static_integer(context, range.hi) orelse return null;
    return .{ low, high - @intFromBool(!range.incl) };
}

// `T x` matches every value (it binds like a name) when the scrutinee coerces to `T`.
// poison on either side matches too, its error is reported already
fn type_pattern_widens(
    static_pool: *StaticPool,
    scrutinee_type: StaticPool.Index,
    cast_type: StaticPool.Index,
) bool {
    if (cast_type == scrutinee_type) return true;
    if (cast_type == .poison_type or scrutinee_type == .poison_type) return true;
    return static_pool.coercion(scrutinee_type, cast_type) != .incompatible;
}
