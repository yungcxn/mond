const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const NamePool = @import("../NamePool.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const FunctionContext = Resolver.FunctionContext;
const Declarations = @import("Declarations.zig");
const NodeId = ParseTree.NodeId;
const constructs = @import("../../language/constructs.zig");
const operators = @import("../../language/operators.zig");

// expressions: the walk over a body, every node gets its type here or in the module of its kind
const Expressions = @This();

// the dereference an index reads through: `p.*[i]` reads one element of what `p` points to
indexed_dereference: NodeId = 0,
open_lengths: std.ArrayList(struct { node: NodeId, array_type: StaticPool.Index }) = .empty,

pub fn owning_resolver(self: *Expressions) *Resolver {
    return @alignCast(@fieldParentPtr("expressions", self));
}

// the type of a node, `expected` only guides it (literals, empty arrays, lambdas)
pub fn infer(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;

    const stc_is_redundant = context.is_interpreted and
        tree.props(node).stc and
        !resolver.doctor.has_report_at(node);
    if (stc_is_redundant) _ = resolver.report(.redundant_stc, node, 0, 0);

    const node_type: StaticPool.Index = switch (constructs.construct_of(tree.kind(node))) {
        .literal => resolver.static_values.literal_type(node, expected),
        .name => self.infer_name(node, expected),
        .grouping => self.infer(context, tree.arg(node, 0), expected),
        .block => self.infer_block(context, node, expected),
        .declaration => resolver.declarations.check_statement(context, node),
        .compound_assignment => self.infer_compound_assignment(context, node),
        .increment => self.infer_increment(context, node),
        .arithmetic => self.infer_arithmetic(context, node, expected),
        .comparison => self.infer_comparison(context, node),
        .short_circuit_logic => self.infer_short_circuit_logic(context, node),
        .logical_xor => self.infer_logical_xor(context, node),
        .logical_not => self.infer_logical_not(context, node, expected),
        .numeric_negation => self.infer_numeric_negation(context, node, expected),
        .call, .record_update => resolver.calls.check_call(context, node),
        .member_access => self.infer_member_access(context, node),
        .index => self.infer_index(context, node),
        .dereference => self.infer_dereference(context, node),
        .address_of => self.infer_address_of(context, node, expected),
        .array_literal => self.infer_array_literal(context, node, expected),
        .cast => self.infer_cast(context, node),
        .bit_cast => self.infer_bit_cast(context, node),
        .type_test => self.infer_type_test(context, node),
        .type_of => self.infer_static_query(context, node, .type_type),
        .size_of => self.infer_static_query(context, node, .u64_type),
        .length_or_tag => self.infer_length_or_tag(context, node),
        .branch => resolver.flow.check_if(context, node, expected),
        .loop => resolver.flow.check_loop(context, node, expected),
        .range => self.infer_range(context, node, expected),
        .match => resolver.patterns.check_match(context, node, expected),
        .return_value => self.infer_return_value(context, node),
        .return_void => self.infer_return_void(context, node),
        .loop_jump => resolver.flow.check_jump(context, node, tree.kind(node)),
        .do => self.infer_discarded(context, node, .runit_type),
        .@"defer" => self.infer_discarded(context, node, .unit_type),
        .deinit => self.infer_deinit(context, node),
        .deferred_deinit => self.infer_deinit_operand(context, node, expected),
        .unwrap => resolver.flow.check_unwrap(context, node, expected),
        .macro => resolver.macros.infer(context, node, expected),
        .lambda => self.infer_lambda(node, expected),
        .type_expression, .type_definition => self.infer_type_value(context, node),
        .part => .unit_type,
    };
    return resolver.set_node_type(node, node_type);
}

fn infer_name(self: *Expressions, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const resolver = self.owning_resolver();

    const named = resolver.declarations.use_name(node);
    const declaration = resolver.calls.overload_for(node, named, expected);
    if (declaration == .none) return .poison_type;

    if (resolver.initialization.is_unwritten(declaration)) {
        const name = resolver.decl_pool.get(declaration, .name);
        resolver.doctor.report(.use_before_initialization, node, name, 0);
    }

    const value_type = resolver.decl_pool.get(declaration, .value_type);
    if (value_type == .none) return .poison_type;
    return value_type;
}

fn infer_block(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();

    resolver.scopes.open();
    defer resolver.scopes.close();

    const statements = resolver.tree.manychildren(node);
    // local functions are visible in their whole block
    for (statements) |statement_node| {
        const statement = Declarations.Stmt.from_node(resolver, statement_node);
        const is_typed_function = statement.kind == .function and
            statement.assignees.len == 1 and
            statement.type != 0 and
            resolver.tree.kind(statement.type) == .type_fun;
        if (!is_typed_function) continue;

        const name_node = statement.assignees[0];
        const name = resolver.name_pool.name_of_node(name_node);
        if (resolver.scopes.in_innermost_scope(name) != .none) continue;

        const declaration = resolver.declarations.declare_local(
            name,
            statement.node,
            .function,
            .none,
        );
        resolver.decl_pool.set(declaration, .flags, statement.flags);
        resolver.node_declarations[name_node] = declaration;
    }

    var last_type: StaticPool.Index = .unit_type;
    for (statements, 0..) |statement, i| {
        const is_last = i + 1 == statements.len;
        const declares = resolver.tree.props(statement).declares;

        if (!declares) resolver.scopes.open();
        last_type = self.infer(context, statement, if (is_last) expected else .none);
        if (!declares) resolver.scopes.close();
    }
    return last_type;
}

fn infer_compound_assignment(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const kind = resolver.tree.kind(node);
    const target = resolver.tree.arg(node, 0);
    const value = resolver.tree.arg(node, 1);

    const target_type = resolver.mutability.check_assignable(context, target);

    const appends_to_list = kind == .assign_add and
        resolver.tree.macros and
        resolver.macros.checks_list_append(context, target_type, value);
    if (appends_to_list) return .unit_type;

    const moves_pointer = (kind == .assign_add or kind == .assign_sub) and
        static_pool.is_element_pointer(target_type);
    if (moves_pointer) {
        const negative = resolver.tree.kind(value) == .neg_num;
        const integer_hint: StaticPool.Index = if (negative) .i64_type else .u64_type;
        const operand_type = self.infer_operand(context, value, integer_hint);
        if (operand_type == .poison_type) return .unit_type;
        if (static_pool.properties(operand_type).is_integer) return .unit_type;

        _ = resolver.report(.type_mismatch, value, operand_type, .u64_type);
        return .poison_type;
    }

    _ = self.check(context, value, target_type);
    const integral_mismatch = operators.assigned_operands_of(kind) == .integers and
        !static_pool.properties(target_type).is_integer and
        static_pool.tag(target_type) != .type_variable;
    if (integral_mismatch) return resolver.report_mismatch(node, target_type, .none);
    return self.numeric_result(node, target_type, .unit_type);
}

fn infer_increment(self: *Expressions, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();

    const target_type = resolver.mutability.check_assignable(context, resolver.tree.arg(node, 0));
    if (resolver.static_pool.is_element_pointer(target_type)) return target_type;
    return self.numeric_result(node, target_type, target_type);
}

fn infer_arithmetic(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const left = resolver.tree.arg(node, 0);
    const right = resolver.tree.arg(node, 1);

    const hint: StaticPool.Index = if (resolver.static_pool.is_numeric(expected))
        expected
    else
        .none;
    const operand_type = self.join_operands(context, node, left, right, hint);
    const result_type = blk: {
        const static_pool = &resolver.static_pool;
        const kind = resolver.tree.kind(node);

        const offsets_pointer = (kind == .binary_add or kind == .binary_sub) and
            static_pool.is_element_pointer(operand_type);
        if (offsets_pointer) break :blk operand_type;

        const integral = operators.operands_of(kind) == .integers;
        const integral_mismatch = integral and
            !static_pool.properties(operand_type).is_integer and
            static_pool.tag(operand_type) != .type_variable;
        if (integral_mismatch) break :blk resolver.report_mismatch(node, operand_type, .none);

        break :blk self.numeric_result(node, operand_type, operand_type);
    };

    // arithmetic on constants is folded, a division by zero is an error as soon as it can be seen
    const tree = resolver.tree;
    const foldable = result_type != .poison_type and
        !context.is_abstract and
        (tree.is_literal(left) or resolver.node_static_values[left] != .none and
            constructs.construct_of(tree.kind(left)) == .arithmetic) and
        (tree.is_literal(right) or resolver.node_static_values[right] != .none and
            constructs.construct_of(tree.kind(right)) == .arithmetic);
    if (foldable) {
        _ = resolver.set_node_type(node, result_type);
        _ = resolver.interpreter.evaluate_static(context, node);
    }
    return result_type;
}

fn infer_comparison(self: *Expressions, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const left = resolver.tree.arg(node, 0);
    const right = resolver.tree.arg(node, 1);

    const operand_type = self.join_operands(context, node, left, right, .none);
    if (operand_type == .poison_type) return operand_type;
    // arrays compare element by element, as far as a static length reaches
    const compared = resolver.static_pool.substitute_type_variables(operand_type);
    if (!self.length_is_static(context, compared, node)) {
        return resolver.report(.not_static, node, 0, 0);
    }
    return .bool_type;
}

fn infer_short_circuit_logic(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const initialization = &resolver.initialization;

    const mark = initialization.count;
    defer initialization.release(mark);

    const unwritten_when = resolver.flow.check_condition(context, node);
    initialization.copy(0, unwritten_when[0]);
    initialization.merge(0, unwritten_when[1]);
    return .bool_type;
}

fn infer_logical_xor(self: *Expressions, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();

    _ = self.check(context, resolver.tree.arg(node, 0), .bool_type);
    _ = self.check(context, resolver.tree.arg(node, 1), .bool_type);
    return .bool_type;
}

// `!` is logical on bools and bitwise on integers
fn infer_logical_not(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();

    const operand_type = self.infer(context, resolver.tree.arg(node, 0), expected);
    const is_integer = resolver.static_pool.properties(operand_type).is_integer;
    if (operand_type == .bool_type or is_integer) return operand_type;
    return resolver.report_mismatch(node, operand_type, .bool_type);
}

fn infer_numeric_negation(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    if (resolver.tree.is_literal(node)) return resolver.static_values.literal_type(node, expected);

    const operand_type = self.infer(context, resolver.tree.arg(node, 0), expected);
    return self.numeric_result(node, operand_type, .none);
}

fn infer_index(self: *Expressions, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const indexed = resolver.tree.arg(node, 0);
    const index = resolver.tree.arg(node, 1);

    if (resolver.tree.kind(indexed) == .dereference) self.indexed_dereference = indexed;
    const indexed_type = static_pool.substitute_type_variables(self.infer(context, indexed, .none));
    if (resolver.tree.props(index).range) {
        // checked anyway, so the names in the bounds are resolved and their errors reported
        _ = self.infer(context, index, .none);
        return resolver.report(.genexpr_index, index, 0, 0);
    }

    const index_type = self.infer(context, index, .none);
    if (!static_pool.properties(index_type).is_integer) {
        _ = resolver.report_mismatch(index, index_type, .u64_type);
    }
    if (indexed_type == .poison_type) return indexed_type;

    // pointers index like arrays (`*u8 buf; buf[i]`), arrays auto-deref once
    const through_pointer = static_pool.is_pointer(indexed_type);
    const container_type = static_pool.pointee(indexed_type);
    if (through_pointer and static_pool.is_unstorable(container_type) and !context.is_abstract) {
        return resolver.report(.unstorable_dereference, indexed, indexed_type, 0);
    }
    const is_array = static_pool.get(container_type) == .array_type;
    if (!is_array and !through_pointer) {
        return resolver.report(.type_mismatch, indexed, container_type, .none);
    }
    const element_type = if (is_array)
        static_pool.get(container_type).array_type.element
    else
        container_type;

    // realizations and stcfun bodies leave lengths to the interpreter, their indices may be guarded
    const checks_static_bounds = blk: {
        if (context.is_interpreted) break :blk false;

        const in_realization = context.declaration != .none and
            resolver.generics.template_of.contains(context.declaration);
        if (in_realization) break :blk false;

        const has_static_length = static_pool.static_length(container_type) != null;
        break :blk has_static_length and resolver.tree.is_literal(index);
    };
    if (checks_static_bounds) {
        const static_index = resolver.static_values.static_integer(context, index) orelse
            return element_type;
        const length = static_pool.static_length(container_type).?;
        if (static_index < 0 or static_index >= length) {
            _ = resolver.report(.static_eval_failed, index, 0, 0);
        }
    }
    return element_type;
}

fn infer_dereference(self: *Expressions, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const indexed = self.indexed_dereference == node;
    self.indexed_dereference = 0;
    const operand_type = self.infer(context, resolver.tree.arg(node, 0), .none);
    const pointer_type = static_pool.substitute_type_variables(operand_type);
    if (!static_pool.is_pointer(pointer_type)) {
        return resolver.report_mismatch(node, pointer_type, .none);
    }
    const pointee = static_pool.pointee(pointer_type);
    const reads_element = indexed and static_pool.tag(pointee) == .array_type;
    if (static_pool.is_unstorable(pointee) and !reads_element and !context.is_abstract) {
        return resolver.report(.unstorable_dereference, node, pointer_type, 0);
    }
    return pointee;
}

fn infer_address_of(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const target = resolver.tree.arg(node, 0);

    if (resolver.tree.kind(target) == .identifier) {
        const name = resolver.name_pool.name_of_node(target);
        resolver.initialization.mark_written(resolver.scopes.lookup(&resolver.decl_pool, name));
    }

    const expected_pointer = static_pool.substitute_type_variables(expected);
    const pointee_hint: StaticPool.Index = if (static_pool.is_pointer(expected_pointer))
        static_pool.pointee(expected_pointer)
    else
        .none;
    const target_type = self.infer(context, target, pointee_hint);

    // write access only to what could be written directly
    const mutable = resolver.mutability.writable(target) == .ok;
    const wants_mutable = expected_pointer != .none and
        static_pool.tag(expected_pointer) == .mutable_pointer_type;
    if (mutable and wants_mutable) resolver.mutability.mark_written_through(target);

    if (target_type == .poison_type) return target_type;
    return static_pool.pointer_to(target_type, mutable);
}

// with no expected type elements join, literals last: `[1, -2]` [2]i32, `[x, 300]` (x: u8) [2]u32
fn infer_array_literal(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const expected_array = static_pool.substitute_type_variables(expected);
    var element_type = static_pool.array_element(expected_array);
    const element_type_given = element_type != .none;
    const elements = if (resolver.tree.kind(node) == .array)
        resolver.tree.manychildren(node)
    else
        &[_]NodeId{};

    for (elements) |element| {
        if (!element_type_given and resolver.tree.is_literal(element)) continue;

        const actual_type = self.infer(context, element, element_type);
        if (element_type == .none) {
            element_type = actual_type;
            continue;
        }
        if (!element_type_given) {
            const joined = static_pool.join(element_type, actual_type).joined_type;
            if (joined != .none) {
                element_type = joined;
                continue;
            }
        }
        _ = self.expect_type(element, actual_type, element_type);
    }

    if (!element_type_given) {
        const tree = resolver.tree;
        for (elements) |element| {
            if (tree.is_literal(element)) _ = self.infer(context, element, .none);
        }

        if (element_type == .none) element_type = resolver.flow.common_literal_type(elements);
        if (element_type == .none and elements.len > 0) {
            element_type = resolver.node_types[elements[0]];
        }

        for (elements) |element| {
            if (!tree.is_literal(element) or element_type == .none) continue;

            const literal_type = resolver.static_values.literal_type(element, element_type);
            const joined = static_pool.join(element_type, literal_type).joined_type;
            if (joined != .none) element_type = joined;
        }

        for (elements) |element| {
            if (!tree.is_literal(element)) continue;
            _ = self.expect_type(element, resolver.node_types[element], element_type);
        }
    }
    if (element_type == .none) element_type = static_pool.fresh_type_variable(node);
    return static_pool.array_of(elements.len, element_type);
}

fn infer_cast(self: *Expressions, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const operand_type = self.infer(context, resolver.tree.arg(node, 0), .none);
    const source_type = static_pool.substitute_type_variables(operand_type);
    const target_node = resolver.tree.arg(node, 1);
    const target_type = resolver.types.cast_target(context, target_node, source_type);

    if (target_type == .poison_type or source_type == .poison_type) return .poison_type;
    // `[n]T` or `*[n]T` whose length failed, that failure is reported already
    const has_poisoned_length = blk: {
        const key = static_pool.get(target_type);
        if (key == .array_type) break :blk key.array_type.length == .poison_type;
        if (key != .pointer_type) break :blk false;

        const pointee = static_pool.get(key.pointer_type.pointee);
        break :blk pointee == .array_type and pointee.array_type.length == .poison_type;
    };
    if (has_poisoned_length) return .poison_type;

    if (static_pool.cast_kind(source_type, target_type) == .invalid) {
        return resolver.report(.invalid_cast, node, source_type, target_type);
    }
    return target_type;
}

fn infer_bit_cast(self: *Expressions, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const operand_type = self.infer(context, resolver.tree.arg(node, 0), .none);
    const source_type = static_pool.substitute_type_variables(operand_type);
    const target_type = resolver.types.type_from_node(context, resolver.tree.arg(node, 1));
    if (source_type == .poison_type or target_type == .poison_type) return .poison_type;

    const both_have_layout = static_pool.properties(source_type).has_layout and
        static_pool.properties(target_type).has_layout;
    if (!both_have_layout or
        static_pool.layout(target_type).size < static_pool.layout(source_type).size)
    {
        return resolver.report(.invalid_cast, node, source_type, target_type);
    }
    return target_type;
}

fn infer_type_test(self: *Expressions, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const type_node = resolver.tree.arg(node, 1);

    const operand_type = self.infer(context, resolver.tree.arg(node, 0), .none);
    const value_type = static_pool.through_pointer(operand_type);

    // the root of a tree is known once it is evaluated
    if (resolver.tree.macros and static_pool.is_tree(value_type)) {
        resolver.node_static_values[type_node] = resolver.types.type_from_node(context, type_node);
        return .bool_type;
    }

    const evaluated = if (context.is_interpreted)
        resolver.static_values.evaluate_or_defer(context, type_node) orelse .none
    else
        resolver.types.type_from_node(context, type_node);
    const names_stcfun = evaluated != .none and static_pool.tag(evaluated) == .static_function;
    const tested_type = if (names_stcfun)
        resolver.types.type_from_node(context, type_node)
    else
        evaluated;
    resolver.node_static_values[type_node] = tested_type;

    // the static answer of a type test, `.none` when only the runtime knows it
    resolver.node_static_values[node] = blk: {
        if (tested_type == .none) break :blk .none;
        if (context.is_interpreted and static_pool.tag(value_type) == .meta_type) break :blk .none;

        if (static_pool.template_of(tested_type) != .none) {
            if (resolver.generics.realizes(value_type, tested_type)) break :blk .bool_true;
            break :blk .bool_false;
        }
        if (static_pool.template_of(value_type) != .none) break :blk .none;

        const matches = value_type == tested_type or
            static_pool.implements(value_type, tested_type);
        if (matches) break :blk .bool_true;
        if (static_pool.tag(value_type) == .trait_type) break :blk .none;
        break :blk .bool_false;
    };
    return .bool_type;
}

// `typeof`, `sizeof` and `alignof`: questions about the operand answered at compile time
fn infer_static_query(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    result_type: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const operand = resolver.tree.arg(node, 0);

    _ = self.infer(context, operand, .none);

    const names_template = resolver.tree.kind(operand) == .identifier and
        resolver.generics.is_template(resolver.node_declarations[operand]);
    if (names_template) return resolver.report(.unrealized_template, operand, 0, 0);

    _ = resolver.static_values.try_evaluate(context, node);
    return result_type;
}

// ranges are sequences of their bound type, so `for` and slicing treat them like arrays
fn infer_range(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const first_bound = resolver.tree.arg(node, 0);
    const second_bound = resolver.tree.arg(node, 1);

    const expected_type = static_pool.substitute_type_variables(expected);
    const range = ParseTree.Range.from_node(resolver.tree, node);
    const hint = blk: {
        const expected_element = static_pool.array_element(expected_type);
        const expected_bound_type: StaticPool.Index = if (expected_element != .none)
            expected_element
        else if (static_pool.is_numeric(expected_type))
            expected_type
        else
            .none;
        if (expected_bound_type == .none) break :blk .none;

        for ([_]NodeId{ range.lo, range.hi }) |bound| {
            if (bound == 0 or !resolver.tree.is_literal(bound)) continue;
            const literal_type = resolver.static_values.literal_type(bound, expected_bound_type);
            if (literal_type != expected_bound_type) break :blk .none;
        }
        break :blk expected_bound_type;
    };

    const bound_type = if (range.lo != 0 and range.hi != 0)
        self.join_operands(context, node, first_bound, second_bound, hint)
    else
        self.infer_operand(context, first_bound, hint);
    if (!static_pool.properties(bound_type).is_integer) {
        return resolver.report_mismatch(node, bound_type, .u64_type);
    }

    const length = static_pool.fresh_type_variable(node);
    return static_pool.intern(.{ .array_type = .{ .length = length, .element = bound_type } });
}

fn infer_return_value(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
) StaticPool.Index {
    const value = self.owning_resolver().tree.arg(node, 0);

    if (context.return_type == .none) {
        _ = self.infer(context, value, .none);
    } else {
        _ = self.check(context, value, context.return_type);
    }
    self.reject_escape(context, value);
    return .never_type;
}

fn infer_return_void(self: *Expressions, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    if (context.return_type == .none) return .never_type;

    const coercion = resolver.static_pool.coercion(.unit_type, context.return_type);
    if (coercion == .incompatible) {
        return resolver.report(.ret_type_mismatch, node, .unit_type, context.return_type);
    }
    return .never_type;
}

fn infer_discarded(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    result_type: StaticPool.Index,
) StaticPool.Index {
    _ = self.infer(context, self.owning_resolver().tree.arg(node, 0), .none);
    return result_type;
}

fn infer_deinit(self: *Expressions, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();
    const operand = resolver.tree.arg(node, 0);

    _ = self.infer_deinit_operand(context, node, .none);
    if (resolver.tree.kind(operand) != .identifier) return .unit_type;

    // a deinitialized local has to be written again before it is read
    const declaration = resolver.node_declarations[operand];
    if (declaration == .none) return .unit_type;
    if (resolver.decl_pool.get(declaration, .flags).is_global) return .unit_type;

    if (resolver.initialization.bit_of(declaration)) |bit| {
        resolver.initialization.put(0, bit, true);
    } else {
        resolver.initialization.track(declaration);
    }
    return .unit_type;
}

fn infer_deinit_operand(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const operand_type = self.infer(context, resolver.tree.arg(node, 0), expected);
    const deinit_type = static_pool.substitute_type_variables(operand_type);
    const lacks_deinit = deinit_type != .poison_type and
        static_pool.lookup_member(deinit_type, .deinit) == .none;
    if (lacks_deinit) resolver.doctor.report(.no_deinit, node, deinit_type, 0);
    return operand_type;
}

// lambdas and local functions are checked on the spot and see the enclosing locals
fn infer_lambda(self: *Expressions, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const declaration = resolver.decl_pool.push(.empty, node, .function, .none, .{});
    resolver.node_declarations[node] = declaration;
    resolver.declarations.ensure_signature(declaration);

    const expected_type = static_pool.substitute_type_variables(expected);
    const lambda_type = resolver.decl_pool.get(declaration, .value_type);
    // an expected function type with equal parameters settles a return type the lambda leaves open
    const takes_expected_return_type = blk: {
        if (expected_type == .none or static_pool.tag(expected_type) != .function_type) {
            break :blk false;
        }
        if (lambda_type == .none or static_pool.tag(lambda_type) != .function_type) {
            break :blk false;
        }

        const lambda_function = static_pool.get(lambda_type).function_type;
        const expected_function = static_pool.get(expected_type).function_type;
        const same_parameters = std.mem.eql(
            StaticPool.Index,
            lambda_function.parameters,
            expected_function.parameters,
        );
        if (!same_parameters) break :blk false;

        const lambda_return = static_pool.substitute_type_variables(lambda_function.return_type);
        break :blk static_pool.tag(lambda_return) == .type_variable;
    };
    if (takes_expected_return_type) {
        _ = static_pool.unify(
            static_pool.get(lambda_type).function_type.return_type,
            static_pool.get(expected_type).function_type.return_type,
        );
    }

    resolver.declarations.check_body(declaration);
    return resolver.decl_pool.get(declaration, .value_type);
}

// type expressions in value position: the value is a type
fn infer_type_value(self: *Expressions, context: *FunctionContext, node: NodeId) StaticPool.Index {
    const resolver = self.owning_resolver();

    if (resolver.static_values.evaluate_or_defer(context, node)) |type_value| {
        return resolver.static_pool.type_of(type_value);
    }
    return resolver.types.meta_type_of_node(node);
}

// a closure's environment lives in the frame that made it, so a value that may hold one stays
// below that frame: called and passed down, never returned, stored outside the frame or handed to
// c. a stcfun runs at compile time, its closures may go anywhere
pub fn reject_escape(self: *Expressions, context: *FunctionContext, node: NodeId) void {
    if (context.is_interpreted or !self.may_capture(node)) return;
    self.owning_resolver().doctor.report(.escaping_closure, node, 0, 0);
}

// whether a value may hold a closure: a lambda or local function using locals of a running frame,
// what is made of one, or a runtime variable or parameter that holds function values
pub fn may_capture(self: *Expressions, node: NodeId) bool {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;
    const static_pool = &resolver.static_pool;
    const decl_pool = &resolver.decl_pool;
    if (node == 0) return false;
    // a function named or written here is static only without captures
    const construct = constructs.construct_of(tree.kind(node));
    const names_function = construct == .lambda or construct == .name;
    if (!names_function and resolver.node_static_values[node] != .none) return false;
    const value_type = static_pool.substitute_type_variables(resolver.node_types[node]);
    if (construct != .branch and !static_pool.holds_function_value(value_type)) return false;
    return switch (construct) {
        .grouping, .branch, .array_literal, .record_update, .unwrap => {
            for (tree.children(node)) |child| if (self.may_capture(child)) return true;
            return false;
        },
        .block => tree.manychildren(node).len > 0 and
            self.may_capture(tree.manychildren(node)[tree.manychildren(node).len - 1]),
        .match => {
            for (tree.manychildren(tree.arg(node, 1))) |arm| {
                if (self.may_capture(tree.arg(arm, 1))) return true;
            }
            return false;
        },
        // a record or case made of its arguments, any other call returns nothing of its frame
        .call => {
            const callee_type = resolver.node_types[tree.arg(node, 0)];
            if (static_pool.tag(callee_type) != .meta_type) return false;
            for (tree.manychildren(tree.arg(node, 1))) |argument| {
                if (self.may_capture(tree.arg_value(argument))) return true;
            }
            return false;
        },
        .member_access, .index => {
            const base = tree.arg(node, 0);
            return static_pool.is_pointer(resolver.node_types[base]) or self.may_capture(base);
        },
        .lambda => resolver.bodies.captures_of(decl_pool, resolver.node_declarations[node]).len > 0,
        .name => {
            const declaration = resolver.node_declarations[node];
            if (declaration == .none or decl_pool.get(declaration, .flags).is_global) return false;
            if (decl_pool.get(declaration, .kind).is_function()) {
                return resolver.bodies.captures_of(decl_pool, declaration).len > 0;
            }
            return resolver.node_static_values[node] == .none and
                decl_pool.get(declaration, .static_value) == .none;
        },
        .dereference => true,
        else => false,
    };
}

// a place outside the frame: a global, or memory reached through a pointer
pub fn is_outside_frame(self: *Expressions, place: NodeId) bool {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;
    var node = place;
    while (true) switch (tree.kind(node)) {
        .capture => node = tree.arg(node, 0),
        .member, .array_index => {
            const base = tree.arg(node, 0);
            if (resolver.static_pool.is_pointer(resolver.node_types[base])) return true;
            node = base;
        },
        .identifier, .identifier_self => {
            const declaration = resolver.node_declarations[node];
            return declaration != .none and resolver.decl_pool.get(declaration, .flags).is_global;
        },
        else => return true,
    };
}

pub fn expect_type(
    self: *Expressions,
    node: NodeId,
    actual: StaticPool.Index,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    // a poisoned value settles what it was expected to infer, so the error does not spread
    const settles_expected = actual == .poison_type and
        expected != .none and
        static_pool.has_type_variables(expected);
    if (settles_expected) _ = static_pool.unify(expected, .poison_type);

    if (expected == .none or actual == .poison_type or expected == .poison_type) return actual;

    // literals take the expected type directly (an unbound var: their default, which binds the var)
    const given_type = if (resolver.tree.is_literal(node))
        resolver.set_node_type(node, resolver.static_values.literal_type(node, expected))
    else
        actual;
    if (static_pool.coercion(given_type, expected) != .incompatible) return expected;

    if (static_pool.unify(given_type, expected) == .infinite) {
        return resolver.report(.infinite_type, node, given_type, expected);
    }
    return resolver.report(.type_mismatch, node, given_type, expected);
}

// the type of a node held to `expected`
pub fn check(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    expected: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const node_type = self.infer(context, node, expected);

    // a case with a payload is a constructor, a value of it needs the payload
    const is_payload_constructor = node_type != .poison_type and
        resolver.tree.kind(node) == .member and
        static_pool.tag(node_type) == .variant_case_type and
        static_pool.get(node_type).variant_case_type.payload != .none;
    if (is_payload_constructor) return resolver.report(.type_mismatch, node, node_type, expected);

    return self.expect_type(node, node_type, expected);
}

fn infer_length_or_tag(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const operand_type = self.infer(context, resolver.tree.arg(node, 0), .none);
    if (operand_type == .poison_type) return operand_type;

    const owner = static_pool.pointee(static_pool.substitute_type_variables(operand_type));
    const is_length = resolver.tree.kind(node) == .lenof;
    if (is_length and static_pool.tag(owner) == .array_type) {
        if (self.length_is_static(context, owner, node)) return .u64_type;
        return resolver.report(.not_static, node, 0, 0);
    }
    const is_value = static_pool.tag(operand_type) != .meta_type;
    const tag_type = static_pool.tag_type_of(owner);
    if (!is_length and is_value and tag_type != .none) return tag_type;
    const operator = resolver.name_pool.intern(if (is_length) "lenof" else "tagof");
    return resolver.report(.invalid_operand, node, operator, operand_type);
}

fn infer_member_access(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const parent = resolver.tree.arg(node, 0);
    const name = resolver.name_pool.name_of_node(resolver.tree.arg(node, 1));

    const parent_type = self.infer(context, parent, .none);
    if (parent_type == .poison_type) return parent_type;

    // `Type.Case`, `Type.init`, `Stream(i32).None` are members of the type value
    const on_type = static_pool.tag(parent_type) == .meta_type;
    const base_type = if (on_type)
        resolver.static_values.evaluate_or_defer(context, parent) orelse return .poison_type
    else
        static_pool.substitute_type_variables(parent_type);
    if (base_type == .poison_type) return base_type;

    // of a tree: a view or child, of the type `ast`: a kind
    if (resolver.tree.macros and static_pool.is_tree(base_type)) {
        if (on_type) return resolver.macros.tree_kind_member(node, name);
        return resolver.macros.tree_member(base_type, name);
    }
    const through_opaque = !on_type and static_pool.is_pointer(base_type) and
        static_pool.tag(static_pool.pointee(base_type)) != .array_type and
        static_pool.is_unstorable(static_pool.pointee(base_type));
    if (through_opaque and !context.is_abstract) {
        return resolver.report(.unstorable_dereference, parent, base_type, 0);
    }
    if (static_pool.tag(base_type) == .type_variable) {
        return resolver.report(.uninferable_type, parent, base_type, .none);
    }

    const template = static_pool.template_of(base_type);
    if (template != .none) return resolver.generics.template_member(node, template, name);
    // a view parameter only has the members its template promises
    const view_template_lacks_member = blk: {
        if (resolver.tree.kind(parent) != .identifier) break :blk false;

        const parent_declaration = resolver.node_declarations[parent];
        if (parent_declaration == .none) break :blk false;
        if (!resolver.decl_pool.get(parent_declaration, .flags).is_view) break :blk false;

        const template_source = resolver.generics.template_source_of(base_type);
        if (template_source == .none) break :blk false;

        const template_type = static_pool.intern(.{ .template_type = template_source });
        break :blk resolver.generics.template_member(node, template_type, name) == .poison_type;
    };
    if (view_template_lacks_member) return .poison_type;

    return switch (static_pool.lookup_member(base_type, name)) {
        .field => |field| if (on_type)
            resolver.report(.unknown_member, node, name, base_type)
        else
            field.field_type,
        .method => |method_declaration| self.use_method(node, method_declaration),
        .trait_method => |trait_method| self.use_method(
            node,
            static_pool.trait_method_declaration(trait_method),
        ),
        .case => |case_type| case_type,
        .builtin_init, .builtin_deinit => self.builtin_lifecycle_type(base_type, name),
        .none, .builtin_len => resolver.report(.unknown_member, node, name, base_type),
    };
}

// a length is static: a runtime-length array has none, unless what holds it is evaluated while
// compiling (trees, static values, stcfun bodies)
pub fn length_is_static(
    self: *Expressions,
    context: *FunctionContext,
    array_type: StaticPool.Index,
    node: NodeId,
) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const array = static_pool.pointee(static_pool.substitute_type_variables(array_type));
    if (static_pool.tag(array) != .array_type) return true;
    const length = static_pool.get(array).array_type.length;
    const is_open = static_pool.tag(length) == .type_variable;
    if (length != StaticPool.dyn_len and !is_open) return true;
    // a length-generic body is checked once for all lengths, each realization has its own
    if (context.is_interpreted or context.is_abstract) return true;
    if (static_pool.contains_trees(array)) return true;
    if (resolver.static_values.try_evaluate(context, node)) |evaluated| {
        if (evaluated != StaticPool.dyn_len) return true;
    }
    if (!is_open) return false;
    if (resolver.tree.props(node).range) return true;
    self.open_lengths.append(resolver.allocator, .{ .node = node, .array_type = array }) catch {
        @panic("OOM");
    };
    return true;
}

pub fn report_runtime_lengths(self: *Expressions) void {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    for (self.open_lengths.items) |open_length| {
        const array = static_pool.substitute_type_variables(open_length.array_type);
        if (static_pool.get(array).array_type.length != StaticPool.dyn_len) continue;
        _ = resolver.report(.not_static, open_length.node, 0, 0);
    }
}

fn builtin_lifecycle_type(
    self: *Expressions,
    base_type: StaticPool.Index,
    name: NamePool.Index,
) StaticPool.Index {
    const return_type: StaticPool.Index = if (name == .init) base_type else .unit_type;
    return self.owning_resolver().static_pool.intern(.{ .function_type = .{
        .category = .default,
        .parameters = &.{},
        .return_type = return_type,
    } });
}

fn use_method(self: *Expressions, node: NodeId, method: DeclPool.Index) StaticPool.Index {
    const resolver = self.owning_resolver();
    resolver.node_declarations[node] = method;
    return resolver.types.declaration_type(method);
}

// `result` when the operand is numeric, the operand type itself for a `.none` result
fn numeric_result(
    self: *Expressions,
    node: NodeId,
    operand_type: StaticPool.Index,
    result: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;

    const numeric = static_pool.is_numeric(operand_type) or
        static_pool.tag(operand_type) == .type_variable;
    if (!numeric) return resolver.report_mismatch(node, operand_type, .none);
    if (result == .none) return operand_type;
    return result;
}

fn infer_operand(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    hint: StaticPool.Index,
) StaticPool.Index {
    if (self.owning_resolver().tree.is_literal(node)) return self.check(context, node, hint);
    return self.infer(context, node, hint);
}

// both sides of a binary operator: the non-literal side first, so a literal takes its type
fn join_operands(
    self: *Expressions,
    context: *FunctionContext,
    node: NodeId,
    left: NodeId,
    right: NodeId,
    hint: StaticPool.Index,
) StaticPool.Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const kind = resolver.tree.kind(node);

    // a literal on the left waits for a right side that is no literal or a float literal
    const swapped = blk: {
        const tree = resolver.tree;
        if (!tree.is_literal(left)) break :blk false;
        if (!tree.is_literal(right)) break :blk true;

        var negated = false;
        break :blk tree.kind(tree.literal_core(right, &negated)) == .float;
    };
    const first = if (swapped) right else left;
    const second = if (swapped) left else right;

    const first_type = self.infer_operand(context, first, hint);

    const is_add = kind == .binary_add;
    const may_offset_pointer = is_add or !swapped and kind == .binary_sub;
    if (may_offset_pointer and static_pool.is_element_pointer(first_type)) {
        const negative = resolver.tree.kind(second) == .neg_num;
        const integer_hint: StaticPool.Index = if (negative) .i64_type else .u64_type;
        const operand_type = self.infer_operand(context, second, integer_hint);
        if (operand_type == .poison_type) return first_type;
        if (static_pool.properties(operand_type).is_integer) return first_type;

        _ = resolver.report(.type_mismatch, second, operand_type, .u64_type);
        return .poison_type;
    }

    const second_type = self.infer_operand(context, second, first_type);

    const offsets_second = is_add and
        static_pool.is_element_pointer(second_type) and
        static_pool.properties(first_type).is_integer;
    if (offsets_second) return second_type;

    if (first_type == .poison_type or second_type == .poison_type) return .poison_type;

    const both_are_types = static_pool.tag(first_type) == .meta_type and
        static_pool.tag(second_type) == .meta_type;
    if (both_are_types) return first_type;

    var joined = static_pool.join(first_type, second_type).joined_type;
    if (joined == .none) {
        // `self == Toggle.On`
        const first_pointee = static_pool.through_pointer(first_type);
        const second_pointee = static_pool.through_pointer(second_type);
        joined = static_pool.join(first_pointee, second_pointee).joined_type;
    }
    if (joined == .none) return resolver.report(.type_mismatch, node, first_type, second_type);
    return joined;
}
