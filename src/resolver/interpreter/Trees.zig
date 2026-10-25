const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Lexer = @import("../../Lexer.zig");
const Parser = @import("../../Parser.zig");
const StaticPool = @import("../StaticPool.zig");
const NamePool = @import("../NamePool.zig");
const Interpreter = @import("../Interpreter.zig");
const Resolver = @import("../../Resolver.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;
const Arity = @TypeOf(ParseTree.Node.nk_childc[0]);

// trees: code as a value, a pool value naming its root node; a stored tree is a copy of its own,
// a `*ast` shares; a quote copies its code with the holes filled, a landed tree is made hygienic
const Trees = @This();

// how a name in a quote names: it refers, declares (`x = ..`, a parameter) or labels (`.x`)
const Mode = enum { plain, binds, label, pattern };

pub fn owning_interpreter(self: *Trees) *Interpreter {
    return @alignCast(@fieldParentPtr("trees", self));
}

pub fn evaluate(self: *Trees, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    return switch (resolver.tree.kind(node)) {
        .quote => self.evaluate_quote(node),
        .splice => self.splice(node),
        .refl => self.reflect(node),
        .include, .include_raw => self.include(node),
        else => interpreter.fail(node, .stray_unquote, 0, 0),
    };
}

// `quote`: its code copied, the holes filled, each name it writes marked with its function
fn evaluate_quote(self: *Trees, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    // the tree the checker made: a stcfun called with it is realized once
    const checked = resolver.node_static_values[node];
    if (!interpreter.has_body_frame() and checked != .none) {
        return .of(&resolver.static_pool, checked);
    }

    const quote_type = self.type_at(node);
    const owner = interpreter.node_info(.declaration, node);
    // the hygiene of a name is its function plus one, zero for none
    const hygiene: u32 = if (owner == .none) 0 else @backingInt(owner) + 1;

    const code = resolver.tree.arg(node, 0);
    const root = self.fill(code, hygiene, .plain) orelse return .poison;
    return self.tree_value(quote_type, root);
}

// the code is there in the next pass, until then the splice has no value
fn splice(self: *Trees, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const macros = &resolver.macros;

    const outer = macros.at;
    macros.splicing += 1;
    macros.at = resolver.tree.first_token(node);
    defer macros.splicing -= 1;
    defer macros.at = outer;

    const mark = resolver.doctor.diagnostics.len();
    const value = interpreter.evaluate(resolver.tree.arg(node, 0));
    const clean = !value.is(.poison_type) and resolver.doctor.diagnostics.len() == mark;
    if (clean) self.expand(node, interpreter.interned(value));
    _ = macros.end_splice(true, mark, .none);
    return .poison;
}

// `refl f`: the declaration's tree, a bare `refl` the whole file
fn reflect(self: *Trees, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const reflected_type = self.type_at(node);

    const declaration = interpreter.node_info(.declaration, node);
    // a bare `refl`: a block of the roots, made once a pass
    if (declaration == .none and resolver.macros.file == 0) {
        resolver.macros.file = resolver.tree.push_node(.block);
        resolver.tree.set_children(resolver.macros.file, resolver.roots);
    }
    const root = if (declaration == .none)
        resolver.macros.file
    else
        resolver.decl_pool.get(declaration, .node);
    return self.tree_value(reflected_type, root);
}

// a type checked now when evaluated before the checker met it (`fun f = <m(..)>` resolves f)
fn type_at(self: *Trees, node: NodeId) Index {
    const interpreter = self.owning_interpreter();
    const checked = interpreter.node_info(.node_type, node);
    if (checked != .none or interpreter.has_body_frame()) return checked;
    const context = interpreter.function_context;
    return interpreter.owning_resolver().expressions.infer(context, node, .none);
}

pub fn tree_value(self: *Trees, tree_type: Index, root: NodeId) Value {
    const static_pool = &self.owning_interpreter().owning_resolver().static_pool;
    const value_type = if (tree_type == .none) .ast_type else tree_type;
    return .pooled(static_pool.intern(.{
        .tree_value = .{ .tree_type = value_type, .node = root },
    }));
}

// the root of a tree or a `*ast`, null for any other value
pub fn node_of(self: *Trees, value: Value) ?NodeId {
    const static_pool = &self.owning_interpreter().owning_resolver().static_pool;
    if (!value.is_pooled() or value.is(.none)) return null;
    if (static_pool.tag(value.index()) != .tree_value) return null;
    return static_pool.get(value.index()).tree_value.node;
}

// a root kind is stored plus one, zero stands for any kind
fn root_kind_code(kind: Kind) u16 {
    return @as(u16, @backingInt(kind)) + 1;
}

inline fn arity(kind: Kind) Arity {
    return ParseTree.Node.nk_childc[@backingInt(kind)];
}

// a value stored (in a variable, a parameter, an element) owns copies of its trees, `*ast`s share
pub fn keep(self: *Trees, value: Value) Value {
    const static_pool = &self.owning_interpreter().owning_resolver().static_pool;
    if (!value.is_pooled() or value.is(.none)) return value;

    const index = value.index();
    switch (static_pool.tag(index)) {
        .tree_value => return self.keep_tree(value, index),
        .aggregate_value => return self.keep_aggregate(value, index),
        .variant_value => return self.keep_variant(value, index),
        .int_type,
        .float_type,
        .simple_type,
        .meta_type,
        .array_type,
        .slice_type,
        .pointer_type,
        .mutable_pointer_type,
        .function_type,
        .record_type,
        .variant_type,
        .variant_case_type,
        .unified_variant_type,
        .variant_subset_type,
        .trait_type,
        .static_function,
        .template_type,
        .type_variable,
        .ast_type,
        .int_value,
        .float_value,
        .simple_value,
        .string_value,
        .function_value,
        => return value,
    }
}

// a case value keeps the trees of its payload like any aggregate
fn keep_variant(self: *Trees, value: Value, index: Index) Value {
    const static_pool = &self.owning_interpreter().owning_resolver().static_pool;
    const variant_value = static_pool.get(index).variant_value;
    if (variant_value.payload == .none) return value;

    const kept_payload = self.keep(.pooled(variant_value.payload)).index();
    if (kept_payload == variant_value.payload) return value;
    return .pooled(static_pool.intern(.{ .variant_value = .{
        .case = variant_value.case,
        .payload = kept_payload,
    } }));
}

fn keep_tree(self: *Trees, value: Value, index: Index) Value {
    const resolver = self.owning_interpreter().owning_resolver();
    const stored = resolver.static_pool.get(index).tree_value;
    if (resolver.static_pool.is_pointer(stored.tree_type)) return value;

    const copied = resolver.tree.copy(resolver.tree, stored.node, resolver.src_bytes, false, null);
    return self.tree_value(stored.tree_type, copied);
}

fn keep_aggregate(self: *Trees, value: Value, index: Index) Value {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;
    const aggregate_type = static_pool.get(index).aggregate_value.value_type;
    if (aggregate_type == .none or !static_pool.contains_trees(aggregate_type)) return value;

    const mark = interpreter.pool_indices.len;
    defer interpreter.pool_indices.len = mark;
    // by index: interning may move the elements
    for (0..static_pool.get(index).aggregate_value.elements.len) |j| {
        const element = static_pool.get(index).aggregate_value.elements[j];
        interpreter.pool_indices.push(self.keep(.pooled(element)).index());
    }
    return .pooled(static_pool.intern(.{ .aggregate_value = .{
        .value_type = aggregate_type,
        .elements = interpreter.pool_indices.buffer[mark..interpreter.pool_indices.len],
    } }));
}

// the code a splice stands for from now on: a landed copy of the tree, nothing for a unit
pub fn expand(self: *Trees, node: NodeId, code: Index) void {
    const resolver = self.owning_interpreter().owning_resolver();
    if (code == .poison_type) return;

    const expansion: NodeId = blk: {
        const static_pool = &resolver.static_pool;
        if (code == .unit_value) break :blk resolver.tree.push_node(.block);
        if (static_pool.tag(code) == .tree_value) {
            const root = static_pool.get(code).tree_value.node;
            if (self.is_declared_again(node, root)) break :blk resolver.tree.push_node(.block);
            break :blk self.land(root, .none);
        }

        const found_type = static_pool.type_of(code);
        _ = self.owning_interpreter().fail(node, .type_mismatch, found_type, .ast_type);
        return;
    };
    // the free second slot of a splice holds its expansion plus one, zero while it has none
    resolver.tree.ast_nodes.column(.args)[node][1] = expansion + 1;
    resolver.macros.expanded += 1;
    resolver.macros.last = node;
}

// a copy for the program, written at the evaluated splice, hygienic, fitted to the list `into`
// a `@` in it outside a quote (from an included file, made by `ast.Unquote(..)`) is stray
fn land(self: *Trees, code: NodeId, into: Kind) NodeId {
    const resolver = self.owning_interpreter().owning_resolver();
    const tree = resolver.tree;
    const copied = tree.copy(tree, code, resolver.src_bytes, false, resolver.macros.at);
    // code written as a declaration (`mut u32 a = 7`) landing in a field or parameter list is one
    const landed = blk: {
        if (into == .partial__variant_def_param_tuple) break :blk variant_case(tree, copied);
        const is_field = into == .partial__type_def_param_tuple;
        if (!is_field and into != .partial__fun_def_param_tuple) break :blk copied;

        var declaration = copied;
        const mutable = tree.kind(declaration) == .mod_mut;
        if (mutable) declaration = tree.arg(declaration, 0);
        const default = if (tree.kind(declaration) == .assign_typed)
            tree.arg(declaration, 1)
        else
            0;
        if (default != 0) declaration = tree.arg(declaration, 0);
        if (tree.kind(declaration) != .def_var) break :blk copied;

        const declared_type = tree.arg(declaration, 0);
        const name = tree.arg(declaration, 1);
        if (is_field) {
            as_label(tree, name);
            var parameter = tree.push_node_with(
                .partial__type_def_param,
                .{ .type = declared_type },
            );
            parameter = tree.push_node_with(
                .partial__type_def_param_named,
                .{ .param = parameter, .identifier = name },
            );
            if (default != 0) {
                parameter = tree.push_node_with(
                    .partial__type_def_param_default,
                    .{ .param = parameter, .default_value = default },
                );
            }
            if (!mutable) break :blk parameter;
            break :blk tree.push_node_with(.partial__type_def_param_mut, .{ .param = parameter });
        }

        var parameter = tree.push_node_with(.partial__fun_def_param, .{ .type = declared_type });
        parameter = tree.push_node_with(
            .partial__fun_def_param_named,
            .{ .param = parameter, .identifier = name },
        );
        if (default != 0) {
            parameter = tree.push_node_with(
                .partial__fun_def_param_default,
                .{ .param = parameter, .default_value = default },
            );
        }
        break :blk parameter;
    };
    tree.land(landed, &resolver.session.fresh_name_count);
    resolver.macros.report_stray_unquotes(landed, false);
    return landed;
}

fn variant_case(tree: *ParseTree, code: NodeId) NodeId {
    switch (tree.kind(code)) {
        .identifier => {
            as_label(tree, code);
            return tree.push_node_with(.partial__variant_def_param, .{ .name = code });
        },
        .assign => {
            const named = variant_case(tree, tree.arg(code, 0));
            if (named == tree.arg(code, 0)) return code;
            return tree.push_node_with(
                .partial__variant_def_param_tagged,
                .{ .param = named, .tag_value = tree.arg(code, 1) },
            );
        },
        .fun_call => {
            if (tree.kind(tree.arg(code, 0)) != .identifier) return code;
            const named = variant_case(tree, tree.arg(code, 0));
            const mark = tree.scratch.len;
            defer tree.scratch.len = mark;
            for (0..tree.arg(tree.arg(code, 1), 1)) |i| {
                const argument = tree.manychildren(tree.arg(code, 1))[i];
                const field_type = tree.arg_value(argument);
                tree.scratch.push(tree.push_node_with(
                    .partial__type_def_param,
                    .{ .type = field_type },
                ));
            }
            const fields = tree.push_node(.partial__type_def_param_tuple);
            tree.set_children(fields, tree.scratch.buffer[mark..tree.scratch.len]);
            return tree.push_node_with(
                .partial__variant_def_param_typed,
                .{ .param = named, .def_type = fields },
            );
        },
        else => return code,
    }
}

fn as_label(tree: *ParseTree, name: NodeId) void {
    if (tree.kind(name) != .identifier or tree.arg(name, 1) == 0) return;
    tree.words.column(.binds)[tree.arg(name, 1) - 1] = false;
}

fn fill(self: *Trees, written: NodeId, owner: u32, mode: Mode) ?NodeId {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;
    if (written == 0) return 0;

    var node = written;
    while (tree.kind(node) == .capture) node = tree.arg(node, 0);
    if (!interpreter.charge_steps(node, 1)) return null;

    const kind = tree.kind(node);
    switch (kind) {
        // a quote within keeps its holes for when it is evaluated
        .quote => return tree.copy(tree, node, resolver.src_bytes, false, null),
        .unquote => return self.hole(tree.arg(node, 0)),
        .paste => return self.paste(node),
        .unquote_list => {
            _ = interpreter.fail(node, .stray_unquote, 0, 0);
            return null;
        },
        .identifier => return self.fill_name(node, owner, mode),
        else => {},
    }

    switch (arity(kind)) {
        .none => return tree.push_node(kind),
        .data => return tree.copy(tree, node, resolver.src_bytes, false, null),
        .one, .two => return self.fill_pair(node, owner, mode),
        .many => return self.fill_list(node, owner, mode),
    }
}

fn fill_name(self: *Trees, node: NodeId, owner: u32, mode: Mode) NodeId {
    const resolver = self.owning_interpreter().owning_resolver();
    const tree = resolver.tree;

    // copied out first: the text may live in the tree's own text bytes, which pushing a word grows
    var buffer: [256]u8 = undefined;
    const text = tree.text(node, resolver.src_bytes);
    const fits = text.len <= buffer.len;
    const copy = if (fits) buffer[0..text.len] else resolver.temporary_slice(u8, text.len);
    @memcpy(copy, text);

    // `_`, the compiler's `$` names and the protocol names are no names of the quote
    const own = mode != .label and
        text.len > 0 and
        text[0] != '$' and
        !std.mem.eql(u8, text, "_") and
        !NamePool.is_protocol(text);
    const hygiene = if (own) owner else 0;
    const binds = own and (mode == .binds or mode == .pattern);
    return tree.push_word(.identifier, tree.arg(node, 0), copy, hygiene, binds);
}

inline fn fill_pair(self: *Trees, node: NodeId, owner: u32, mode: Mode) ?NodeId {
    const tree = self.owning_interpreter().owning_resolver().tree;
    const kind = tree.kind(node);

    const first_mode = mode_of(tree, node, 0, mode);
    const first = self.fill(tree.arg(node, 0), owner, first_mode) orelse return null;
    var second: NodeId = 0;
    if (arity(kind) == .two) {
        const second_mode = mode_of(tree, node, 1, mode);
        second = self.fill(tree.arg(node, 1), owner, second_mode) orelse return null;
    }

    const filled = tree.push_node(kind);
    tree.ast_nodes.column(.args)[filled] = .{ first, second };
    return filled;
}

inline fn fill_list(self: *Trees, node: NodeId, owner: u32, mode: Mode) ?NodeId {
    const tree = self.owning_interpreter().owning_resolver().tree;
    const mark = tree.scratch.len;
    defer tree.scratch.len = mark;

    // by index: filling a hole may grow the lists of the tree
    for (0..tree.arg(node, 1)) |i| {
        const child = tree.extra_childrefs.buffer[tree.arg(node, 0) + i];
        if (tree.kind(child) == .unquote_list) {
            if (!self.spread(tree.arg(child, 0))) return null;
            continue;
        }
        const child_mode = mode_of(tree, node, @intCast(i), mode);
        const filled = self.fill(child, owner, child_mode) orelse return null;
        tree.scratch.push(filled);
    }

    const filled_list = tree.push_node(tree.kind(node));
    tree.set_children(filled_list, tree.scratch.buffer[mark..tree.scratch.len]);
    return filled_list;
}

// how the child `i` of `node` names
fn mode_of(tree: *const ParseTree, node: NodeId, i: u32, mode: Mode) Mode {
    const kind = tree.kind(node);
    return switch (kind) {
        .member => if (i == 1) .label else .plain,
        .partial__fun_call_assigned_param => if (i == 0) .label else mode,
        .partial__type_def_param_named, .partial__variant_def_param => .label,
        .assign,
        .labelarrow,
        .selftag_arrow,
        .for_var_in_seq,
        .stcfor_var_in_seq,
        .partial__fun_def_param_named,
        .partial__match_case_pattern_typecast,
        => binder_mode(kind, i, mode),
        // a function or type declared in a quote keeps the program's name, a variable the quote's
        .def_var => if (i == 0) .plain else switch (tree.kind(tree.arg(node, 0))) {
            .type_fun, .type_stcfun, .type_inlfun, .type_type, .type_variant, .type_trait => .label,
            else => .binds,
        },
        .partial__destructure,
        .partial__fun_call_param_tuple,
        .partial__match_case_pattern_or,
        => mode,
        .fun_call => if (i == 1) mode else .plain,
        .partial__match_case => if (i == 0) .pattern else .plain,
        .partial__match_case_where => if (i == 0) mode else .plain,
        else => .plain,
    };
}

// the binder of `x = ..` is its first child, of the other binding nodes their second
fn binder_mode(kind: Kind, i: u32, mode: Mode) Mode {
    if (i == @intFromBool(kind != .assign)) return .binds;
    if (mode == .pattern and kind != .partial__match_case_pattern_typecast) return .pattern;
    return .plain;
}

// `@x`: what `x` holds if known where the quote is evaluated, else the name `x` where it lands
fn hole(self: *Trees, expression: NodeId) ?NodeId {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;

    var root = expression;
    while (tree.kind(root) == .member or tree.kind(root) == .array_index) root = tree.arg(root, 0);
    if (tree.kind(root) == .identifier and !self.known(root)) {
        return tree.copy(tree, expression, resolver.src_bytes, false, null);
    }

    const value = interpreter.evaluate(expression);
    if (value.is(.poison_type)) return null;

    // the value put into code: a tree as a copy of it, a static value as the literal or type it is
    if (self.node_of(value)) |value_root| {
        return tree.copy(tree, value_root, resolver.src_bytes, false, null);
    }
    return self.code_of(tree.first_token(expression), value) orelse {
        _ = interpreter.fail(expression, .not_static, interpreter.interned(value), 0);
        return null;
    };
}

fn code_of(self: *Trees, token: u32, value: Value) ?NodeId {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const tree = resolver.tree;
    if (value.value_type == .bool_type) {
        return tree.push_node(if (value.bits != 0) .boolean_true else .boolean_false);
    }
    if (Value.is_int(value.value_type)) {
        // a negative number is written as the negation of its magnitude
        const signed = static_pool.get(value.value_type).int_type.signedness == .signed;
        const negative = signed and @as(i64, @bitCast(value.bits)) < 0;
        const magnitude = if (negative) 0 -% value.bits else value.bits;

        var buffer: [64]u8 = undefined;
        const digits = std.fmt.bufPrint(&buffer, "{d}", .{magnitude}) catch unreachable;
        const literal = tree.push_word(.int, token, digits, 0, false);
        if (!negative) return literal;
        return tree.push_node_with(.neg_num, .{ .subnode = literal });
    }
    if (Value.is_float(value.value_type)) {
        // a float's decimal digits are many for large and tiny magnitudes, so no fixed buffer
        const arena = interpreter.owning_resolver().temporary_arena.allocator();
        const digits = std.fmt.allocPrint(arena, "{d}", .{value.as_float()}) catch @panic("OOM");
        return tree.push_word(.float, token, digits, 0, false);
    }

    const index = interpreter.interned(value);
    if (static_pool.tag(index) == .string_value) {
        // the literal of a text: its quotes and backslashes escaped
        const text = static_pool.get(index).string_value;
        const escaped = resolver.temporary_slice(u8, text.len * 2);

        var length: usize = 0;
        for (text) |char| {
            if (char == '"' or char == '\\' or char == '\n') {
                escaped[length] = '\\';
                length += 1;
            }
            escaped[length] = if (char == '\n') 'n' else char;
            length += 1;
        }
        return resolver.tree.push_word(.string, token, escaped[0..length], 0, false);
    }
    if (static_pool.properties(index).is_type) return self.type_tree(token, index);
    return null;
}

fn known(self: *Trees, id: NodeId) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const declaration = interpreter.node_info(.declaration, id);
    if (declaration == .none) return false;

    if (interpreter.variables.cell_of_declaration(declaration)) |cell| {
        return !interpreter.memory.buffer[cell].is(.none);
    }
    return resolver.decl_pool.get(declaration, .static_value) != .none;
}

// `@..xs`: the trees of a list (or the children of a tree) as children of the list around
fn spread(self: *Trees, expression: NodeId) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;

    const value = interpreter.evaluate(expression);
    if (value.is(.poison_type)) return false;
    if (self.node_of(value)) |root| {
        // a tree without a list of children spreads as itself
        if (arity(tree.kind(root)) != .many) {
            tree.scratch.push(tree.copy(tree, root, resolver.src_bytes, false, null));
            return true;
        }

        // by index: copying grows the lists of the tree
        for (0..tree.arg(root, 1)) |i| {
            const child = tree.extra_childrefs.buffer[tree.arg(root, 0) + i];
            tree.scratch.push(tree.copy(tree, child, resolver.src_bytes, false, null));
        }
        return true;
    }

    const length = interpreter.aggregate_length(value) orelse {
        _ = interpreter.fail(expression, .type_mismatch, interpreter.value_type(value), .ast_type);
        return false;
    };
    for (0..length) |i| {
        const item = interpreter.element(value, @intCast(i));
        const item_root = self.node_of(item) orelse {
            const item_type = interpreter.value_type(item);
            _ = interpreter.fail(expression, .type_mismatch, item_type, .ast_type);
            return false;
        };
        tree.scratch.push(tree.copy(tree, item_root, resolver.src_bytes, false, null));
    }
    return true;
}

// `get_@(x)`: one name of the name before and the name or text `x` is
fn paste(self: *Trees, node: NodeId) ?NodeId {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;

    const value = interpreter.evaluate(tree.arg(tree.arg(node, 1), 0));
    if (value.is(.poison_type)) return null;

    const tail = self.text_of(value) orelse {
        _ = interpreter.fail(node, .type_mismatch, interpreter.value_type(value), .ast_type);
        return null;
    };
    const head = tree.arg(node, 0);
    const head_text = tree.text(head, resolver.src_bytes);
    const arena = resolver.temporary_arena.allocator();
    const joined = std.fmt.allocPrint(arena, "{s}{s}", .{ head_text, tail }) catch @panic("OOM");
    return tree.push_word(.identifier, tree.arg(head, 0), joined, 0, false);
}

// the text a name, a literal or a string is
pub fn text_of(self: *Trees, value: Value) ?[]const u8 {
    const resolver = self.owning_interpreter().owning_resolver();
    const static_pool = &resolver.static_pool;
    if (self.node_of(value)) |root| {
        if (arity(resolver.tree.kind(root)) != .data) return null;
        const text = resolver.tree.text(root, resolver.src_bytes);
        const copy = resolver.temporary_slice(u8, text.len);
        @memcpy(copy, text);
        return copy;
    }

    const index = self.owning_interpreter().interned(value);
    if (static_pool.tag(index) == .string_value) return static_pool.get(index).string_value;
    if (static_pool.tag(index) != .aggregate_value) return null;
    const aggregate = static_pool.get(index).aggregate_value;
    if (static_pool.array_element(aggregate.value_type) != .u8_type) return null;
    const bytes = resolver.temporary_slice(u8, aggregate.elements.len);
    for (bytes, aggregate.elements) |*byte, element| {
        byte.* = @intCast(Value.of(static_pool, element).bits);
    }
    return bytes;
}

// the keyword kind (`type_u32`) of each builtin type index (`u32_type`) that has one
const keyword_kinds = blk: {
    var kinds: [Index.first_dynamic]?Kind = @splat(null);
    const ti = @typeInfo(Index).@"enum";
    for (ti.field_names, ti.field_values) |fname, fval| {
        if (!std.mem.endsWith(u8, fname, "_type")) continue;
        const keyword = "type_" ++ fname[0 .. fname.len - "_type".len];
        if (@hasField(Kind, keyword)) kinds[fval] = @field(Kind, keyword);
    }
    break :blk kinds;
};

// a type as code naming it: a keyword, a pointer or array of one, a declared type by its name
fn type_tree(self: *Trees, token: u32, named: Index) ?NodeId {
    const resolver = self.owning_interpreter().owning_resolver();
    const tree = resolver.tree;
    if (@backingInt(named) < keyword_kinds.len) {
        if (keyword_kinds[@backingInt(named)]) |keyword| return tree.push_node(keyword);
    }

    switch (resolver.static_pool.get(named)) {
        .pointer_type => |pointer| {
            const pointee = self.type_tree(token, pointer.pointee) orelse return null;
            const code = tree.push_node(if (pointer.is_mutable) .type_ptrmut else .type_ptr);
            tree.set_children(code, pointee);
            return code;
        },
        .array_type => |array| return self.array_type_tree(token, array),
        .slice_type => |slice| {
            const element = self.type_tree(token, slice.element) orelse return null;
            return tree.push_node_with(.type_slice, .{ .type = element });
        },
        // `V -- V.A -- ..`, a case as the member of its variant
        .variant_subset_type => |subset| {
            var code = self.type_tree(token, subset.whole) orelse return null;
            for (0..subset.removed.len) |i| {
                const unit = resolver.static_pool.get(named).variant_subset_type.removed[i];
                const part = if (resolver.static_pool.tag(unit) == .variant_case_type) blk: {
                    const removed_case = resolver.static_pool.get(unit).variant_case_type;
                    const variant = self.type_tree(token, removed_case.variant) orelse return null;
                    const case_text = resolver.name_pool.text_of(removed_case.name);
                    const name = tree.push_word(.identifier, token, case_text, 0, false);
                    break :blk tree.push_node_with(.member, .{ .parent = variant, .member = name });
                } else self.type_tree(token, unit) orelse return null;
                code = tree.push_node_with(.variant_difference, .{
                    .left_type = code,
                    .right_type = part,
                });
            }
            return code;
        },
        // `u7`, `i24`: a width without a keyword
        .int_type => |int| {
            var buffer: [4]u8 = undefined;
            const sign: u8 = if (int.signedness == .signed) 'i' else 'u';
            const name = std.fmt.bufPrint(&buffer, "{c}{d}", .{ sign, int.bits }) catch unreachable;
            return tree.push_word(.identifier, token, name, 0, false);
        },
        .float_type,
        .simple_type,
        .meta_type,
        .function_type,
        .record_type,
        .variant_type,
        .variant_case_type,
        .unified_variant_type,
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
        => {
            const declaration = resolver.static_pool.nominal_declaration(named);
            if (declaration == .none) return null;
            const name = resolver.decl_pool.get(declaration, .name);
            const is_realized = resolver.generics.template_of.contains(declaration);
            if (is_realized or name == .empty) return self.realized_type_tree(token, named);
            return tree.push_word(.identifier, token, resolver.name_pool.text_of(name), 0, false);
        },
    }
}

fn realized_type_tree(self: *Trees, token: u32, named: Index) ?NodeId {
    const resolver = self.owning_interpreter().owning_resolver();
    const static_pool = &resolver.static_pool;
    const tree = resolver.tree;
    var realizations = resolver.generics.realizations.iterator();
    const key = while (realizations.next()) |entry| {
        if (entry.value_ptr.* == named) break entry.key_ptr.*;
    } else return null;
    if (static_pool.tag(key.args_tuple) != .aggregate_value) return null;

    const name = resolver.name_pool.text_of(resolver.decl_pool.get(key.generic_tuple, .name));
    const callee = tree.push_word(.identifier, token, name, 0, false);
    const count = static_pool.get(key.args_tuple).aggregate_value.elements.len;
    const arguments = resolver.temporary_slice(NodeId, count);
    for (arguments, 0..) |*argument, i| {
        const element = static_pool.get(key.args_tuple).aggregate_value.elements[i];
        argument.* = self.code_of(token, .of(static_pool, element)) orelse return null;
    }
    const tuple = tree.push_node(.partial__fun_call_param_tuple);
    tree.set_children(tuple, arguments);
    return tree.push_node_with(.fun_call, .{ .callable = callee, .fun_param_tuple = tuple });
}

fn array_type_tree(self: *Trees, token: u32, array: StaticPool.ArrayType) ?NodeId {
    const resolver = self.owning_interpreter().owning_resolver();
    const tree = resolver.tree;

    const element = self.type_tree(token, array.element) orelse return null;
    if (array.length == StaticPool.dyn_len) {
        return tree.push_node_with(.type_array_unlengthed, .{ .type = element });
    }

    var buffer: [24]u8 = undefined;
    const length_bits = resolver.static_pool.get(array.length).int_value.bits;
    const digits = std.fmt.bufPrint(&buffer, "{d}", .{length_bits}) catch unreachable;
    const length = tree.push_word(.int, token, digits, 0, false);
    return tree.push_node_with(.type_array, .{ .length = length, .type = element });
}

// `include "f.mn"`: a block of copies of the declarations of a file next to the compiled one, the
// ones without `pub` under names of their own. `includeraw` copies them under the names written
fn include(self: *Trees, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const path = resolver.tree.arg(node, 0);
    const name = if (resolver.tree.kind(path) == .string)
        resolver.tree.text(path, resolver.src_bytes)
    else
        self.text_of(interpreter.evaluate(path)) orelse return .poison;
    const included = switch (self.read(node, name)) {
        .included => |block| block,
        .failed => |failure| {
            const file = resolver.name_pool.intern_copy(name);
            const reason = resolver.name_pool.intern_copy(@errorName(failure.reason));
            return interpreter.fail(failure.at, .include_failed, file, reason);
        },
    };
    return self.tree_value(.ast_type, included);
}

const max_include_bytes = 50 << 20;
const no_file = std.math.maxInt(u32);

const Read = union(enum) { included: NodeId, failed: struct { at: NodeId, reason: anyerror } };

fn read(self: *Trees, node: NodeId, name: []const u8) Read {
    const resolver = self.owning_interpreter().owning_resolver();
    const tree = resolver.tree;
    const allocator = resolver.allocator;

    // relative to the file the `include` is written in, a library reads its own neighbours
    const includer = included_file(resolver, node);
    const written_in = if (includer) |file| file.path else resolver.session.path;
    const directory = std.fs.path.dirname(written_in) orelse ".";
    const path = std.fs.path.resolve(allocator, &.{ directory, name }) catch |err| {
        return .{ .failed = .{ .at = node, .reason = err } };
    };
    // a file another namespace has lands nothing again, both reach the same names
    const namespace = resolver.session.namespace_of_include(node);
    if (namespace) |declared| for (resolver.session.namespaces.items, 0..) |other, i| {
        if (other.file == no_file or other.is_raw != declared.is_raw) continue;
        if (!std.mem.eql(u8, resolver.session.files.items[other.file].path, path)) continue;
        declared.of = @intCast(i);
        allocator.free(path);
        return .{ .included = tree.push_node(.block) };
    };
    const io = resolver.session.io orelse {
        allocator.free(path);
        return .{ .failed = .{ .at = node, .reason = error.NoIo } };
    };
    const limit: std.Io.Limit = .limited(max_include_bytes);
    const bytes = std.Io.Dir.cwd().readFileAlloc(io, path, allocator, limit) catch |err| {
        allocator.free(path);
        return .{ .failed = .{ .at = node, .reason = err } };
    };
    defer allocator.free(bytes);
    const region = tree.text_bytes.len;
    tree.text_bytes.append(bytes);
    const length: u32 = @intCast(bytes.len);
    if (namespace) |declared| declared.file = @intCast(resolver.session.files.items.len);
    resolver.session.files.append(allocator, .{ .path = path, .at = region, .len = length }) catch {
        @panic("OOM");
    };
    const origin = tree.first_token(tree.arg(node, 0));

    var lexer = Lexer{ .src_bytes = bytes, .tokens = .init(allocator, 1024) };
    defer lexer.tokens.deinit();
    lexer.gen_tokens() catch |err| {
        const at = tree.push_word(.identifier, origin, "", 0, false);
        tree.words.column(.at)[tree.words.len() - 1] = region + (lexer.cursor -| 1);
        return .{ .failed = .{ .at = at, .reason = err } };
    };
    var parser = Parser.init(allocator, lexer.tokens, bytes, lexer.tokens.column(.span));
    defer parser.deinit();
    parser.build_ast() catch |err| {
        const at = tree.push_word(.identifier, origin, "", 0, false);
        const failing = lexer.tokens.column(.span)[parser.tok_cursor -| 1];
        tree.words.column(.at)[tree.words.len() - 1] = region + failing[0];
        return .{ .failed = .{ .at = at, .reason = err } };
    };

    const mark = tree.scratch.len;
    defer tree.scratch.len = mark;
    const owner = std.math.maxInt(u32) - resolver.session.fresh_name_count;
    resolver.session.fresh_name_count += 1;
    const first_copied = tree.ast_nodes.len();
    const raw = tree.kind(node) == .include_raw;
    var private_names: std.ArrayList(NodeId) = .empty;
    defer private_names.deinit(allocator);
    // what a namespace shows, as written
    var shown_names: std.ArrayList([]const u8) = .empty;
    defer shown_names.deinit(allocator);
    for (parser.global_store.items()) |root| {
        const first_of_root = tree.ast_nodes.len();
        const copied = tree.copy(&parser.tree, root, bytes, false, null);
        for (first_of_root..tree.ast_nodes.len()) |i| {
            const leaf: NodeId = @intCast(i);
            const span = parser.tree.span_store[tree.token(leaf) orelse continue];
            tree.words.push(.{
                .at = region + span[0],
                .len = span[1] - span[0],
                .owner = 0,
                .binds = false,
            });
            tree.ast_nodes.column(.args)[leaf] = .{ origin, tree.words.len() };
        }
        tree.scratch.push(copied);
        const is_shown = raw or parser.tree.kind(root) == .mod_pub;
        if (is_shown and namespace == null) continue;
        const bare = without_modifiers(tree, copied);
        const declared = name_view(tree, bare, def_var(tree, copied), .{});
        if (declared == 0 or tree.kind(declared) != .identifier) continue;
        if (tree.arg(declared, 1) == 0) continue;
        if (is_shown) {
            const word = tree.arg(declared, 1) - 1;
            const written = bytes[tree.words.column(.at)[word] - region ..];
            shown_names.append(allocator, written[0..tree.words.column(.len)[word]]) catch {
                @panic("OOM");
            };
            continue;
        }
        tree.words.column(.binds)[tree.arg(declared, 1) - 1] = true;
        private_names.append(allocator, declared) catch @panic("OOM");
    }
    for (first_copied..tree.ast_nodes.len()) |i| {
        const copied: NodeId = @intCast(i);
        if (tree.kind(copied) != .identifier or tree.arg(copied, 1) == 0) continue;
        for (private_names.items) |declared| {
            const text = tree.text(declared, resolver.src_bytes);
            if (!std.mem.eql(u8, tree.text(copied, resolver.src_bytes), text)) continue;
            tree.words.column(.owner)[tree.arg(copied, 1) - 1] = owner;
        }
        // a namespace's names land as ``x`name``
        for (shown_names.items) |written| {
            if (!std.mem.eql(u8, tree.text(copied, resolver.src_bytes), written)) continue;
            const word = tree.arg(copied, 1) - 1;
            tree.words.column(.at)[word] = tree.text_bytes.len;
            tree.words.column(.len)[word] += @intCast(1 + namespace.?.name.len);
            tree.text_bytes.append(written);
            tree.text_bytes.push('`');
            tree.text_bytes.append(namespace.?.name);
            break;
        }
    }

    const included = tree.push_node(.block);
    tree.set_children(included, tree.scratch.buffer[mark..tree.scratch.len]);
    return .{ .included = included };
}

// the included file a subtree was written in, the one holding its first word; null for the
// compiled file
fn included_file(resolver: *Resolver, node: NodeId) ?*Resolver.Session.File {
    const tree = resolver.tree;
    const subtree = tree.subtree(node);
    const word = for (subtree[0]..subtree[1]) |i| {
        const leaf: NodeId = @intCast(i);
        if (tree.token(leaf) != null and tree.arg(leaf, 1) != 0) break tree.arg(leaf, 1);
    } else return null;
    return resolver.session.file_at(tree.words.column(.at)[word - 1]);
}

// a file is declared once like a module: a top splice of an `include` of a file the program
// declared already lands nothing, so libraries may include what their includer includes too
fn is_declared_again(self: *Trees, splice_node: NodeId, block: NodeId) bool {
    const resolver = self.owning_interpreter().owning_resolver();
    const tree = resolver.tree;
    const operand_kind = tree.kind(tree.arg(splice_node, 0));
    const declares_file = operand_kind == .include or operand_kind == .include_raw;
    if (!resolver.macros.top or !declares_file or tree.manychildren(block).len == 0) return false;
    if (resolver.session.namespace_of_include(tree.arg(splice_node, 0)) != null) return false;

    const file = included_file(resolver, tree.manychildren(block)[0]) orelse return false;
    for (resolver.session.files.items) |other| {
        if (other.is_declared and std.mem.eql(u8, other.path, file.path)) return true;
    }
    file.is_declared = true;
    return false;
}

// views of trees: a declaration, function, type, field or parameter by its parts, a node by fields

// a declaration without its `pub`, `mut` and `stc`
fn without_modifiers(tree: *const ParseTree, declaration: NodeId) NodeId {
    var bare = declaration;
    while (true) {
        const kind = tree.kind(bare);
        if (kind != .mod_pub and kind != .mod_mut and kind != .mod_stc) return bare;
        bare = tree.arg(bare, 0);
    }
}

// what a declaration declares (`fun f = ..` is its function), anything else itself
fn subject(tree: *const ParseTree, declaration: NodeId) NodeId {
    const bare = without_modifiers(tree, declaration);
    const kind = tree.kind(bare);
    if (kind == .assign or kind == .assign_typed) return tree.arg(bare, 1);
    return bare;
}

fn def_var(tree: *const ParseTree, declaration: NodeId) NodeId {
    const bare = without_modifiers(tree, declaration);
    if (tree.kind(bare) == .assign_typed) return tree.arg(bare, 0);
    if (tree.kind(bare) == .def_var) return bare;
    return 0;
}

fn is_parameter(kind: Kind) bool {
    const value = @backingInt(kind);
    const of_function = value >= @backingInt(Kind.partial__fun_def_param) and
        value <= @backingInt(Kind.partial__fun_def_param_where_else);
    const of_type = value >= @backingInt(Kind.partial__type_def_param) and
        value <= @backingInt(Kind.partial__type_def_param_where_else);
    return of_function or of_type;
}

// the node a view or field of `node` is, null when it has none
fn view(self: *Trees, node: NodeId, name: NamePool.Index) ?NodeId {
    const tree = self.owning_interpreter().owning_resolver().tree;
    const subject_node = subject(tree, node);
    const declared = def_var(tree, node);
    const parameter = if (is_parameter(tree.kind(node)))
        ParseTree.Param.from_node(tree, node)
    else
        ParseTree.Param{};

    const found: NodeId = switch (name) {
        .name => name_view(tree, node, declared, parameter),
        .type => if (declared != 0) tree.arg(declared, 0) else parameter.ty,
        .assigned => if (subject_node != node) subject_node else 0,
        .defval => parameter.default,
        .guard => parameter.where,
        .body => if (tree.kind(subject_node) == .def_fun) tree.arg(subject_node, 1) else 0,
        .rettype => return_type_view(tree, subject_node),
        else => 0,
    };
    const child = if (found == 0) self.field_view(node, name) else found;
    return if (child == 0) null else child;
}

fn name_view(
    tree: *const ParseTree,
    node: NodeId,
    declared: NodeId,
    parameter: ParseTree.Param,
) NodeId {
    if (declared != 0) return tree.arg(declared, 1);
    if (tree.kind(node) == .assign) return tree.arg(node, 0);
    if (is_parameter(tree.kind(node))) return parameter.name;

    var bare = node;
    while (true) {
        const kind = tree.kind(bare);
        const wrapped = kind == .partial__variant_def_param_typed or
            kind == .partial__variant_def_param_tagged;
        if (!wrapped) break;
        bare = tree.arg(bare, 0);
    }
    return if (tree.kind(bare) == .partial__variant_def_param) tree.arg(bare, 0) else 0;
}

fn return_type_view(tree: *const ParseTree, subject_node: NodeId) NodeId {
    if (tree.kind(subject_node) != .def_fun) return 0;
    const header = tree.arg(subject_node, 0);
    if (tree.kind(header) != .partial__fun_def_header_ret) return 0;
    return tree.arg(header, 1);
}

// any other name is a field of the node's kind (`x.cond`)
fn field_view(self: *Trees, node: NodeId, name: NamePool.Index) NodeId {
    const resolver = self.owning_interpreter().owning_resolver();
    const tree = resolver.tree;
    const kind = tree.kind(node);
    const fields = ParseTree.Node.nk_field_names[@backingInt(kind)];
    // the named children of a node: those in its two slots
    const field_count: usize = switch (arity(kind)) {
        .one => 1,
        .two => 2,
        .none, .data, .many => 0,
    };

    for (0..field_count) |i| {
        if (std.mem.eql(u8, fields[i], resolver.name_pool.text_of(name))) {
            return tree.arg(node, @intCast(i));
        }
    }
    return 0;
}

// the list node a list view of `node` is; a type without one grows it when written
fn list(self: *Trees, node: NodeId, name: NamePool.Index, grow: bool) ?NodeId {
    const tree = self.owning_interpreter().owning_resolver().tree;
    const subject_node = subject(tree, node);
    switch (name) {
        .decls => return if (tree.kind(node) == .block) node else null,
        .params => {
            if (tree.kind(subject_node) != .def_fun) return null;
            return tree.arg(tree.arg(subject_node, 0), 0);
        },
        .fields, .cases => return member_list(tree, subject_node, name),
        .methods, .traits => return self.trait_list(subject_node, name, grow),
        else => return null,
    }
}

// `.fields` of a record, `.cases` of a variant
fn member_list(tree: *const ParseTree, subject_node: NodeId, name: NamePool.Index) ?NodeId {
    const core = ParseTree.Def.from_node(tree, subject_node).core;
    const wanted: Kind = if (name == .fields)
        .partial__type_def_param_tuple
    else
        .partial__variant_def_param_tuple;
    if (tree.kind(tree.arg(core, 0)) != wanted) return null;

    const core_kind = tree.kind(core);
    const defines_type = core_kind == .def_type or
        core_kind == .def_type_packed or
        core_kind == .def_variant or
        core_kind == .def_variant_packed;
    return if (defines_type) tree.arg(core, 0) else null;
}

// `.methods` and `.traits` of a trait or of the trait part of a type
fn trait_list(self: *Trees, subject_node: NodeId, name: NamePool.Index, grow: bool) ?NodeId {
    const resolver = self.owning_interpreter().owning_resolver();
    const tree = resolver.tree;
    const subject_kind = tree.kind(subject_node);

    const is_trait = subject_kind == .def_trait or subject_kind == .def_trait_implof;
    var trait = if (is_trait) subject_node else ParseTree.Def.from_node(tree, subject_node).body;
    if (trait == 0) {
        if (resolver.declarations.declared_type_kind(subject_node) == .variable) return null;
        // read, a type without `!{}` has no methods and implements nothing
        if (!grow) {
            if (name == .methods) return tree.push_node(.partial__trait_def_body);
            return tree.push_node(.partial__trait_def_implof_tuple);
        }

        // the type moves into one with an empty `!{}`
        const inner = tree.push_node(tree.kind(subject_node));
        tree.ast_nodes.column(.args)[inner] = tree.ast_nodes.column(.args)[subject_node];
        const empty_body = tree.push_node(.partial__trait_def_body);
        trait = tree.push_node_with(.def_trait, .{ .body = empty_body });

        const is_variant = resolver.declarations.declared_type_kind(subject_node) == .variant;
        const wrapper = tree.push_node(if (is_variant) .def_variant_implof else .def_type_implof);
        tree.ast_nodes.column(.args)[wrapper] = .{ inner, trait };
        tree.overwrite(subject_node, wrapper);
    }

    // the methods of a `def_trait_implof` are its second child
    const has_implof = tree.kind(trait) == .def_trait_implof;
    if (name == .methods) return tree.arg(trait, @intFromBool(has_implof));
    if (has_implof) return tree.arg(trait, 0);
    if (!grow) return tree.push_node(.partial__trait_def_implof_tuple);

    // a trait without an `implof` list becomes a `def_trait_implof` with an empty one
    const tuple = tree.push_node(.partial__trait_def_implof_tuple);
    const body = tree.arg(trait, 0);
    tree.ast_nodes.column(.nk)[trait] = .def_trait_implof;
    tree.ast_nodes.column(.args)[trait] = .{ tuple, body };
    return tuple;
}

// `x.name`, `x.cond`: a view or child of `x`, `x.src` its text, list views as `[]ast`
pub fn member(self: *Trees, node: NodeId, base: Value) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;

    const root = self.node_of(base).?;
    const name = resolver.name_pool.name_of_node(tree.arg(node, 1));
    const member_type = self.type_at(node);
    switch (name) {
        .src => return .pooled(resolver.static_pool.intern(.{ .string_value = self.src_of(root) })),
        .ismut => {
            const kind = tree.kind(root);
            return .boolean(is_parameter(kind) and ParseTree.Param.from_node(tree, root).is_mut);
        },
        .children, .decls, .fields, .cases, .methods, .params, .traits => {
            const static_pool = &resolver.static_pool;
            const children = if (name == .children) tree.children(root) else blk: {
                const list_node = self.list(root, name, false) orelse {
                    return interpreter.fail(node, .unknown_member, name, .ast_type);
                };
                break :blk tree.manychildren(list_node);
            };

            const mark = interpreter.pool_indices.len;
            defer interpreter.pool_indices.len = mark;
            for (children) |child| {
                if (child == 0) continue;
                const element_type = static_pool.array_element(member_type);
                interpreter.pool_indices.push(self.tree_value(element_type, child).index());
            }
            return .pooled(static_pool.intern(.{ .aggregate_value = .{
                .value_type = member_type,
                .elements = interpreter.pool_indices.buffer[mark..interpreter.pool_indices.len],
            } }));
        },
        else => {
            const viewed = self.view(root, name) orelse {
                return interpreter.fail(node, .unknown_member, name, .ast_type);
            };
            return self.tree_value(member_type, viewed);
        },
    }
}

// the source a tree was written as, a made name its text, a keyword (`u32`, `true`) itself
fn src_of(self: *Trees, root: NodeId) []const u8 {
    const resolver = self.owning_interpreter().owning_resolver();
    const tree = resolver.tree;
    const kind = tree.kind(root);
    if (arity(kind) == .data) return tree.text(root, resolver.src_bytes);

    var bounds: [2]u32 = .{ std.math.maxInt(u32), 0 };
    token_bounds(tree, root, &bounds);
    if (bounds[0] > bounds[1]) {
        switch (kind) {
            .boolean_true => return "true",
            .boolean_false => return "false",
            .identifier_self => return "self",
            else => {},
        }

        const value = @backingInt(kind);
        const is_type_keyword = value >= @backingInt(Kind.type_u8) and
            value <= @backingInt(Kind.type_stcfun);
        if (!is_type_keyword) return "";
        return @tagName(kind)["type_".len..];
    }

    const spans = tree.span_store;
    var first, var last = bounds;
    var leading = root;
    while (leading != 0) : (leading = edge_child(tree, leading, 0)) {
        for (0..operator_tokens.get(tree.kind(leading))[0]) |_| {
            if (first > 0) first -= 1;
            while (first > 0 and self.token_is(first, "(")) first -= 1;
        }
    }
    var trailing = root;
    while (trailing != 0) : (trailing = edge_child(tree, trailing, 1)) {
        for (0..operator_tokens.get(tree.kind(trailing))[1]) |_| {
            if (last + 1 < spans.len) last += 1;
            while (last + 1 < spans.len and self.token_is(last, ")")) last += 1;
        }
    }

    var depth: i32 = 0;
    var lowest: i32 = 0;
    for (first..last + 1) |token| {
        depth += self.bracket(token);
        lowest = @min(lowest, depth);
    }
    while (lowest < 0 and first > 0 and self.bracket(first - 1) > 0) : (lowest += 1) first -= 1;
    depth -= lowest;
    while (depth > 0 and last + 1 < spans.len and self.bracket(last + 1) < 0) : (depth -= 1) {
        last += 1;
    }
    return resolver.src_bytes[spans[first][0]..spans[last][1]];
}

const operator_tokens = std.EnumArray(Kind, [2]u8).initDefault(.{ 0, 0 }, .{
    .neg_num = .{ 1, 0 },
    .neg_logic = .{ 1, 0 },
    .inc_prefix = .{ 1, 0 },
    .dec_prefix = .{ 1, 0 },
    .sizeof = .{ 1, 0 },
    .alignof = .{ 1, 0 },
    .lenof = .{ 1, 0 },
    .tagof = .{ 1, 0 },
    .typeof = .{ 1, 0 },
    .if_then = .{ 1, 0 },
    .stcif_then = .{ 1, 0 },
    .@"while" = .{ 1, 0 },
    .stcwhile = .{ 1, 0 },
    .for_seq = .{ 1, 0 },
    .stcfor_seq = .{ 1, 0 },
    .match = .{ 1, 0 },
    .stcmatch = .{ 1, 0 },
    .type_ptr = .{ 1, 0 },
    .type_ptrmut = .{ 1, 0 },
    .type_array_unlengthed = .{ 2, 0 },
    .type_slice = .{ 3, 0 },
    .array = .{ 1, 0 },
    .refl = .{ 1, 0 },
    .unquote = .{ 1, 0 },
    .unquote_list = .{ 2, 0 },
    .splice = .{ 1, 1 },
    .dereference = .{ 0, 1 },
    .address_of = .{ 0, 1 },
    .inc_postfix = .{ 0, 1 },
    .dec_postfix = .{ 0, 1 },
});

fn token_bounds(tree: *const ParseTree, node: NodeId, bounds: *[2]u32) void {
    if (tree.token(node)) |token| {
        bounds.* = .{ @min(bounds[0], token), @max(bounds[1], token) };
        return;
    }
    for (tree.children(node)) |child| {
        if (child != 0) token_bounds(tree, child, bounds);
    }
}

fn edge_child(tree: *const ParseTree, node: NodeId, side: u1) NodeId {
    const children = tree.children(node);
    if (children.len == 0) return 0;
    if (side == 0) return if (children[0] != 0) children[0] else children[children.len - 1];
    return if (children[children.len - 1] != 0) children[children.len - 1] else children[0];
}

fn token_text(self: *Trees, token: usize) []const u8 {
    const resolver = self.owning_interpreter().owning_resolver();
    const bytes = resolver.src_bytes;
    const span = resolver.tree.span_store[token];
    const quoted = span[0] > 0 and span[1] < bytes.len and
        (bytes[span[0] - 1] == '"' or bytes[span[0] - 1] == '\'') and
        bytes[span[1]] == bytes[span[0] - 1];
    return if (quoted) "" else bytes[span[0]..span[1]];
}

fn token_is(self: *Trees, token: usize, text: []const u8) bool {
    return std.mem.eql(u8, self.token_text(token), text);
}

fn bracket(self: *Trees, token: usize) i32 {
    const text = self.token_text(token);
    if (text.len == 0) return 0;
    if (std.mem.indexOfScalar(u8, "([{", text[text.len - 1]) != null) return 1;
    if (text.len == 1 and std.mem.indexOfScalar(u8, ")]}", text[0]) != null) return -1;
    return 0;
}

// `ast.Identifier`: the type of trees of that root
pub fn case(self: *Trees, node: NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const name = resolver.name_pool.name_of_node(resolver.tree.arg(node, 1));
    const kind = ParseTree.Node.named.get(resolver.name_pool.text_of(name)) orelse {
        return interpreter.fail(node, .unknown_member, name, .ast_type);
    };
    return .pooled(resolver.static_pool.ast_type_of(.none, root_kind_code(kind)));
}

// `x.v = y`, `x.* = y`, `x.decls[i] = y` make the node there a landed copy of `y`
// false when the place is no tree place
pub fn write(self: *Trees, node: NodeId, value: Value) bool {
    const interpreter = self.owning_interpreter();
    const tree = interpreter.owning_resolver().tree;
    const kind = tree.kind(node);
    if (kind != .member and kind != .dereference and kind != .array_index) return false;

    const base = tree.arg(node, 0);
    // a tree place is in a tree, or for `x.decls[i]` in a list view of the tree `x`
    const static_pool = &interpreter.owning_resolver().static_pool;
    const is_tree_place = static_pool.is_tree(interpreter.checked_type(base)) or
        (kind == .array_index and
            tree.kind(base) == .member and
            static_pool.is_tree(interpreter.checked_type(tree.arg(base, 0))));
    if (!is_tree_place) return false;

    var into: Kind = .none;
    const source = self.node_of(value);
    const target: ?NodeId = if (source == null) null else switch (kind) {
        .dereference => self.node_of(interpreter.evaluate(base)),
        .member => self.member_target(node, base),
        .array_index => self.element_target(node, base, &into),
        else => unreachable,
    };
    if (target == ParseTree.none_node) return true;
    if (target == null or source == null) {
        if (!value.is(.poison_type)) _ = interpreter.fail(node, .not_static, 0, 0);
        return true;
    }

    if (self.writable(node, target.?)) tree.overwrite(target.?, self.land(source.?, into));
    return true;
}

fn member_target(self: *Trees, node: NodeId, base: NodeId) ?NodeId {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const root = self.node_of(interpreter.evaluate(base)) orelse return null;
    const name = resolver.name_pool.name_of_node(resolver.tree.arg(node, 1));
    return self.view(root, name) orelse self.grown_view(node, root, name);
}

fn grown_view(self: *Trees, at: NodeId, root: NodeId, name: NamePool.Index) ?NodeId {
    const tree = self.owning_interpreter().owning_resolver().tree;
    const kind = tree.kind(root);
    const of_function = @backingInt(kind) <= @backingInt(Kind.partial__fun_def_param_where_else);
    const slot: Kind = switch (name) {
        .defval => if (of_function)
            .partial__fun_def_param_default
        else
            .partial__type_def_param_default,
        .guard => if (of_function)
            .partial__fun_def_param_where
        else
            .partial__type_def_param_where,
        .rettype => {
            const function = subject(tree, root);
            if (tree.kind(function) != .def_fun) return null;
            const header = tree.arg(function, 0);
            if (tree.kind(header) != .partial__fun_def_header) return null;
            if (!self.writable(at, root)) return ParseTree.none_node;

            const placeholder = tree.push_node(.none);
            tree.ast_nodes.column(.nk)[header] = .partial__fun_def_header_ret;
            tree.ast_nodes.column(.args)[header] = .{ tree.arg(header, 0), placeholder };
            return placeholder;
        },
        else => return null,
    };
    if (!is_parameter(kind)) return null;
    if (!self.writable(at, root)) return ParseTree.none_node;

    const inner = tree.push_node(kind);
    tree.ast_nodes.column(.args)[inner] = tree.ast_nodes.column(.args)[root];
    const placeholder = tree.push_node(.none);
    const wrapper = tree.push_node(slot);
    tree.ast_nodes.column(.args)[wrapper] = .{ inner, placeholder };
    tree.overwrite(root, wrapper);
    return placeholder;
}

fn element_target(self: *Trees, node: NodeId, base: NodeId, into: *Kind) ?NodeId {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;

    const root = self.node_of(interpreter.evaluate(tree.arg(base, 0))) orelse return null;
    const name = resolver.name_pool.name_of_node(tree.arg(base, 1));
    const list_node = self.list(root, name, false) orelse return null;
    const index = interpreter.evaluate(tree.arg(node, 1));
    into.* = tree.kind(list_node);

    if (!Value.is_int(index.value_type)) return null;
    const length = tree.arg(list_node, 1);
    if (index.bits >= length) {
        // like indexing an array: the index is out of range, not unknown
        _ = interpreter.fail(node, .static_eval_failed, interpreter.interned(index), length);
        return null;
    }
    return tree.manychildren(list_node)[@intCast(index.bits)];
}

// `xs += y` of trees: y (or each tree of it) appended to a list view or a `[]ast` variable
// null when `xs` is no list of trees
pub fn append(self: *Trees, node: NodeId) ?Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const static_pool = &resolver.static_pool;
    const tree = resolver.tree;
    const target = tree.arg(node, 0);

    const list_type = static_pool.substitute_type_variables(interpreter.checked_type(target));
    if (list_type == .none or static_pool.tag(list_type) != .array_type) return null;
    if (!static_pool.is_tree(static_pool.get(list_type).array_type.element)) return null;

    const value = interpreter.evaluate(tree.arg(node, 1));
    if (value.is(.poison_type)) return value;

    const mark = interpreter.pool_indices.len;
    defer interpreter.pool_indices.len = mark;
    // a tree is one item, a list of trees each of its elements
    if (self.node_of(value) != null) {
        interpreter.pool_indices.push(value.index());
    } else {
        for (0..interpreter.aggregate_length(value) orelse 0) |i| {
            const element = interpreter.element(value, @intCast(i));
            interpreter.pool_indices.push(interpreter.interned(element));
        }
    }

    const appends_to_view = tree.kind(target) == .member and
        static_pool.is_tree(interpreter.checked_type(tree.arg(target, 0)));
    if (appends_to_view) {
        const root = self.node_of(interpreter.evaluate(tree.arg(target, 0))) orelse return .poison;
        const name = resolver.name_pool.name_of_node(tree.arg(target, 1));
        const list_node = self.list(root, name, true) orelse {
            return interpreter.fail(target, .unknown_member, name, .ast_type);
        };
        if (!self.writable(node, list_node)) return .poison;

        const items = resolver.temporary_slice(NodeId, interpreter.pool_indices.len - mark);
        for (interpreter.pool_indices.items()[mark..], 0..) |tree_index, i| {
            const appended = resolver.static_pool.get(tree_index).tree_value.node;
            items[i] = self.land(appended, tree.kind(list_node));
        }
        tree.grow_list(list_node, items);
        return .unit;
    }

    const cell = interpreter.variables.cell_of_place(target) orelse return .poison;
    const old = interpreter.memory.buffer[cell];
    const old_length = interpreter.aggregate_length(old) orelse 0;
    const added = interpreter.pool_indices.len - mark;

    const start = interpreter.allocate_cells(old_length + added);
    for (0..old_length) |i| {
        interpreter.memory.buffer[start + i] = interpreter.element(old, @intCast(i));
    }
    for (interpreter.pool_indices.items()[mark..], old_length..) |tree_index, i| {
        const owned = interpreter.owned_copy(.pooled(tree_index));
        interpreter.memory.buffer[start + i] = owned;
    }
    interpreter.store_cell(cell, .block(list_type, start, old_length + added));
    return .unit;
}

// the program is written while a splice is evaluated, a declaration until it is resolved
// what macros made is theirs to write
fn writable(self: *Trees, at: NodeId, target: NodeId) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const is_file = target == resolver.macros.file;
    if (target >= resolver.macros.pass_len and !is_file) return true;

    const root = if (is_file) 0 else resolver.macros.root_of(target);
    const declaration = if (root == 0) .none else resolver.node_declarations[root];
    const open = resolver.macros.splicing > 0 and (declaration == .none or
        resolver.decl_pool.get(declaration, .state) == .unresolved);
    if (open) {
        resolver.macros.edited = true;
        return true;
    }

    _ = interpreter.fail(at, .frozen_declaration, declaration, 0);
    return false;
}

// `x.&` of a tree: a `*ast` to it, `p.*` of one: the tree
pub fn address(self: *Trees, node: NodeId) ?Value {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;
    const operand = interpreter.owning_resolver().tree.arg(node, 0);
    if (!static_pool.is_tree(interpreter.checked_type(operand))) return null;
    if (static_pool.is_pointer(interpreter.checked_type(operand))) return null;

    const value = interpreter.evaluate(operand);
    const pointer_type = self.type_at(node);
    const root = self.node_of(value) orelse return value;
    return self.tree_value(pointer_type, root);
}

// `x with (lhs = y)`, `x with (rhs.lhs = y)`: a copy of x with the named child replaced, and of
// each node on the way to it
pub fn with(self: *Trees, node: NodeId, base: Value) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;

    var updated = self.node_of(base).?;
    const arguments = tree.arg(node, 1);
    // by index: evaluating an argument may grow the tree and move its child lists
    for (0..tree.manychildren(arguments).len) |argument_index| {
        const argument = tree.manychildren(arguments)[argument_index];
        const value = interpreter.evaluate(tree.arg_value(argument));
        var child = self.node_of(value) orelse {
            if (value.is(.poison_type)) return value;
            const value_type = interpreter.value_type(value);
            return interpreter.fail(argument, .type_mismatch, value_type, .ast_type);
        };

        // the names of the path from the root on, the nodes it passes and the slots it takes
        var names: [16]NodeId = undefined;
        var depth: usize = 0;
        var step = tree.arg_name(argument);
        while (tree.kind(step) == .member and depth + 1 < names.len) : (step = tree.arg(step, 0)) {
            names[depth] = tree.arg(step, 1);
            depth += 1;
        }
        names[depth] = step;
        depth += 1;
        std.mem.reverse(NodeId, names[0..depth]);
        var passed: [16]NodeId = undefined;
        var slots: [16]u1 = undefined;
        passed[0] = updated;
        for (names[0..depth], 0..) |name, i| {
            // the named children of a node: those in its two slots
            const kind = tree.kind(passed[i]);
            const fields = ParseTree.Node.nk_field_names[@backingInt(kind)];
            const field_count: usize = switch (arity(kind)) {
                .one => 1,
                .two => 2,
                .none, .data, .many => 0,
            };
            const is_name = tree.kind(name) == .identifier;
            const names_pool = &resolver.name_pool;
            const text = if (is_name) names_pool.text_of(names_pool.name_of_node(name)) else "";
            slots[i] = for (fields[0..field_count], 0..) |field, slot| {
                if (is_name and std.mem.eql(u8, field, text)) break @intCast(slot);
            } else {
                const tree_kind = self.kind_of(interpreter.interned(base));
                const shown_name = resolver.name_pool.name_of_node(name);
                return interpreter.fail(argument, .unknown_named_argument, shown_name, tree_kind);
            };
            if (i + 1 < depth) passed[i + 1] = tree.arg(passed[i], slots[i]);
        }
        // copies from the innermost node out, each holding the one below
        var i = depth;
        while (i > 0) {
            i -= 1;
            const copy = tree.push_node(tree.kind(passed[i]));
            var children: [2]NodeId = tree.ast_nodes.column(.args)[passed[i]];
            children[slots[i]] = child;
            tree.ast_nodes.column(.args)[copy] = children;
            child = copy;
        }
        updated = child;
    }
    return self.tree_value(resolver.static_pool.pointee(interpreter.value_type(base)), updated);
}

// `ast(T)`, `ast.Kind(..)` making a node from its children or a name or literal from its text
pub fn call(self: *Trees, node: NodeId, target: Index, arguments: []const NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;

    const ast_type = resolver.static_pool.get(target).ast_type;
    // `ast(T)`: the type of trees producing T, `ast(())` of code producing nothing
    if (ast_type.root_kind == 0) {
        const code = tree.arg_value(arguments[0]);
        const produces_nothing = tree.kind(code) == .def_fun_declaration and
            tree.params_of(code).len == 0;
        if (produces_nothing) return .pooled(resolver.static_pool.ast_type_of(.unit_type, 0));

        const produced = interpreter.types.type_of_node(code) orelse return .poison;
        return .pooled(resolver.static_pool.ast_type_of(produced, 0));
    }

    const kind: Kind = @fromBackingInt(@intCast(ast_type.root_kind - 1));
    const mark = interpreter.pool_indices.len;
    defer interpreter.pool_indices.len = mark;
    // read anew per argument: `arguments` lists the call's children, and evaluating may grow the
    // tree and move them
    for (0..arguments.len) |i| {
        const argument = tree.manychildren(tree.arg(node, 1))[i];
        const value = interpreter.evaluate(tree.arg_value(argument));
        if (value.is(.poison_type)) return value;
        interpreter.pool_indices.push(interpreter.interned(value));
    }

    const values = interpreter.pool_indices.buffer[mark..interpreter.pool_indices.len];
    const made = switch (arity(kind)) {
        .none => tree.push_node(kind),
        .data => self.made_word(node, kind, values[0]) orelse return .poison,
        .one, .two, .many => self.made_node(node, kind, values) orelse return .poison,
    };
    return self.tree_value(target, made);
}

fn made_word(self: *Trees, node: NodeId, kind: Kind, text_index: Index) ?NodeId {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const token = resolver.tree.first_token(node);
    const text = self.text_of(.pooled(text_index)) orelse {
        const text_type = resolver.static_pool.type_of(text_index);
        _ = interpreter.fail(node, .type_mismatch, text_type, .ast_type);
        return null;
    };
    return resolver.tree.push_word(kind, token, text, 0, false);
}

fn made_node(self: *Trees, node: NodeId, kind: Kind, values: []const Index) ?NodeId {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;

    const children = resolver.temporary_slice(NodeId, values.len);
    for (values, children) |value, *child| {
        child.* = self.node_of(.pooled(value)) orelse {
            const value_type = resolver.static_pool.type_of(value);
            _ = interpreter.fail(node, .type_mismatch, value_type, .ast_type);
            return null;
        };
    }

    const made = tree.push_node(kind);
    if (arity(kind) == .many) {
        tree.set_children(made, children);
    } else {
        const second = if (children.len > 1) children[1] else 0;
        tree.ast_nodes.column(.args)[made] = .{ children[0], second };
    }
    return made;
}

// `fresh "tmp"`: a name like no other, `crash (tree, "..")` ends evaluating with an error there
pub fn builtin(self: *Trees, node: NodeId, name: NamePool.Index, arguments: []const NodeId) Value {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;

    // taken before evaluating: evaluation may grow the tree and move the argument list
    const second_argument = if (arguments.len > 1) arguments[1] else 0;
    const first = interpreter.evaluate(tree.arg_value(arguments[0]));
    if (first.is(.poison_type)) return first;
    if (name == .fresh) {
        const session = &resolver.session;
        const stem_text = self.text_of(first) orelse "";
        const counter = session.fresh_name_count;
        const arena = resolver.temporary_arena.allocator();
        const fresh = std.fmt.allocPrint(arena, "{s}`{d}", .{ stem_text, counter }) catch
            @panic("OOM");
        session.fresh_name_count += 1;

        const identifier_type =
            resolver.static_pool.ast_type_of(.none, root_kind_code(.identifier));
        const token = tree.first_token(node);
        const identifier = tree.push_word(.identifier, token, fresh, 0, false);
        return self.tree_value(identifier_type, identifier);
    }

    const message = interpreter.evaluate(tree.arg_value(second_argument));
    if (message.is(.poison_type)) return message;

    const at = self.node_of(first) orelse return .poison;
    const text = resolver.name_pool.intern_copy(self.text_of(message) orelse return .poison);
    resolver.doctor.report(.crash, at, text, 0);
    return .poison;
}

// a tree for a parameter `ast.Kind` (or each of a list for `[]ast.Kind`) has a root of that kind
pub fn admits(self: *Trees, value: Value, parameter_type: Index) bool {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;
    if (!static_pool.contains_trees(parameter_type)) return true;

    const element_type = static_pool.array_element(parameter_type);
    if (element_type != .none) {
        for (0..interpreter.aggregate_length(value) orelse 0) |i| {
            if (!self.admits(interpreter.element(value, @intCast(i)), element_type)) return false;
        }
        return true;
    }

    const tree_type = static_pool.pointee(parameter_type);
    if (tree_type == .none or static_pool.tag(tree_type) != .ast_type) return true;
    const root_kind = static_pool.get(tree_type).ast_type.root_kind;
    if (root_kind == 0) return true;

    const root = self.node_of(value) orelse return true;
    return root_kind_code(interpreter.owning_resolver().tree.kind(root)) == root_kind;
}

pub fn rejection(self: *Trees, value: Value, parameter_type: Index) [2]Index {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;
    const element_type = static_pool.array_element(parameter_type);
    if (element_type != .none and static_pool.contains_trees(element_type)) {
        for (0..interpreter.aggregate_length(value) orelse 0) |i| {
            const element = interpreter.element(value, @intCast(i));
            if (!self.admits(element, element_type)) return self.rejection(element, element_type);
        }
    }
    return .{ self.kind_of(interpreter.interned(value)), parameter_type };
}

// the type of trees of the root of a tree value (`ast.BinaryAdd`), for what is reported
pub fn kind_of(self: *Trees, value: Index) Index {
    const resolver = self.owning_interpreter().owning_resolver();
    const static_pool = &resolver.static_pool;
    if (static_pool.tag(value) != .tree_value) return static_pool.type_of(value);

    const root = static_pool.get(value).tree_value.node;
    return static_pool.ast_type_of(.none, root_kind_code(resolver.tree.kind(root)));
}

// `x oftype ast(fun)`: the root makes what the type says (a function, a type), `ast.Kind` its kind
pub fn has_type(self: *Trees, root: NodeId, tested: Index) bool {
    const resolver = self.owning_interpreter().owning_resolver();
    const static_pool = &resolver.static_pool;
    if (static_pool.tag(tested) != .ast_type) return false;

    const ast_type = static_pool.get(tested).ast_type;
    if (ast_type.root_kind != 0) {
        return root_kind_code(resolver.tree.kind(root)) == ast_type.root_kind;
    }
    if (ast_type.produces == .none) return true;

    // what a declaration makes: a function, a type, a variant or a trait, none for a variable
    const made_type: Index = blk: {
        const tree = resolver.tree;
        const declared = def_var(tree, root);
        const subject_node = subject(tree, root);

        if (declared != 0) break :blk switch (tree.kind(tree.arg(declared, 0))) {
            .type_fun, .type_stcfun, .type_inlfun => .fun_type,
            .type_type => .type_type,
            .type_variant => .variant_type,
            .type_trait => .trait_type,
            else => .none,
        };
        if (tree.kind(subject_node) == .def_fun) break :blk .fun_type;
        break :blk switch (resolver.declarations.declared_type_kind(subject_node)) {
            .variable => .none,
            else => |kind| kind.meta_type(.type_type),
        };
    };
    return made_type == ast_type.produces;
}

// a tree against a pattern: a name takes it, `ast.Kind(..)` tests root and children, a quote shape
pub fn matches(self: *Trees, pattern: NodeId, value: Value) bool {
    const interpreter = self.owning_interpreter();
    const tree = interpreter.owning_resolver().tree;
    const root = self.node_of(value).?;

    switch (tree.kind(pattern)) {
        .identifier => {
            interpreter.patterns.bind_name(pattern, value);
            return true;
        },
        .partial__match_case_pattern_or => {
            for (tree.manychildren(pattern)) |alternative| {
                if (self.matches(alternative, value)) return true;
            }
            return false;
        },
        .partial__match_case_where => {
            if (!self.matches(tree.arg(pattern, 0), value)) return false;
            const holds = interpreter.evaluate(tree.arg(pattern, 1));
            return holds.value_type == .bool_type and holds.bits != 0;
        },
        .quote => return self.shape(tree.arg(pattern, 0), root),
        .fun_call => return self.matches_children(pattern, root),
        else => return self.matches_tree_type(pattern, root),
    }
}

// `ast.Kind(a, lhs = b)`: the root's kind, then its children by position or by field name
inline fn matches_children(self: *Trees, pattern: NodeId, root: NodeId) bool {
    const interpreter = self.owning_interpreter();
    const tree = interpreter.owning_resolver().tree;

    const checked_target = interpreter.node_info(.node_type, pattern);
    const target = if (checked_target != .none)
        checked_target
    else
        interpreter.interned(interpreter.evaluate(tree.arg(pattern, 0)));
    if (!self.has_type(root, target)) return false;

    const arguments = tree.arg(pattern, 1);
    // by index and anew per child: matching may evaluate, which grows the tree and moves lists
    for (0..tree.manychildren(arguments).len) |i| {
        const argument = tree.manychildren(arguments)[i];
        const position: usize = blk: {
            if (tree.arg_name(argument) == 0) break :blk i;

            const name_pool = &interpreter.owning_resolver().name_pool;
            const fields = ParseTree.Node.nk_field_names[@backingInt(tree.kind(root))];
            for (fields, 0..) |field, j| {
                const name_index = name_pool.name_of_node(tree.arg_name(argument));
                const name = name_pool.text_of(name_index);
                if (std.mem.eql(u8, field, name)) break :blk j;
            }
            return false;
        };
        const children = tree.children(root);
        if (position >= children.len) return false;

        const child = self.tree_value(.ast_type, children[position]);
        if (!self.matches(tree.arg_value(argument), child)) return false;
    }
    return true;
}

// any other pattern is a tree type (`ast.Kind`, `ast(fun)`) the root has
inline fn matches_tree_type(self: *Trees, pattern: NodeId, root: NodeId) bool {
    const interpreter = self.owning_interpreter();
    const static_pool = &interpreter.owning_resolver().static_pool;
    const expected = interpreter.evaluate(pattern);
    const is_tree_type = expected.is_pooled() and
        !expected.is(.none) and
        static_pool.tag(expected.index()) == .ast_type;
    return is_tree_type and self.has_type(root, expected.index());
}

// a quote pattern: holes take the trees where they stand (`@..xs` a list's rest), the rest is equal
fn shape(self: *Trees, written_pattern: NodeId, written_code: NodeId) bool {
    const interpreter = self.owning_interpreter();
    const resolver = interpreter.owning_resolver();
    const tree = resolver.tree;

    var pattern = written_pattern;
    var code = written_code;
    while (tree.kind(pattern) == .capture) pattern = tree.arg(pattern, 0);
    while (tree.kind(code) == .capture) code = tree.arg(code, 0);

    if (tree.kind(pattern) == .unquote) {
        interpreter.patterns.bind_name(tree.arg(pattern, 0), self.tree_value(.ast_type, code));
        return true;
    }
    if (tree.kind(pattern) != tree.kind(code)) return false;

    switch (arity(tree.kind(pattern))) {
        .none => return true,
        .data => {
            const pattern_text = tree.text(pattern, resolver.src_bytes);
            return std.mem.eql(u8, pattern_text, tree.text(code, resolver.src_bytes));
        },
        .one => return self.shape(tree.arg(pattern, 0), tree.arg(code, 0)),
        .two => return self.shape_pair(pattern, code),
        .many => return self.shape_list(pattern, code),
    }
}

// an optional first child is absent in both or of the same shape
inline fn shape_pair(self: *Trees, pattern: NodeId, code: NodeId) bool {
    const tree = self.owning_interpreter().owning_resolver().tree;
    const pattern_first = tree.arg(pattern, 0);
    const code_first = tree.arg(code, 0);

    if ((pattern_first == 0) != (code_first == 0)) return false;
    if (pattern_first != 0 and !self.shape(pattern_first, code_first)) return false;
    return self.shape(tree.arg(pattern, 1), tree.arg(code, 1));
}

inline fn shape_list(self: *Trees, pattern: NodeId, code: NodeId) bool {
    const tree = self.owning_interpreter().owning_resolver().tree;
    const pattern_items = tree.manychildren(pattern);
    const code_items = tree.manychildren(code);
    const rest_at = for (pattern_items, 0..) |item, i| {
        if (tree.kind(item) == .unquote_list) break i;
    } else pattern_items.len;
    const fixed_count = pattern_items.len - @intFromBool(rest_at < pattern_items.len);
    if (code_items.len < fixed_count) return false;
    if (rest_at == pattern_items.len and code_items.len != fixed_count) return false;
    const rest_count = code_items.len - fixed_count;

    for (pattern_items, 0..) |item, i| {
        // `@..xs` takes the items between those before and after it as a `[]ast`
        if (i == rest_at) {
            const interpreter = self.owning_interpreter();
            const static_pool = &interpreter.owning_resolver().static_pool;
            const binder = tree.arg(item, 0);
            const rest = code_items[i..][0..rest_count];

            const mark = interpreter.pool_indices.len;
            defer interpreter.pool_indices.len = mark;
            for (rest) |rest_item| {
                interpreter.pool_indices.push(self.tree_value(.ast_type, rest_item).index());
            }

            const list_type = static_pool.intern(.{
                .array_type = .{ .length = StaticPool.dyn_len, .element = .ast_type },
            });
            const bound = static_pool.intern(.{ .aggregate_value = .{
                .value_type = list_type,
                .elements = interpreter.pool_indices.buffer[mark..interpreter.pool_indices.len],
            } });
            interpreter.patterns.bind_name(binder, .pooled(bound));
            continue;
        }
        const at = if (i > rest_at) i - 1 + rest_count else i;
        if (!self.shape(item, code_items[at])) return false;
    }
    return true;
}
