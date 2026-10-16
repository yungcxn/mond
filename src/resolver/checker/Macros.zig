const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const NamePool = @import("../NamePool.zig");
const Declarations = @import("Declarations.zig");
const DeclPool = @import("../DeclPool.zig");
const FunctionContext = Resolver.FunctionContext;
const NodeId = ParseTree.NodeId;
const Index = StaticPool.Index;

// macros: code as a value (`quote`), put back as code (`<x>`), the program read and written
// (`refl`), other files (`include`); trees are `ast(T)` values run by interpreter/Trees.zig
const Macros = @This();

// a pass keeps each expansion in its splice node; one that expanded anything rebuilds the tree
// and resolving starts over, so the last pass compiles a program without a trace of macros
pub const max_passes = 64;

// nodes from here on were made in this pass
pass_len: NodeId,
// splices expanded in this pass
expanded: u32 = 0,
// declarations written in this pass
edited: bool = false,
// a splice failed in this pass, its errors end the pass
failed: bool = false,
// the splice evaluated last
last: NodeId = 0,
// the token of the splice evaluated now: landing code is written there, so its errors are at it
at: u32 = 0,
// the top splices run: quotes stay untyped, typing would resolve what the splices may still write
top: bool = false,
// a quote's code is checked for its type only
quoting: u32 = 0,
// a splice is evaluated, the only time the program may be written
splicing: u32 = 0,
// the node `refl $file` reads, made on demand
file: NodeId = 0,
// where the subtree of each root starts, made once a pass by the first write into the program
starts: []NodeId = &.{},

pub fn owning_resolver(self: *Macros) *Resolver {
    return @alignCast(@fieldParentPtr("macros", self));
}

// `@` outside the code of a quote has nothing to unquote (what an unquote takes is no code of it)
// reported before resolving: a name written with it (`a@b`, `x.@y`, `f(@x = 1)`) would read as none
pub fn report_stray_unquotes(self: *Macros, node: NodeId, quoted: bool) void {
    const resolver = self.owning_resolver();
    const kind = resolver.tree.kind(node);
    const is_unquote = kind == .unquote or kind == .unquote_list or kind == .paste;
    if (!quoted and is_unquote) {
        resolver.doctor.report(.stray_unquote, node, 0, 0);
        return;
    }

    const children_quoted = kind == .quote or
        quoted and kind != .unquote and kind != .unquote_list;
    for (resolver.tree.children(node)) |child| {
        if (child != 0) self.report_stray_unquotes(child, children_quoted);
    }
}

// the splices at the top run first and in order, before anything is resolved: a declaration may
// be written until it is resolved. true when there are any
pub fn expand_roots(self: *Macros) bool {
    const resolver = self.owning_resolver();
    var context = FunctionContext{};
    var any = false;
    self.top = true;
    defer self.top = false;
    for (resolver.roots) |root| {
        if (resolver.tree.kind(root) != .splice) continue;
        any = true;
        _ = resolver.expressions.infer(&context, root, .none);
    }
    return any;
}

pub fn infer(self: *Macros, context: *FunctionContext, node: NodeId, expected: Index) Index {
    const resolver = self.owning_resolver();
    return switch (resolver.tree.kind(node)) {
        .quote => self.infer_quote(context, node, expected),
        .splice => self.splice(context, node),
        .refl => self.refl(node),
        .include, .include_raw => self.infer_include(context, node),
        // a hole is typed by the quote around it, anywhere else it means nothing
        .unquote, .unquote_list, .paste => {
            if (self.quoting > 0) return resolver.node_types[node];
            return resolver.report(.stray_unquote, node, 0, 0);
        },
        // the construct table sends only macro kinds here
        else => unreachable,
    };
}

fn infer_quote(self: *Macros, context: *FunctionContext, node: NodeId, expected: Index) Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const body = resolver.tree.arg(node, 0);
    // the owner of the names the quote declares, for its hygiene
    resolver.node_declarations[node] = context.declaration;
    self.holes(context, body);

    const wanted = static_pool.substitute_type_variables(expected);
    const produces_hint = if (wanted != .none and static_pool.tag(wanted) == .ast_type)
        static_pool.get(wanted).ast_type.produces
    else
        .none;
    // what a quote's code produces as far as it is known where it is written: declarations by
    // their kind, statements nothing, an expression is checked with its holes as what they hold
    // none when that fails (a name only where it lands)
    const produced: Index = blk: {
        switch (resolver.tree.kind(body)) {
            .block => break :blk .unit_type,
            .def_fun => break :blk .fun_type,
            .partial__match_case => break :blk .none,
            else => {},
        }

        const declared_type_kind = resolver.declarations.declared_type_kind(body);
        if (declared_type_kind != .variable) break :blk declared_type_kind.meta_type(.type_type);
        if (resolver.tree.props(body).declares) {
            const kind = Declarations.Stmt.from_node(resolver, body).kind;
            break :blk switch (kind) {
                .variable => .unit_type,
                .record, .type_alias, .variant, .trait => kind.meta_type(.type_type),
                .parameter,
                .static_parameter,
                .field,
                .function,
                .static_function,
                .inlined_function,
                .variant_case,
                .trait_member,
                .pattern_binder,
                .arrow_binder,
                .loop_variable,
                .self,
                .autoins_arg,
                .autoins_it,
                => .fun_type,
            };
        }

        if (self.top or !self.typable(body)) break :blk .none;
        // the type is kept only when checking it reported nothing and left nothing open
        const mark = resolver.doctor.diagnostics.len();
        self.quoting += 1;
        resolver.scopes.open();
        const body_type = static_pool.substitute_type_variables(
            resolver.expressions.infer(context, body, produces_hint),
        );
        resolver.scopes.close();
        self.quoting -= 1;

        const is_known = resolver.doctor.diagnostics.len() == mark and
            body_type != .poison_type and
            !static_pool.has_type_variables(body_type);
        resolver.doctor.rewind(mark);
        break :blk if (is_known) body_type else .none;
    };
    return static_pool.ast_type_of(produced, 0);
}

fn infer_include(self: *Macros, context: *FunctionContext, node: NodeId) Index {
    const resolver = self.owning_resolver();
    const path = resolver.tree.arg(node, 0);
    if (resolver.tree.kind(path) == .string) return .ast_type;
    const path_type = resolver.expressions.check(context, path, self.string_type());
    return if (path_type == .poison_type) path_type else .ast_type;
}

// the holes of a quote are checked where it is written: `@x` is what `x` holds when `x` is declared
// here, else the name `x` where the quote lands. a quote within has holes of its own
fn holes(self: *Macros, context: *FunctionContext, node: NodeId) void {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;
    switch (tree.kind(node)) {
        .quote => return,
        .paste => return self.holes(context, tree.arg(node, 1)),
        .unquote, .unquote_list => self.type_hole(context, node),
        else => switch (ParseTree.Node.nk_childc[@intFromEnum(tree.kind(node))]) {
            .one => self.holes(context, tree.arg(node, 0)),
            .two => for (0..2) |i| {
                const child = tree.arg(node, @intCast(i));
                if (child != 0) self.holes(context, child);
            },
            // by index: checking a hole may grow the lists of the tree
            .many => for (0..tree.arg(node, 1)) |i| {
                self.holes(context, tree.extra_childrefs.buffer[tree.arg(node, 0) + i]);
            },
            .none, .data => {},
        },
    }
}

fn type_hole(self: *Macros, context: *FunctionContext, node: NodeId) void {
    const resolver = self.owning_resolver();
    const held = resolver.tree.arg(node, 0);
    var root = held;
    while (resolver.tree.kind(root) == .member or resolver.tree.kind(root) == .array_index) {
        root = resolver.tree.arg(root, 0);
    }

    const is_landing_name = resolver.tree.kind(root) == .identifier and
        resolver.scopes.lookup(&resolver.decl_pool, resolver.name_pool.name_of_node(root)) == .none;
    if (is_landing_name) {
        resolver.node_types[node] = .poison_type;
        return;
    }

    const held_type = resolver.static_pool.substitute_type_variables(
        resolver.expressions.infer(context, held, .none),
    );
    // a tree stands for the code it produces; other values holding trees have no code to stand for
    const static_pool = &resolver.static_pool;
    const is_tree = static_pool.tag(held_type) == .ast_type;
    resolver.node_types[node] = blk: {
        if (is_tree and static_pool.get(held_type).ast_type.produces != .none) {
            break :blk static_pool.get(held_type).ast_type.produces;
        }
        if (static_pool.contains_trees(held_type)) break :blk .poison_type;
        break :blk held_type;
    };
}

// an expression checked without leaving a trace: nothing in it declares or jumps
fn typable(self: *Macros, node: NodeId) bool {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;
    switch (tree.kind(node)) {
        .quote => return true,
        .def_fun,
        .def_fun_declaration,
        .block,
        .unquote_list,
        .paste,
        .ret,
        .ret_void,
        .brk,
        .cont,
        .@"defer",
        .deinit,
        .inlined_defer_deinit,
        .inc_prefix,
        .dec_prefix,
        .inc_postfix,
        .dec_postfix,
        .assign_add,
        .assign_sub,
        .assign_mul,
        .assign_div,
        .assign_mod,
        => return false,
        else => {
            if (tree.props(node).declares) return false;
            if (resolver.declarations.declared_type_kind(node) != .variable) return false;
        },
    }

    switch (ParseTree.Node.nk_childc[@intFromEnum(tree.kind(node))]) {
        .one => return self.typable(tree.arg(node, 0)),
        .two => {
            const first = tree.arg(node, 0);
            if (first != 0 and !self.typable(first)) return false;
            const second = tree.arg(node, 1);
            return second == 0 or self.typable(second);
        },
        .many => {
            for (tree.manychildren(node)) |child| {
                if (!self.typable(child)) return false;
            }
            return true;
        },
        .none, .data => return true,
    }
}

// `<x>`: what the tree `x` produces. it is expanded right away unless the code around is only
// checked, in a stcfun the interpreter expands it when it runs
// the program may be written while `x` is checked too: a stcfun call is evaluated then
fn splice(self: *Macros, context: *FunctionContext, node: NodeId) Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const spliced = resolver.tree.arg(node, 0);
    const is_live = self.quoting == 0 and !context.is_abstract and !context.is_interpreted;
    const outer_at = self.at;
    if (is_live) {
        self.splicing += 1;
        self.at = resolver.tree.first_token(node);
    }
    defer if (is_live) {
        self.splicing -= 1;
        self.at = outer_at;
    };

    const mark = resolver.doctor.diagnostics.len();
    const tree_type = static_pool.substitute_type_variables(
        resolver.expressions.infer(context, spliced, .none),
    );
    if (tree_type == .poison_type) return self.end_splice(is_live, mark, tree_type);
    if (static_pool.tag(tree_type) != .ast_type and tree_type != .unit_type) {
        const mismatch = resolver.report(.type_mismatch, spliced, tree_type, .ast_type);
        return self.end_splice(is_live, mark, mismatch);
    }

    // a unit splice puts nothing back, a tree of unknown code anything
    const produced_type: Index = blk: {
        if (tree_type == .unit_type) break :blk .unit_type;
        const produced = static_pool.get(tree_type).ast_type.produces;
        if (produced == .none) break :blk .poison_type;
        break :blk produced;
    };
    if (!is_live) return self.end_splice(is_live, mark, produced_type);

    // a stcfun call has its value from being checked, it runs once
    const checked_value = resolver.node_static_values[spliced];
    const value = if (checked_value != .none)
        checked_value
    else
        resolver.interpreter.evaluate_static(context, spliced);
    if (resolver.doctor.diagnostics.len() == mark) resolver.interpreter.trees.expand(node, value);
    return self.end_splice(is_live, mark, produced_type);
}

// after a splice: nodes made while it was checked have rows in the node tables, the errors of
// one expanded end the pass
pub fn end_splice(self: *Macros, live: bool, mark: usize, result_type: Index) Index {
    const resolver = self.owning_resolver();
    resolver.grow_node_tables();
    if (live) self.failed = self.failed or resolver.doctor.diagnostics.len() > mark;
    return result_type;
}

// `refl x`: the declaration of `x` as a tree to read and write, `refl $file` the program
// nothing gets resolved by it
fn refl(self: *Macros, node: NodeId) Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const reflected = resolver.tree.arg(node, 0);
    const name = resolver.name_pool.name_of_node(reflected);
    if (name == .file) return static_pool.pointer_to(.ast_type, true);

    const declaration = if (name == .none)
        .none
    else
        resolver.scopes.lookup(&resolver.decl_pool, name);
    if (declaration == .none) return resolver.report(.undefined_name, reflected, name, 0);
    resolver.node_declarations[node] = declaration;
    resolver.node_declarations[reflected] = declaration;
    const produced: Index = switch (resolver.decl_pool.get(declaration, .kind)) {
        .function, .static_function, .inlined_function, .trait_member => .fun_type,
        .record, .type_alias => .type_type,
        .variant => .variant_type,
        .trait => .trait_type,
        .variable,
        .parameter,
        .static_parameter,
        .field,
        .variant_case,
        .pattern_binder,
        .arrow_binder,
        .loop_variable,
        .self,
        .autoins_arg,
        .autoins_it,
        => .none,
    };
    return static_pool.pointer_to(static_pool.ast_type_of(produced, 0), true);
}

// `ast.Identifier`: the type of trees with a root of that kind
pub fn tree_kind_member(self: *Macros, node: NodeId, name: NamePool.Index) Index {
    const resolver = self.owning_resolver();
    const kind = ParseTree.Node.named.get(resolver.name_pool.text_of(name)) orelse {
        return resolver.report(.unknown_member, node, name, .ast_type);
    };
    // a root kind is stored shifted by one, 0 is a tree of any kind
    return resolver.static_pool.ast_type_of(.none, @as(u16, @intFromEnum(kind)) + 1);
}

// the views of trees (`x.$name`), what each gives and is: the checker types them by it, the
// language server offers them
pub const View = struct {
    name: NamePool.Index,
    gives: enum { tree, list, text, flag },
    doc: []const u8,
};
pub const views = [_]View{
    .{ .name = .src, .gives = .text, .doc = "the source it was written as" },
    .{ .name = .children, .gives = .list, .doc = "its children, of any node" },
    .{
        .name = .name,
        .gives = .tree,
        .doc = "the name of a declaration, parameter, field or case",
    },
    .{ .name = .type, .gives = .tree, .doc = "the type of a declaration, parameter or field" },
    .{ .name = .value, .gives = .tree, .doc = "what a declaration declares" },
    .{ .name = .params, .gives = .list, .doc = "the parameters of a function" },
    .{ .name = .ret, .gives = .tree, .doc = "the return type of a function" },
    .{ .name = .body, .gives = .tree, .doc = "the body of a function" },
    .{ .name = .fields, .gives = .list, .doc = "the fields of a type" },
    .{ .name = .cases, .gives = .list, .doc = "the cases of a variant" },
    .{ .name = .methods, .gives = .list, .doc = "the methods of a type or trait" },
    .{ .name = .implof, .gives = .list, .doc = "the traits a type implements" },
    .{ .name = .default, .gives = .tree, .doc = "the default of a parameter or field" },
    .{ .name = .where, .gives = .tree, .doc = "the condition of a parameter or field" },
    .{ .name = .mut, .gives = .flag, .doc = "whether a parameter or field is mut" },
    .{
        .name = .decls,
        .gives = .list,
        .doc = "the declarations of a block, an include or `refl $file`",
    },
};

// a member of a tree: a view or a child by its field name (`cond`, `lhs`). it is written when the
// tree is reached through a `*ast` (as a field through a `*T`), the elements of a list view of one
// are `*ast`
pub fn tree_member(self: *Macros, base: Index, name: NamePool.Index) Index {
    const static_pool = &self.owning_resolver().static_pool;
    const base_type = static_pool.substitute_type_variables(base);
    const is_writable = static_pool.tag(base_type) == .mutable_pointer_type;
    const element: Index = if (is_writable) static_pool.pointer_to(.ast_type, true) else .ast_type;
    for (views) |view| {
        if (view.name != name) continue;
        return switch (view.gives) {
            .tree => .ast_type,
            .list => static_pool.intern(.{
                .array_type = .{ .length = StaticPool.dyn_len, .element = element },
            }),
            .text => self.string_type(),
            .flag => .bool_type,
        };
    }
    return .ast_type;
}

// what is written into an element of a list view (`t.$fields[0] = x`): a tree, the element is
// replaced by it
pub fn tree_place_type(self: *Macros, node: NodeId, value_type: Index) Index {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    if (resolver.tree.kind(node) != .array_index) return value_type;
    const list = resolver.tree.arg(node, 0);
    if (resolver.tree.kind(list) != .member) return value_type;
    if (!static_pool.is_tree(resolver.node_types[resolver.tree.arg(list, 0)])) return value_type;
    return if (static_pool.is_tree(value_type)) .ast_type else value_type;
}

// `ast(T)`, `ast.Kind(..)` making a node of that kind from its children (a name or literal from
// its text)
pub fn check_tree_call(
    self: *Macros,
    context: *FunctionContext,
    node: NodeId,
    target: Index,
    arguments: []const NodeId,
) Index {
    const resolver = self.owning_resolver();
    const tree_type = resolver.static_pool.get(target).ast_type;
    if (tree_type.root_kind == 0) {
        // `ast(T)`: the type of trees producing T
        if (target != .ast_type or arguments.len != 1) {
            return resolver.report(.wrong_arity, node, arguments.len, 1);
        }
        const produced = resolver.tree.arg_value(arguments[0]);
        if (resolver.tree.kind(produced) != .def_fun_declaration) {
            _ = resolver.types.type_from_node(context, produced);
        }
        return .type_type;
    }

    const child_count = ParseTree.Node.nk_childc[tree_type.root_kind - 1];
    const wanted: usize = switch (child_count) {
        .data, .one => 1,
        .two => 2,
        .none => 0,
        .many => arguments.len,
    };
    if (arguments.len != wanted) {
        return resolver.report(.wrong_arity, node, arguments.len, wanted);
    }

    for (arguments) |argument| {
        const child_type = if (child_count == .data) self.string_type() else Index.ast_type;
        _ = resolver.expressions.check(context, resolver.tree.arg_value(argument), child_type);
    }
    return target;
}

// `$fresh("tmp")`: a name no other name is, `$error(tree, "..")` stops the expansion with an error
// at the tree
pub fn check_builtin(
    self: *Macros,
    context: *FunctionContext,
    node: NodeId,
    name: NamePool.Index,
    arguments: []const NodeId,
) Index {
    const resolver = self.owning_resolver();
    const wanted: usize = if (name == .fresh) 1 else 2;
    if (arguments.len != wanted) return resolver.report(.wrong_arity, node, arguments.len, wanted);

    const tree = resolver.tree;
    if (name == .fresh) {
        _ = resolver.expressions.check(context, tree.arg_value(arguments[0]), self.string_type());
        // a root kind is stored shifted by one, 0 is a tree of any kind
        const root_kind_code = @as(u16, @intFromEnum(ParseTree.Node.Kind.identifier)) + 1;
        return resolver.static_pool.ast_type_of(.none, root_kind_code);
    }
    _ = resolver.expressions.check(context, tree.arg_value(arguments[0]), .ast_type);
    _ = resolver.expressions.check(context, tree.arg_value(arguments[1]), self.string_type());
    return .never_type;
}

// `list += x` of a `[]ast` (or `[]*ast`): a tree or the trees of a list appended
pub fn checks_list_append(
    self: *Macros,
    context: *FunctionContext,
    list_type: Index,
    value: NodeId,
) bool {
    const resolver = self.owning_resolver();
    const static_pool = &resolver.static_pool;
    const resolved_list_type = static_pool.substitute_type_variables(list_type);
    if (resolved_list_type == .none) return false;
    if (static_pool.tag(resolved_list_type) != .array_type) return false;
    if (!static_pool.is_tree(static_pool.get(resolved_list_type).array_type.element)) return false;

    const value_type = static_pool.substitute_type_variables(
        resolver.expressions.infer(context, value, .none),
    );
    if (value_type != .poison_type) {
        const is_tree_or_tree_list = static_pool.is_tree(value_type) or
            (static_pool.tag(value_type) == .array_type and
                static_pool.is_tree(static_pool.get(value_type).array_type.element));
        if (!is_tree_or_tree_list) {
            _ = resolver.report(.type_mismatch, value, value_type, resolved_list_type);
        }
    }
    return true;
}

// the binders of a quote pattern: `@x` takes the tree where it stands, `@_` any tree
pub fn quote_pattern(self: *Macros, node: NodeId) void {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;
    switch (tree.kind(node)) {
        .unquote, .unquote_list => self.bind_quote_hole(node),
        else => switch (ParseTree.Node.nk_childc[@intFromEnum(tree.kind(node))]) {
            .one => self.quote_pattern(tree.arg(node, 0)),
            .two => for ([_]NodeId{ tree.arg(node, 0), tree.arg(node, 1) }) |child| {
                if (child != 0) self.quote_pattern(child);
            },
            .many => for (tree.manychildren(node)) |child| self.quote_pattern(child),
            .none, .data => {},
        },
    }
}

pub fn report_duplicate_holes(self: *Macros, pattern: NodeId) void {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;
    switch (tree.kind(pattern)) {
        .partial__match_case_pattern_or => for (tree.manychildren(pattern)) |alternative| {
            self.report_duplicate_holes(alternative);
        },
        .quote => {
            var binders: std.ArrayList(NodeId) = .empty;
            defer binders.deinit(resolver.allocator);
            self.collect_holes(tree.arg(pattern, 0), &binders);
        },
        else => {},
    }
}

fn collect_holes(self: *Macros, node: NodeId, binders: *std.ArrayList(NodeId)) void {
    const resolver = self.owning_resolver();
    const tree = resolver.tree;
    if (tree.kind(node) != .unquote and tree.kind(node) != .unquote_list) {
        for (tree.children(node)) |child| {
            if (child != 0) self.collect_holes(child, binders);
        }
        return;
    }

    const binder = tree.arg(node, 0);
    const name = resolver.name_pool.name_of_node(binder);
    if (name == .none or name == .underscore) return;
    for (binders.items) |earlier| {
        if (resolver.name_pool.name_of_node(earlier) != name) continue;
        return resolver.doctor.report(.duplicate_declaration, binder, name, DeclPool.Index.none);
    }
    binders.append(resolver.allocator, binder) catch @panic("OOM");
}

fn bind_quote_hole(self: *Macros, node: NodeId) void {
    const resolver = self.owning_resolver();
    const binder = resolver.tree.arg(node, 0);
    const name = resolver.name_pool.name_of_node(binder);
    if (name == .none or name == .underscore) return;

    resolver.declarations.report_redeclaration(name, binder);
    const bound_type = if (resolver.tree.kind(node) == .unquote)
        Index.ast_type
    else
        resolver.static_pool.intern(.{
            .array_type = .{ .length = StaticPool.dyn_len, .element = .ast_type },
        });
    resolver.node_declarations[binder] =
        resolver.declarations.declare_local(name, binder, .pattern_binder, bound_type);
    _ = resolver.set_node_type(binder, bound_type);
}

// the root whose subtree holds `node`, 0 for none: subtrees of roots are in order and contiguous
// until the pass writes
pub fn root_of(self: *Macros, node: NodeId) NodeId {
    const resolver = self.owning_resolver();
    if (self.starts.len != resolver.roots.len) {
        // the old table is replaced, only the last one is freed when the resolver ends
        resolver.allocator.free(self.starts);
        self.starts = resolver.allocator.alloc(NodeId, resolver.roots.len) catch @panic("OOM");
        for (resolver.roots, self.starts) |root, *start| start.* = resolver.tree.subtree(root)[0];
    }

    var i = self.starts.len;
    while (i > 0) : (i -= 1) {
        if (self.starts[i - 1] <= node) return resolver.roots[i - 1];
    }
    return 0;
}

// `[]u8`: what `$src` is and builtins take
pub fn string_type(self: *Macros) Index {
    return self.owning_resolver().static_pool.intern(.{
        .array_type = .{ .length = StaticPool.dyn_len, .element = .u8_type },
    });
}
