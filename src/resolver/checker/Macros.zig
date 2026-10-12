const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const NamePool = @import("../NamePool.zig");
const Decls = @import("Decls.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;
const Index = StaticPool.Index;

// macros: code as a value (`quote`), put back as code where it stands (`<x>`), the program read and written (`refl`),
// other files (`include`). a tree is a value of type `ast(T)`: code producing T, `ast` for any, `ast.Kind` for a root of
// that kind, evaluated by the interpreter (see interpreter/Trees.zig)
//
// how a program changes: a pass evaluates the splices it meets and keeps each expansion in its splice node. a pass that
// expanded anything ends with the tree rebuilt and resolving starts over, the last pass compiles a program no macro
// changes anymore and has no trace of them. the splices at the top run first and in order, before anything is resolved,
// a declaration may be written until it is resolved
const Macros = @This();

pub const max_passes = 64;

// nodes from here on were made in this pass
pass_len: NodeId,
// splices expanded and declarations written in this pass, whether a splice failed, the splice evaluated last and the token of
// the one evaluated now: code landing in the program is written there (its errors are at the splice that made it)
expanded: u32 = 0,
edited: bool = false,
failed: bool = false,
last: NodeId = 0,
at: u32 = 0,
// the splices at the top run: quotes are not typed, typing would resolve what the splices may still write
top: bool = false,
// a quote's code is checked for its type only
quoting: u32 = 0,
// a splice is evaluated, the only time the program may be written
splicing: u32 = 0,
// the node `refl $file` reads, made on demand
file: NodeId = 0,
// names made by macros, over all passes
fresh: u32 = 0,
// where the subtree of each root starts, made once a pass by the first write into the program
starts: []NodeId = &.{},

pub fn res(self: *Macros) *Resolver {
    return @alignCast(@fieldParentPtr("macros", self));
}

// `@` outside the code of a quote (what an unquote takes is no code of it): there is nothing to unquote. it is reported
// before anything is resolved, a name written with it (`a@b`, `x.@y`, `f(@x = 1)`) would be read as none
pub fn strays(self: *Macros, n: NodeId, quoted: bool) void {
    const r = self.res();
    const k = r.tree.kind(n);
    if (!quoted and (k == .unquote or k == .unquote_list or k == .paste)) {
        r.doc.report(.stray_unquote, n, 0, 0);
        return;
    }
    for (r.tree.children(n)) |c| if (c != 0) self.strays(c, k == .quote or quoted and k != .unquote and k != .unquote_list);
}

// the splices at the top, in order. true when there are any
pub fn expand_roots(self: *Macros) bool {
    const r = self.res();
    var ctx = FnCtx{};
    var any = false;
    self.top = true;
    defer self.top = false;
    for (r.roots) |root| if (r.tree.kind(root) == .splice) {
        any = true;
        _ = r.exprs.infer(&ctx, root, .none);
    };
    return any;
}

pub fn infer(self: *Macros, ctx: *FnCtx, n: NodeId, expected: Index) Index {
    const r = self.res();
    const sp = &r.static_pool;
    return switch (r.tree.kind(n)) {
        .quote => blk: {
            const body = r.tree.arg(n, 0);
            // the owner of the names the quote declares, for its hygiene
            r.node_decl[n] = ctx.decl;
            self.holes(ctx, body);
            const want = sp.apply_vars(&r.abstract_pool, expected);
            break :blk sp.ast_of(self.produces(ctx, body, if (want != .none and sp.tag(want) == .ast_type) sp.get(want).ast.of else .none), 0);
        },
        .splice => self.splice(ctx, n),
        .refl => self.refl(n),
        .include => blk: {
            if (r.tree.kind(r.tree.arg(n, 0)) != .string) break :blk r.report(.type_mismatch, r.tree.arg(n, 0), r.exprs.infer(ctx, r.tree.arg(n, 0), .none), self.string());
            break :blk .ast_type;
        },
        // a hole is typed by the quote around it, anywhere else it means nothing
        else => if (self.quoting > 0) r.node_type[n] else r.report(.stray_unquote, n, 0, 0),
    };
}

// the holes of a quote are checked where it is written: `@x` is what `x` holds when `x` is declared here,
// else the name `x` where the quote lands. a quote within has holes of its own
fn holes(self: *Macros, ctx: *FnCtx, n: NodeId) void {
    const r = self.res();
    const sp = &r.static_pool;
    switch (r.tree.kind(n)) {
        .quote => return,
        .paste => return self.holes(ctx, r.tree.arg(n, 1)),
        .unquote, .unquote_list => {
            const x = r.tree.arg(n, 0);
            var root = x;
            while (r.tree.kind(root) == .member or r.tree.kind(root) == .array_index) root = r.tree.arg(root, 0);
            if (r.tree.kind(root) == .identifier and r.scopes.lookup(&r.decl_pool, r.name_pool.name_of(root)) == .none) {
                r.node_type[n] = .poison_type;
                return;
            }
            const t = sp.apply_vars(&r.abstract_pool, r.exprs.infer(ctx, x, .none));
            r.node_type[n] = if (sp.tag(t) == .ast_type and sp.get(t).ast.of != .none) sp.get(t).ast.of else if (sp.holds_trees(t)) .poison_type else t;
        },
        else => switch (ParseTree.Node.nk_childc[@intFromEnum(r.tree.kind(n))]) {
            .one => self.holes(ctx, r.tree.arg(n, 0)),
            .two => for (0..2) |i| if (r.tree.arg(n, @intCast(i)) != 0) self.holes(ctx, r.tree.arg(n, @intCast(i))),
            // by index: checking a hole may grow the lists of the tree
            .many => for (0..r.tree.arg(n, 1)) |i| self.holes(ctx, r.tree.extra_childrefs.buf[r.tree.arg(n, 0) + i]),
            else => {},
        },
    }
}

// what a quote's code produces as far as it is known where it is written: declarations by their kind, statements
// nothing, an expression is checked with its holes as what they hold. none when that fails (a name only where it lands)
fn produces(self: *Macros, ctx: *FnCtx, body: NodeId, hint: Index) Index {
    const r = self.res();
    const sp = &r.static_pool;
    switch (r.tree.kind(body)) {
        .block => return .unit_type,
        .def_fun => return .fun_type,
        .partial__match_case => return .none,
        else => {},
    }
    if (r.decls.type_kind(body) != .variable) return r.decls.type_kind(body).meta(.type_type);
    if (r.tree.props(body).declares) return switch (Decls.Stmt.from_node(r, body).kind) {
        .variable => .unit_type,
        .record, .type_alias, .variant, .trait => |k| k.meta(.type_type),
        else => .fun_type,
    };
    if (self.top or !self.typable(body)) return .none;
    const mark = r.doc.diagnostics.len();
    self.quoting += 1;
    r.scopes.push();
    const t = sp.apply_vars(&r.abstract_pool, r.exprs.infer(ctx, body, hint));
    r.scopes.pop();
    self.quoting -= 1;
    const ok = r.doc.diagnostics.len() == mark and t != .poison_type and !sp.has_vars(t);
    r.doc.rewind(mark);
    return if (ok) t else .none;
}

// an expression checked without leaving a trace: nothing in it declares or jumps
fn typable(self: *Macros, n: NodeId) bool {
    const r = self.res();
    switch (r.tree.kind(n)) {
        .quote => return true,
        .def_fun, .def_fun_declaration, .block, .unquote_list, .paste, .ret, .ret_void, .brk, .cont, .@"defer", .deinit, .inlined_defer_deinit, .inc_prefix, .dec_prefix, .inc_postfix, .dec_postfix, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod => return false,
        else => if (r.tree.props(n).declares or r.decls.type_kind(n) != .variable) return false,
    }
    return switch (ParseTree.Node.nk_childc[@intFromEnum(r.tree.kind(n))]) {
        .one => self.typable(r.tree.arg(n, 0)),
        .two => (r.tree.arg(n, 0) == 0 or self.typable(r.tree.arg(n, 0))) and (r.tree.arg(n, 1) == 0 or self.typable(r.tree.arg(n, 1))),
        .many => for (r.tree.manychildren(n)) |c| {
            if (!self.typable(c)) break false;
        } else true,
        else => true,
    };
}

// `<x>`: what the tree `x` produces. it is expanded right away unless the code around is only checked, in a stcfun the
// interpreter expands it when it runs. the program may be written while `x` is checked too: a stcfun call is evaluated then
fn splice(self: *Macros, ctx: *FnCtx, n: NodeId) Index {
    const r = self.res();
    const sp = &r.static_pool;
    const x = r.tree.arg(n, 0);
    const live = self.quoting == 0 and !ctx.abstract and !ctx.interpreted;
    const outer = self.at;
    if (live) {
        self.splicing += 1;
        self.at = r.tree.first_token(n);
    }
    defer if (live) {
        self.splicing -= 1;
        self.at = outer;
    };
    const mark = r.doc.diagnostics.len();
    const t = sp.apply_vars(&r.abstract_pool, r.exprs.infer(ctx, x, .none));
    if (t == .poison_type) return self.ended(live, mark, t);
    if (sp.tag(t) != .ast_type and t != .unit_type) return self.ended(live, mark, r.report(.type_mismatch, x, t, .ast_type));
    const of: Index = if (t == .unit_type) .unit_type else if (sp.get(t).ast.of == .none) .poison_type else sp.get(t).ast.of;
    if (!live) return self.ended(live, mark, of);
    // a stcfun call has its value from being checked, it runs once
    const v = if (r.node_value[x] != .none) r.node_value[x] else r.interpreter.eval_static(ctx, x);
    if (r.doc.diagnostics.len() == mark) r.interpreter.trees.expand(n, v);
    return self.ended(live, mark, of);
}

// after a splice: nodes made while it was checked have rows in the node tables, the errors of one expanded end the pass
pub fn ended(self: *Macros, live: bool, mark: usize, t: Index) Index {
    const r = self.res();
    r.fit();
    if (live) self.failed = self.failed or r.doc.diagnostics.len() > mark;
    return t;
}

// `refl x`: the declaration of `x` as a tree to read and write, `refl $file` the program. nothing gets resolved by it
fn refl(self: *Macros, n: NodeId) Index {
    const r = self.res();
    const sp = &r.static_pool;
    const x = r.tree.arg(n, 0);
    const name = r.name_pool.name_of(x);
    if (name == .file) return sp.ptr_of(.ast_type, true);
    const d = if (name == .none) .none else r.scopes.lookup(&r.decl_pool, name);
    if (d == .none) return r.report(.undefined_name, x, name, 0);
    r.node_decl[n] = d;
    r.node_decl[x] = d;
    const of: Index = switch (r.decl_pool.get_kind(d)) {
        .function, .static_function, .inlined_function, .trait_member => .fun_type,
        .record, .type_alias => .type_type,
        .variant => .variant_type,
        .trait => .trait_type,
        else => .none,
    };
    return sp.ptr_of(sp.ast_of(of, 0), true);
}

// `ast.Identifier`: the type of trees with a root of that kind
pub fn case(self: *Macros, node: NodeId, name: NamePool.Index) Index {
    const r = self.res();
    const k = ParseTree.Node.named.get(r.name_pool.get(name)) orelse return r.report(.unknown_member, node, name, .ast_type);
    return r.static_pool.ast_of(.none, @as(u16, @intFromEnum(k)) + 1);
}

// the views of trees (`x.$name`), what each gives and is: the checker types them by it, the language server offers them
pub const View = struct { name: NamePool.Index, gives: enum { tree, list, text, flag }, doc: []const u8 };
pub const views = [_]View{
    .{ .name = .src, .gives = .text, .doc = "the source it was written as" },
    .{ .name = .children, .gives = .list, .doc = "its children, of any node" },
    .{ .name = .name, .gives = .tree, .doc = "the name of a declaration, parameter, field or case" },
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
    .{ .name = .decls, .gives = .list, .doc = "the declarations of a block, an include or `refl $file`" },
};

// a member of a tree: a view or a child by its field name (`cond`, `lhs`). it is written when the tree is reached
// through a `*ast` (as a field through a `*T`), the elements of a list view of one are `*ast`
pub fn member(self: *Macros, base: Index, name: NamePool.Index) Index {
    const r = self.res();
    const sp = &r.static_pool;
    const elem = if (sp.tag(sp.apply_vars(&r.abstract_pool, base)) == .ptr_mut_type) sp.ptr_of(.ast_type, true) else Index.ast_type;
    for (views) |v| if (v.name == name) return switch (v.gives) {
        .tree => .ast_type,
        .list => sp.intern(.{ .array_type = .{ .len = StaticPool.dyn_len, .elem = elem } }),
        .text => self.string(),
        .flag => .bool_type,
    };
    return .ast_type;
}

// what is written into an element of a list view (`t.$fields[0] = x`): a tree, the element is replaced by it
pub fn place(self: *Macros, n: NodeId, t: Index) Index {
    const r = self.res();
    const sp = &r.static_pool;
    if (r.tree.kind(n) != .array_index or r.tree.kind(r.tree.arg(n, 0)) != .member or !sp.is_tree(r.node_type[r.tree.arg(r.tree.arg(n, 0), 0)])) return t;
    return if (sp.is_tree(t)) .ast_type else t;
}

// `ast(T)`, `ast.Kind(..)` making a node of that kind from its children (a name or literal from its text)
pub fn call(self: *Macros, ctx: *FnCtx, node: NodeId, target: Index, args: []const NodeId) Index {
    const r = self.res();
    const a = r.static_pool.get(target).ast;
    if (a.case == 0) {
        if (target != .ast_type or args.len != 1) return r.report(.wrong_arity, node, args.len, 1);
        if (r.tree.kind(r.tree.arg_value(args[0])) != .def_fun_declaration) _ = r.types.lower(ctx, r.tree.arg_value(args[0]));
        return .type_type;
    }
    const childc = ParseTree.Node.nk_childc[a.case - 1];
    const want: usize = switch (childc) {
        .data, .one => 1,
        .two => 2,
        .none => 0,
        .many => args.len,
    };
    if (args.len != want) return r.report(.wrong_arity, node, args.len, want);
    for (args) |x| _ = r.exprs.check(ctx, r.tree.arg_value(x), if (childc == .data) self.string() else .ast_type);
    return target;
}

// `$fresh("tmp")`: a name no other name is, `$error(tree, "..")` stops the expansion with an error at the tree
pub fn builtin(self: *Macros, ctx: *FnCtx, node: NodeId, name: NamePool.Index, args: []const NodeId) Index {
    const r = self.res();
    const want: usize = if (name == .fresh) 1 else 2;
    if (args.len != want) return r.report(.wrong_arity, node, args.len, want);
    if (name == .fresh) {
        _ = r.exprs.check(ctx, r.tree.arg_value(args[0]), self.string());
        return r.static_pool.ast_of(.none, @as(u16, @intFromEnum(ParseTree.Node.Kind.identifier)) + 1);
    }
    _ = r.exprs.check(ctx, r.tree.arg_value(args[0]), .ast_type);
    _ = r.exprs.check(ctx, r.tree.arg_value(args[1]), self.string());
    return .never_type;
}

// `list += x` of a `[]ast` (or `[]*ast`): a tree or the trees of a list appended
pub fn grows(self: *Macros, ctx: *FnCtx, lt: Index, value: NodeId) bool {
    const r = self.res();
    const sp = &r.static_pool;
    const t = sp.apply_vars(&r.abstract_pool, lt);
    if (t == .none or sp.tag(t) != .array_type or !sp.is_tree(sp.get(t).array_type.elem)) return false;
    const vt = sp.apply_vars(&r.abstract_pool, r.exprs.infer(ctx, value, .none));
    if (vt != .poison_type and !sp.is_tree(vt) and !(sp.tag(vt) == .array_type and sp.is_tree(sp.get(vt).array_type.elem))) _ = r.report(.type_mismatch, value, vt, t);
    return true;
}

// the binders of a quote pattern: `@x` takes the tree where it stands, `@_` any tree
pub fn quote_pattern(self: *Macros, n: NodeId) void {
    const r = self.res();
    switch (r.tree.kind(n)) {
        .unquote, .unquote_list => {
            const x = r.tree.arg(n, 0);
            const name = r.name_pool.name_of(x);
            if (name == .none or name == .underscore) return;
            r.decls.redeclared(name, x);
            const t = if (r.tree.kind(n) == .unquote) Index.ast_type else r.static_pool.intern(.{ .array_type = .{ .len = StaticPool.dyn_len, .elem = .ast_type } });
            r.node_decl[x] = r.decls.declare_local(name, x, .pattern_binder, t);
            _ = r.set(x, t);
        },
        else => switch (ParseTree.Node.nk_childc[@intFromEnum(r.tree.kind(n))]) {
            .one => self.quote_pattern(r.tree.arg(n, 0)),
            .two => for ([_]NodeId{ r.tree.arg(n, 0), r.tree.arg(n, 1) }) |c| if (c != 0) self.quote_pattern(c),
            .many => for (r.tree.manychildren(n)) |c| self.quote_pattern(c),
            else => {},
        },
    }
}

// the root whose subtree holds `n`, 0 for none: subtrees of roots are in order and contiguous until the pass writes
pub fn root_of(self: *Macros, n: NodeId) NodeId {
    const r = self.res();
    if (self.starts.len != r.roots.len) {
        self.starts = r.alloc.alloc(NodeId, r.roots.len) catch @panic("OOM");
        for (r.roots, self.starts) |root, *s| s.* = r.tree.subtree(root)[0];
    }
    var i = self.starts.len;
    while (i > 0) : (i -= 1) if (self.starts[i - 1] <= n) return r.roots[i - 1];
    return 0;
}

// `[]u8`: what `$src` is and builtins take
pub fn string(self: *Macros) Index {
    return self.res().static_pool.intern(.{ .array_type = .{ .len = StaticPool.dyn_len, .elem = .u8_type } });
}
