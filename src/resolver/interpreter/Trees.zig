const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Lexer = @import("../../Lexer.zig");
const Parser = @import("../../Parser.zig");
const StaticPool = @import("../StaticPool.zig");
const NamePool = @import("../NamePool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;

// trees: code as a value. a tree is a pool value naming its root node. like any value it is stored as a copy of its own
// (see kept), a `*ast` shares the tree it points to and writes it in place. a quote copies its code with the holes filled,
// a tree lands (is spliced or written into the program) as a copy of its own, made hygienic (see ParseTree.land)
const Trees = @This();

// how a name in a quote names: it refers, declares (`x = ..`, a parameter) or labels (`.x`, `f(x = ..)`), in a pattern it declares
const Mode = enum { plain, binds, label, pattern };

pub fn interp(self: *Trees) *Interpreter {
    return @alignCast(@fieldParentPtr("trees", self));
}

pub fn eval(self: *Trees, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    return switch (r.tree.kind(n)) {
        // the tree the checker made: a stcfun called with it is realized once
        .quote => if (!ip.framed() and r.node_value[n] != .none) .of(&r.static_pool, r.node_value[n]) else self.quote(n),
        .splice => blk: {
            // the code is there in the next pass, until then the splice has no value
            const outer = r.macros.at;
            r.macros.splicing += 1;
            r.macros.at = r.tree.first_token(n);
            defer r.macros.splicing -= 1;
            defer r.macros.at = outer;
            const mark = r.doc.diagnostics.len();
            const v = ip.eval(r.tree.arg(n, 0));
            if (!v.is(.poison_type) and r.doc.diagnostics.len() == mark) self.expand(n, ip.pool(v));
            _ = r.macros.ended(true, mark, .none);
            break :blk .poison;
        },
        .refl => blk: {
            const t = self.type_at(n);
            break :blk self.value(t, if (ip.info(.decl, n) == .none) self.file() else r.decl_pool.get_node(ip.info(.decl, n)));
        },
        .include => self.include(n),
        else => ip.fail(n, .stray_unquote, 0, 0),
    };
}

// the type of a node, checked now when evaluated before the checker met it (`fun f = <m(..)>` is evaluated to resolve f)
fn type_at(self: *Trees, n: NodeId) Index {
    const ip = self.interp();
    const t = ip.info(.ty, n);
    return if (t != .none or ip.framed()) t else ip.res().exprs.infer(ip.ctx, n, .none);
}

pub fn value(self: *Trees, t: Index, n: NodeId) Value {
    return .pooled(self.interp().res().static_pool.intern(.{ .tree = .{ .ty = if (t == .none) .ast_type else t, .node = n } }));
}

// the root of a tree or a `*ast`, null for any other value
pub fn node_of(self: *Trees, v: Value) ?NodeId {
    const sp = &self.interp().res().static_pool;
    if (!v.is_pool() or v.is(.none) or sp.tag(v.index()) != .tree_value) return null;
    return sp.get(v.index()).tree.node;
}

// a value stored (in a variable, a parameter, an element): its trees copied, nothing else holds them. `*ast`s share
pub fn kept(self: *Trees, v: Value) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    if (!v.is_pool() or v.is(.none)) return v;
    const i = v.index();
    switch (sp.tag(i)) {
        .tree_value => {
            const x = sp.get(i).tree;
            return if (sp.is_ptr(x.ty)) v else self.value(x.ty, r.tree.copy(r.tree, x.node, r.src_bytes, false, null));
        },
        .aggregate_value => {
            const ty = sp.get(i).aggregate.ty;
            if (ty == .none or !sp.holds_trees(ty)) return v;
            const mark = ip.ids.head;
            defer ip.ids.head = mark;
            // by index: interning may move the elements
            for (0..sp.get(i).aggregate.elems.len) |j| ip.ids.push(self.kept(.pooled(sp.get(i).aggregate.elems[j])).index());
            return .pooled(sp.intern(.{ .aggregate = .{ .ty = ty, .elems = ip.ids.buf[mark..ip.ids.head] } }));
        },
        else => return v,
    }
}

// the code a splice stands for from now on: a landed copy of the tree, nothing for a unit
pub fn expand(self: *Trees, n: NodeId, v: Index) void {
    const r = self.interp().res();
    const t = r.tree;
    if (v == .poison_type) return;
    const x = if (v == .unit_value) t.push_node(.block) else if (r.static_pool.tag(v) == .tree_value) self.land(r.static_pool.get(v).tree.node, .none) else {
        _ = self.interp().fail(n, .type_mismatch, r.static_pool.type_of(v), .ast_type);
        return;
    };
    t.ast_nodes.pool.args.buf[n][1] = x + 1;
    r.macros.expanded += 1;
    r.macros.last = n;
}

// a copy of a tree for the program: written at the splice evaluated, made hygienic. `into` the list it lands in. a `@` in
// it outside a quote (from an included file, made by `ast.Unquote(..)`) is stray
fn land(self: *Trees, x: NodeId, into: Kind) NodeId {
    const r = self.interp().res();
    const c = as_param(r.tree, r.tree.copy(r.tree, x, r.src_bytes, false, r.macros.at), into);
    r.tree.land(c, &r.macros.fresh);
    r.macros.strays(c, false);
    return c;
}

// code written as a declaration (`mut u32 a = 7`) landing in a list of fields or parameters is one of them
fn as_param(t: *ParseTree, c: NodeId, into: Kind) NodeId {
    if (into != .partial__type_def_param_tuple and into != .partial__fun_def_param_tuple) return c;
    const field = into == .partial__type_def_param_tuple;
    var n = c;
    const mutable = t.kind(n) == .mod_mut;
    if (mutable) n = t.arg(n, 0);
    const default = if (t.kind(n) == .assign_typed) t.arg(n, 1) else 0;
    if (default != 0) n = t.arg(n, 0);
    if (t.kind(n) != .def_var) return c;
    var p = if (field) t.push_node_with(.partial__type_def_param, .{ .type = t.arg(n, 0) }) else t.push_node_with(.partial__fun_def_param, .{ .type = t.arg(n, 0) });
    p = if (field) t.push_node_with(.partial__type_def_param_named, .{ .param = p, .identifier = t.arg(n, 1) }) else t.push_node_with(.partial__fun_def_param_named, .{ .param = p, .identifier = t.arg(n, 1) });
    if (default != 0) p = if (field) t.push_node_with(.partial__type_def_param_default, .{ .param = p, .default_value = default }) else t.push_node_with(.partial__fun_def_param_default, .{ .param = p, .default_value = default });
    return if (mutable and field) t.push_node_with(.partial__type_def_param_mut, .{ .param = p }) else p;
}

// `quote`: its code copied, the holes filled, each name it writes marked with the function it is written in (its hygiene)
fn quote(self: *Trees, n: NodeId) Value {
    const ip = self.interp();
    const t = self.type_at(n);
    const owner = ip.info(.decl, n);
    const root = self.fill(ip.res().tree.arg(n, 0), if (owner == .none) 0 else @intFromEnum(owner) + 1, .plain) orelse return .poison;
    return self.value(t, root);
}

fn fill(self: *Trees, n0: NodeId, owner: u32, mode: Mode) ?NodeId {
    const ip = self.interp();
    const r = ip.res();
    const t = r.tree;
    if (n0 == 0) return 0;
    var n = n0;
    while (t.kind(n) == .capture) n = t.arg(n, 0);
    if (!ip.charge(n, 1)) return null;
    const k = t.kind(n);
    switch (k) {
        // a quote within keeps its holes for when it is evaluated
        .quote => return t.copy(t, n, r.src_bytes, false, null),
        .unquote => return self.hole(t.arg(n, 0)),
        .paste => return self.paste(n),
        .unquote_list => {
            _ = ip.fail(n, .stray_unquote, 0, 0);
            return null;
        },
        .identifier => {
            var buf: [256]u8 = undefined;
            const text = t.text(n, r.src_bytes);
            if (text.len > buf.len) return t.copy(t, n, r.src_bytes, false, null);
            @memcpy(buf[0..text.len], text);
            // `_` and the compiler's `$` names are no names of the quote
            const own = mode != .label and text.len > 0 and text[0] != '$' and !std.mem.eql(u8, text, "_");
            return t.push_word(.identifier, t.arg(n, 0), buf[0..text.len], if (own) owner else 0, own and (mode == .binds or mode == .pattern));
        },
        else => {},
    }
    switch (ParseTree.Node.nk_childc[@intFromEnum(k)]) {
        .none => return t.push_node(k),
        .data => return t.copy(t, n, r.src_bytes, false, null),
        .one, .two => {
            const a = self.fill(t.arg(n, 0), owner, mode_of(t, n, 0, mode)) orelse return null;
            var b: NodeId = 0;
            if (ParseTree.Node.nk_childc[@intFromEnum(k)] == .two) b = self.fill(t.arg(n, 1), owner, mode_of(t, n, 1, mode)) orelse return null;
            const c = t.push_node(k);
            t.ast_nodes.pool.args.buf[c] = .{ a, b };
            return c;
        },
        .many => {
            const mark = t.scratch.head;
            defer t.scratch.head = mark;
            // by index: filling a hole may grow the lists of the tree
            for (0..t.arg(n, 1)) |i| {
                const c = t.extra_childrefs.buf[t.arg(n, 0) + i];
                if (t.kind(c) == .unquote_list) {
                    if (!self.spread(t.arg(c, 0))) return null;
                    continue;
                }
                const x = self.fill(c, owner, mode_of(t, n, @intCast(i), mode)) orelse return null;
                t.scratch.push(x);
            }
            const c = t.push_node(k);
            t.set_children(c, t.scratch.buf[mark..t.scratch.head]);
            return c;
        },
    }
}

// how the child `i` of `n` names
fn mode_of(t: *const ParseTree, n: NodeId, i: u32, mode: Mode) Mode {
    const k = t.kind(n);
    return switch (k) {
        .member => if (i == 1) .label else .plain,
        .partial__fun_call_assigned_param => if (i == 0) .label else mode,
        .partial__type_def_param_named, .partial__variant_def_param => .label,
        .assign, .labelarrow, .selftag_arrow, .for_var_in_seq, .stcfor_var_in_seq, .partial__fun_def_param_named, .partial__match_case_pattern_typecast => if (i == @intFromBool(k != .assign)) .binds else if (mode == .pattern and k != .partial__match_case_pattern_typecast) .pattern else .plain,
        // the name of a function or type declared in a quote is the program's (global), a variable's the quote's
        .def_var => if (i == 0) .plain else switch (t.kind(t.arg(n, 0))) {
            .type_fun, .type_stcfun, .type_inlfun, .type_type, .type_variant, .type_trait => .label,
            else => .binds,
        },
        .partial__destructure, .partial__fun_call_param_tuple, .partial__match_case_pattern_or => mode,
        .fun_call => if (i == 1) mode else .plain,
        .partial__match_case => if (i == 0) .pattern else .plain,
        else => .plain,
    };
}

// `@x`: what `x` holds when it is known where the quote is evaluated, else the name `x` where the quote lands
fn hole(self: *Trees, x: NodeId) ?NodeId {
    const ip = self.interp();
    const r = ip.res();
    var root = x;
    while (r.tree.kind(root) == .member or r.tree.kind(root) == .array_index) root = r.tree.arg(root, 0);
    if (r.tree.kind(root) == .identifier and !self.known(root)) return r.tree.copy(r.tree, x, r.src_bytes, false, null);
    const v = ip.eval(x);
    if (v.is(.poison_type)) return null;
    return self.lift(x, v);
}

fn known(self: *Trees, id: NodeId) bool {
    const ip = self.interp();
    const r = ip.res();
    const d = ip.info(.decl, id);
    if (d == .none) return false;
    if (ip.variables.slot(d)) |c| return !ip.mem.buf[c].is(.none);
    return r.decl_pool.get_value(d) != .none;
}

// `@..xs`: the trees of a list (or the children of a tree) as children of the list around
fn spread(self: *Trees, x: NodeId) bool {
    const ip = self.interp();
    const r = ip.res();
    const t = r.tree;
    const v = ip.eval(x);
    if (v.is(.poison_type)) return false;
    if (self.node_of(v)) |root| {
        if (ParseTree.Node.nk_childc[@intFromEnum(t.kind(root))] != .many) {
            t.scratch.push(t.copy(t, root, r.src_bytes, false, null));
            return true;
        }
        for (0..t.arg(root, 1)) |i| t.scratch.push(t.copy(t, t.extra_childrefs.buf[t.arg(root, 0) + i], r.src_bytes, false, null));
        return true;
    }
    const len = ip.span(v) orelse {
        _ = ip.fail(x, .type_mismatch, ip.vtype(v), .ast_type);
        return false;
    };
    for (0..len) |i| {
        const e = self.node_of(ip.elem(v, @intCast(i))) orelse {
            _ = ip.fail(x, .type_mismatch, ip.vtype(ip.elem(v, @intCast(i))), .ast_type);
            return false;
        };
        t.scratch.push(t.copy(t, e, r.src_bytes, false, null));
    }
    return true;
}

// `get_@(x)`: one name of the name before and the name or text `x` is
fn paste(self: *Trees, n: NodeId) ?NodeId {
    const ip = self.interp();
    const r = ip.res();
    const t = r.tree;
    const v = ip.eval(t.arg(t.arg(n, 1), 0));
    if (v.is(.poison_type)) return null;
    var buf: [256]u8 = undefined;
    const tail = self.text_of(v) orelse {
        _ = ip.fail(n, .type_mismatch, ip.vtype(v), .ast_type);
        return null;
    };
    const s = std.fmt.bufPrint(&buf, "{s}{s}", .{ t.text(t.arg(n, 0), r.src_bytes), tail }) catch return null;
    return t.push_word(.identifier, t.arg(t.arg(n, 0), 0), s, 0, false);
}

// the text a name, a literal or a string is
fn text_of(self: *Trees, v: Value) ?[]const u8 {
    const r = self.interp().res();
    const sp = &r.static_pool;
    if (self.node_of(v)) |x| return if (ParseTree.Node.nk_childc[@intFromEnum(r.tree.kind(x))] == .data) r.tree.text(x, r.src_bytes) else null;
    const i = self.interp().pool(v);
    return if (sp.tag(i) == .string_value) sp.get(i).string else null;
}

// a value put into code: a tree as a copy of it, a static value as the literal or type it is
fn lift(self: *Trees, at: NodeId, v: Value) ?NodeId {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const t = r.tree;
    if (self.node_of(v)) |x| return t.copy(t, x, r.src_bytes, false, null);
    const tok = t.first_token(at);
    var buf: [64]u8 = undefined;
    if (v.ty == .bool_type) return t.push_node(if (v.bits != 0) .boolean_true else .boolean_false);
    if (Value.is_int(v.ty)) {
        const neg = Value.is_int(v.ty) and @intFromEnum(v.ty) >= @intFromEnum(Index.i8_type) and @as(i64, @bitCast(v.bits)) < 0;
        const lit = t.push_word(.int, tok, std.fmt.bufPrint(&buf, "{d}", .{if (neg) 0 -% v.bits else v.bits}) catch unreachable, 0, false);
        return if (neg) t.push_node_with(.neg_num, .{ .subnode = lit }) else lit;
    }
    if (Value.is_float(v.ty)) return t.push_word(.float, tok, std.fmt.bufPrint(&buf, "{d}", .{v.f()}) catch unreachable, 0, false);
    const i = ip.pool(v);
    if (sp.tag(i) == .string_value) {
        // the literal of a text: its quotes and backslashes escaped
        const s = sp.get(i).string;
        const out = r.scratch(u8, s.len * 2);
        var len: usize = 0;
        for (s) |c| {
            if (c == '"' or c == '\\' or c == '\n') {
                out[len] = '\\';
                len += 1;
            }
            out[len] = if (c == '\n') 'n' else c;
            len += 1;
        }
        return t.push_word(.string, tok, out[0..len], 0, false);
    }
    if (sp.get_tag_prop(i).is_type) return self.type_tree(tok, i) orelse {
        _ = ip.fail(at, .not_static, i, 0);
        return null;
    };
    _ = ip.fail(at, .not_static, i, 0);
    return null;
}

// a type as code naming it: a keyword, a pointer or array of one, a declared type by its name
fn type_tree(self: *Trees, tok: u32, ty: Index) ?NodeId {
    const r = self.interp().res();
    const sp = &r.static_pool;
    const t = r.tree;
    const keywords = comptime blk: {
        var m: [Index.first_dynamic]?Kind = @splat(null);
        for (@typeInfo(Index).@"enum".fields) |f| if (std.mem.endsWith(u8, f.name, "_type") and @hasField(Kind, "type_" ++ f.name[0 .. f.name.len - 5])) {
            m[f.value] = @field(Kind, "type_" ++ f.name[0 .. f.name.len - 5]);
        };
        break :blk m;
    };
    if (@intFromEnum(ty) < keywords.len) if (keywords[@intFromEnum(ty)]) |k| return t.push_node(k);
    switch (sp.get(ty)) {
        .ptr_type => |p| {
            const c = self.type_tree(tok, p.child) orelse return null;
            const x = t.push_node(if (p.mutable) .type_ptrmut else .type_ptr);
            t.set_children(x, c);
            return x;
        },
        .array_type => |a| {
            const e = self.type_tree(tok, a.elem) orelse return null;
            if (a.len == StaticPool.dyn_len) return t.push_node_with(.type_array_unlengthed, .{ .type = e });
            var buf: [24]u8 = undefined;
            const len = t.push_word(.int, tok, std.fmt.bufPrint(&buf, "{d}", .{sp.get(a.len).int.bits}) catch unreachable, 0, false);
            return t.push_node_with(.type_array, .{ .length = len, .type = e });
        },
        else => {
            const d = sp.nominal_decl(&r.abstract_pool, ty);
            if (d == .none) return null;
            return t.push_word(.identifier, tok, r.name_pool.get(r.decl_pool.get_name(d)), 0, false);
        },
    }
}

// `refl $file`: a block of the roots, made once a pass
fn file(self: *Trees) NodeId {
    const r = self.interp().res();
    if (r.macros.file == 0) {
        r.macros.file = r.tree.push_node(.block);
        r.tree.set_children(r.macros.file, r.roots);
    }
    return r.macros.file;
}

// `include "f.mn"`: a block of copies of the public declarations of the file, found next to the one compiled
fn include(self: *Trees, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const name = r.tree.text(r.tree.arg(n, 0), r.src_bytes);
    return self.value(.ast_type, self.read(n, name) orelse return ip.fail(n, .include_failed, r.name_pool.intern_owned(name), 0));
}

fn read(self: *Trees, n: NodeId, name: []const u8) ?NodeId {
    const r = self.interp().res();
    const t = r.tree;
    const path = std.fs.path.join(r.alloc, &.{ std.fs.path.dirname(r.path) orelse ".", name }) catch return null;
    defer r.alloc.free(path);
    const bytes = std.Io.Dir.cwd().readFileAlloc(r.io orelse return null, path, r.alloc, .limited(50 << 20)) catch return null;
    defer r.alloc.free(bytes);
    var lexer = Lexer{ .src_bytes = bytes, .tokens = .init(r.alloc, 1024) };
    defer lexer.tokens.deinit();
    lexer.gen_tokens() catch return null;
    var p = Parser.init(r.alloc, lexer.tokens, bytes, lexer.tokens.sliced_field(.span));
    defer p.deinit();
    p.build_ast() catch return null;
    const mark = t.scratch.head;
    defer t.scratch.head = mark;
    for (p.global_store.sliced()) |root| if (p.tree.kind(root) == .mod_pub) t.scratch.push(t.copy(&p.tree, root, bytes, false, t.arg(t.arg(n, 0), 0)));
    const b = t.push_node(.block);
    t.set_children(b, t.scratch.buf[mark..t.scratch.head]);
    return b;
}

// views of trees: a declaration by its parts, a function, type, field or parameter by theirs, any node by the fields of its kind

// what a declaration declares (`fun f = ..` is its function), anything else itself
fn subject(t: *const ParseTree, x: NodeId) NodeId {
    var n = x;
    while (t.kind(n) == .mod_pub or t.kind(n) == .mod_mut or t.kind(n) == .mod_stc) n = t.arg(n, 0);
    return if (t.kind(n) == .assign or t.kind(n) == .assign_typed) t.arg(n, 1) else n;
}

// the def_var of a declaration
fn def_var(t: *const ParseTree, x: NodeId) NodeId {
    var n = x;
    while (t.kind(n) == .mod_pub or t.kind(n) == .mod_mut or t.kind(n) == .mod_stc) n = t.arg(n, 0);
    return if (t.kind(n) == .assign_typed) t.arg(n, 0) else if (t.kind(n) == .def_var) n else 0;
}

fn is_param(k: Kind) bool {
    return @intFromEnum(k) >= @intFromEnum(Kind.partial__fun_def_param) and @intFromEnum(k) <= @intFromEnum(Kind.partial__fun_def_param_where_else) or
        @intFromEnum(k) >= @intFromEnum(Kind.partial__type_def_param) and @intFromEnum(k) <= @intFromEnum(Kind.partial__type_def_param_where_else);
}

// the node a view or field of `x` is, null when it has none
fn view(self: *Trees, x: NodeId, name: NamePool.Index) ?NodeId {
    const r = self.interp().res();
    const t = r.tree;
    const s = subject(t, x);
    const v = def_var(t, x);
    const p = if (is_param(t.kind(x))) ParseTree.Param.from_node(t, x) else ParseTree.Param{};
    const got: NodeId = switch (name) {
        .name => if (v != 0) t.arg(v, 1) else if (t.kind(x) == .assign) t.arg(x, 0) else if (is_param(t.kind(x))) p.name else case_name(t, x),
        .type => if (v != 0) t.arg(v, 0) else p.ty,
        .value => if (s != x) s else 0,
        .default => p.default,
        .where => p.where,
        .body => if (t.kind(s) == .def_fun) t.arg(s, 1) else 0,
        .ret => if (t.kind(s) == .def_fun and t.kind(t.arg(s, 0)) == .partial__fun_def_header_ret) t.arg(t.arg(s, 0), 1) else 0,
        else => blk: {
            const fields = ParseTree.Node.nk_field_names[@intFromEnum(t.kind(x))];
            const k = ParseTree.Node.nk_childc[@intFromEnum(t.kind(x))];
            for (0..@as(usize, if (k == .one) 1 else if (k == .two) 2 else 0)) |i| if (std.mem.eql(u8, fields[i], r.name_pool.get(name))) break :blk t.arg(x, @intCast(i));
            break :blk 0;
        },
    };
    return if (got == 0) null else got;
}

fn case_name(t: *const ParseTree, x: NodeId) NodeId {
    var n = x;
    while (t.kind(n) == .partial__variant_def_param_typed or t.kind(n) == .partial__variant_def_param_tagged) n = t.arg(n, 0);
    return if (t.kind(n) == .partial__variant_def_param) t.arg(n, 0) else 0;
}

// the list node a list view of `x` is. a type that has none grows it when it is written (`$methods`, `$implof`)
fn list(self: *Trees, x: NodeId, name: NamePool.Index, grow: bool) ?NodeId {
    const r = self.interp().res();
    const t = r.tree;
    const s = subject(t, x);
    switch (name) {
        .decls => return if (t.kind(x) == .block) x else null,
        .params => return if (t.kind(s) == .def_fun) t.arg(t.arg(s, 0), 0) else null,
        .fields, .cases => {
            const c = ParseTree.Def.from_node(t, s).core;
            const want: Kind = if (name == .fields) .partial__type_def_param_tuple else .partial__variant_def_param_tuple;
            return if (t.kind(t.arg(c, 0)) == want and (t.kind(c) == .def_type or t.kind(c) == .def_type_packed or t.kind(c) == .def_variant or t.kind(c) == .def_variant_unionsized)) t.arg(c, 0) else null;
        },
        .methods, .implof => {
            var tr = if (t.kind(s) == .def_trait or t.kind(s) == .def_trait_implof) s else ParseTree.Def.from_node(t, s).body;
            if (tr == 0) {
                if (!grow or r.decls.type_kind(s) == .variable) return null;
                // the type moves into one with an empty `!{}`
                const inner = t.push_node(t.kind(s));
                t.ast_nodes.pool.args.buf[inner] = t.ast_nodes.pool.args.buf[s];
                tr = t.push_node_with(.def_trait, .{ .body = t.push_node(.partial__trait_def_body) });
                const w = t.push_node(if (r.decls.type_kind(s) == .variant) .def_variant_implof else .def_type_implof);
                t.ast_nodes.pool.args.buf[w] = .{ inner, tr };
                t.overwrite(s, w);
            }
            if (name == .methods) return t.arg(tr, @intFromBool(t.kind(tr) == .def_trait_implof));
            if (t.kind(tr) == .def_trait_implof) return t.arg(tr, 0);
            if (!grow) return null;
            const tuple = t.push_node(.partial__trait_def_implof_tuple);
            const body = t.arg(tr, 0);
            t.ast_nodes.pool.nk.buf[tr] = .def_trait_implof;
            t.ast_nodes.pool.args.buf[tr] = .{ tuple, body };
            return tuple;
        },
        else => return null,
    }
}

// `x.$name`, `x.cond`: a view or child of the tree `x`, `x.$src` its text, `x.$children` and the list views as `[]ast`
pub fn member(self: *Trees, n: NodeId, base: Value) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const t = r.tree;
    const x = self.node_of(base).?;
    const name = r.name_pool.name_of(t.arg(n, 1));
    const ty = self.type_at(n);
    switch (name) {
        .src => return .pooled(sp.intern(.{ .string = self.src_of(x) })),
        .mut => return .boolean(is_param(t.kind(x)) and ParseTree.Param.from_node(t, x).is_mut),
        .children, .decls, .fields, .cases, .methods, .params, .implof => {
            const kids = if (name == .children) t.children(x) else t.manychildren(self.list(x, name, false) orelse return ip.fail(n, .unknown_member, name, .ast_type));
            const mark = ip.ids.head;
            defer ip.ids.head = mark;
            for (kids) |c| if (c != 0) ip.ids.push(self.value(sp.array_elem(ty), c).index());
            return .pooled(sp.intern(.{ .aggregate = .{ .ty = ty, .elems = ip.ids.buf[mark..ip.ids.head] } }));
        },
        else => return self.value(ty, self.view(x, name) orelse return ip.fail(n, .unknown_member, name, .ast_type)),
    }
}

// the source a tree was written as, a made name its text, a keyword (`u32`, `true`) itself
fn src_of(self: *Trees, x: NodeId) []const u8 {
    const r = self.interp().res();
    const k = r.tree.kind(x);
    if (ParseTree.Node.nk_childc[@intFromEnum(k)] == .data) return r.tree.text(x, r.src_bytes);
    const e = r.tree.extent(x) orelse return switch (k) {
        .boolean_true => "true",
        .boolean_false => "false",
        .identifier_self => "self",
        else => if (@intFromEnum(k) >= @intFromEnum(Kind.type_u8) and @intFromEnum(k) <= @intFromEnum(Kind.type_stcfun)) @tagName(k)["type_".len..] else "",
    };
    return r.src_bytes[e[0]..e[1]];
}

// `ast.Identifier`: the type of trees of that root
pub fn case(self: *Trees, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const name = r.name_pool.name_of(r.tree.arg(n, 1));
    const k = ParseTree.Node.named.get(r.name_pool.get(name)) orelse return ip.fail(n, .unknown_member, name, .ast_type);
    return .pooled(r.static_pool.ast_of(.none, @as(u16, @intFromEnum(k)) + 1));
}

// writes into trees: `x.v = y`, `x.* = y`, `x.$decls[i] = y` make the node there a landed copy of `y`. false: no tree place
pub fn write(self: *Trees, n: NodeId, v: Value) bool {
    const ip = self.interp();
    const r = ip.res();
    const t = r.tree;
    const k = t.kind(n);
    if (k != .member and k != .dereference and k != .array_index) return false;
    const base = t.arg(n, 0);
    if (!r.static_pool.is_tree(ip.checked(base)) and !(k == .array_index and t.kind(base) == .member and r.static_pool.is_tree(ip.checked(t.arg(base, 0))))) return false;
    var into: Kind = .none;
    const target: ?NodeId = switch (k) {
        .dereference => self.node_of(ip.eval(base)),
        .member => if (self.node_of(ip.eval(base))) |x| self.view(x, r.name_pool.name_of(t.arg(n, 1))) else null,
        else => blk: {
            const x = self.node_of(ip.eval(t.arg(base, 0))) orelse break :blk null;
            const l = self.list(x, r.name_pool.name_of(t.arg(base, 1)), false) orelse break :blk null;
            const i = ip.eval(t.arg(n, 1));
            into = t.kind(l);
            break :blk if (Value.is_int(i.ty) and i.bits < t.arg(l, 1)) t.manychildren(l)[@intCast(i.bits)] else null;
        },
    };
    const src = self.node_of(v);
    if (target == null or src == null) {
        if (!v.is(.poison_type)) _ = ip.fail(n, .not_static, 0, 0);
        return true;
    }
    if (self.writable(n, target.?)) t.overwrite(target.?, self.land(src.?, into));
    return true;
}

// `xs += y` of trees: y (or each tree of it) appended to a list view of a tree, or to a `[]ast` variable. null: no list of trees
pub fn append(self: *Trees, n: NodeId) ?Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const t = r.tree;
    const target = t.arg(n, 0);
    const lt = sp.apply_vars(&r.abstract_pool, ip.checked(target));
    if (lt == .none or sp.tag(lt) != .array_type or !sp.is_tree(sp.get(lt).array_type.elem)) return null;
    const v = ip.eval(t.arg(n, 1));
    if (v.is(.poison_type)) return v;
    const mark = ip.ids.head;
    defer ip.ids.head = mark;
    if (self.node_of(v) != null) ip.ids.push(v.index()) else for (0..ip.span(v) orelse 0) |i| ip.ids.push(ip.pool(ip.elem(v, @intCast(i))));
    if (t.kind(target) == .member and sp.is_tree(ip.checked(t.arg(target, 0)))) {
        const x = self.node_of(ip.eval(t.arg(target, 0))) orelse return .poison;
        const l = self.list(x, r.name_pool.name_of(t.arg(target, 1)), true) orelse return ip.fail(target, .unknown_member, r.name_pool.name_of(t.arg(target, 1)), .ast_type);
        if (!self.writable(n, l)) return .poison;
        const items = r.scratch(NodeId, ip.ids.head - mark);
        for (ip.ids.buf[mark..ip.ids.head], 0..) |e, i| items[i] = self.land(sp.get(e).tree.node, t.kind(l));
        t.grow_list(l, items);
        return .unit;
    }
    const c = ip.variables.cell(target) orelse return .poison;
    const old = ip.mem.buf[c];
    const len = ip.span(old) orelse 0;
    const at = ip.alloc(len + ip.ids.head - mark);
    for (0..len) |i| ip.mem.buf[at + i] = ip.elem(old, @intCast(i));
    for (ip.ids.buf[mark..ip.ids.head], len..) |e, i| ip.mem.buf[at + i] = ip.own(.pooled(e));
    ip.set(c, .block(lt, at, len + ip.ids.head - mark));
    return .unit;
}

// the program is written while a splice is evaluated, a declaration until it is resolved. what macros made is theirs
fn writable(self: *Trees, at: NodeId, target: NodeId) bool {
    const ip = self.interp();
    const r = ip.res();
    if (target >= r.macros.pass_len) return true;
    const root = r.macros.root_of(target);
    const d = if (root == 0) .none else r.node_decl[root];
    if (r.macros.splicing > 0 and (d == .none or r.decl_pool.get_state(d) == .unresolved)) {
        r.macros.edited = true;
        return true;
    }
    _ = ip.fail(at, .frozen_declaration, d, 0);
    return false;
}

// `x.&` of a tree: a `*ast` to it, `p.*` of one: the tree
pub fn address(self: *Trees, n: NodeId) ?Value {
    const ip = self.interp();
    const r = ip.res();
    const x = r.tree.arg(n, 0);
    if (!r.static_pool.is_tree(ip.checked(x)) or r.static_pool.is_ptr(ip.checked(x))) return null;
    const v = ip.eval(x);
    return self.value(self.type_at(n), self.node_of(v) orelse return v);
}

// `x with (lhs = y)`: a new root of x's kind, its children those of x but the ones named
pub fn with(self: *Trees, n: NodeId, base: Value) Value {
    const ip = self.interp();
    const r = ip.res();
    const t = r.tree;
    const x = self.node_of(base).?;
    const k = t.kind(x);
    const cc = ParseTree.Node.nk_childc[@intFromEnum(k)];
    if (cc != .one and cc != .two) return ip.fail(n, .not_static, 0, 0);
    var kids: [2]NodeId = t.ast_nodes.pool.args.buf[x];
    for (t.manychildren(t.arg(n, 1))) |a| {
        const name = r.name_pool.get(r.name_pool.name_of(t.arg_name(a)));
        const fields = ParseTree.Node.nk_field_names[@intFromEnum(k)];
        const i: usize = for (0..@as(usize, if (cc == .one) 1 else 2)) |i| {
            if (std.mem.eql(u8, fields[i], name)) break i;
        } else return ip.fail(a, .unknown_named_argument, r.name_pool.name_of(t.arg_name(a)), 0);
        const v = ip.eval(t.arg_value(a));
        kids[i] = self.node_of(v) orelse return if (v.is(.poison_type)) v else ip.fail(a, .type_mismatch, ip.vtype(v), .ast_type);
    }
    const c = t.push_node(k);
    t.ast_nodes.pool.args.buf[c] = kids;
    return self.value(r.static_pool.pointee(ip.vtype(base)), c);
}

// `ast(T)`, `ast.Kind(..)` making a node from its children or a name or literal from its text
pub fn call(self: *Trees, n: NodeId, target: Index, args: []const NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const sp = &r.static_pool;
    const t = r.tree;
    const a = sp.get(target).ast;
    if (a.case == 0) {
        const x = r.tree.arg_value(args[0]);
        // `ast(())`: of code producing nothing
        if (t.kind(x) == .def_fun_declaration and t.params_of(x).len == 0) return .pooled(sp.ast_of(.unit_type, 0));
        return .pooled(sp.ast_of(ip.types.of(x) orelse return .poison, 0));
    }
    const k: Kind = @enumFromInt(a.case - 1);
    const mark = ip.ids.head;
    defer ip.ids.head = mark;
    for (args) |x| {
        const v = ip.eval(t.arg_value(x));
        if (v.is(.poison_type)) return v;
        ip.ids.push(ip.pool(v));
    }
    const vals = ip.ids.buf[mark..ip.ids.head];
    const c = switch (ParseTree.Node.nk_childc[@intFromEnum(k)]) {
        .none => t.push_node(k),
        .data => t.push_word(k, t.first_token(n), self.text_of(.pooled(vals[0])) orelse return ip.fail(n, .type_mismatch, sp.type_of(vals[0]), .ast_type), 0, false),
        else => blk: {
            const kids = r.scratch(NodeId, vals.len);
            for (vals, kids) |v, *kid| kid.* = self.node_of(.pooled(v)) orelse return ip.fail(n, .type_mismatch, sp.type_of(v), .ast_type);
            const x = t.push_node(k);
            if (ParseTree.Node.nk_childc[@intFromEnum(k)] == .many) t.set_children(x, kids) else t.ast_nodes.pool.args.buf[x] = .{ kids[0], if (kids.len > 1) kids[1] else 0 };
            break :blk x;
        },
    };
    return self.value(target, c);
}

// `$fresh("tmp")`: a name like no other, `$error(tree, "..")` an error at the tree that ends the evaluation
pub fn builtin(self: *Trees, n: NodeId, name: NamePool.Index, args: []const NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const t = r.tree;
    const a = ip.eval(t.arg_value(args[0]));
    if (a.is(.poison_type)) return a;
    if (name == .fresh) {
        var buf: [256]u8 = undefined;
        const s = std.fmt.bufPrint(&buf, "{s}`{d}", .{ self.text_of(a) orelse "", r.macros.fresh }) catch return .poison;
        r.macros.fresh += 1;
        return self.value(r.static_pool.ast_of(.none, @as(u16, @intFromEnum(Kind.identifier)) + 1), t.push_word(.identifier, t.first_token(n), s, 0, false));
    }
    const msg = ip.eval(t.arg_value(args[1]));
    if (msg.is(.poison_type)) return msg;
    r.doc.report(.macro_error, self.node_of(a) orelse n, r.name_pool.intern_owned(self.text_of(msg) orelse ""), 0);
    return .poison;
}

// a tree for a parameter `ast.Kind` (or each of a list for `[]ast.Kind`) has a root of that kind
pub fn admits(self: *Trees, v: Value, p: Index) bool {
    const ip = self.interp();
    const sp = &ip.res().static_pool;
    if (!sp.holds_trees(p)) return true;
    const e = sp.array_elem(p);
    if (e != .none) {
        for (0..ip.span(v) orelse 0) |i| if (!self.admits(ip.elem(v, @intCast(i)), e)) return false;
        return true;
    }
    const t = sp.pointee(p);
    if (t == .none or sp.tag(t) != .ast_type or sp.get(t).ast.case == 0) return true;
    const x = self.node_of(v) orelse return true;
    return @intFromEnum(ip.res().tree.kind(x)) + 1 == sp.get(t).ast.case;
}

// the type of trees of the root of a tree value (`ast.BinaryAdd`), for what is reported
pub fn kind_of(self: *Trees, v: Index) Index {
    const r = self.interp().res();
    const sp = &r.static_pool;
    if (sp.tag(v) != .tree_value) return sp.type_of(v);
    return sp.ast_of(.none, @as(u16, @intFromEnum(r.tree.kind(sp.get(v).tree.node))) + 1);
}

// `x oftype ast(fun)`: the root makes what the type says (a declaration of that kind, a function, a type), `ast.Kind` its kind
pub fn oftype(self: *Trees, x: NodeId, ty: Index) bool {
    const r = self.interp().res();
    const sp = &r.static_pool;
    const t = r.tree;
    if (sp.tag(ty) != .ast_type) return false;
    const a = sp.get(ty).ast;
    if (a.case != 0) return @intFromEnum(t.kind(x)) + 1 == a.case;
    if (a.of == .none) return true;
    const v = def_var(t, x);
    const s = subject(t, x);
    const made: Index = if (v != 0) switch (t.kind(t.arg(v, 0))) {
        .type_fun, .type_stcfun, .type_inlfun => .fun_type,
        .type_type, .type_variant, .type_trait => |k| if (k == .type_type) .type_type else if (k == .type_variant) .variant_type else .trait_type,
        else => .none,
    } else if (t.kind(s) == .def_fun) .fun_type else switch (r.decls.type_kind(s)) {
        .variable => .none,
        else => |k| k.meta(.type_type),
    };
    return made == a.of;
}

// a tree against a pattern: a name takes it, `ast.Kind(..)` tests its root and children, a quote its shape
pub fn matches(self: *Trees, p: NodeId, v: Value) bool {
    const ip = self.interp();
    const r = ip.res();
    const t = r.tree;
    const x = self.node_of(v).?;
    switch (t.kind(p)) {
        .identifier => {
            ip.patterns.name(p, v);
            return true;
        },
        .partial__match_case_pattern_or => {
            for (t.manychildren(p)) |alt| if (self.matches(alt, v)) return true;
            return false;
        },
        .quote => return self.shape(t.arg(p, 0), x),
        .fun_call => {
            const h = ip.info(.ty, p);
            const target = if (h != .none) h else ip.pool(ip.eval(t.arg(p, 0)));
            if (!self.oftype(x, target)) return false;
            const fields = ParseTree.Node.nk_field_names[@intFromEnum(t.kind(x))];
            const kids = t.children(x);
            for (t.manychildren(t.arg(p, 1)), 0..) |a, i| {
                const at = if (t.arg_name(a) == 0) i else for (fields, 0..) |f, j| {
                    if (std.mem.eql(u8, f, r.name_pool.get(r.name_pool.name_of(t.arg_name(a))))) break j;
                } else return false;
                if (at >= kids.len or !self.matches(t.arg_value(a), self.value(.ast_type, kids[at]))) return false;
            }
            return true;
        },
        else => {
            const pv = ip.eval(p);
            return pv.is_pool() and !pv.is(.none) and r.static_pool.tag(pv.index()) == .ast_type and self.oftype(x, pv.index());
        },
    }
}

// the shape of a quote pattern: holes take the trees where they stand (`@..xs` the rest of a list), the rest is equal
fn shape(self: *Trees, p0: NodeId, x0: NodeId) bool {
    const ip = self.interp();
    const r = ip.res();
    const t = r.tree;
    var p = p0;
    var x = x0;
    while (t.kind(p) == .capture) p = t.arg(p, 0);
    while (t.kind(x) == .capture) x = t.arg(x, 0);
    if (t.kind(p) == .unquote) {
        ip.patterns.name(t.arg(p, 0), self.value(.ast_type, x));
        return true;
    }
    if (t.kind(p) != t.kind(x)) return false;
    switch (ParseTree.Node.nk_childc[@intFromEnum(t.kind(p))]) {
        .none => return true,
        .data => return std.mem.eql(u8, t.text(p, r.src_bytes), t.text(x, r.src_bytes)),
        .one => return self.shape(t.arg(p, 0), t.arg(x, 0)),
        .two => return (t.arg(p, 0) == 0) == (t.arg(x, 0) == 0) and (t.arg(p, 0) == 0 or self.shape(t.arg(p, 0), t.arg(x, 0))) and self.shape(t.arg(p, 1), t.arg(x, 1)),
        .many => {
            const ps = t.manychildren(p);
            const xs = t.manychildren(x);
            for (ps, 0..) |c, i| {
                if (t.kind(c) == .unquote_list) {
                    const mark = ip.ids.head;
                    defer ip.ids.head = mark;
                    for (xs[@min(i, xs.len)..]) |e| ip.ids.push(self.value(.ast_type, e).index());
                    const sp = &r.static_pool;
                    ip.patterns.name(t.arg(c, 0), .pooled(sp.intern(.{ .aggregate = .{ .ty = sp.intern(.{ .array_type = .{ .len = StaticPool.dyn_len, .elem = .ast_type } }), .elems = ip.ids.buf[mark..ip.ids.head] } })));
                    return true;
                }
                if (i >= xs.len or !self.shape(c, xs[i])) return false;
            }
            return ps.len == xs.len;
        },
    }
}
