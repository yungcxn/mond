const std = @import("std");
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const calls = @import("calls.zig");
const types = @import("types.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;
const Body = Resolver.Body;
const max_nesting = 256;
const NamePool = @import("../NamePool.zig");

pub fn h08_eval_static(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    return self.interpreter.static_value(ctx, node);
}

pub fn deferred(self: *Resolver, ctx: *FnCtx, node: NodeId) ?StaticPool.Index {
    if (!ctx.interpreted) return h08_eval_static(self, ctx, node);
    const before = self.deferrals;
    const v = try_static(self, ctx, node);
    if (v != null and self.deferrals == before) return v;
    self.node_value[node] = .none;
    self.deferrals += 1;
    const s = self.tree.subtree(node);
    for (s[0]..s[1]) |i| switch (self.tree.kind(@intCast(i))) {
        .identifier, .identifier_self => {
            const d = self.h01_lookup(self.name_pool.name_of(self.tree, self.src_bytes, @intCast(i)));
            if (d != .none) self.node_decl[i] = d;
        },
        else => {},
    };
    return null;
}

// static evaluation that leaves no diagnostics behind when the node turns out not to be static
pub fn try_static(self: *Resolver, ctx: *FnCtx, node: NodeId) ?StaticPool.Index {
    const mark = self.doc.diagnostics.len();
    const ty = self.node_type[node];
    const v = h08_eval_static(self, ctx, node);
    if (self.doc.diagnostics.len() == mark and v != .poison_type) return v;
    self.doc.rewind(mark);
    self.node_type[node] = ty;
    self.node_value[node] = .none;
    self.interpreter.unwind = .none;
    return null;
}

pub fn static_of(self: *Resolver, ctx: *FnCtx, n: NodeId) StaticPool.Index {
    const c = Resolver.node_props[@intFromEnum(self.tree.kind(n))];
    return if (c.stc and c.loop and self.node_value[n] != .none) self.node_value[n] else h08_eval_static(self, ctx, n);
}

pub fn static_int(self: *Resolver, ctx: *FnCtx, n: NodeId) ?i128 {
    const sp = &self.static_pool;
    const v = try_static(self, ctx, n) orelse return null;
    if (sp.tag(v) != .int_value) return null;
    const i = sp.get(v).int;
    return if (sp.get(i.ty) == .int_type and sp.get(i.ty).int_type.signedness == .signed) @as(i64, @bitCast(i.bits)) else i.bits;
}

// the static value of a literal: ints as u64 (i64 when negated), floats as f64
pub fn literal_value(self: *Resolver, node: NodeId, negated: bool) StaticPool.Index {
    const sp = &self.static_pool;
    var neg = negated;
    const n = self.literal_core(node, &neg);
    var buf: [4096]u8 = undefined;
    switch (self.tree.kind(n)) {
        .boolean_true => return .bool_true,
        .boolean_false => return .bool_false,
        .string => {
            const s = self.tree.span(n);
            return sp.intern(.{ .string = unescape(self.src_bytes[s[0]..s[1]], &buf) });
        },
        .float => {
            const s = self.tree.span(n);
            const f = std.fmt.parseFloat(f64, self.src_bytes[s[0]..s[1]]) catch return if (self.doc.has(n)) .poison_type else self.report(.type_mismatch, n, .none, .none);
            return sp.intern(.{ .float = .{ .ty = .f64_type, .value = if (neg) -f else f } });
        },
        else => {
            const s = self.tree.span(n);
            const bits: u64 = if (self.tree.kind(n) == .char) unescape(self.src_bytes[s[0]..s[1]], &buf)[0] else std.fmt.parseInt(u64, self.src_bytes[s[0]..s[1]], 0) catch return if (self.doc.has(n)) .poison_type else self.report(.type_mismatch, n, .none, .u64_type);
            return sp.intern(.{ .int = if (neg) .{ .ty = .i64_type, .bits = 0 -% bits } else .{ .ty = .u64_type, .bits = bits } });
        },
    }
}

// untyped literals take the expected type when they fit, otherwise u32 / i32, then u64 / i64, floats f32
pub fn literal_type(self: *Resolver, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    var neg = false;
    const n = self.literal_core(node, &neg);
    const k = self.tree.kind(n);
    if (k == .boolean_true or k == .boolean_false) return .bool_type;
    const v = literal_value(self, n, neg);
    var target = sp.apply_vars(&self.abstract_pool, expected);
    if (k == .string and target != .none and sp.tag(target) == .ptr_type and sp.get(target).ptr_type.child == .u8_type) return target;
    if (k == .string and target != .none and sp.get(target) == .array_type and sp.get(target).array_type.elem == .u8_type and
        sp.tag(sp.get(target).array_type.len) == .int_value and sp.get(sp.get(target).array_type.len).int.bits >= sp.get(v).string.len) return target;
    if (v == .poison_type) return v;
    if (k == .string) return sp.type_of(v);
    if (target != .none and sp.tag(target) == .variant_type) target = sp.single_payload(target); // `Opt8 x = 42`
    const c = if (target == .none) StaticPool.TagProperties{} else sp.get_tag_prop(target);
    if (k == .float) return if (c.is_float) target else .f32_type;
    if ((c.is_integer or c.is_float) and sp.fits(v, target)) return target;
    return if (neg) (if (sp.fits(v, .i32_type)) .i32_type else .i64_type) else if (sp.fits(v, .u32_type)) .u32_type else .u64_type;
}

pub fn retype(self: *Resolver, v: StaticPool.Index, ty: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    if (v == .none or ty == .none) return v;
    if ((sp.tag(v) == .int_value or sp.tag(v) == .float_value) and sp.single_payload(ty) != .none) return self.interpreter.pool(self.interpreter.coerce(.of(sp, v), ty));
    if (sp.tag(v) != .int_value) return v;
    if (sp.get_tag_prop(ty).is_integer) return sp.intern(.{ .int = .{ .ty = ty, .bits = sp.get(v).int.bits } });
    if (!sp.get_tag_prop(ty).is_float) return v;
    const i = sp.get(v).int;
    const signed = sp.get(i.ty) == .int_type and sp.get(i.ty).int_type.signedness == .signed;
    return sp.intern(.{ .float = .{ .ty = ty, .value = if (signed) @floatFromInt(@as(i64, @bitCast(i.bits))) else @floatFromInt(i.bits) } });
}

pub fn h20_instantiate(self: *Resolver, generic: DeclPool.Index, args: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const key = StaticPool.AbstractKey{ .generic_tuple = generic, .args_tuple = args };
    if (sp.realized_abstracts.get(key)) |r| return r;
    const node = self.decl_pool.nodes()[@intFromEnum(generic)];
    // a realization that realizes itself forever eats the static budget and stops there
    if (self.local_scope_marks.head > max_nesting) return self.report(.static_eval_failed, self.interpreter.origin(node), generic, 0);
    if (!self.interpreter.charge(node, 64)) return .poison_type;
    const argv = self.scratch(StaticPool.Index, sp.get(args).aggregate.elems.len);
    const argc = argv.len;
    @memcpy(argv, sp.get(args).aggregate.elems);

    if (self.decl_pool.kinds()[@intFromEnum(generic)] != .static_function) {
        // length-generic function: a new declaration per tuple of lengths, the lengths bound in order of appearance
        self.h06_check_body(generic);
        if (self.decl_pool.states()[@intFromEnum(generic)] == .failed) return .poison_type;
        const d = self.decl_pool.push_decl(self.decl_pool.names()[@intFromEnum(generic)], node, self.decl_pool.kinds()[@intFromEnum(generic)], .none, self.decl_pool.flags()[@intFromEnum(generic)]);
        self.template_of.put(self.alloc, d, generic) catch @panic("OOM");
        const fv = sp.intern(.{ .function = d });
        memo(self, key, fv);
        const outer = self.static_scope.get(generic);
        if (outer) |k| {
            self.static_scope.put(self.alloc, d, k) catch @panic("OOM");
            self.open_scope(true, .none, 0);
            bind_static(self, k.generic_tuple, k.args_tuple);
        }
        defer if (outer != null) self.h04_pop_scope();
        self.h05_ensure_signature(d);
        self.realized_args.put(self.alloc, d, args) catch @panic("OOM");
        const ft = sp.get(self.decl_pool.tys()[@intFromEnum(d)]).function_type;
        const ps = self.scratch(StaticPool.Index, ft.params.len);
        @memcpy(ps, ft.params);
        var i: usize = 0;
        for (ps) |*q| {
            var p = q.*;
            if (!generic_slot(self, p) or i >= argc) continue;
            i += 1;
            if (templated(self, p) != .none) q.* = if (sp.get(p) == .ptr_type) sp.intern(.{ .ptr_type = .{ .child = argv[i - 1], .mutable = sp.get(p).ptr_type.mutable } }) else argv[i - 1];
            if (sp.get(p) == .ptr_type) p = sp.get(p).ptr_type.child;
            if (sp.get(p) == .array_type) _ = sp.unify(&self.abstract_pool, sp.get(p).array_type.len, argv[i - 1]);
        }
        self.decl_pool.tys()[@intFromEnum(d)] = sp.intern(.{ .function_type = .{ .category = ft.category, .params = ps, .ret = ft.ret } });
        self.h06_check_body(d);
        return fv;
    }

    var ctx = FnCtx{ .decl = generic, .in_static = true };
    self.open_scope(true, .none, 0);
    defer self.h04_pop_scope();
    const v = self.value_node(generic);
    const params = self.params_of(v);
    bind_static(self, generic, args);
    for (params) |pn| {
        const w = Resolver.Param.from_node(self, pn).where;
        if (w != 0 and h08_eval_static(self, &ctx, w) == .bool_false) _ = self.report(.stcwhere_violated, w, generic, args);
    }
    const unit = self.tree.arg(v, 1);
    const kind = self.type_kind(unit);
    if (kind != .variable) { // a type: memoized before its body, so it can mention itself (`Stream(Child)` inside Stream)
        const d = self.decl_pool.push_decl(self.decl_pool.names()[@intFromEnum(generic)], unit, kind, .none, .{});
        self.realized_args.put(self.alloc, d, args) catch @panic("OOM");
        self.template_of.put(self.alloc, d, generic) catch @panic("OOM");
        self.decl_pool.values()[@intFromEnum(d)] = sp.reserve_nominal(d);
        memo(self, key, self.decl_pool.values()[@intFromEnum(d)]);
        return types.h19_check_type_def(self, &ctx, d, unit);
    }
    if (self.tree.kind(unit) == .def_fun) {
        const d = self.decl_pool.push_decl(self.decl_pool.names()[@intFromEnum(generic)], unit, .function, .none, .{});
        const fv = sp.intern(.{ .function = d });
        memo(self, key, fv);
        self.static_scope.put(self.alloc, d, key) catch @panic("OOM");
        self.h05_ensure_signature(d);
        self.h06_check_body(d);
        return fv;
    }
    ctx.in_static = false;
    ctx.interpreted = true;
    ctx.ret_type = self.sig(generic).ret;
    const first = self.decl_pool.entries.len();
    const vars = self.abstract_pool.count();
    const outer = self.init_enter();
    const mark = self.doc.diagnostics.len();
    self.check_unit(&ctx, unit);
    ctx.interpreted = false;
    self.init_leave(outer);
    if (self.errors_since(mark, unit)) {
        memo(self, key, .poison_type);
        return .poison_type;
    }
    for (vars..self.abstract_pool.count()) |i| switch (self.tree.kind(self.abstract_pool.pool.sliced_field(.origin)[i])) {
        .@"while", .while_with_repeat_stmt, .loop, .loop_with_repeat_stmt => if (self.abstract_pool.binding(@enumFromInt(i)) == .none) self.abstract_pool.bind(@enumFromInt(i), StaticPool.dyn_len),
        else => {},
    };
    const r = self.interpreter.run(&ctx, unit, capture(self, generic, v, first));
    const made = if (sp.tag(ctx.ret_type) == .meta_type and sp.get_tag_prop(r).is_type) nominal(self, r) else .none;
    if (made != .none and @intFromEnum(made) >= first) self.template_of.put(self.alloc, made, generic) catch @panic("OOM");
    memo(self, key, r);
    return r;
}

// the static parameters of a stcfun as locals holding the arguments of one realization
fn bind_static(self: *Resolver, generic: DeclPool.Index, args: StaticPool.Index) void {
    const sp = &self.static_pool;
    const argv = self.scratch(StaticPool.Index, sp.get(args).aggregate.elems.len);
    @memcpy(argv, sp.get(args).aggregate.elems);
    for (self.params_of(self.value_node(generic)), 0..) |pn, i| {
        const pt = if (sp.has_vars(self.sig(generic).params[i])) sp.type_of(argv[i]) else self.sig(generic).params[i];
        const p = Resolver.Param.from_node(self, pn);
        const d = self.h02_declare_local(self.name_at(p, i), pn, .static_parameter, pt);
        calls.link(self, p.name, d, pt);
        self.decl_pool.values()[@intFromEnum(d)] = retype(self, argv[i], pt);
    }
}

pub fn is_template(self: *Resolver, d: DeclPool.Index) bool {
    if (d == .none or self.decl_pool.kinds()[@intFromEnum(d)] != .static_function or self.decl_pool.tys()[@intFromEnum(d)] == .none) return false;
    const t = self.decl_pool.tys()[@intFromEnum(d)];
    return self.static_pool.tag(t) == .function_type and self.static_pool.tag(self.static_pool.get(t).function_type.ret) == .meta_type;
}

pub fn length_generic(self: *Resolver, ty: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (ty == .none or sp.tag(ty) != .function_type) return false;
    for (0..sp.get(ty).function_type.params.len) |i| {
        const p = sp.get(ty).function_type.params[i];
        if (sp.has_vars(sp.apply_vars(&self.abstract_pool, p)) or sp.tag(p) == .meta_type or templated(self, p) != .none) return true;
    }
    return false;
}

pub fn only_templates(self: *Resolver, ty: StaticPool.Index) bool {
    for (self.static_pool.get(ty).function_type.params) |p| if (generic_slot(self, p) and templated(self, p) == .none) return false;
    return true;
}

// parameters a function is realized for: unlengthed arrays (per length), `type` parameters (per type) and templates (per realization)
pub fn generic_slot(self: *Resolver, p: StaticPool.Index) bool {
    return self.static_pool.has_vars(p) or self.static_pool.tag(p) == .meta_type or templated(self, p) != .none;
}

pub fn templated(self: *Resolver, p: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    if (p == .none or p == .poison_type) return .none;
    const t = sp.pointee(p);
    return if (sp.tag(t) == .template_type) t else .none;
}

pub fn realizes(self: *Resolver, t0: StaticPool.Index, tmpl: StaticPool.Index) bool {
    const sp = &self.static_pool;
    const t = unwrapped(self, t0);
    const g = sp.get(tmpl).template_type;
    if (t == tmpl or source_of(self, t) == g) return true;
    const own: []const StaticPool.Index = switch (sp.get(t)) {
        .custom_type => |c| c.traits,
        .variant_type => |v| v.traits,
        else => &.{},
    };
    for (own) |tr| if (sp.tag(tr) == .trait_type and self.template_of.get(sp.get(tr).trait_type.decl) == g) return true;
    return false;
}

pub fn passes(self: *Resolver, t0: StaticPool.Index, p: StaticPool.Index) bool {
    const sp = &self.static_pool;
    const t = sp.apply_vars(&self.abstract_pool, t0);
    if (t == .poison_type) return true;
    if (sp.is_ptr(p) != sp.is_ptr(t)) return false;
    if (sp.get(p) == .ptr_type and sp.get(p).ptr_type.mutable and !sp.get(t).ptr_type.mutable) return false;
    return realizes(self, t, templated(self, p));
}

pub fn unwrapped(self: *Resolver, t0: StaticPool.Index) StaticPool.Index {
    const t = self.deref(t0);
    return if (self.static_pool.tag(t) == .variant_case_type) self.static_pool.get(t).variant_case_type.variant else t;
}

fn nominal(self: *Resolver, t0: StaticPool.Index) DeclPool.Index {
    return switch (self.static_pool.get(unwrapped(self, t0))) {
        .custom_type => |c| c.decl,
        .variant_type => |v| v.decl,
        .trait_type => |x| x.decl,
        else => .none,
    };
}

pub fn source_of(self: *Resolver, t: StaticPool.Index) DeclPool.Index {
    const d = nominal(self, t);
    return if (d == .none) .none else self.template_of.get(d) orelse .none;
}

pub fn sibling(self: *Resolver, ctx: *FnCtx, t: StaticPool.Index, st: StaticPool.Index) bool {
    if (templated(self, st) != .none) return realizes(self, t, templated(self, st));
    if (templated(self, t) != .none) return realizes(self, st, templated(self, t));
    const g = source_of(self, st);
    return g != .none and source_of(self, t) == g and opened(self, ctx);
}

pub fn opened(self: *Resolver, ctx: *FnCtx) bool {
    const g = (if (ctx.decl == .none) null else self.template_of.get(ctx.decl)) orelse return false;
    const ty = self.decl_pool.tys()[@intFromEnum(g)];
    if (ty == .none or self.static_pool.tag(ty) != .function_type) return false;
    for (self.static_pool.get(ty).function_type.params) |p| if (templated(self, p) != .none) return true;
    return false;
}

pub fn holds_template(self: *Resolver, t: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (t == .none or t == .poison_type) return false;
    return switch (sp.get(t)) {
        .template_type => true,
        .ptr_type => |x| holds_template(self, x.child),
        .array_type => |x| holds_template(self, x.elem),
        .function_type => |f| for (f.params) |x| {
            if (holds_template(self, x)) break true;
        } else holds_template(self, f.ret),
        else => false,
    };
}

pub fn open_type_var(self: *Resolver, t: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (t == .none or !sp.has_vars(t)) return false;
    return switch (sp.get(t)) {
        .abstract_type => true,
        .array_type => |a| open_type_var(self, a.elem),
        .ptr_type => |p| open_type_var(self, p.child),
        .function_type => |f| for (f.params) |p| {
            if (open_type_var(self, p)) break true;
        } else open_type_var(self, f.ret),
        else => false,
    };
}

// the static length an argument gives an unlengthed parameter (`&[5]u32` for `&[]u32`), or none
pub fn arg_len(self: *Resolver, t0: StaticPool.Index, p0: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    var t = sp.apply_vars(&self.abstract_pool, t0);
    var p = p0;
    if (t == .poison_type) return .none;
    if (sp.get(p) == .ptr_type) {
        if (sp.get(t) != .ptr_type or (sp.get(p).ptr_type.mutable and !sp.get(t).ptr_type.mutable)) return .none;
        t = sp.get(t).ptr_type.child;
        p = sp.get(p).ptr_type.child;
    }
    if (sp.get(t) != .array_type or sp.get(p) != .array_type or sp.get(t).array_type.elem != sp.get(p).array_type.elem) return .none;
    const len = sp.get(t).array_type.len;
    return if (sp.tag(len) == .int_value or len == StaticPool.dyn_len) len else .none;
}

pub fn template_member(self: *Resolver, node: NodeId, t: StaticPool.Index, name: NamePool.Index) StaticPool.Index {
    const g = self.static_pool.get(t).template_type;
    const kind = self.template(g);
    if (kind == .variable) return self.report(.generic_member, node, name, t);
    const v = self.value_node(g);
    const unit = self.tree.arg(v, 1);
    var ctx = FnCtx{ .in_static = true };
    self.open_scope(true, .none, 0);
    defer self.h04_pop_scope();
    if (kind == .record) if (self.template_field(g, name)) |f| {
        const p = Resolver.Param.from_node(self, f);
        return if (self.mentions(p.ty, v)) self.report(.generic_member, node, name, t) else types.h07_lower_type(self, &ctx, p.ty);
    };
    const w = self.definition(unit);
    const tr = if (self.type_kind(w.core) == .trait) w.core else if (w.body != 0) w.body else return self.report(.unknown_member, node, name, t);
    for (self.tree.manychildren(self.tree.arg(tr, if (self.tree.kind(tr) == .def_trait_implof) 1 else 0))) |s| {
        const parts = Resolver.Stmt.from_node(self, s);
        if (parts.assignees.len != 1 or self.name_pool.name_of(self.tree, self.src_bytes, parts.assignees[0]) != name or !parts.kind.is_fn()) continue;
        return if (self.signature_mentions(parts.values[0], v)) self.report(.generic_member, node, name, t) else types.fun_type(self, &ctx, parts.values[0], .default, .poison_type, .none);
    }
    return self.report(.unknown_member, node, name, t);
}

// the node tables of one checked body or type definition, as realizations share their nodes
pub fn snapshot(self: *Resolver, decl: DeclPool.Index, root: NodeId, first: u32) void {
    self.body_of.put(self.alloc, decl, self.bodies.len()) catch @panic("OOM");
    self.bodies.push(capture(self, decl, root, first));
}

fn capture(self: *Resolver, decl: DeclPool.Index, root: NodeId, first: u32) Body {
    const lo, const hi = self.tree.subtree(root);
    const b = Body{ .decl = decl, .lo = lo, .len = hi - lo, .start = self.body_nodes.len(), .first = first, .locals = self.decl_pool.entries.len() - first };
    self.body_nodes.pool.ty.append(self.node_type[lo..hi]);
    self.body_nodes.pool.decl.append(self.node_decl[lo..hi]);
    self.body_nodes.pool.value.append(self.node_value[lo..hi]);
    return b;
}

fn memo(self: *Resolver, key: StaticPool.AbstractKey, v: StaticPool.Index) void {
    self.static_pool.realized_abstracts.put(self.alloc, key, v) catch @panic("OOM");
}

pub fn unescape(raw: []const u8, buf: []u8) []const u8 {
    if (raw.len > buf.len) return raw;
    var n: usize = 0;
    var i: usize = 0;
    while (i < raw.len) : (i += 1) {
        var c = raw[i];
        if (c == '\\' and i + 1 < raw.len) {
            i += 1;
            if (raw[i] == 'x' and i + 2 < raw.len) if (std.fmt.parseInt(u8, raw[i + 1 .. i + 3], 16)) |x| {
                buf[n] = x;
                n += 1;
                i += 2;
                continue;
            } else |_| {};
            c = switch (raw[i]) {
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                '0' => 0,
                else => raw[i],
            };
        }
        buf[n] = c;
        n += 1;
    }
    return buf[0..n];
}
