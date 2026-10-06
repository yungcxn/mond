const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const syntax = @import("../syntax.zig");
const StaticPool = @import("../StaticPool.zig");
const decls = @import("decls.zig");
const exprs = @import("exprs.zig");
const types = @import("types.zig");
const statics = @import("statics.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// control flow: if, loops and unwraps, the types branches join to, the written locals they leave

// control flow: if, loops and unwraps, the types branches join to, the written locals they leave

// control flow: if, loops and unwraps, the types branches join to, the written locals they leave

pub fn h15_check_branching(self: *Resolver, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const k = self.tree.kind(node);
    const has_else = k == .if_else or k == .stcif_else;
    const it = if (has_else) self.tree.arg(node, 0) else node;
    const cond = self.tree.arg(it, 0);
    const then = self.tree.arg(it, 1);
    const stc = k == .stcif_then or k == .stcif_else;
    const c = if (ctx.interpreted or stc and ctx.abstract) statics.try_static(self, ctx, cond) orelse .none else if (stc) statics.h08_eval_static(self, ctx, cond) else .none;
    if (c == .bool_true or c == .bool_false or c != .none and !ctx.interpreted) {
        _ = self.set(cond, .bool_type);
        if (c == .bool_true) return branch(self, ctx, then, expected);
        if (c != .bool_false) return if (c == .poison_type) c else self.report(.type_mismatch, cond, self.static_pool.type_of(c), .bool_type);
        return if (has_else) branch(self, ctx, self.tree.arg(node, 1), expected) else .unit_type;
    }
    // binders of the condition (`x ?<- v`) are visible in the then branch only
    const m = self.inits.count;
    defer self.inits.release(m);
    self.scopes.h03_push_scope();
    const w = condition(self, ctx, cond);
    self.inits.copy(0, w[0]);
    const was = self.static_pool.concrete(&self.abstract_pool, expected);
    const tt = branch(self, ctx, then, expected);
    const after_then = self.inits.new();
    if (tt != .never_type) self.inits.copy(after_then, 0);
    self.inits.copy(0, w[1]);
    self.scopes.h04_pop_scope();
    if (!has_else) {
        self.inits.merge(0, after_then);
        const valued = tt != .never_type and tt != .runit_type and tt != .poison_type and tt != .unit_type;
        return if (self.static_pool.concrete(&self.abstract_pool, expected) and valued) self.report(.runit_mixing, node, tt, .unit_type) else merge(self, node, tt, .unit_type, if (valued) .none else expected);
    }
    const et = branch(self, ctx, self.tree.arg(node, 1), expected);
    if (et == .never_type) self.inits.copy(0, after_then) else self.inits.merge(0, after_then);
    const ts = if (was) tt else settle(self, then, tt, expected);
    return merge(self, node, adapt(self, then, ts, et), adapt(self, self.tree.arg(node, 1), et, ts), expected);
}

// the locals not written yet when a condition is true and when it is false: `and` runs its right side only after a true left one
pub fn condition(self: *Resolver, ctx: *FnCtx, n: NodeId) [2]u32 {
    const k = self.tree.kind(n);
    if (k == .capture) {
        const w = condition(self, ctx, self.tree.arg(n, 0));
        _ = self.set(n, self.node_type[self.tree.arg(n, 0)]);
        return w;
    }
    if (k != .binary_logic_and and k != .binary_logic_or) {
        _ = exprs.check(self, ctx, n, .bool_type);
        const s = self.inits.save(0);
        return .{ s, s };
    }
    const l = condition(self, ctx, self.tree.arg(n, 0));
    self.inits.copy(0, l[@intFromBool(k == .binary_logic_or)]);
    const r = condition(self, ctx, self.tree.arg(n, 1));
    _ = self.set(n, .bool_type);
    const both = self.inits.save(l[@intFromBool(k == .binary_logic_and)]);
    self.inits.merge(both, r[@intFromBool(k == .binary_logic_and)]);
    return if (k == .binary_logic_and) .{ r[0], both } else .{ both, r[1] };
}

// the first type of the literals among `ns` that every one of them fits
pub fn literals_type(self: *Resolver, ns: []const NodeId) StaticPool.Index {
    for (ns) |c| if (syntax.is_literal(self.tree, c)) {
        const ct = self.node_type[c];
        for (ns) |n| {
            if (syntax.is_literal(self.tree, n) and statics.literal_type(self, n, ct) != ct) break;
        } else return ct;
    };
    return .none;
}

// a literal branch takes the type of the others (`if c: n else: 3`)
pub fn adapt(self: *Resolver, n: NodeId, t: StaticPool.Index, other: StaticPool.Index) StaticPool.Index {
    if (!syntax.is_literal(self.tree, n) or other == .none or statics.literal_type(self, n, other) != other) return t;
    return self.set(n, other);
}

pub fn h16_check_loop(self: *Resolver, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const k = self.tree.kind(node);
    const lp = syntax.Loop.from_node(self.tree, node);
    const exp = sp.apply_vars(&self.abstract_pool, expected);
    const elem_hint = sp.array_elem(exp);
    self.scopes.h03_push_scope();
    defer self.scopes.h04_pop_scope();
    if (lp.cond != 0) _ = exprs.check(self, ctx, lp.cond, .bool_type);
    if (lp.repeat != 0) _ = exprs.h09_check_expr(self, ctx, lp.repeat, .none);
    if (lp.cond != 0 and lp.repeat != 0) _ = self.set(lp.head, .unit_type);
    if (lp.seq != 0) {
        const st = sp.pointee(sp.apply_vars(&self.abstract_pool, exprs.h09_check_expr(self, ctx, lp.seq, if (elem_hint != .none and sp.get_tag_prop(elem_hint).is_integer and syntax.props(self.tree.kind(lp.seq)).range) exp else .none)));
        const elem = switch (sp.lookup_member(st, if (sp.get(st) == .array_type) .len else .next)) {
            .builtin_len => sp.get(st).array_type.elem,
            .method => |m| types.fn_ret(self, m),
            .trait_method => |m| types.fn_ret(self, sp.method_decl(m)),
            else => self.mismatch(lp.seq, st, .none),
        };
        const v = lp.variable;
        const it = decls.h02_declare_local(self, if (v != 0) self.name_pool.name_of(self.tree, self.src_bytes, v) else .it, if (v != 0) v else lp.head, if (v != 0) .loop_variable else .autoins_it, elem);
        self.node_decl[lp.head] = it;
        if (v != 0) {
            self.node_decl[v] = it;
            _ = self.set(v, elem);
            _ = self.set(lp.head, .unit_type);
        }
    }
    const m = self.inits.count;
    defer self.inits.release(m);
    const at_exit = self.inits.save(0);
    self.inits.exits.push(self.inits.new());
    ctx.loop_depth += 1;
    const jumps = self.jumps;
    // a stc loop body is static per iteration: checked like a stcfun body, evaluated with the loop
    const outer = ctx.interpreted;
    ctx.interpreted = outer or syntax.props(k).stc;
    const bt = exprs.h09_check_expr(self, ctx, lp.body, if (expected == .none) .none else if (elem_hint != .none) elem_hint else sp.fresh_var(&self.abstract_pool, lp.body));
    ctx.interpreted = outer;
    ctx.loop_depth -= 1;
    const broke = self.jumps[0] != jumps[0];
    const stepped = !broke and self.jumps[1] == jumps[1];
    self.jumps = jumps;
    self.inits.exits.head -= 1;
    if (lp.cond == 0 and lp.seq == 0) self.inits.clear(at_exit);
    self.inits.merge(at_exit, self.inits.exits.buf[self.inits.exits.head]);
    self.inits.copy(0, at_exit);
    if (!ctx.interpreted and !ctx.abstract and syntax.props(k).stc) _ = statics.static_of(self, ctx, node);
    // used as a value: an array of the body values; brk ends it without adding one, cont skips one
    if (lp.cond == 0 and lp.seq == 0 and !broke and elem_hint == .none) return .never_type;
    if (expected == .none) return .unit_type;
    const n = if (stepped and lp.seq != 0) steps(self, ctx, lp.seq) else null;
    return sp.intern(.{ .array_type = .{ .len = if (n) |x| sp.intern(.{ .int = .{ .ty = .u64_type, .bits = x } }) else sp.fresh_var(&self.abstract_pool, node), .elem = if (bt == .never_type or bt == .runit_type) (if (elem_hint != .none) elem_hint else .unit_type) else bt } });
}

// the static number of steps of a `for` over a range with static bounds or an array of static length
fn steps(self: *Resolver, ctx: *FnCtx, seq: NodeId) ?u64 {
    const sp = &self.static_pool;
    if (!syntax.props(self.tree.kind(seq)).range) {
        const st = sp.pointee(sp.apply_vars(&self.abstract_pool, self.node_type[seq]));
        return if (st != .poison_type and sp.tag(st) == .array_type and sp.tag(sp.get(st).array_type.len) == .int_value) sp.get(sp.get(st).array_type.len).int.bits else null;
    }
    const g = syntax.Range.from_node(self.tree, seq);
    if (g.hi == 0) return null;
    const lo = if (g.lo == 0) 0 else statics.static_int(self, ctx, g.lo) orelse return null;
    const hi = (statics.static_int(self, ctx, g.hi) orelse return null) + @intFromBool(g.incl);
    return if (hi > lo) @intCast(hi - lo) else 0;
}

// binders belong to their statement: a block scopes every non-declaring statement, a declaration its values
pub fn h17_check_unwrap(self: *Resolver, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const k = self.tree.kind(node);
    const vt = self.static_pool.apply_vars(&self.abstract_pool, exprs.h09_check_expr(self, ctx, self.tree.arg(node, 0), if (k == .labelarrow) expected else .none));
    if (k == .labelarrow) {
        bind_label(self, self.tree.arg(node, 1), vt);
        return vt;
    }
    const pt = payload_of(self, vt);
    if (pt == .none) return self.mismatch(self.tree.arg(node, 0), vt, .none);
    return switch (k) {
        .selftag_unwrap_fallback => blk: {
            const before = self.inits.save(0);
            _ = exprs.check(self, ctx, self.tree.arg(node, 1), pt);
            self.inits.copy(0, before);
            self.inits.release(before);
            break :blk pt;
        },
        .selftag_arrow => blk: {
            bind_label(self, self.tree.arg(node, 1), pt);
            break :blk .bool_type;
        },
        else => pt,
    };
}

// a branch of if / match: unit blocks and nested ifs / matches are runit, a plain unit value is not
pub fn branch(self: *Resolver, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    return settle(self, node, self.static_pool.apply_vars(&self.abstract_pool, exprs.h09_check_expr(self, ctx, node, expected)), expected);
}

pub fn settle(self: *Resolver, node: NodeId, t0: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    const t = if (t0 == .unit_type and syntax.props(self.tree.kind(node)).runit) .runit_type else t0;
    if (!self.static_pool.concrete(&self.abstract_pool, expected) or t == .never_type or t == .runit_type or t == .poison_type) return t;
    if (t == .unit_type and expected != .unit_type) return self.report(.runit_mixing, node, t, expected);
    return exprs.h10_expect(self, node, t, expected);
}

pub fn merge(self: *Resolver, node: NodeId, acc: StaticPool.Index, t: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    if (self.static_pool.concrete(&self.abstract_pool, expected)) return expected;
    if (acc == .none) return t;
    const j = self.static_pool.join(&self.abstract_pool, acc, t);
    if (j.ty != .none) return j.ty;
    if (expected == .none) return if (acc == .unit_type or t == .unit_type) .unit_type else self.report(.type_mismatch, node, acc, t);
    return self.report(if (acc == .unit_type or t == .unit_type) .runit_mixing else .type_mismatch, node, acc, t);
}

// `<- name` binds the value, `<- a, b` destructures a record in field order
pub fn bind_label(self: *Resolver, label: NodeId, t: StaticPool.Index) void {
    const sp = &self.static_pool;
    if (self.tree.kind(label) != .partial__destructure) {
        decls.redeclared(self, self.name_pool.name_of(self.tree, self.src_bytes, label), label);
        self.node_decl[label] = decls.h02_declare_local(self, self.name_pool.name_of(self.tree, self.src_bytes, label), label, .arrow_binder, t);
        _ = self.set(label, t);
        return;
    }
    const rt = sp.apply_vars(&self.abstract_pool, t);
    for (self.tree.manychildren(label), 0..) |id, i| {
        const ft = if (sp.tag(rt) == .record_type and i < sp.get(rt).custom_type.field_types.len) sp.get(rt).custom_type.field_types[i] else self.mismatch(id, t, .none);
        decls.redeclared(self, self.name_pool.name_of(self.tree, self.src_bytes, id), id);
        self.node_decl[id] = decls.h02_declare_local(self, self.name_pool.name_of(self.tree, self.src_bytes, id), id, .arrow_binder, ft);
        _ = self.set(id, ft);
    }
}

// what `??` / `?<-` unwrap: the payload of a case, or of the first case that has one
pub fn payload_of(self: *Resolver, t0: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const t = sp.apply_vars(&self.abstract_pool, t0);
    const case = switch (sp.tag(t)) {
        .variant_case_type => t,
        .variant_type => sp.payload_case(t),
        else => .none,
    };
    if (case == .none) return .none;
    const p = sp.get(case).variant_case_type.payload;
    if (p == .none) return .none;
    const f = sp.get(p).custom_type.field_types;
    return if (f.len == 1) f[0] else p;
}
