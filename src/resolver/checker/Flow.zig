const std = @import("std");
const DynBuf = @import("../../ds/dynbuf.zig").DynBuf;
const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const FnCtx = Resolver.FnCtx;
const NodeId = ParseTree.NodeId;

// control flow: if, loops and unwraps, the types branches join to, the written locals they leave
const Flow = @This();

// brk and cont seen so far: a loop without a brk never ends, one without either yields one element per step
jumps: [2]u32 = .{ 0, 0 },
// per open loop the set of unwritten locals its exits merge into
exits: DynBuf(u32),

pub fn init(alloc: std.mem.Allocator) Flow {
    return .{ .exits = .init(alloc, 16) };
}

pub fn deinit(self: *Flow) void {
    self.exits.deinit();
}

pub fn res(self: *Flow) *Resolver {
    return @alignCast(@fieldParentPtr("flow", self));
}

pub fn check_if(self: *Flow, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const b = ParseTree.Branch.from_node(r.tree, node);
    const cond = b.cond;
    const then = b.then;
    const stc = r.tree.props(node).stc;
    const c = if (ctx.interpreted or stc and ctx.abstract) r.statics.try_static(ctx, cond) orelse .none else if (stc) r.interpreter.eval_static(ctx, cond) else .none;
    if (c == .bool_true or c == .bool_false or c != .none and !ctx.interpreted) {
        _ = r.set(cond, .bool_type);
        if (c == .bool_true) return self.branch(ctx, then, expected);
        if (c != .bool_false) return if (c == .poison_type) c else r.report(.type_mismatch, cond, r.static_pool.type_of(c), .bool_type);
        return if (b.@"else" != 0) self.branch(ctx, b.@"else", expected) else .unit_type;
    }
    // binders of the condition (`x ?<- v`) are visible in the then branch only
    const m = r.inits.count;
    defer r.inits.release(m);
    r.scopes.push();
    const w = self.condition(ctx, cond);
    r.inits.copy(0, w[0]);
    const was = r.static_pool.concrete(&r.abstract_pool, expected);
    const tt = self.branch(ctx, then, expected);
    const after_then = r.inits.new();
    if (tt != .never_type) r.inits.copy(after_then, 0);
    r.inits.copy(0, w[1]);
    r.scopes.pop();
    if (b.@"else" == 0) {
        r.inits.merge(0, after_then);
        const valued = tt != .never_type and tt != .runit_type and tt != .poison_type and tt != .unit_type;
        return if (r.static_pool.concrete(&r.abstract_pool, expected) and valued) r.report(.runit_mixing, node, tt, .unit_type) else self.merge(node, tt, .unit_type, if (valued) .none else expected);
    }
    const et = self.branch(ctx, b.@"else", expected);
    if (et == .never_type) r.inits.copy(0, after_then) else r.inits.merge(0, after_then);
    const ts = if (was) tt else self.settle(then, tt, expected);
    return self.merge(node, self.adapt(then, ts, et), self.adapt(b.@"else", et, ts), expected);
}

// the locals not written yet when a condition is true and when it is false: `and` runs its right side only after a true left one
pub fn condition(self: *Flow, ctx: *FnCtx, n: NodeId) [2]u32 {
    const r = self.res();
    const k = r.tree.kind(n);
    if (k == .capture) {
        const w = self.condition(ctx, r.tree.arg(n, 0));
        _ = r.set(n, r.node_type[r.tree.arg(n, 0)]);
        return w;
    }
    if (k != .binary_logic_and and k != .binary_logic_or) {
        _ = r.exprs.check(ctx, n, .bool_type);
        const s = r.inits.save(0);
        return .{ s, s };
    }
    const l = self.condition(ctx, r.tree.arg(n, 0));
    r.inits.copy(0, l[@intFromBool(k == .binary_logic_or)]);
    const rhs = self.condition(ctx, r.tree.arg(n, 1));
    _ = r.set(n, .bool_type);
    const both = r.inits.save(l[@intFromBool(k == .binary_logic_and)]);
    r.inits.merge(both, rhs[@intFromBool(k == .binary_logic_and)]);
    return if (k == .binary_logic_and) .{ rhs[0], both } else .{ both, rhs[1] };
}

// the first type of the literals among `ns` that every one of them fits
pub fn literals_type(self: *Flow, ns: []const NodeId) StaticPool.Index {
    const r = self.res();
    for (ns) |c| if (r.tree.is_literal(c)) {
        const ct = r.node_type[c];
        for (ns) |n| {
            if (r.tree.is_literal(n) and r.statics.literal_type(n, ct) != ct) break;
        } else return ct;
    };
    return .none;
}

// a literal branch takes the type of the others (`if c: n else: 3`)
pub fn adapt(self: *Flow, n: NodeId, t: StaticPool.Index, other: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    if (!r.tree.is_literal(n) or other == .none or r.statics.literal_type(n, other) != other) return t;
    return r.set(n, other);
}

pub fn check_loop(self: *Flow, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const sp = &r.static_pool;
    const lp = ParseTree.Loop.from_node(r.tree, node);
    const exp = sp.apply_vars(&r.abstract_pool, expected);
    const elem_hint = sp.array_elem(exp);
    r.scopes.push();
    defer r.scopes.pop();
    if (lp.cond != 0) _ = r.exprs.check(ctx, lp.cond, .bool_type);
    if (lp.repeat != 0) _ = r.exprs.infer(ctx, lp.repeat, .none);
    if (lp.cond != 0 and lp.repeat != 0) _ = r.set(lp.head, .unit_type);
    if (lp.seq != 0) {
        const st = sp.pointee(sp.apply_vars(&r.abstract_pool, r.exprs.infer(ctx, lp.seq, if (elem_hint != .none and sp.get_tag_prop(elem_hint).is_integer and r.tree.props(lp.seq).range) exp else .none)));
        const elem = switch (sp.lookup_member(st, if (sp.get(st) == .array_type) .len else .next)) {
            .builtin_len => sp.get(st).array_type.elem,
            .method => |m| self.fn_ret(m),
            .trait_method => |m| self.fn_ret(sp.method_decl(m)),
            else => r.mismatch(lp.seq, st, .none),
        };
        const v = lp.variable;
        const it = r.decls.declare_local(if (v != 0) r.name_pool.name_of(v) else .it, if (v != 0) v else lp.head, if (v != 0) .loop_variable else .autoins_it, elem);
        r.node_decl[lp.head] = it;
        if (v != 0) {
            r.node_decl[v] = it;
            _ = r.set(v, elem);
            _ = r.set(lp.head, .unit_type);
        }
    }
    const m = r.inits.count;
    defer r.inits.release(m);
    const at_exit = r.inits.save(0);
    self.exits.push(r.inits.new());
    ctx.loop_depth += 1;
    const jumps = self.jumps;
    // a stc loop body is static per iteration: checked like a stcfun body, evaluated with the loop
    const outer = ctx.interpreted;
    ctx.interpreted = outer or r.tree.props(node).stc;
    const bt = r.exprs.infer(ctx, lp.body, if (expected == .none) .none else if (elem_hint != .none) elem_hint else sp.fresh_var(&r.abstract_pool, lp.body));
    ctx.interpreted = outer;
    ctx.loop_depth -= 1;
    const broke = self.jumps[0] != jumps[0];
    const stepped = !broke and self.jumps[1] == jumps[1];
    self.jumps = jumps;
    self.exits.head -= 1;
    if (lp.cond == 0 and lp.seq == 0) r.inits.clear(at_exit);
    r.inits.merge(at_exit, self.exits.buf[self.exits.head]);
    r.inits.copy(0, at_exit);
    if (!ctx.interpreted and !ctx.abstract and r.tree.props(node).stc) _ = r.statics.static_of(ctx, node);
    // used as a value: an array of the body values; brk ends it without adding one, cont skips one
    if (lp.cond == 0 and lp.seq == 0 and !broke and elem_hint == .none) return .never_type;
    if (expected == .none) return .unit_type;
    const n = if (stepped and lp.seq != 0) self.steps(ctx, lp.seq) else null;
    return sp.intern(.{ .array_type = .{ .len = if (n) |x| sp.intern(.{ .int = .{ .ty = .u64_type, .bits = x } }) else sp.fresh_var(&r.abstract_pool, node), .elem = if (bt == .never_type or bt == .runit_type) (if (elem_hint != .none) elem_hint else .unit_type) else bt } });
}

// the static number of steps of a `for` over a range with static bounds or an array of static length
fn steps(self: *Flow, ctx: *FnCtx, seq: NodeId) ?u64 {
    const r = self.res();
    const sp = &r.static_pool;
    if (!r.tree.props(seq).range) {
        const st = sp.pointee(sp.apply_vars(&r.abstract_pool, r.node_type[seq]));
        return sp.static_len(st);
    }
    const g = ParseTree.Range.from_node(r.tree, seq);
    if (g.hi == 0) return null;
    const lo = if (g.lo == 0) 0 else r.statics.static_int(ctx, g.lo) orelse return null;
    const hi = (r.statics.static_int(ctx, g.hi) orelse return null) + @intFromBool(g.incl);
    return if (hi > lo) @intCast(hi - lo) else 0;
}

pub fn jump(self: *Flow, ctx: *FnCtx, node: NodeId, k: ParseTree.Node.Kind) StaticPool.Index {
    const r = self.res();
    if (ctx.loop_depth == 0) return r.report(if (k == .brk) .brk_outside_loop else .cont_outside_loop, node, 0, 0);
    self.jumps[@intFromBool(k == .cont)] += 1;
    if (k == .brk and self.exits.head > 0) r.inits.merge(self.exits.buf[self.exits.head - 1], 0);
    return .never_type;
}

// binders belong to their statement: a block scopes every non-declaring statement, a declaration its values
pub fn check_unwrap(self: *Flow, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const k = r.tree.kind(node);
    const vt = r.static_pool.apply_vars(&r.abstract_pool, r.exprs.infer(ctx, r.tree.arg(node, 0), if (k == .labelarrow) expected else .none));
    if (k == .labelarrow) {
        self.bind_label(r.tree.arg(node, 1), vt);
        return vt;
    }
    const pt = r.static_pool.payload_of(&r.abstract_pool, vt);
    if (pt == .none) return r.mismatch(r.tree.arg(node, 0), vt, .none);
    return switch (k) {
        .selftag_unwrap_fallback => blk: {
            const before = r.inits.save(0);
            _ = r.exprs.check(ctx, r.tree.arg(node, 1), pt);
            r.inits.copy(0, before);
            r.inits.release(before);
            break :blk pt;
        },
        .selftag_arrow => blk: {
            self.bind_label(r.tree.arg(node, 1), pt);
            break :blk .bool_type;
        },
        else => pt,
    };
}

// a branch of if / match: unit blocks and nested ifs / matches are runit, a plain unit value is not
pub fn branch(self: *Flow, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    return self.settle(node, r.static_pool.apply_vars(&r.abstract_pool, r.exprs.infer(ctx, node, expected)), expected);
}

pub fn settle(self: *Flow, node: NodeId, t0: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    const t = if (t0 == .unit_type and r.tree.props(node).runit) .runit_type else t0;
    if (!r.static_pool.concrete(&r.abstract_pool, expected) or t == .never_type or t == .runit_type or t == .poison_type) return t;
    if (t == .unit_type and expected != .unit_type) return r.report(.runit_mixing, node, t, expected);
    return r.exprs.expect(node, t, expected);
}

pub fn merge(self: *Flow, node: NodeId, acc: StaticPool.Index, t: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    const r = self.res();
    if (r.static_pool.concrete(&r.abstract_pool, expected)) return expected;
    if (acc == .none) return t;
    const j = r.static_pool.join(&r.abstract_pool, acc, t);
    if (j.ty != .none) return j.ty;
    if (expected == .none) return if (acc == .unit_type or t == .unit_type) .unit_type else r.report(.type_mismatch, node, acc, t);
    return r.report(if (acc == .unit_type or t == .unit_type) .runit_mixing else .type_mismatch, node, acc, t);
}

// `<- name` binds the value, `<- a, b` destructures a record in field order
pub fn bind_label(self: *Flow, label: NodeId, t: StaticPool.Index) void {
    const r = self.res();
    const sp = &r.static_pool;
    if (r.tree.kind(label) != .partial__destructure) {
        r.decls.redeclared(r.name_pool.name_of(label), label);
        r.node_decl[label] = r.decls.declare_local(r.name_pool.name_of(label), label, .arrow_binder, t);
        _ = r.set(label, t);
        return;
    }
    const rt = sp.apply_vars(&r.abstract_pool, t);
    for (r.tree.manychildren(label), 0..) |id, i| {
        const ft = if (sp.tag(rt) == .record_type and i < sp.get(rt).custom_type.field_types.len) sp.field_type(rt, i) else r.mismatch(id, t, .none);
        r.decls.redeclared(r.name_pool.name_of(id), id);
        r.node_decl[id] = r.decls.declare_local(r.name_pool.name_of(id), id, .arrow_binder, ft);
        _ = r.set(id, ft);
    }
}

fn fn_ret(self: *Flow, d: DeclPool.Index) StaticPool.Index {
    const r = self.res();
    const t = r.types.decl_type(d);
    return if (r.static_pool.tag(t) == .function_type) r.static_pool.get(t).function_type.ret else .poison_type;
}
