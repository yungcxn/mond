const std = @import("std");
const DynBuf = @import("../../ds/dynbuf.zig").DynBuf;
const ParseTree = @import("../../ParseTree.zig");
const StaticPool = @import("../StaticPool.zig");
const DeclPool = @import("../DeclPool.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;

// control flow: blocks, branches, loops, unwraps, jumps and defers
const Flow = @This();

const Defer = struct { node: NodeId, cell: u32 };

// the defers of the open blocks
defers: DynBuf(Defer),

pub fn init(a: std.mem.Allocator) Flow {
    return .{ .defers = .init(a, 16) };
}

pub fn deinit(self: *Flow) void {
    self.defers.deinit();
}

pub fn interp(self: *Flow) *Interpreter {
    return @alignCast(@fieldParentPtr("flow", self));
}

pub fn jump(self: *Flow, n: NodeId, k: Kind) Value {
    const ip = self.interp();
    const x: Value = if (k == .ret) ip.eval(ip.res().tree.arg(n, 0)) else .unit;
    ip.unwind = switch (k) {
        .brk => .brk,
        .cont => .cont,
        else => .ret,
    };
    return x;
}

pub fn defer_(self: *Flow, n: NodeId, k: Kind) Value {
    const ip = self.interp();
    if (k == .@"defer") {
        self.defers.push(.{ .node = ip.res().tree.arg(n, 0), .cell = Interpreter.no_cell });
        return .unit;
    }
    const x = ip.eval(ip.res().tree.arg(n, 0));
    self.defers.push(.{ .node = n, .cell = ip.put(ip.own(x)) });
    return x;
}

pub fn branch(self: *Flow, n: NodeId) Value {
    const ip = self.interp();
    const b = ParseTree.Branch.from_node(ip.res().tree, n);
    const c = ip.eval(b.cond);
    if (c.ty != .bool_type) return if (c.is(.poison_type)) c else ip.fail(b.cond, .type_mismatch, ip.pool(c), .bool_type);
    if (c.bits != 0) return ip.eval(b.then);
    return if (b.@"else" != 0) ip.eval(b.@"else") else .unit;
}

pub fn block(self: *Flow, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const scoped = !ip.framed();
    if (scoped) r.scopes.push();
    defer if (scoped) r.scopes.pop();
    const mark = self.defers.head;
    var v: Value = .unit;
    for (r.tree.manychildren(n)) |s| {
        v = ip.eval(s);
        if (ip.unwind != .none or v.is(.poison_type)) break;
    }
    const u = ip.unwind;
    while (self.defers.head > mark) {
        self.defers.head -= 1;
        const d = self.defers.buf[self.defers.head];
        ip.unwind = .none;
        if (d.cell == Interpreter.no_cell) _ = ip.eval(d.node) else ip.calls.deinit_cell(d.node, d.cell);
    }
    ip.unwind = u;
    return v;
}

pub fn loop(self: *Flow, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const framed = ip.framed();
    if (!framed) r.scopes.push();
    defer if (!framed) r.scopes.pop();
    const l = ParseTree.Loop.from_node(r.tree, n);
    const pre = l.repeat != 0 and l.cond == 0;
    var seq: Value = .empty;
    var lo: Value = .empty;
    var hi: Value = .empty;
    var incl = false;
    var it: DeclPool.Index = .none;
    var iter: Index = .none;
    var recv: Value = .empty;
    if (l.seq != 0) {
        const s = l.seq;
        if (r.tree.props(s).range) {
            const g = ParseTree.Range.from_node(r.tree, s);
            lo = if (g.lo != 0) ip.eval(g.lo) else .int(.u64_type, 0);
            if (g.hi != 0) hi = ip.eval(g.hi);
            incl = g.incl;
            if (!Value.is_int(lo.ty) or !(hi.is(.none) or Value.is_int(hi.ty))) return if (lo.is(.poison_type) or hi.is(.poison_type)) .poison else ip.fail(s, .not_static, 0, 0);
            lo = .fit(lo, r.static_pool.elem_type(&r.abstract_pool, ip.info(.ty, s)));
        } else {
            const assignable = r.tree.props(s).assignable;
            const sp = &r.static_pool;
            const early = assignable and !r.tree.props(s).name and !(framed and sp.tag(sp.pointee(sp.apply_vars(&r.abstract_pool, ip.info(.ty, s)))) == .array_type);
            const c0: ?u32 = if (early) ip.variables.cell(s) orelse return .poison else null;
            const sv = if (c0) |c| ip.mem.buf[c] else ip.eval(s);
            seq = ip.deref(sv);
            if (seq.is(.poison_type)) return seq;
            if (ip.count(seq) == null) {
                const c = c0 orelse if (assignable) ip.variables.cell(s) orelse return .poison else ip.put(sv);
                const held = ip.mem.buf[c];
                recv = if (held.is_ref()) held else .ref(sp.ptr_of(ip.vtype(held), true), c);
                iter = ip.vtype(ip.deref(held));
                seq = .empty;
            }
        }
        it = if (framed) ip.info(.decl, l.head) else r.decls.declare_local(if (l.variable != 0) r.name_pool.name_of(l.variable) else .it, n, .loop_variable, .none);
    }
    const want = !framed or r.static_pool.tag(r.static_pool.apply_vars(&r.abstract_pool, ip.info(.ty, n))) == .array_type;
    const mark = ip.list.head;
    defer ip.list.head = mark;
    const total = if (seq.is(.none)) 0 else ip.count(seq).?;
    var cur = lo;
    var i: u32 = 0;
    var last = false;
    while (!last) : (i += 1) {
        if (!lo.is(.none)) {
            if (!hi.is(.none) and (if (incl) Value.less(hi, cur) else !Value.less(cur, hi))) break;
            ip.variables.bind(it, cur);
            last = incl and cur.bits == hi.bits;
            cur = .int(cur.ty, cur.bits +% 1);
        } else if (!seq.is(.none)) {
            if (i >= total) break;
            ip.variables.bind(it, ip.elem(seq, i));
        } else if (iter != .none) {
            const more = ip.calls.method(l.seq, iter, .has_next, recv);
            if (more.ty != .bool_type) return if (more.is(.poison_type)) more else ip.fail(l.seq, .type_mismatch, ip.pool(more), .bool_type);
            if (more.bits == 0) break;
            const x = ip.calls.method(l.seq, iter, .next, recv);
            if (x.is(.poison_type)) return x;
            ip.variables.bind(it, x);
        }
        if (pre and ip.eval(l.repeat).is(.poison_type)) return .poison;
        if (l.cond != 0) {
            const c = ip.eval(l.cond);
            if (c.ty != .bool_type) return if (c.is(.poison_type)) c else ip.fail(l.cond, .type_mismatch, ip.pool(c), .bool_type);
            if (c.bits == 0) break;
        }
        const v = ip.eval(l.body);
        if (v.is(.poison_type)) return v;
        switch (ip.unwind) {
            .brk => {
                ip.unwind = .none;
                break;
            },
            .ret => return v,
            .cont => ip.unwind = .none,
            .none => if (want) ip.list.push(v),
        }
        if (!pre and l.repeat != 0 and ip.eval(l.repeat).is(.poison_type)) return .poison;
    }
    if (!want) return .unit;
    const len = ip.list.head - mark;
    var et = r.static_pool.elem_type(&r.abstract_pool, ip.info(.ty, n));
    if (et == .none) et = ip.types.joined(ip.list.buf[mark..][0..len]);
    const at = ip.alloc(len);
    for (0..len) |j| ip.fill(at + j, ip.list.buf[mark + j], et);
    return .block(r.static_pool.array_of(len, et), at, len);
}

pub fn unwrap(self: *Flow, n: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    const k = r.tree.kind(n);
    if (!ip.framed() and (k == .labelarrow or k == .selftag_arrow)) return ip.fail(n, .not_static, 0, 0);
    const v = ip.eval(r.tree.arg(n, 0));
    if (v.is(.poison_type) or ip.unwind != .none) return v;
    if (k == .labelarrow) {
        ip.patterns.label(r.tree.arg(n, 1), v);
        return v;
    }
    const sp = &r.static_pool;
    const c = ip.patterns.case_of(v);
    const p = if (c == .none or sp.tag(ip.info(.ty, r.tree.arg(n, 0))) == .variant_case_type or sp.payload_case(sp.get(c).variant_case_type.variant) == c) ip.patterns.payload(v) else null;
    return switch (k) {
        .selftag_arrow => blk: {
            if (p) |x| ip.patterns.label(r.tree.arg(n, 1), x);
            break :blk .boolean(p != null);
        },
        .selftag_unwrap_fallback => p orelse ip.eval(r.tree.arg(n, 1)),
        else => p orelse ip.fail(n, .static_eval_failed, ip.pool(v), 0),
    };
}
