const std = @import("std");
const DynBuf = @import("../../ds/dynbuf.zig").DynBuf;
const ParseTree = @import("../../ParseTree.zig");
const DeclPool = @import("../DeclPool.zig");
const Decls = @import("../checker/Decls.zig");
const Interpreter = @import("../Interpreter.zig");
const Value = @import("Value.zig");
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;

// variables: names mapped to cells, reads and writes of locals and statics
const Variables = @This();

const Adopted = struct { decl: DeclPool.Index, cell: u32 };

// statics written by an evaluation, held in cells until it ends
adopted: DynBuf(Adopted),

pub fn init(a: std.mem.Allocator) Variables {
    return .{ .adopted = .init(a, 16) };
}

pub fn deinit(self: *Variables) void {
    self.adopted.deinit();
}

pub fn interp(self: *Variables) *Interpreter {
    return @alignCast(@fieldParentPtr("variables", self));
}

pub fn slot(self: *Variables, d: DeclPool.Index) ?u32 {
    const ip = self.interp();
    const x = @intFromEnum(d);
    var i = ip.frames.head;
    while (i > 0) {
        i -= 1;
        const f = ip.frames.buf[i];
        if (f.body.len == 0) break;
        if (x -% f.body.first < f.body.locals) return f.base + x - f.body.first;
        if (ip.calls.captured(f, d)) |c| return c;
    }
    var j = self.adopted.head;
    while (j > 0) {
        j -= 1;
        if (self.adopted.buf[j].decl == d) return self.adopted.buf[j].cell;
    }
    return null;
}

fn impure(self: *Variables, n: NodeId) bool {
    const ip = self.interp();
    const r = ip.res();
    var i = ip.frames.head;
    while (i > 0) {
        i -= 1;
        const f = ip.frames.buf[i];
        if (f.body.len == 0) return false;
        if (f.body.decl != .none and r.decl_pool.get_kind(f.body.decl) == .static_function) {
            _ = ip.report(.impure_stcfun, n, 0, 0);
            return true;
        }
    }
    return false;
}

pub fn flush(self: *Variables, mark: u32) void {
    const ip = self.interp();
    const r = ip.res();
    while (self.adopted.head > mark) {
        self.adopted.head -= 1;
        const a = self.adopted.buf[self.adopted.head];
        r.decl_pool.set_value(a.decl, r.statics.retype(ip.export_(r.decl_pool.get_node(a.decl), ip.mem.buf[a.cell]), r.decl_pool.get_ty(a.decl)));
    }
}

fn decl_of(self: *Variables, n: NodeId) DeclPool.Index {
    const ip = self.interp();
    return if (ip.framed()) ip.info(.decl, n) else ip.res().decls.use(n);
}

fn stored(self: *Variables, n: NodeId, d: DeclPool.Index) Value {
    const ip = self.interp();
    const r = ip.res();
    const v = r.decl_pool.get_value(d);
    if (v != .none) return .of(&r.static_pool, v);
    return if (r.decl_pool.get_state(d) == .failed) .poison else ip.fail(n, .not_static, r.name_pool.name_of(n), 0);
}

pub fn peek(self: *Variables, d: DeclPool.Index) Value {
    const ip = self.interp();
    if (self.slot(d)) |s| if (!ip.mem.buf[s].is(.none)) return ip.mem.buf[s];
    return .of(&ip.res().static_pool, ip.res().decl_pool.get_value(d));
}

pub fn load(self: *Variables, n: NodeId) Value {
    const ip = self.interp();
    const d = self.decl_of(n);
    if (d == .none) return if (ip.framed()) ip.fail(n, .undefined_name, ip.res().name_pool.name_of(n), 0) else .poison;
    if (ip.framed() and ip.res().decl_pool.get_kind(d) == .function and !ip.res().decl_pool.get_flags(d).is_global) return ip.calls.closure(d);
    const v = self.peek(d);
    return if (v.is(.none)) self.stored(n, d) else v;
}

pub fn bind(self: *Variables, d: DeclPool.Index, v: Value) void {
    const ip = self.interp();
    const r = ip.res();
    if (d == .none) return;
    if (self.slot(d)) |s| return ip.set(s, v);
    if (r.decl_pool.get_ty(d) == .none) r.decl_pool.set_ty(d, ip.vtype(v));
    r.decl_pool.set_value(d, ip.pool(v));
}

pub fn store(self: *Variables, n: NodeId, d: DeclPool.Index, v: Value) bool {
    const ip = self.interp();
    const r = ip.res();
    if (d == .none) return true;
    if (self.slot(d)) |s| {
        ip.fill(s, v, r.decl_pool.get_ty(d));
        return true;
    }
    if (self.impure(n)) return false;
    r.decl_pool.set_value(d, r.statics.retype(ip.export_(r.decl_pool.get_node(d), v), r.decl_pool.get_ty(d)));
    return true;
}

fn write(self: *Variables, n: NodeId, v: Value) void {
    const ip = self.interp();
    const r = ip.res();
    if (r.tree.kind(n) == .capture) return self.write(r.tree.arg(n, 0), v);
    if (r.tree.props(n).name) {
        _ = self.store(n, self.decl_of(n), v);
        return;
    }
    const mark = self.adopted.head;
    const c = self.cell(n) orelse return;
    ip.set(c, ip.own(.fit(v, ip.mem.buf[c].ty)));
    self.flush(mark);
}

pub fn cell(self: *Variables, n: NodeId) ?u32 {
    const ip = self.interp();
    const r = ip.res();
    const k = r.tree.kind(n);
    if (k == .capture) return self.cell(r.tree.arg(n, 0));
    if (r.tree.props(n).name) {
        const d = self.decl_of(n);
        if (d == .none) return null;
        if (self.slot(d)) |s| return s;
        if (r.decl_pool.get_kind(d) != .static_parameter and self.impure(n)) return null;
        const c = ip.put(self.stored(n, d));
        self.adopted.push(.{ .decl = d, .cell = c });
        return c;
    }
    if (k == .dereference) {
        const p = ip.eval(r.tree.arg(n, 0));
        if (p.is_ref()) return p.at();
        if (!p.is(.poison_type)) _ = ip.report(.not_static, n, 0, 0);
        return null;
    }
    // a constant of a type (`Light.Green`) is a value like any other
    if (k != .array_index and k != .member or k == .member and r.static_pool.tag(ip.checked(r.tree.arg(n, 0))) == .meta_type) {
        const v = ip.eval(n);
        return if (v.is(.poison_type)) null else ip.put(ip.own(v));
    }
    var c = self.cell(r.tree.arg(n, 0)) orelse return null;
    const through = ip.mem.buf[c].is_ref();
    if (through) c = ip.mem.buf[c].at();
    const agg = ip.thaw(c);
    const i: u64 = if (k == .array_index) blk: {
        const iv = ip.eval(r.tree.arg(n, 1));
        if (!Value.is_int(iv.ty)) return null;
        break :blk iv.bits;
    } else if (agg.is_heap()) switch (r.static_pool.lookup_member(agg.ty, r.name_pool.name_of(r.tree.arg(n, 1)))) {
        .field => |f| f.index,
        else => return null,
    } else 0;
    if (!agg.is_heap()) {
        if (through and k == .array_index) return c + @as(u32, @intCast(i));
        if (!agg.is(.poison_type)) _ = ip.report(.not_static, n, 0, 0);
        return null;
    }
    if (i >= agg.len()) {
        _ = ip.report(.static_eval_failed, n, @as(u32, @truncate(i)), agg.len());
        return null;
    }
    return agg.at() + @as(u32, @intCast(i));
}

pub fn declare(self: *Variables, n0: NodeId) Value {
    const ip = self.interp();
    const r = ip.res();
    if (!ip.framed()) {
        _ = r.decls.check_stmt(ip.ctx, n0);
        return .unit;
    }
    const s = Decls.Stmt.from_node(r, n0);
    if (s.kind != .variable) {
        if (!s.kind.is_type_decl()) return .unit;
        const t = ip.eval(s.values[0]);
        for (s.assignees) |id| _ = self.store(id, ip.info(.decl, id), t);
        return if (t.is(.poison_type)) t else .unit;
    }
    const values = s.values;
    const shared: Value = if (values.len == 1) ip.eval(values[0]) else .empty;
    if (ip.unwind != .none or shared.is(.poison_type)) return shared;
    if (s.assignees.len == 1 and !r.tree.props(s.assignees[0]).name) {
        self.write(s.assignees[0], shared);
        return .unit;
    }
    const d0 = if (s.assignees.len > 0) ip.info(.decl, s.assignees[0]) else .none;
    const mark = ip.list.head;
    defer ip.list.head = mark;
    if (values.len > 1) for (values) |v| {
        const x = ip.eval(v);
        if (ip.unwind != .none or x.is(.poison_type)) return x;
        ip.list.push(x);
    };
    const dyn = if (s.type != 0 and d0 != .none and ip.info(.value, s.type) == .none and r.static_pool.poisoned(r.decl_pool.get_ty(d0))) ip.types.of(s.type) orelse return .poison else .none;
    for (s.assignees, 0..) |id, i| {
        const d = ip.info(.decl, id);
        if (d == .none) continue;
        const x = if (values.len > 1) ip.list.buf[mark + i] else if (values.len == 1) shared else ip.zero(if (dyn != .none) dyn else r.decl_pool.get_ty(d));
        if (x.is(.poison_type)) return x;
        if (dyn != .none and values.len > 0 and !ip.types.admits(x, dyn)) return ip.fail(values[@min(i, values.len - 1)], .type_mismatch, ip.vtype(x), dyn);
        if (!self.store(id, d, ip.coerce(x, dyn))) return .poison;
    }
    return .unit;
}

pub fn update(self: *Variables, n: NodeId, k: Kind) Value {
    const ip = self.interp();
    const r = ip.res();
    const target = r.tree.arg(n, 0);
    const compound = @intFromEnum(k) >= @intFromEnum(Kind.assign_add);
    const operand: Value = if (compound) ip.eval(r.tree.arg(n, 1)) else .empty;
    if (operand.is(.poison_type) or ip.unwind != .none) return operand;
    const mark = self.adopted.head;
    const c: ?u32 = if (r.tree.props(target).name) null else self.cell(target) orelse return .poison;
    const old = if (c) |i| ip.mem.buf[i] else ip.eval(target);
    if (old.is(.poison_type) or ip.unwind != .none) return old;
    const op: Kind = switch (k) {
        .inc_prefix, .inc_postfix, .assign_add => .binary_add,
        .dec_prefix, .dec_postfix, .assign_sub => .binary_sub,
        .assign_mul => .binary_mul,
        .assign_div => .binary_div,
        else => .binary_mod,
    };
    const new = ip.arith(n, op, old, if (compound) operand else .int(if (Value.is_int(old.ty)) old.ty else .u64_type, 1));
    if (new.is(.poison_type)) return new;
    if (c) |i| {
        ip.set(i, ip.own(.fit(new, old.ty)));
        self.flush(mark);
    } else self.write(target, new);
    return if (compound) .unit else if (k == .inc_postfix or k == .dec_postfix) old else new;
}

pub fn address(self: *Variables, n: NodeId) Value {
    const ip = self.interp();
    const c = self.cell(ip.res().tree.arg(n, 0)) orelse return .poison;
    return .ref(if (ip.framed()) ip.info(.ty, n) else ip.res().static_pool.ptr_of(ip.vtype(ip.mem.buf[c]), true), c);
}

pub fn dereference(self: *Variables, n: NodeId) Value {
    const ip = self.interp();
    const p = ip.eval(ip.res().tree.arg(n, 0));
    return if (p.is_ref()) ip.mem.buf[p.at()] else if (p.is(.poison_type)) p else ip.fail(n, .not_static, ip.pool(p), 0);
}

pub fn deinit_assignable(self: *Variables, n: NodeId) Value {
    const ip = self.interp();
    const c = self.cell(ip.res().tree.arg(n, 0)) orelse return .poison;
    ip.calls.deinit_cell(n, if (ip.mem.buf[c].is_ref()) ip.mem.buf[c].at() else c);
    return .unit;
}
