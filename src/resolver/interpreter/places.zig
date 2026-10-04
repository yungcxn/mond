const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const DeclPool = @import("../DeclPool.zig");
const Interpreter = @import("../Interpreter.zig");
const calls = @import("calls.zig");
const types = @import("types.zig");
const Value = @import("Value.zig");
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;

pub fn named(k: Kind) bool {
    return k == .identifier or k == .identifier_self;
}

pub fn slot(self: *Interpreter, d: DeclPool.Index) ?u32 {
    const x = @intFromEnum(d);
    var i = self.frames.head;
    while (i > 0) {
        i -= 1;
        const f = self.frames.buf[i];
        if (f.body.len == 0) break;
        if (x -% f.body.first < f.body.locals) return f.base + x - f.body.first;
        if (self.captured(f, d)) |c| return c;
    }
    var j = self.adopted.head;
    while (j > 0) {
        j -= 1;
        if (self.adopted.buf[j].decl == d) return self.adopted.buf[j].cell;
    }
    return null;
}

fn impure(self: *Interpreter, n: NodeId) bool {
    const r = self.res();
    var i = self.frames.head;
    while (i > 0) {
        i -= 1;
        const f = self.frames.buf[i];
        if (f.body.len == 0) return false;
        if (f.body.decl != .none and r.decl_pool.kinds()[@intFromEnum(f.body.decl)] == .static_function) {
            _ = self.report(.impure_stcfun, n, 0, 0);
            return true;
        }
    }
    return false;
}

pub fn flush(self: *Interpreter, mark: u32) void {
    const r = self.res();
    while (self.adopted.head > mark) {
        self.adopted.head -= 1;
        const a = self.adopted.buf[self.adopted.head];
        r.decl_pool.values()[@intFromEnum(a.decl)] = r.retype(self.export_(r.decl_pool.nodes()[@intFromEnum(a.decl)], self.mem.buf[a.cell]), r.decl_pool.tys()[@intFromEnum(a.decl)]);
    }
}

fn decl_of(self: *Interpreter, n: NodeId) DeclPool.Index {
    return if (self.framed()) self.info(.decl, n) else self.res().use(n);
}

fn stored(self: *Interpreter, n: NodeId, d: DeclPool.Index) Value {
    const r = self.res();
    const v = r.decl_pool.values()[@intFromEnum(d)];
    if (v != .none) return .of(&r.static_pool, v);
    return if (r.decl_pool.states()[@intFromEnum(d)] == .failed) .poison else self.fail(n, .not_static, r.name_pool.name_of(r.tree, r.src_bytes, n), 0);
}

pub fn peek(self: *Interpreter, d: DeclPool.Index) Value {
    if (slot(self, d)) |s| if (!self.mem.buf[s].is(.none)) return self.mem.buf[s];
    return .of(&self.res().static_pool, self.res().decl_pool.values()[@intFromEnum(d)]);
}

pub fn load(self: *Interpreter, n: NodeId) Value {
    const d = decl_of(self, n);
    if (d == .none) return if (self.framed()) self.fail(n, .undefined_name, self.res().name_pool.name_of(self.res().tree, self.res().src_bytes, n), 0) else .poison;
    if (self.framed() and self.res().decl_pool.kinds()[@intFromEnum(d)] == .function and !self.res().decl_pool.flags()[@intFromEnum(d)].is_global) return self.closure(d);
    const v = peek(self, d);
    return if (v.is(.none)) stored(self, n, d) else v;
}

pub fn bind(self: *Interpreter, d: DeclPool.Index, v: Value) void {
    const r = self.res();
    if (d == .none) return;
    if (slot(self, d)) |s| return self.set(s, v);
    if (r.decl_pool.tys()[@intFromEnum(d)] == .none) r.decl_pool.tys()[@intFromEnum(d)] = self.vtype(v);
    r.decl_pool.values()[@intFromEnum(d)] = self.pool(v);
}

pub fn store(self: *Interpreter, n: NodeId, d: DeclPool.Index, v: Value) bool {
    const r = self.res();
    if (d == .none) return true;
    if (slot(self, d)) |s| {
        self.fill(s, v, r.decl_pool.tys()[@intFromEnum(d)]);
        return true;
    }
    if (impure(self, n)) return false;
    r.decl_pool.values()[@intFromEnum(d)] = r.retype(self.export_(r.decl_pool.nodes()[@intFromEnum(d)], v), r.decl_pool.tys()[@intFromEnum(d)]);
    return true;
}

fn write(self: *Interpreter, n: NodeId, v: Value) void {
    const r = self.res();
    if (r.tree.kind(n) == .capture) return write(self, r.tree.arg(n, 0), v);
    if (named(r.tree.kind(n))) {
        _ = store(self, n, decl_of(self, n), v);
        return;
    }
    const mark = self.adopted.head;
    const c = cell(self, n) orelse return;
    self.set(c, self.own(.fit(v, self.mem.buf[c].ty)));
    flush(self, mark);
}

pub fn cell(self: *Interpreter, n: NodeId) ?u32 {
    const r = self.res();
    const k = r.tree.kind(n);
    if (k == .capture) return cell(self, r.tree.arg(n, 0));
    if (named(k)) {
        const d = decl_of(self, n);
        if (d == .none) return null;
        if (slot(self, d)) |s| return s;
        if (impure(self, n)) return null;
        const c = self.put(stored(self, n, d));
        self.adopted.push(.{ .decl = d, .cell = c });
        return c;
    }
    if (k == .dereference) {
        const p = self.eval(r.tree.arg(n, 0));
        if (p.is_ref()) return p.at();
        if (!p.is(.poison_type)) _ = self.report(.not_static, n, 0, 0);
        return null;
    }
    // a constant of a type (`Light.Green`) is a value like any other
    if (k != .array_index and k != .member or k == .member and self.res().static_pool.tag(self.checked(r.tree.arg(n, 0))) == .meta_type) {
        const v = self.eval(n);
        return if (v.is(.poison_type)) null else self.put(self.own(v));
    }
    var c = cell(self, r.tree.arg(n, 0)) orelse return null;
    const through = self.mem.buf[c].is_ref();
    if (through) c = self.mem.buf[c].at();
    const agg = self.thaw(c);
    const i: u64 = if (k == .array_index) blk: {
        const iv = self.eval(r.tree.arg(n, 1));
        if (!Value.is_int(iv.ty)) return null;
        break :blk iv.bits;
    } else if (agg.is_heap()) switch (r.static_pool.lookup_member(agg.ty, r.name_pool.name_of(r.tree, r.src_bytes, r.tree.arg(n, 1)))) {
        .field => |f| f.index,
        else => return null,
    } else 0;
    if (!agg.is_heap()) {
        if (through and k == .array_index) return c + @as(u32, @intCast(i));
        if (!agg.is(.poison_type)) _ = self.report(.not_static, n, 0, 0);
        return null;
    }
    if (i >= agg.len()) {
        _ = self.report(.static_eval_failed, n, @as(u32, @truncate(i)), agg.len());
        return null;
    }
    return agg.at() + @as(u32, @intCast(i));
}

pub fn declare(self: *Interpreter, n0: NodeId) Value {
    const r = self.res();
    if (!self.framed()) {
        _ = r.h11_check_assign(self.ctx, n0);
        return .unit;
    }
    const s = Resolver.Stmt.from_node(r, n0);
    if (s.kind != .variable) {
        if (!Resolver.is_type_decl(s.kind)) return .unit;
        const t = self.eval(s.values[0]);
        for (s.assignees) |id| _ = store(self, id, self.info(.decl, id), t);
        return if (t.is(.poison_type)) t else .unit;
    }
    const values = s.values;
    const shared: Value = if (values.len == 1) self.eval(values[0]) else .empty;
    if (self.unwind != .none or shared.is(.poison_type)) return shared;
    if (s.assignees.len == 1 and !named(r.tree.kind(s.assignees[0]))) {
        write(self, s.assignees[0], shared);
        return .unit;
    }
    const d0 = if (s.assignees.len > 0) self.info(.decl, s.assignees[0]) else .none;
    const dyn = if (s.type != 0 and d0 != .none and self.info(.value, s.type) == .none and types.unknown(&r.static_pool, r.decl_pool.tys()[@intFromEnum(d0)])) types.of(self, s.type) orelse return .poison else .none;
    for (s.assignees, 0..) |id, i| {
        const d = self.info(.decl, id);
        if (d == .none) continue;
        const x = if (values.len > 1) self.eval(values[i]) else if (values.len == 1) shared else self.zero(if (dyn != .none) dyn else r.decl_pool.tys()[@intFromEnum(d)]);
        if (x.is(.poison_type)) return x;
        if (dyn != .none and values.len > 0 and !types.admits(self, x, dyn)) return self.fail(values[@min(i, values.len - 1)], .type_mismatch, self.vtype(x), dyn);
        if (!store(self, id, d, self.coerce(x, dyn))) return .poison;
    }
    return .unit;
}

pub fn update(self: *Interpreter, n: NodeId, k: Kind) Value {
    const r = self.res();
    const target = r.tree.arg(n, 0);
    const compound = @intFromEnum(k) >= @intFromEnum(Kind.assign_add);
    const operand: Value = if (compound) self.eval(r.tree.arg(n, 1)) else .empty;
    if (operand.is(.poison_type) or self.unwind != .none) return operand;
    const mark = self.adopted.head;
    const c: ?u32 = if (named(r.tree.kind(target))) null else cell(self, target) orelse return .poison;
    const old = if (c) |i| self.mem.buf[i] else self.eval(target);
    if (old.is(.poison_type) or self.unwind != .none) return old;
    const op: Kind = switch (k) {
        .inc_prefix, .inc_postfix, .assign_add => .binary_add,
        .dec_prefix, .dec_postfix, .assign_sub => .binary_sub,
        .assign_mul => .binary_mul,
        .assign_div => .binary_div,
        else => .binary_mod,
    };
    const new = self.arith(n, op, old, if (compound) operand else .int(if (Value.is_int(old.ty)) old.ty else .u64_type, 1));
    if (new.is(.poison_type)) return new;
    if (c) |i| {
        self.set(i, self.own(.fit(new, old.ty)));
        flush(self, mark);
    } else write(self, target, new);
    return if (compound) .unit else if (k == .inc_postfix or k == .dec_postfix) old else new;
}

pub fn address(self: *Interpreter, n: NodeId) Value {
    const c = cell(self, self.res().tree.arg(n, 0)) orelse return .poison;
    return .ref(if (self.framed()) self.info(.ty, n) else self.res().self_ptr(self.vtype(self.mem.buf[c])), c);
}

pub fn dereference(self: *Interpreter, n: NodeId) Value {
    const p = self.eval(self.res().tree.arg(n, 0));
    return if (p.is_ref()) self.mem.buf[p.at()] else if (p.is(.poison_type)) p else self.fail(n, .not_static, self.pool(p), 0);
}

pub fn deinit(self: *Interpreter, n: NodeId) Value {
    const c = cell(self, self.res().tree.arg(n, 0)) orelse return .poison;
    calls.deinit(self, n, if (self.mem.buf[c].is_ref()) self.mem.buf[c].at() else c);
    return .unit;
}
