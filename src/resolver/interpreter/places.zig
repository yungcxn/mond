const ParseTree = @import("../../ParseTree.zig");
const Resolver = @import("../../Resolver.zig");
const Interpreter = @import("../Interpreter.zig");
const calls = @import("calls.zig");
const types = @import("types.zig");
const Value = @import("Value.zig");
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;
const Decl = Resolver.Decl;

pub fn named(k: Kind) bool {
    return k == .identifier or k == .identifier_self;
}

fn slot(ip: *Interpreter, d: Decl.Index) ?u32 {
    const x = @intFromEnum(d);
    var i = ip.frames.head;
    while (i > 0) {
        i -= 1;
        const f = ip.frames.buf[i];
        if (f.body.len == 0) break;
        if (x -% f.body.first < f.body.locals) return f.base + x - f.body.first;
    }
    var j = ip.adopted.head;
    while (j > 0) {
        j -= 1;
        if (ip.adopted.buf[j].decl == d) return ip.adopted.buf[j].cell;
    }
    return null;
}

fn impure(ip: *Interpreter, n: NodeId) bool {
    const r = ip.res();
    var i = ip.frames.head;
    while (i > 0) {
        i -= 1;
        const f = ip.frames.buf[i];
        if (f.body.len == 0) return false;
        if (f.body.decl != .none and r.dp(.kind, f.body.decl).* == .static_function) {
            _ = ip.report(.impure_stcfun, n, 0, 0);
            return true;
        }
    }
    return false;
}

pub fn flush(ip: *Interpreter, mark: u32) void {
    const r = ip.res();
    while (ip.adopted.head > mark) {
        ip.adopted.head -= 1;
        const a = ip.adopted.buf[ip.adopted.head];
        r.dp(.value, a.decl).* = r.retype(ip.export_(r.dp(.node, a.decl).*, ip.mem.buf[a.cell]), r.dp(.ty, a.decl).*);
    }
}

fn decl_of(ip: *Interpreter, n: NodeId) Decl.Index {
    return if (ip.framed()) ip.info(.decl, n) else ip.res().use(n);
}

fn stored(ip: *Interpreter, n: NodeId, d: Decl.Index) Value {
    const r = ip.res();
    const v = r.dp(.value, d).*;
    if (v != .none) return .of(&r.static_pool, v);
    return if (r.dp(.state, d).* == .failed) .poison else ip.fail(n, .not_static, r.name_of(n), 0);
}

pub fn peek(ip: *Interpreter, d: Decl.Index) Value {
    if (slot(ip, d)) |s| if (!ip.mem.buf[s].is(.none)) return ip.mem.buf[s];
    return .of(&ip.res().static_pool, ip.res().dp(.value, d).*);
}

pub fn load(ip: *Interpreter, n: NodeId) Value {
    const d = decl_of(ip, n);
    if (d == .none) return if (ip.framed()) ip.fail(n, .undefined_name, ip.res().name_of(n), 0) else .poison;
    const v = peek(ip, d);
    return if (v.is(.none)) stored(ip, n, d) else v;
}

pub fn bind(ip: *Interpreter, d: Decl.Index, v: Value) void {
    const r = ip.res();
    if (d == .none) return;
    if (slot(ip, d)) |s| return ip.set(s, v);
    if (r.dp(.ty, d).* == .none) r.dp(.ty, d).* = ip.vtype(v);
    r.dp(.value, d).* = ip.pool(v);
}

pub fn store(ip: *Interpreter, n: NodeId, d: Decl.Index, v: Value) bool {
    const r = ip.res();
    if (d == .none) return true;
    if (slot(ip, d)) |s| {
        ip.fill(s, v, r.dp(.ty, d).*);
        return true;
    }
    if (impure(ip, n)) return false;
    r.dp(.value, d).* = r.retype(ip.export_(r.dp(.node, d).*, v), r.dp(.ty, d).*);
    return true;
}

fn write(ip: *Interpreter, n: NodeId, v: Value) void {
    const r = ip.res();
    if (r.nk(n) == .capture) return write(ip, r.arg(n, 0), v);
    if (named(r.nk(n))) {
        _ = store(ip, n, decl_of(ip, n), v);
        return;
    }
    const mark = ip.adopted.head;
    const c = cell(ip, n) orelse return;
    ip.set(c, ip.own(.fit(v, ip.mem.buf[c].ty)));
    flush(ip, mark);
}

pub fn cell(ip: *Interpreter, n: NodeId) ?u32 {
    const r = ip.res();
    const k = r.nk(n);
    if (k == .capture) return cell(ip, r.arg(n, 0));
    if (named(k)) {
        const d = decl_of(ip, n);
        if (d == .none) return null;
        if (slot(ip, d)) |s| return s;
        if (impure(ip, n)) return null;
        const c = ip.put(stored(ip, n, d));
        ip.adopted.push(.{ .decl = d, .cell = c });
        return c;
    }
    if (k == .dereference) {
        const p = ip.eval(r.arg(n, 0));
        if (p.is_ref()) return p.at();
        if (!p.is(.poison_type)) _ = ip.report(.not_static, n, 0, 0);
        return null;
    }
    // a constant of a type (`Light.Green`) is a value like any other
    if (k != .array_index and k != .member or k == .member and ip.res().static_pool.tag(ip.checked(r.arg(n, 0))) == .meta_type) {
        const v = ip.eval(n);
        return if (v.is(.poison_type)) null else ip.put(ip.own(v));
    }
    var c = cell(ip, r.arg(n, 0)) orelse return null;
    const through = ip.mem.buf[c].is_ref();
    if (through) c = ip.mem.buf[c].at();
    const agg = ip.thaw(c);
    const i: u64 = if (k == .array_index) blk: {
        const iv = ip.eval(r.arg(n, 1));
        if (!Value.is_int(iv.ty)) return null;
        break :blk iv.bits;
    } else if (agg.is_heap()) switch (r.static_pool.lookup_member(agg.ty, r.name_of(r.arg(n, 1)))) {
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

pub fn declare(ip: *Interpreter, n0: NodeId) Value {
    const r = ip.res();
    if (!ip.framed()) {
        _ = r.h11_check_assign(ip.ctx, n0);
        return .unit;
    }
    const s = r.statement(n0);
    if (s.kind != .variable) {
        if (!Resolver.is_type_decl(s.kind)) return .unit;
        const t = ip.eval(s.value);
        for (s.ids) |id| _ = store(ip, id, ip.info(.decl, id), t);
        return if (t.is(.poison_type)) t else .unit;
    }
    const values = s.values;
    const shared: Value = if (values.len == 1) ip.eval(values[0]) else .empty;
    if (ip.unwind != .none or shared.is(.poison_type)) return shared;
    if (s.ids.len == 1 and !named(r.nk(s.ids[0]))) {
        write(ip, s.ids[0], shared);
        return .unit;
    }
    const d0 = if (s.ids.len > 0) ip.info(.decl, s.ids[0]) else .none;
    const dyn = if (s.type != 0 and d0 != .none and ip.info(.value, s.type) == .none and types.unknown(&r.static_pool, r.dp(.ty, d0).*)) types.of(ip, s.type) orelse return .poison else .none;
    for (s.ids, 0..) |id, i| {
        const d = ip.info(.decl, id);
        if (d == .none) continue;
        const x = if (values.len > 1) ip.eval(values[i]) else if (values.len == 1) shared else ip.zero(if (dyn != .none) dyn else r.dp(.ty, d).*);
        if (x.is(.poison_type)) return x;
        if (dyn != .none and values.len > 0 and !types.admits(ip, x, dyn)) return ip.fail(values[@min(i, values.len - 1)], .type_mismatch, ip.vtype(x), dyn);
        if (!store(ip, id, d, ip.coerce(x, dyn))) return .poison;
    }
    return .unit;
}

pub fn update(ip: *Interpreter, n: NodeId, k: Kind) Value {
    const r = ip.res();
    const target = r.arg(n, 0);
    const compound = @intFromEnum(k) >= @intFromEnum(Kind.assign_add);
    const operand: Value = if (compound) ip.eval(r.arg(n, 1)) else .empty;
    if (operand.is(.poison_type) or ip.unwind != .none) return operand;
    const mark = ip.adopted.head;
    const c: ?u32 = if (named(r.nk(target))) null else cell(ip, target) orelse return .poison;
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
        flush(ip, mark);
    } else write(ip, target, new);
    return if (compound) .unit else if (k == .inc_postfix or k == .dec_postfix) old else new;
}

pub fn address(ip: *Interpreter, n: NodeId) Value {
    const c = cell(ip, ip.res().arg(n, 0)) orelse return .poison;
    return .ref(if (ip.framed()) ip.info(.ty, n) else ip.res().self_ptr(ip.vtype(ip.mem.buf[c])), c);
}

pub fn dereference(ip: *Interpreter, n: NodeId) Value {
    const p = ip.eval(ip.res().arg(n, 0));
    return if (p.is_ref()) ip.mem.buf[p.at()] else if (p.is(.poison_type)) p else ip.fail(n, .not_static, ip.pool(p), 0);
}

pub fn deinit(ip: *Interpreter, n: NodeId) Value {
    const c = cell(ip, ip.res().arg(n, 0)) orelse return .poison;
    calls.deinit(ip, n, if (ip.mem.buf[c].is_ref()) ip.mem.buf[c].at() else c);
    return .unit;
}
