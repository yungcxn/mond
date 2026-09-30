const std = @import("std");
const DynBuf = @import("../ds/dynbuf.zig").DynBuf;
const ParseTree = @import("../ParseTree.zig");
const Resolver = @import("../Resolver.zig");
const StaticPool = @import("StaticPool.zig");
const Value = @import("interpreter/Value.zig");
const places = @import("interpreter/places.zig");
const control = @import("interpreter/control.zig");
const calls = @import("interpreter/calls.zig");
const types = @import("interpreter/types.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;
const Decl = Resolver.Decl;

const Interpreter = @This();

const step_budget: u32 = 1_000_000;
pub const max_depth: u32 = 256;
pub const no_cell = std.math.maxInt(u32);

const Frame = struct { body: Resolver.Body, base: u32 };
const Session = struct { ctx: *Resolver.FnCtx, mem: u32, adopted: u32 };
const Adopted = struct { decl: Decl.Index, cell: u32 };
const Defer = struct { node: NodeId, cell: u32 };

budget: u32 = step_budget,
depth: u32 = 0,
unwind: enum { none, ret, brk, cont } = .none,
ctx: *Resolver.FnCtx = undefined,
frames: DynBuf(Frame),
mem: DynBuf(Value),
list: DynBuf(Value),
ids: DynBuf(Index),
adopted: DynBuf(Adopted),
defers: DynBuf(Defer),
// a block stored into a cell older than its frame stays until that cell is gone
floor: u32 = 0,
floor_cell: u32 = no_cell,

pub fn init(a: std.mem.Allocator) Interpreter {
    return .{ .frames = .init(a, 64), .mem = .init(a, 1024), .list = .init(a, 256), .ids = .init(a, 256), .adopted = .init(a, 16), .defers = .init(a, 16) };
}

pub fn deinit(ip: *Interpreter) void {
    inline for (.{ &ip.frames, &ip.mem, &ip.list, &ip.ids, &ip.adopted, &ip.defers }) |b| b.deinit();
}

pub fn res(ip: *Interpreter) *Resolver {
    return @alignCast(@fieldParentPtr("interpreter", ip));
}

fn open(ip: *Interpreter, ctx: *Resolver.FnCtx, body: Resolver.Body) Session {
    if (ip.depth == 0) ip.budget = step_budget;
    ip.depth += 1;
    const s = Session{ .ctx = ip.ctx, .mem = ip.mem.head, .adopted = ip.adopted.head };
    ip.ctx = ctx;
    ip.enter(body);
    return s;
}

fn close(ip: *Interpreter, s: Session) void {
    places.flush(ip, s.adopted);
    ip.depth -= 1;
    ip.frames.head -= 1;
    ip.truncate(s.mem);
    ip.ctx = s.ctx;
}

pub fn export_(ip: *Interpreter, n: NodeId, v: Value) Index {
    return if (ip.escapes(v)) ip.res().report(.not_static, n, 0, 0) else ip.pool(v);
}

pub fn static_value(ip: *Interpreter, ctx: *Resolver.FnCtx, n: NodeId) Index {
    const s = ip.open(ctx, .{});
    defer ip.close(s);
    const v = ip.export_(n, ip.eval(n));
    if (v != .poison_type) ip.res().node_value[n] = v;
    return v;
}

pub fn static_match(ip: *Interpreter, ctx: *Resolver.FnCtx, pat: NodeId, v: Index) bool {
    const s = ip.open(ctx, .{});
    defer ip.close(s);
    return control.matches(ip, pat, Value.of(&ip.res().static_pool, v));
}

pub fn run(ip: *Interpreter, ctx: *Resolver.FnCtx, root: NodeId, body: Resolver.Body) Index {
    const s = ip.open(ctx, body);
    defer ip.close(s);
    return ip.export_(root, ip.result(ip.eval(root)));
}

pub fn enter(ip: *Interpreter, body: Resolver.Body) void {
    ip.frames.push(.{ .body = body, .base = ip.alloc(body.locals) });
}

pub fn leave(ip: *Interpreter, keep: bool) void {
    ip.frames.head -= 1;
    if (!keep) ip.truncate(ip.frames.buf[ip.frames.head].base);
}

fn truncate(ip: *Interpreter, to: u32) void {
    if (ip.floor_cell < to) {
        ip.mem.head = @max(to, @min(ip.floor, ip.mem.head));
        return;
    }
    ip.mem.head = to;
    ip.floor = 0;
    ip.floor_cell = no_cell;
}

pub fn set(ip: *Interpreter, c: usize, v: Value) void {
    ip.mem.buf[c] = v;
    if (!v.is_heap() or c >= ip.top().base) return;
    ip.floor = @max(ip.floor, ip.mem.head);
    ip.floor_cell = @min(ip.floor_cell, @as(u32, @intCast(c)));
}

pub fn detached(ip: *Interpreter, n: NodeId) Value {
    ip.frames.push(.{ .body = .{}, .base = ip.mem.head });
    defer ip.frames.head -= 1;
    return ip.eval(n);
}

fn top(ip: *Interpreter) Frame {
    return ip.frames.buf[ip.frames.head - 1];
}

pub fn result(ip: *Interpreter, v: Value) Value {
    defer ip.unwind = .none;
    return if (ip.unwind == .none or ip.unwind == .ret) v else .unit;
}

pub fn charge(ip: *Interpreter, n: NodeId, cost: u32) bool {
    if (ip.depth == 0) ip.budget = step_budget;
    if (ip.budget > cost) {
        ip.budget -= cost;
        return true;
    }
    if (ip.budget > 0) _ = ip.res().report(.static_eval_failed, n, 0, 0);
    ip.budget = 0;
    return false;
}

pub fn fail(ip: *Interpreter, n: NodeId, code: @import("Doctor.zig").Disorder, a: anytype, b: anytype) Value {
    if (!ip.res().errors_since(0, n)) _ = ip.res().report(code, n, a, b);
    return .poison;
}

pub fn framed(ip: *Interpreter) bool {
    return ip.top().body.len != 0;
}

pub fn hint(ip: *Interpreter, n: NodeId) Index {
    return if (ip.framed()) ip.info(.ty, n) else .none;
}

pub fn checked(ip: *Interpreter, n: NodeId) Index {
    return if (ip.framed()) ip.info(.ty, n) else ip.res().h09_check_expr(ip.ctx, n, .none);
}

pub fn info(ip: *Interpreter, comptime field: @EnumLiteral(), n: NodeId) @FieldType(Resolver.NodeInfo, @tagName(field)) {
    return ip.res().node_info(ip.top().body, field, n);
}

pub fn alloc(ip: *Interpreter, n: u32) u32 {
    const at = ip.mem.head;
    ip.mem.extend(n, .empty);
    return at;
}

pub fn put(ip: *Interpreter, v: Value) u32 {
    ip.mem.push(v);
    return ip.mem.head - 1;
}

pub fn fill(ip: *Interpreter, c: usize, v: Value, t: Index) void {
    ip.set(c, ip.own(ip.coerce(v, t)));
}

pub fn vtype(ip: *Interpreter, v: Value) Index {
    return if (!v.is_pool()) v.ty else if (v.is(.none)) .none else ip.res().static_pool.type_of(v.index());
}

pub fn deref(ip: *Interpreter, v: Value) Value {
    return if (v.is_ref()) ip.mem.buf[v.at()] else v;
}

pub fn count(ip: *Interpreter, v: Value) ?u32 {
    const t = ip.vtype(v);
    return if (t == .none or ip.res().static_pool.tag(t) == .record_type) null else ip.span(v);
}

pub fn span(ip: *Interpreter, v: Value) ?u32 {
    if (v.is_heap()) return v.len();
    if (!v.is_pool() or v.is(.none)) return null;
    const sp = &ip.res().static_pool;
    return switch (sp.get(v.index())) {
        .aggregate => |a| @intCast(a.elems.len),
        .string => |s| @intCast(s.len),
        else => null,
    };
}

pub fn elem(ip: *Interpreter, v: Value, i: u32) Value {
    if (v.is_heap()) return ip.mem.buf[v.at() + i];
    const sp = &ip.res().static_pool;
    return switch (sp.get(v.index())) {
        .aggregate => |a| .of(sp, a.elems[i]),
        .string => |s| .int(.u8_type, s[i]),
        else => .poison,
    };
}

pub fn escapes(ip: *Interpreter, v: Value) bool {
    if (v.is_ref()) return true;
    if (!v.is_heap()) return false;
    for (0..v.len()) |i| if (ip.mem.buf[v.at() + i].is(.none) or ip.escapes(ip.mem.buf[v.at() + i])) return true;
    return false;
}

pub fn pool(ip: *Interpreter, v: Value) Index {
    if (v.is_pool()) return v.index();
    if (v.is_ref()) return .poison_type;
    const sp = &ip.res().static_pool;
    if (!v.is_heap()) return Value.scalar(sp, v);
    const mark = ip.ids.head;
    defer ip.ids.head = mark;
    for (0..v.len()) |i| {
        const x = ip.pool(ip.mem.buf[v.at() + i]);
        ip.ids.push(x);
    }
    return sp.intern(.{ .aggregate = .{ .ty = v.ty, .elems = ip.ids.buf[mark..ip.ids.head] } });
}

pub fn own(ip: *Interpreter, v: Value) Value {
    if (!v.is_heap()) return v;
    const at = ip.alloc(v.len());
    for (0..v.len()) |i| {
        const x = ip.own(ip.mem.buf[v.at() + i]);
        ip.mem.buf[at + i] = x;
    }
    return .block(v.ty, at, v.len());
}

pub fn thaw(ip: *Interpreter, c: u32) Value {
    const v = ip.mem.buf[c];
    if (!v.is_pool()) return v;
    const n = ip.span(v) orelse return v;
    const at = ip.alloc(n);
    for (0..n) |i| ip.mem.buf[at + i] = ip.elem(v, @intCast(i));
    ip.set(c, .block(ip.vtype(v), at, n));
    return ip.mem.buf[c];
}

pub fn coerce(ip: *Interpreter, v: Value, t: Index) Value {
    const sp = &ip.res().static_pool;
    if (t == .none or t == .poison_type or v.is_pool() or v.is_heap()) return .fit(v, t);
    if (v.is_ref()) {
        if (!sp.is_ptr(t)) return v;
        const c = v.at();
        return .ref(t, if (sp.tag(sp.pointee(t)) != .array_type and ip.count(ip.mem.buf[c]) != null) ip.thaw(c).at() else c);
    }
    if (sp.single_payload(t) == .none) return .fit(v, t);
    const case = sp.payload_case(t);
    const rec = sp.get(case).variant_case_type.payload;
    const x = ip.pool(.fit(v, sp.get(rec).custom_type.field_types[0]));
    const agg = sp.intern(.{ .aggregate = .{ .ty = rec, .elems = &.{x} } });
    return .pooled(sp.intern(.{ .variant_value = .{ .case = case, .payload = agg } }));
}

pub fn zero(ip: *Interpreter, t: Index) Value {
    const sp = &ip.res().static_pool;
    if (Value.is_int(t)) return .int(t, 0);
    if (Value.is_float(t)) return .float(t, 0);
    if (t == .bool_type) return .boolean(false);
    if (t == .none or t == .poison_type) return .empty;
    if (sp.tag(t) == .record_type) return calls.construct(ip, t, &.{});
    if (sp.tag(t) == .variant_type) return ip.zero_case(sp.get(t).variant_type);
    if (sp.tag(t) != .array_type or sp.tag(sp.get(t).array_type.len) != .int_value) return .empty;
    const n: u32 = @intCast(sp.get(sp.get(t).array_type.len).int.bits);
    const at = ip.alloc(n);
    for (0..n) |i| {
        const x = ip.zero(sp.get(t).array_type.elem);
        ip.mem.buf[at + i] = x;
    }
    return .block(t, at, n);
}

// all-zero bytes: the case tagged 0, or for `tagof self` the payload holding 0
fn zero_case(ip: *Interpreter, v: StaticPool.VariantType) Value {
    const sp = &ip.res().static_pool;
    var payload: Index = .none;
    for (v.cases) |c| {
        const cs = sp.get(c).variant_case_type;
        if (v.tag_mode == .self and cs.payload != .none) payload = c else if (sp.tag(cs.tag) == .int_value and sp.get(cs.tag).int.bits == 0) return calls.construct(ip, c, &.{});
    }
    return if (payload != .none) calls.construct(ip, payload, &.{}) else .empty;
}

pub fn eval(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const sp = &r.static_pool;
    if (!ip.charge(n, 1)) return .poison;
    const b = ip.top().body;
    if (n -% b.lo < b.len) {
        const c = r.body_nodes.pool.value.buf[b.start + n - b.lo];
        if (c != .none) return .of(sp, c);
    }
    const k = r.nk(n);
    const a0 = r.arg(n, 0);
    const a1 = r.arg(n, 1);
    return switch (k) {
        .int, .char, .float, .string, .boolean_true, .boolean_false => .fit(.of(sp, r.literal_value(n, false)), ip.hint(n)),
        .neg_num => if (r.is_literal(n)) .fit(.of(sp, r.literal_value(a0, true)), ip.hint(n)) else ip.unary(n, k, ip.eval(a0)),
        .neg_logic => ip.unary(n, k, ip.eval(a0)),
        .capture, .do => ip.eval(a0),
        .ret, .ret_void, .brk, .cont => control.jump(ip, n, k),
        .identifier, .identifier_self => places.load(ip, n),
        .block => control.block(ip, n),
        .def_var, .assign, .assign_typed, .mod_pub, .mod_mut, .mod_stc => places.declare(ip, n),
        .inc_prefix, .dec_prefix, .inc_postfix, .dec_postfix, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod => places.update(ip, n, k),
        .binary_logic_and, .binary_logic_or => blk: {
            const l = ip.eval(a0);
            break :blk if (l.ty == .bool_type and (l.bits != 0) == (k == .binary_logic_or)) l else ip.arith(n, k, l, ip.eval(a1));
        },
        .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod, .binary_pow, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and, .binary_eq, .binary_neq, .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq, .binary_logic_xor => ip.arith(n, k, ip.eval(a0), ip.eval(a1)),
        .if_then, .stcif_then, .if_else, .stcif_else => control.branch(ip, n, k),
        .match, .stcmatch => control.match(ip, n),
        .for_seq, .stcfor_seq, .for_var_in_seq, .stcfor_var_in_seq, .@"while", .stcwhile, .while_with_repeat_stmt, .stcwhile_with_repeat_stmt, .loop, .stcloop, .loop_with_repeat_stmt, .stcloop_with_repeat_stmt => control.loop(ip, n),
        .selftag_unwrap, .selftag_unwrap_fallback, .selftag_arrow, .labelarrow => control.unwrap(ip, n),
        .array, .array_empty => ip.array(n),
        .array_index => ip.index(n),
        .member => calls.member(ip, n),
        .fun_call => calls.call(ip, n),
        .with => calls.with(ip, n),
        .address_of => places.address(ip, n),
        .dereference => places.dereference(ip, n),
        .deinit => places.deinit(ip, n),
        .@"defer", .inlined_defer_deinit => control.defer_(ip, n, k),
        .as => types.cast(ip, n),
        .asbits => types.asbits(ip, n),
        .oftype => types.oftype(ip, n),
        .sizeof => types.sizeof(ip, n),
        else => types.static(ip, n, k),
    };
}

fn unary(ip: *Interpreter, n: NodeId, k: Kind, v: Value) Value {
    if (v.is(.poison_type)) return v;
    return Value.unary(k, v, ip.hint(n)) orelse ip.fail(n, .not_static, ip.pool(v), 0);
}

pub fn arith(ip: *Interpreter, n: NodeId, k: Kind, a: Value, b: Value) Value {
    if (a.is(.poison_type) or b.is(.poison_type)) return .poison;
    if (b.is_ref() and Value.is_int(a.ty) and k == .binary_add) return ip.arith(n, k, b, a);
    if (a.is_ref() and Value.is_int(b.ty) and (k == .binary_add or k == .binary_sub)) return .ref(a.ty, if (k == .binary_add) a.at() +% @as(u32, @truncate(b.bits)) else a.at() -% @as(u32, @truncate(b.bits)));
    const x: Value = if (a.is_heap()) .pooled(ip.pool(a)) else a;
    const y: Value = if (b.is_heap()) .pooled(ip.pool(b)) else b;
    return Value.binary(k, x, y, ip.hint(n)) catch |e| ip.fail(n, if (e == error.Invalid) .static_eval_failed else .not_static, ip.pool(x), ip.pool(y));
}

fn array(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const elems = if (r.nk(n) == .array) r.kids(n) else &[_]NodeId{};
    const len: u32 = @intCast(elems.len);
    const ct = r.static_pool.apply_vars(&r.abstract_pool, ip.hint(n));
    var et = types.elem_type(ip, ct);
    const at = ip.alloc(len);
    for (elems, 0..) |e, i| {
        const x = ip.eval(e);
        if (x.is(.poison_type)) return x;
        ip.fill(at + i, x, et);
    }
    const whole = et != .none and !r.static_pool.has_vars(ct);
    if (et == .none) et = if (len > 0) ip.vtype(ip.mem.buf[at]) else .unit_type;
    return .block(if (whole) ct else types.array_type(ip, len, et), at, len);
}

fn index(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
    const base = ip.eval(r.arg(n, 0));
    if (base.is(.poison_type)) return base;
    const agg = ip.deref(base);
    const i = ip.eval(r.arg(n, 1));
    if (i.is(.poison_type)) return i;
    if (!Value.is_int(i.ty)) return ip.fail(n, .not_static, 0, 0);
    const len = ip.count(agg) orelse return if (base.is_ref()) ip.mem.buf[base.at() + @as(u32, @intCast(i.bits))] else ip.fail(n, .not_static, 0, 0);
    if (i.bits >= len) return ip.fail(n, .static_eval_failed, ip.pool(i), len);
    return ip.elem(agg, @intCast(i.bits));
}
