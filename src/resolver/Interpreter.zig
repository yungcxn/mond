const std = @import("std");
const DynBuf = @import("../ds/dynbuf.zig").DynBuf;
const ParseTree = @import("../ParseTree.zig");
const Resolver = @import("../Resolver.zig");
const StaticPool = @import("StaticPool.zig");
const DeclPool = @import("DeclPool.zig");
const Value = @import("interpreter/Value.zig");
const places = @import("interpreter/places.zig");
const control = @import("interpreter/control.zig");
const calls = @import("interpreter/calls.zig");
const types = @import("interpreter/types.zig");
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;

const Interpreter = @This();

const step_budget: u32 = 1_000_000;
pub const max_depth: u32 = 256;
pub const no_cell = std.math.maxInt(u32);

// env: the closure a frame was called through, its captures resolve to the closure's cells
const Frame = struct { body: Resolver.Body, base: u32, env: Value = .empty };
const Session = struct { ctx: *Resolver.FnCtx, mem: u32, adopted: u32 };
const Adopted = struct { decl: DeclPool.Index, cell: u32 };
const Defer = struct { node: NodeId, cell: u32 };

budget: u32 = step_budget,
depth: u32 = 0,
// the node whose evaluation is running, an exhausted budget or depth is its failure
root: NodeId = 0,
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
caps: std.AutoHashMapUnmanaged(DeclPool.Index, [2]u32) = .empty,
cap_list: DynBuf(DeclPool.Index),

pub fn init(a: std.mem.Allocator) Interpreter {
    return .{ .frames = .init(a, 64), .mem = .init(a, 1024), .list = .init(a, 256), .ids = .init(a, 256), .adopted = .init(a, 16), .defers = .init(a, 16), .cap_list = .init(a, 64) };
}

pub fn deinit(self: *Interpreter) void {
    self.frames.deinit();
    self.mem.deinit();
    self.list.deinit();
    self.ids.deinit();
    self.adopted.deinit();
    self.defers.deinit();
    self.cap_list.deinit();
}

pub fn res(self: *Interpreter) *Resolver {
    return @alignCast(@fieldParentPtr("interpreter", self));
}

fn open(self: *Interpreter, ctx: *Resolver.FnCtx, body: Resolver.Body) Session {
    if (self.depth == 0) self.budget = step_budget;
    self.depth += 1;
    const s = Session{ .ctx = self.ctx, .mem = self.mem.head, .adopted = self.adopted.head };
    self.ctx = ctx;
    self.enter(body);
    return s;
}

fn close(self: *Interpreter, s: Session) void {
    places.flush(self, s.adopted);
    self.depth -= 1;
    self.frames.head -= 1;
    self.truncate(s.mem);
    self.ctx = s.ctx;
}

pub fn export_(self: *Interpreter, n: NodeId, v: Value) Index {
    return if (self.escapes(v)) self.report(.not_static, n, 0, 0) else self.pool(v);
}

pub fn static_value(self: *Interpreter, ctx: *Resolver.FnCtx, n: NodeId) Index {
    if (self.depth == 0) self.root = n;
    const s = self.open(ctx, .{});
    defer self.close(s);
    const v = self.export_(n, self.eval(n));
    if (v != .poison_type) self.res().node_value[n] = v;
    return v;
}

pub fn static_match(self: *Interpreter, ctx: *Resolver.FnCtx, pat: NodeId, v: Index) bool {
    if (self.depth == 0) self.root = pat;
    const s = self.open(ctx, .{});
    defer self.close(s);
    return control.matches(self, pat, Value.of(&self.res().static_pool, v));
}

pub fn run(self: *Interpreter, ctx: *Resolver.FnCtx, root: NodeId, body: Resolver.Body) Index {
    const s = self.open(ctx, body);
    defer self.close(s);
    return self.export_(root, self.coerce(self.result(self.eval(root)), ctx.ret_type));
}

pub fn enter(self: *Interpreter, body: Resolver.Body) void {
    self.frames.push(.{ .body = body, .base = self.alloc(body.locals) });
}

pub fn leave(self: *Interpreter, keep: bool) void {
    self.frames.head -= 1;
    if (!keep) self.truncate(self.frames.buf[self.frames.head].base);
}

fn truncate(self: *Interpreter, to: u32) void {
    if (self.floor_cell < to) {
        self.mem.head = @max(to, @min(self.floor, self.mem.head));
        return;
    }
    self.mem.head = to;
    self.floor = 0;
    self.floor_cell = no_cell;
}

pub fn set(self: *Interpreter, c: usize, v: Value) void {
    self.mem.buf[c] = v;
    if (!v.is_heap() or c >= self.top().base) return;
    self.floor = @max(self.floor, self.mem.head);
    self.floor_cell = @min(self.floor_cell, @as(u32, @intCast(c)));
}

pub fn top(self: *Interpreter) Frame {
    return self.frames.buf[self.frames.head - 1];
}

pub fn result(self: *Interpreter, v: Value) Value {
    defer self.unwind = .none;
    return if (self.unwind == .none or self.unwind == .ret) v else .unit;
}

pub fn charge(self: *Interpreter, n: NodeId, cost: u32) bool {
    if (self.depth == 0) self.budget = step_budget;
    if (self.budget > cost) {
        self.budget -= cost;
        return true;
    }
    if (self.budget > 0) _ = self.fail(self.origin(n), .static_eval_failed, 0, 0);
    self.budget = 0;
    return false;
}

pub fn origin(self: *const Interpreter, n: NodeId) NodeId {
    return if (self.depth > 0) self.root else n;
}

pub fn fail(self: *Interpreter, n: NodeId, code: @import("Doctor.zig").Disorder, a: anytype, b: anytype) Value {
    if (!self.res().errors_since(0, n)) _ = self.report(code, n, a, b);
    return .poison;
}

// checking is over for evaluated nodes: a failure is diagnosed without poisoning their types, `try_static` may rewind it
pub fn report(self: *Interpreter, code: @import("Doctor.zig").Disorder, n: NodeId, a: anytype, b: anytype) Index {
    self.res().doc.h21_report(code, n, a, b);
    return .poison_type;
}

pub fn framed(self: *Interpreter) bool {
    return self.top().body.len != 0;
}

pub fn hint(self: *Interpreter, n: NodeId) Index {
    return if (self.framed()) self.info(.ty, n) else self.res().node_type[n];
}

pub fn checked(self: *Interpreter, n: NodeId) Index {
    return if (self.framed()) self.info(.ty, n) else self.res().h09_check_expr(self.ctx, n, .none);
}

pub fn info(self: *Interpreter, comptime field: @EnumLiteral(), n: NodeId) @FieldType(Resolver.EphemeralNodeInfo, @tagName(field)) {
    return self.res().node_info(self.top().body, field, n);
}

pub fn alloc(self: *Interpreter, n: u32) u32 {
    const at = self.mem.head;
    self.mem.extend(n, .empty);
    return at;
}

pub fn put(self: *Interpreter, v: Value) u32 {
    self.mem.push(v);
    return self.mem.head - 1;
}

pub fn fill(self: *Interpreter, c: usize, v: Value, t: Index) void {
    self.set(c, self.own(self.coerce(v, t)));
}

pub fn vtype(self: *Interpreter, v: Value) Index {
    return if (!v.is_pool()) v.ty else if (v.is(.none)) .none else if (self.res().static_pool.tag(v.index()) == .variant_case_type) v.index() else self.res().static_pool.type_of(v.index());
}

pub fn deref(self: *Interpreter, v: Value) Value {
    return if (v.is_ref()) self.mem.buf[v.at()] else v;
}

pub fn count(self: *Interpreter, v: Value) ?u32 {
    const t = self.vtype(v);
    return if (t == .none or self.res().static_pool.tag(t) == .record_type or self.res().static_pool.tag(t) == .variant_case_type) null else self.span(v);
}

pub fn span(self: *Interpreter, v: Value) ?u32 {
    if (v.is_heap()) return v.len();
    if (!v.is_pool() or v.is(.none)) return null;
    const sp = &self.res().static_pool;
    return switch (sp.get(v.index())) {
        .aggregate => |a| @intCast(a.elems.len),
        .string => |s| @intCast(s.len),
        else => null,
    };
}

pub fn elem(self: *Interpreter, v: Value, i: u32) Value {
    if (v.is_heap()) return self.mem.buf[v.at() + i];
    const sp = &self.res().static_pool;
    return switch (sp.get(v.index())) {
        .aggregate => |a| .of(sp, a.elems[i]),
        .string => |s| .int(.u8_type, s[i]),
        else => .poison,
    };
}

pub fn escapes(self: *Interpreter, v: Value) bool {
    if (v.is_ref() or v.is_heap() and self.res().static_pool.tag(v.ty) == .function_type) return true;
    if (!v.is_heap()) return false;
    for (0..v.len()) |i| if (self.mem.buf[v.at() + i].is(.none) or self.escapes(self.mem.buf[v.at() + i])) return true;
    return false;
}

pub fn pool(self: *Interpreter, v: Value) Index {
    if (v.is_pool()) return v.index();
    if (v.is_ref()) return .poison_type;
    const sp = &self.res().static_pool;
    if (!v.is_heap()) return Value.scalar(sp, v);
    const mark = self.ids.head;
    defer self.ids.head = mark;
    for (0..v.len()) |i| {
        const x = self.pool(self.mem.buf[v.at() + i]);
        self.ids.push(x);
    }
    return sp.intern(.{ .aggregate = .{ .ty = v.ty, .elems = self.ids.buf[mark..self.ids.head] } });
}

pub fn own(self: *Interpreter, v: Value) Value {
    if (!v.is_heap()) return v;
    const at = self.alloc(v.len());
    for (0..v.len()) |i| {
        const x = self.own(self.mem.buf[v.at() + i]);
        self.mem.buf[at + i] = x;
    }
    return .block(v.ty, at, v.len());
}

pub fn thaw(self: *Interpreter, c: u32) Value {
    const v = self.mem.buf[c];
    if (!v.is_pool()) return v;
    const n = self.span(v) orelse return v;
    const at = self.alloc(n);
    for (0..n) |i| self.mem.buf[at + i] = self.elem(v, @intCast(i));
    self.set(c, .block(self.vtype(v), at, n));
    return self.mem.buf[c];
}

pub fn coerce(self: *Interpreter, v: Value, t: Index) Value {
    const sp = &self.res().static_pool;
    if (t == .none or t == .poison_type or v.is_pool() or v.is_heap()) return .fit(v, t);
    if (v.is_ref()) {
        if (!sp.is_ptr(t)) return v;
        const c = v.at();
        return .ref(t, if (sp.tag(sp.pointee(t)) != .array_type and self.count(self.mem.buf[c]) != null) self.thaw(c).at() else c);
    }
    if (sp.single_payload(t) == .none) return .fit(v, t);
    const case = sp.payload_case(t);
    const rec = sp.get(case).variant_case_type.payload;
    const x = self.pool(.fit(v, sp.get(rec).custom_type.field_types[0]));
    const agg = sp.intern(.{ .aggregate = .{ .ty = rec, .elems = &.{x} } });
    return .pooled(sp.intern(.{ .variant_value = .{ .case = case, .payload = agg } }));
}

pub fn zero(self: *Interpreter, t: Index) Value {
    const sp = &self.res().static_pool;
    if (Value.is_int(t)) return .int(t, 0);
    if (Value.is_float(t)) return .float(t, 0);
    if (t == .bool_type) return .boolean(false);
    if (t == .none or t == .poison_type) return .empty;
    if (sp.tag(t) == .record_type) return calls.construct(self, t, &.{});
    if (sp.tag(t) == .variant_type) return self.zero_case(sp.get(t).variant_type);
    if (sp.tag(t) != .array_type or sp.tag(sp.get(t).array_type.len) != .int_value) return .empty;
    const n: u32 = @intCast(sp.get(sp.get(t).array_type.len).int.bits);
    const at = self.alloc(n);
    for (0..n) |i| {
        const x = self.zero(sp.get(t).array_type.elem);
        self.mem.buf[at + i] = x;
    }
    return .block(t, at, n);
}

// all-zero bytes: the case tagged 0, or for `tagof self` the payload holding 0
fn zero_case(self: *Interpreter, v: StaticPool.VariantType) Value {
    const sp = &self.res().static_pool;
    var payload: Index = .none;
    for (v.cases) |c| {
        const cs = sp.get(c).variant_case_type;
        if (v.tag_mode == .self and cs.payload != .none) payload = c else if (sp.tag(cs.tag) == .int_value and sp.get(cs.tag).int.bits == 0) return calls.construct(self, c, &.{});
    }
    return if (payload != .none) calls.construct(self, payload, &.{}) else .empty;
}

pub fn captures(self: *Interpreter, d: DeclPool.Index) []const DeclPool.Index {
    if (self.caps.get(d)) |c| return self.cap_list.buf[c[0]..][0..c[1]];
    const start = self.cap_list.head;
    self.res().captures(d, &self.cap_list);
    self.caps.put(self.frames.alloc, d, .{ start, self.cap_list.head - start }) catch @panic("OOM");
    return self.cap_list.buf[start..self.cap_list.head];
}

// a function as a value: with captures a block of the function and its environment, like the lowerer's closure
pub fn closure(self: *Interpreter, d: DeclPool.Index) Value {
    const r = self.res();
    const f: Value = .of(&r.static_pool, r.decl_pool.values()[@intFromEnum(d)]);
    const caps = self.captures(d);
    if (caps.len == 0) return f;
    const at = self.alloc(@intCast(caps.len + 1));
    self.mem.buf[at] = f;
    for (caps, 1..) |c, i| {
        const s = places.slot(self, c);
        const x: Value = if (s != null and r.by_ref(c)) .ref(r.self_ptr(r.decl_pool.tys()[@intFromEnum(c)]), s.?) else self.own(places.peek(self, c));
        self.mem.buf[at + i] = x;
    }
    return .block(r.decl_pool.tys()[@intFromEnum(d)], at, @intCast(caps.len + 1));
}

// the cell of a capture of the closure a frame runs in
pub fn captured(self: *Interpreter, f: Frame, d: DeclPool.Index) ?u32 {
    if (!f.env.is_heap() or f.body.decl == .none) return null;
    const k = std.mem.indexOfScalar(DeclPool.Index, self.captures(f.body.decl), d) orelse return null;
    const c = f.env.at() + 1 + @as(u32, @intCast(k));
    return if (self.mem.buf[c].is_ref() and self.res().by_ref(d)) self.mem.buf[c].at() else c;
}

pub fn eval(self: *Interpreter, n: NodeId) Value {
    const r = self.res();
    const sp = &r.static_pool;
    if (!self.charge(n, 1)) return .poison;
    const b = self.top().body;
    if (n -% b.lo < b.len) {
        const c = r.body_nodes.pool.value.buf[b.start + n - b.lo];
        if (c != .none) return .of(sp, c);
    }
    const k = r.tree.kind(n);
    const a0 = r.tree.arg(n, 0);
    const a1 = r.tree.arg(n, 1);
    return switch (k) {
        .int, .char, .float, .string, .boolean_true, .boolean_false => .fit(.of(sp, r.literal_value(n, false)), self.hint(n)),
        .neg_num => if (r.is_literal(n)) .fit(.of(sp, r.literal_value(a0, true)), self.hint(n)) else self.unary(n, k, self.eval(a0)),
        .neg_logic => self.unary(n, k, self.eval(a0)),
        .capture, .do => self.eval(a0),
        .ret, .ret_void, .brk, .cont => control.jump(self, n, k),
        .identifier, .identifier_self => places.load(self, n),
        .block => control.block(self, n),
        .def_var, .assign, .assign_typed, .mod_pub, .mod_mut, .mod_stc => places.declare(self, n),
        .inc_prefix, .dec_prefix, .inc_postfix, .dec_postfix, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod => places.update(self, n, k),
        .binary_logic_and, .binary_logic_or => blk: {
            const l = self.eval(a0);
            break :blk if (l.ty == .bool_type and (l.bits != 0) == (k == .binary_logic_or)) l else self.arith(n, k, l, self.eval(a1));
        },
        .binary_add, .binary_sub, .binary_mul, .binary_add_wrap, .binary_sub_wrap, .binary_mul_wrap, .binary_div, .binary_mod, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and, .binary_eq, .binary_neq, .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq, .binary_logic_xor => self.arith(n, k, self.eval(a0), self.eval(a1)),
        .if_then, .stcif_then, .if_else, .stcif_else => control.branch(self, n, k),
        .match, .stcmatch => control.match(self, n),
        .for_seq, .stcfor_seq, .for_var_in_seq, .stcfor_var_in_seq, .@"while", .stcwhile, .while_with_repeat_stmt, .stcwhile_with_repeat_stmt, .loop, .stcloop, .loop_with_repeat_stmt, .stcloop_with_repeat_stmt => control.loop(self, n),
        .selftag_unwrap, .selftag_unwrap_fallback, .selftag_arrow, .labelarrow => control.unwrap(self, n),
        .array, .array_empty => self.array(n),
        .array_index => self.index(n),
        .member => calls.member(self, n),
        .fun_call => calls.call(self, n),
        .with => calls.with(self, n),
        .address_of => places.address(self, n),
        .dereference => places.dereference(self, n),
        .deinit => places.deinit(self, n),
        .@"defer", .inlined_defer_deinit => control.defer_(self, n, k),
        .as => types.cast(self, n),
        .asbits => types.asbits(self, n),
        .oftype => types.oftype(self, n),
        .sizeof => types.sizeof(self, n),
        else => types.static(self, n, k),
    };
}

fn unary(self: *Interpreter, n: NodeId, k: Kind, v: Value) Value {
    if (v.is(.poison_type)) return v;
    return Value.unary(k, v, self.hint(n)) catch |e| self.fail(n, if (e == error.Invalid) .static_eval_failed else .not_static, self.pool(v), 0);
}

pub fn arith(self: *Interpreter, n: NodeId, k: Kind, a: Value, b: Value) Value {
    if (a.is(.poison_type) or b.is(.poison_type)) return .poison;
    if (b.is_ref() and Value.is_int(a.ty) and k == .binary_add) return self.arith(n, k, b, a);
    if (a.is_ref() and Value.is_int(b.ty) and (k == .binary_add or k == .binary_sub)) return .ref(a.ty, if (k == .binary_add) a.at() +% @as(u32, @truncate(b.bits)) else a.at() -% @as(u32, @truncate(b.bits)));
    if (a.is_ref() != b.is_ref()) return self.arith(n, k, self.deref(a), self.deref(b));
    // references into the same memory order by their cells
    if (a.is_ref() and b.is_ref()) return Value.binary(k, .int(.u64_type, a.at()), .int(.u64_type, b.at()), .bool_type) catch self.fail(n, .not_static, 0, 0);
    const x: Value = if (a.is_heap()) .pooled(self.pool(a)) else a;
    const y: Value = if (b.is_heap()) .pooled(self.pool(b)) else b;
    return Value.binary(k, x, y, self.hint(n)) catch |e| self.fail(n, if (e == error.Invalid) .static_eval_failed else .not_static, self.pool(x), self.pool(y));
}

fn array(self: *Interpreter, n: NodeId) Value {
    const r = self.res();
    const elems = if (r.tree.kind(n) == .array) r.tree.manychildren(n) else &[_]NodeId{};
    const len: u32 = @intCast(elems.len);
    const ct = r.static_pool.apply_vars(&r.abstract_pool, self.hint(n));
    var et = types.elem_type(self, ct);
    const at = self.alloc(len);
    for (elems, 0..) |e, i| {
        const x = self.eval(e);
        if (x.is(.poison_type)) return x;
        self.fill(at + i, x, et);
    }
    const whole = et != .none and !r.static_pool.has_vars(ct);
    if (et == .none) et = types.joined(self, self.mem.buf[at..][0..len]);
    return .block(if (whole) ct else types.array_type(self, len, et), at, len);
}

fn index(self: *Interpreter, n: NodeId) Value {
    const r = self.res();
    const base = self.eval(r.tree.arg(n, 0));
    if (base.is(.poison_type)) return base;
    const agg = self.deref(base);
    const i = self.eval(r.tree.arg(n, 1));
    if (i.is(.poison_type)) return i;
    if (!Value.is_int(i.ty)) return self.fail(n, .not_static, 0, 0);
    const len = self.count(agg) orelse return if (base.is_ref()) self.mem.buf[base.at() + @as(u32, @intCast(i.bits))] else self.fail(n, .not_static, 0, 0);
    if (i.bits >= len) return self.fail(n, .static_eval_failed, self.pool(i), len);
    return self.elem(agg, @intCast(i.bits));
}
