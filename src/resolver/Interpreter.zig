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

// env: the closure a frame was called through, its captures resolve to the closure's cells
const Frame = struct { body: Resolver.Body, base: u32, env: Value = .empty };
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
caps: std.AutoHashMapUnmanaged(Decl.Index, [2]u32) = .empty,
cap_list: DynBuf(Decl.Index),

pub fn init(a: std.mem.Allocator) Interpreter {
    return .{ .frames = .init(a, 64), .mem = .init(a, 1024), .list = .init(a, 256), .ids = .init(a, 256), .adopted = .init(a, 16), .defers = .init(a, 16), .cap_list = .init(a, 64) };
}

<<<<<<< HEAD
pub fn deinit(ip: *Interpreter) void {
    inline for (.{ &ip.frames, &ip.mem, &ip.list, &ip.ids, &ip.adopted, &ip.defers, &ip.cap_list }) |b| b.deinit();
    ip.caps.deinit(ip.frames.alloc);
=======
pub fn deinit(self: *Interpreter) void {
    self.frames.deinit();
    self.mem.deinit();
    self.list.deinit();
    self.ids.deinit();
    self.adopted.deinit();
    self.defers.deinit();
>>>>>>> 931c932 (chore: small adjs.)
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

<<<<<<< HEAD
fn close(ip: *Interpreter, s: Session) void {
    places.flush(ip, s.adopted);
    ip.depth -= 1;
    ip.frames.head -= 1;
    ip.truncate(s.mem);
    ip.ctx = s.ctx;
}

pub fn export_(ip: *Interpreter, n: NodeId, v: Value) Index {
    return if (ip.escapes(v)) ip.report(.not_static, n, 0, 0) else ip.pool(v);
=======
fn close(self: *Interpreter, s: Session) void {
    places.flush(self, s.adopted);
    self.depth -= 1;
    self.frames.head -= 1;
    self.mem.head = s.mem;
    self.ctx = s.ctx;
}

pub fn export_(self: *Interpreter, n: NodeId, v: Value) Index {
    return if (self.escapes(v)) self.res().report(.not_static, n, 0, 0) else self.pool(v);
>>>>>>> 931c932 (chore: small adjs.)
}

pub fn static_value(self: *Interpreter, ctx: *Resolver.FnCtx, n: NodeId) Index {
    const s = self.open(ctx, .{});
    defer self.close(s);
    const v = self.export_(n, self.eval(n));
    if (v != .poison_type) self.res().node_value[n] = v;
    return v;
}

pub fn static_match(self: *Interpreter, ctx: *Resolver.FnCtx, pat: NodeId, v: Index) bool {
    const s = self.open(ctx, .{});
    defer self.close(s);
    return control.matches(self, pat, Value.of(&self.res().static_pool, v));
}

pub fn run(self: *Interpreter, ctx: *Resolver.FnCtx, root: NodeId, body: Resolver.Body) Index {
    const s = self.open(ctx, body);
    defer self.close(s);
    return self.export_(root, self.result(self.eval(root)));
}

pub fn enter(self: *Interpreter, body: Resolver.Body) void {
    self.frames.push(.{ .body = body, .base = self.alloc(body.locals) });
}

<<<<<<< HEAD
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

pub fn top(ip: *Interpreter) Frame {
    return ip.frames.buf[ip.frames.head - 1];
=======
pub fn leave(self: *Interpreter, keep: bool) void {
    self.frames.head -= 1;
    if (!keep) self.mem.head = self.frames.buf[self.frames.head].base;
}

pub fn detached(self: *Interpreter, n: NodeId) Value {
    self.frames.push(.{ .body = .{}, .base = self.mem.head });
    defer self.frames.head -= 1;
    return self.eval(n);
}

fn top(self: *Interpreter) Frame {
    return self.frames.buf[self.frames.head - 1];
>>>>>>> 931c932 (chore: small adjs.)
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
<<<<<<< HEAD
    if (ip.budget > 0) _ = ip.report(.static_eval_failed, n, 0, 0);
    ip.budget = 0;
    return false;
}

pub fn fail(ip: *Interpreter, n: NodeId, code: @import("Doctor.zig").Disorder, a: anytype, b: anytype) Value {
    if (!ip.res().errors_since(0, n)) _ = ip.report(code, n, a, b);
    return .poison;
}

// checking is over for evaluated nodes: a failure is diagnosed without poisoning their types, `try_static` may rewind it
pub fn report(ip: *Interpreter, code: @import("Doctor.zig").Disorder, n: NodeId, a: anytype, b: anytype) Index {
    ip.res().doc.h21_report(code, n, a, b);
    return .poison_type;
}

pub fn framed(ip: *Interpreter) bool {
    return ip.top().body.len != 0;
}

pub fn hint(ip: *Interpreter, n: NodeId) Index {
    return if (ip.framed()) ip.info(.ty, n) else ip.res().node_type[n];
=======
    if (self.budget > 0) _ = self.res().report(.static_eval_failed, n, 0, 0);
    self.budget = 0;
    return false;
}

pub fn fail(self: *Interpreter, n: NodeId, code: @import("Doctor.zig").Disorder, a: anytype, b: anytype) Value {
    if (!self.res().errors_since(0, n)) _ = self.res().report(code, n, a, b);
    return .poison;
}

pub fn framed(self: *Interpreter) bool {
    return self.top().body.len != 0;
}

pub fn hint(self: *Interpreter, n: NodeId) Index {
    return if (self.framed()) self.info(.ty, n) else .none;
>>>>>>> 931c932 (chore: small adjs.)
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

<<<<<<< HEAD
pub fn fill(ip: *Interpreter, c: usize, v: Value, t: Index) void {
    ip.set(c, ip.own(ip.coerce(v, t)));
=======
pub fn fill(self: *Interpreter, c: usize, v: Value, t: Index) void {
    const x = self.own(self.coerce(v, t));
    self.mem.buf[c] = x;
>>>>>>> 931c932 (chore: small adjs.)
}

pub fn vtype(self: *Interpreter, v: Value) Index {
    return if (!v.is_pool()) v.ty else if (v.is(.none)) .none else self.res().static_pool.type_of(v.index());
}

pub fn deref(self: *Interpreter, v: Value) Value {
    return if (v.is_ref()) self.mem.buf[v.at()] else v;
}

<<<<<<< HEAD
pub fn count(ip: *Interpreter, v: Value) ?u32 {
    const t = ip.vtype(v);
    return if (t == .none or ip.res().static_pool.tag(t) == .record_type or ip.res().static_pool.tag(t) == .variant_case_type) null else ip.span(v);
=======
pub fn count(self: *Interpreter, v: Value) ?u32 {
    const t = self.vtype(v);
    return if (t == .none or self.res().static_pool.tag(t) == .record_type) null else self.span(v);
>>>>>>> 931c932 (chore: small adjs.)
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

<<<<<<< HEAD
pub fn escapes(ip: *Interpreter, v: Value) bool {
    if (v.is_ref() or v.is_heap() and ip.res().static_pool.tag(v.ty) == .function_type) return true;
    if (!v.is_heap()) return false;
    for (0..v.len()) |i| if (ip.mem.buf[v.at() + i].is(.none) or ip.escapes(ip.mem.buf[v.at() + i])) return true;
=======
pub fn escapes(self: *Interpreter, v: Value) bool {
    if (v.is_ref()) return true;
    if (!v.is_heap()) return false;
    for (0..v.len()) |i| if (self.escapes(self.mem.buf[v.at() + i])) return true;
>>>>>>> 931c932 (chore: small adjs.)
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
<<<<<<< HEAD
    const n = ip.span(v) orelse return v;
    const at = ip.alloc(n);
    for (0..n) |i| ip.mem.buf[at + i] = ip.elem(v, @intCast(i));
    ip.set(c, .block(ip.vtype(v), at, n));
    return ip.mem.buf[c];
=======
    const n = self.span(v) orelse return v;
    const at = self.alloc(n);
    for (0..n) |i| self.mem.buf[at + i] = self.elem(v, @intCast(i));
    self.mem.buf[c] = .block(self.vtype(v), at, n);
    return self.mem.buf[c];
>>>>>>> 931c932 (chore: small adjs.)
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
<<<<<<< HEAD
    if (sp.tag(t) == .record_type) return calls.construct(ip, t, &.{});
    if (sp.tag(t) == .variant_type) return ip.zero_case(sp.get(t).variant_type);
=======
    if (sp.tag(t) == .record_type) return calls.construct(self, t, &.{});
>>>>>>> 931c932 (chore: small adjs.)
    if (sp.tag(t) != .array_type or sp.tag(sp.get(t).array_type.len) != .int_value) return .empty;
    const n: u32 = @intCast(sp.get(sp.get(t).array_type.len).int.bits);
    const at = self.alloc(n);
    for (0..n) |i| {
        const x = self.zero(sp.get(t).array_type.elem);
        self.mem.buf[at + i] = x;
    }
    return .block(t, at, n);
}

<<<<<<< HEAD
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

pub fn captures(ip: *Interpreter, d: Decl.Index) []const Decl.Index {
    if (ip.caps.get(d)) |c| return ip.cap_list.buf[c[0]..][0..c[1]];
    const start = ip.cap_list.head;
    ip.res().captures(d, &ip.cap_list);
    ip.caps.put(ip.frames.alloc, d, .{ start, ip.cap_list.head - start }) catch @panic("OOM");
    return ip.cap_list.buf[start..ip.cap_list.head];
}

// a function as a value: with captures a block of the function and its environment, like the lowerer's closure
pub fn closure(ip: *Interpreter, d: Decl.Index) Value {
    const r = ip.res();
    const f: Value = .of(&r.static_pool, r.dp(.value, d).*);
    const caps = ip.captures(d);
    if (caps.len == 0) return f;
    const at = ip.alloc(@intCast(caps.len + 1));
    ip.mem.buf[at] = f;
    for (caps, 1..) |c, i| {
        const s = places.slot(ip, c);
        const x: Value = if (s != null and r.by_ref(c)) .ref(r.self_ptr(r.dp(.ty, c).*), s.?) else ip.own(places.peek(ip, c));
        ip.mem.buf[at + i] = x;
    }
    return .block(r.dp(.ty, d).*, at, @intCast(caps.len + 1));
}

// the cell of a capture of the closure a frame runs in
pub fn captured(ip: *Interpreter, f: Frame, d: Decl.Index) ?u32 {
    if (!f.env.is_heap() or f.body.decl == .none) return null;
    const k = std.mem.indexOfScalar(Decl.Index, ip.captures(f.body.decl), d) orelse return null;
    const c = f.env.at() + 1 + @as(u32, @intCast(k));
    return if (ip.mem.buf[c].is_ref() and ip.res().by_ref(d)) ip.mem.buf[c].at() else c;
}

pub fn eval(ip: *Interpreter, n: NodeId) Value {
    const r = ip.res();
=======
pub fn eval(self: *Interpreter, n: NodeId) Value {
    const r = self.res();
>>>>>>> 931c932 (chore: small adjs.)
    const sp = &r.static_pool;
    if (!self.charge(n, 1)) return .poison;
    const b = self.top().body;
    if (n -% b.lo < b.len) {
        const c = r.body_nodes.pool.value.buf[b.start + n - b.lo];
        if (c != .none) return .of(sp, c);
    }
    const k = r.nk(n);
    const a0 = r.arg(n, 0);
    const a1 = r.arg(n, 1);
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
<<<<<<< HEAD
        .binary_add, .binary_sub, .binary_mul, .binary_add_wrap, .binary_sub_wrap, .binary_mul_wrap, .binary_div, .binary_mod, .binary_pow, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and, .binary_eq, .binary_neq, .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq, .binary_logic_xor => ip.arith(n, k, ip.eval(a0), ip.eval(a1)),
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
=======
        .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod, .binary_pow, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and, .binary_eq, .binary_neq, .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq, .binary_logic_xor => self.arith(n, k, self.eval(a0), self.eval(a1)),
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
>>>>>>> 931c932 (chore: small adjs.)
    };
}

fn unary(self: *Interpreter, n: NodeId, k: Kind, v: Value) Value {
    if (v.is(.poison_type)) return v;
<<<<<<< HEAD
    return Value.unary(k, v, ip.hint(n)) catch |e| ip.fail(n, if (e == error.Invalid) .static_eval_failed else .not_static, ip.pool(v), 0);
=======
    return Value.unary(k, v, self.hint(n)) orelse self.fail(n, .not_static, self.pool(v), 0);
>>>>>>> 931c932 (chore: small adjs.)
}

pub fn arith(self: *Interpreter, n: NodeId, k: Kind, a: Value, b: Value) Value {
    if (a.is(.poison_type) or b.is(.poison_type)) return .poison;
    if (b.is_ref() and Value.is_int(a.ty) and k == .binary_add) return self.arith(n, k, b, a);
    if (a.is_ref() and Value.is_int(b.ty) and (k == .binary_add or k == .binary_sub)) return .ref(a.ty, if (k == .binary_add) a.at() +% @as(u32, @truncate(b.bits)) else a.at() -% @as(u32, @truncate(b.bits)));
<<<<<<< HEAD
    if (a.is_ref() != b.is_ref()) return ip.arith(n, k, ip.deref(a), ip.deref(b));
    // references into the same memory order by their cells
    if (a.is_ref() and b.is_ref()) return Value.binary(k, .int(.u64_type, a.at()), .int(.u64_type, b.at()), .bool_type) catch ip.fail(n, .not_static, 0, 0);
    const x: Value = if (a.is_heap()) .pooled(ip.pool(a)) else a;
    const y: Value = if (b.is_heap()) .pooled(ip.pool(b)) else b;
    return Value.binary(k, x, y, ip.hint(n)) catch |e| ip.fail(n, if (e == error.Invalid) .static_eval_failed else .not_static, ip.pool(x), ip.pool(y));
=======
    const x: Value = if (a.is_heap()) .pooled(self.pool(a)) else a;
    const y: Value = if (b.is_heap()) .pooled(self.pool(b)) else b;
    return Value.binary(k, x, y, self.hint(n)) catch |e| self.fail(n, if (e == error.Invalid) .static_eval_failed else .not_static, self.pool(x), self.pool(y));
>>>>>>> 931c932 (chore: small adjs.)
}

fn array(self: *Interpreter, n: NodeId) Value {
    const r = self.res();
    const elems = if (r.nk(n) == .array) r.kids(n) else &[_]NodeId{};
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
    if (et == .none) et = if (len > 0) self.vtype(self.mem.buf[at]) else .unit_type;
    return .block(if (whole) ct else types.array_type(self, len, et), at, len);
}

fn index(self: *Interpreter, n: NodeId) Value {
    const r = self.res();
    const base = self.eval(r.arg(n, 0));
    if (base.is(.poison_type)) return base;
    const agg = self.deref(base);
    const i = self.eval(r.arg(n, 1));
    if (i.is(.poison_type)) return i;
    if (!Value.is_int(i.ty)) return self.fail(n, .not_static, 0, 0);
    const len = self.count(agg) orelse return if (base.is_ref()) self.mem.buf[base.at() + @as(u32, @intCast(i.bits))] else self.fail(n, .not_static, 0, 0);
    if (i.bits >= len) return self.fail(n, .static_eval_failed, self.pool(i), len);
    return self.elem(agg, @intCast(i.bits));
}
