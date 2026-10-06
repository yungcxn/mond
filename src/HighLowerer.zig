const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const ParseTree = @import("ParseTree.zig");
const syntax = @import("resolver/syntax.zig");
const Resolver = @import("Resolver.zig");
const StaticPool = @import("resolver/StaticPool.zig");
const NamePool = @import("resolver/NamePool.zig");
const BodyPool = @import("resolver/BodyPool.zig");
const DeclPool = @import("resolver/DeclPool.zig");
const HighIr = @import("high_lowerer/HighIr.zig");
const decls = @import("resolver/checker/decls.zig");
const types = @import("resolver/checker/types.zig");
const calls = @import("resolver/checker/calls.zig");
const control = @import("resolver/checker/control.zig");
const statics = @import("resolver/checker/statics.zig");
const Ref = HighIr.Ref;
const Op = HighIr.Op;
const Index = StaticPool.Index;
const NodeId = ParseTree.NodeId;
const Kind = ParseTree.Node.Kind;

const HighLowerer = @This();
const none: u32 = std.math.maxInt(u32);

const Scratch = struct { op: Op, ty: Index, a: u32, b: u32, block: u32 };
const BlockState = struct { sealed: bool, preds: u32, pending: u32, count: u32 };
const Edge = struct { from: u32, next: u32 };
const Pending = struct { v: u32, phi: u32, next: u32 };
const Loop = struct { brk: u32, cont: u32, defers: u32 };
const Defer = struct { node: NodeId, val: Ref, ty: Index };
const Key = struct { op: Op, ty: Index, a: u32, b: u32 };

alloc: std.mem.Allocator,
r: *Resolver,
sp: *StaticPool,
ir: HighIr,
base: u32,
fn_of: std.AutoHashMapUnmanaged(DeclPool.Index, u32) = .empty,
head_of: std.AutoHashMapUnmanaged(DeclPool.Index, DeclPool.Index) = .empty,
next_of: std.AutoHashMapUnmanaged(DeclPool.Index, DeclPool.Index) = .empty,
global_of: std.AutoHashMapUnmanaged(DeclPool.Index, u32) = .empty,
caps_of: std.AutoHashMapUnmanaged(DeclPool.Index, [2]u32) = .empty,
cap_list: DynBuf(DeclPool.Index),
queue: DynBuf(DeclPool.Index),
insts: SoD(Scratch),
blocks: SoD(BlockState),
edges: SoD(Edge),
pending: SoD(Pending),
extra: DynBuf(u32),
tmp: DynBuf(u32),
alias: DynBuf(u32),
remap: DynBuf(u32),
var_types: DynBuf(Index),
params: DynBuf(Ref),
defers: DynBuf(Defer),
loops: DynBuf(Loop),
defs: std.AutoHashMapUnmanaged(u64, Ref) = .empty,
lvn: std.AutoHashMapUnmanaged(Key, Ref) = .empty,
slots: std.AutoHashMapUnmanaged(DeclPool.Index, Ref) = .empty,
taken: std.AutoHashMapUnmanaged(DeclPool.Index, void) = .empty,
cur: u32 = 0,
dead: bool = false,
ret_ty: Index = .unit_type,
body: BodyPool.Body = .{},

pub fn init(alloc: std.mem.Allocator, r: *Resolver) HighLowerer {
    return .{
        .alloc = alloc,
        .r = r,
        .sp = &r.static_pool,
        .ir = .init(alloc),
        .base = r.decl_pool.entries.len(),
        .cap_list = .init(alloc, 64),
        .queue = .init(alloc, 256),
        .insts = .init(alloc, 1024),
        .blocks = .init(alloc, 128),
        .edges = .init(alloc, 256),
        .pending = .init(alloc, 64),
        .extra = .init(alloc, 1024),
        .tmp = .init(alloc, 256),
        .alias = .init(alloc, 1024),
        .remap = .init(alloc, 1024),
        .var_types = .init(alloc, 64),
        .params = .init(alloc, 16),
        .defers = .init(alloc, 16),
        .loops = .init(alloc, 16),
    };
}

pub fn deinit(self: *HighLowerer) void {
    self.fn_of.deinit(self.alloc);
    self.head_of.deinit(self.alloc);
    self.next_of.deinit(self.alloc);
    self.global_of.deinit(self.alloc);
    self.caps_of.deinit(self.alloc);
    self.defs.deinit(self.alloc);
    self.lvn.deinit(self.alloc);
    self.slots.deinit(self.alloc);
    self.taken.deinit(self.alloc);

    self.ir.deinit();

    self.cap_list.deinit();
    self.queue.deinit();
    self.insts.deinit();
    self.blocks.deinit();
    self.edges.deinit();
    self.pending.deinit();
    self.extra.deinit();
    self.tmp.deinit();
    self.alias.deinit();
    self.remap.deinit();
    self.var_types.deinit();
    self.params.deinit();
    self.defers.deinit();
    self.loops.deinit();
}

pub fn lower(self: *HighLowerer) void {
    const bodies = self.r.bodies.list.sliced();
    var heads = self.r.scopes.globals.valueIterator();
    while (heads.next()) |h| self.group(h.*);
    const d = self.r.decl_pool.entries.sliced();
    for (0..d.name.len) |i| if (d.flags[i].is_global and d.kind[i] == .variable) {
        put(self.alloc, &self.global_of, @enumFromInt(i), self.ir.globals.len());
        self.ir.globals.push(.{ .decl = @enumFromInt(i), .ty = self.apply(d.ty[i]), .init = if (d.flags[i].is_stc) d.value[i] else .none });
    };
    for (bodies.decl) |bd| if (self.r.decl_pool.kinds()[@intFromEnum(bd)].is_fn() and !self.head_of.contains(bd)) {
        _ = self.func(bd);
    };
    self.ir.init_fn = self.ir.functions.len();
    self.ir.functions.push(.{ .decl = .none, .ty = self.sp.intern(.{ .function_type = .{ .category = .default, .params = &.{}, .ret = .unit_type } }), .first_block = 0, .blocks = 0, .first_inst = 0, .insts = 0, .captures = 0 });
    var i: u32 = 0;
    while (i < self.queue.head) : (i += 1) self.lower_fn(self.queue.buf[i]);
    self.lower_init();
}

fn put(alloc: std.mem.Allocator, m: anytype, k: @FieldType(@TypeOf(m.*).KV, "key"), v: @FieldType(@TypeOf(m.*).KV, "value")) void {
    m.put(alloc, k, v) catch @panic("OOM");
}

fn group(self: *HighLowerer, first: DeclPool.Index) void {
    var c = first;
    while (c != .none) : (c = self.r.decl_pool.next_overloads()[@intFromEnum(c)]) {
        const rc = decls.real(self.r, c);
        if (!self.r.bodies.of.contains(rc)) continue;
        var h = first;
        while (h != c) : (h = self.r.decl_pool.next_overloads()[@intFromEnum(h)]) {
            const rh = decls.real(self.r, h);
            if (!self.r.bodies.of.contains(rh) or !calls.same_params(self.r, rh, rc)) continue;
            put(self.alloc, &self.head_of, rc, rh);
            var last = rh;
            while (self.next_of.get(last)) |n| last = n;
            put(self.alloc, &self.next_of, last, rc);
            break;
        }
    }
}

fn func(self: *HighLowerer, d0: DeclPool.Index) u32 {
    const d = self.head_of.get(d0) orelse d0;
    const gop = self.fn_of.getOrPut(self.alloc, d) catch @panic("OOM");
    if (gop.found_existing) return gop.value_ptr.*;
    gop.value_ptr.* = self.ir.functions.len();
    self.ir.functions.push(.{ .decl = d, .ty = self.apply(self.r.decl_pool.tys()[@intFromEnum(d)]), .first_block = 0, .blocks = 0, .first_inst = 0, .insts = 0, .captures = @intCast(self.captures(d).len) });
    if (self.r.bodies.of.contains(d)) self.queue.push(d);
    return gop.value_ptr.*;
}

fn apply(self: *HighLowerer, t: Index) Index {
    return if (t == .none) t else self.sp.apply_vars(&self.r.abstract_pool, t);
}

fn ty(self: *HighLowerer, n: NodeId) Index {
    return self.apply(self.r.node_info(self.body, .ty, n));
}

fn decl(self: *HighLowerer, n: NodeId) DeclPool.Index {
    return self.r.node_info(self.body, .decl, n);
}

fn static_of(self: *HighLowerer, n: NodeId) ?Index {
    const v = self.r.node_info(self.body, .value, n);
    return if (v == .none or v == .poison_type) null else v;
}

fn ptr(self: *HighLowerer, t: Index) Index {
    return self.sp.intern(.{ .ptr_type = .{ .child = t, .mutable = true } });
}

fn is_ptr(self: *HighLowerer, t: Index) bool {
    return t != .none and self.sp.get(t) == .ptr_type;
}

fn child(self: *HighLowerer, t: Index) Index {
    return self.sp.get(t).ptr_type.child;
}

fn has_value(t: Index) bool {
    return t != .none and t != .unit_type and t != .runit_type and t != .never_type and t != .poison_type;
}

fn var_ty(self: *HighLowerer, v: u32) Index {
    return if (v < self.base) self.apply(self.r.decl_pool.tys()[v]) else self.var_types.buf[v - self.base];
}

fn temp(self: *HighLowerer, t: Index) u32 {
    self.var_types.push(t);
    return self.base + self.var_types.head - 1;
}

fn int(self: *HighLowerer, t: Index, bits: u64) Ref {
    return Ref.of(self.sp.intern(.{ .int = .{ .ty = t, .bits = bits } }));
}

fn unit() Ref {
    return Ref.of(.unit_value);
}

fn ref_ty(self: *HighLowerer, x: Ref) Index {
    if (x == .none) return .none;
    if (x.is_const()) return self.sp.type_of(x.value());
    if (x.is_global()) return self.ptr(self.ir.globals.pool.ty.buf[x.index()]);
    return self.insts.pool.ty.buf[@intFromEnum(x)];
}

fn list(self: *HighLowerer, items: []const u32) u32 {
    const at = self.extra.head;
    self.extra.push(@intCast(items.len));
    self.extra.append(items);
    return at;
}

fn raw(self: *HighLowerer, op: Op, t: Index, a: u32, b: u32, at: u32) Ref {
    self.insts.push(.{ .op = op, .ty = t, .a = a, .b = b, .block = at });
    return @enumFromInt(self.insts.len() - 1);
}

fn emit(self: *HighLowerer, op: Op, t: Index, a0: u32, b0: u32) Ref {
    if (self.dead) return .none;
    if (self.fold(op, t, a0, b0)) |x| return x;
    const swap = op.is_commutative() and b0 < a0;
    const key = Key{ .op = op, .ty = t, .a = if (swap) b0 else a0, .b = if (swap) a0 else b0 };
    if (op.is_pure()) if (self.lvn.get(key)) |hit| return hit;
    const x = self.raw(op, t, key.a, key.b, self.cur);
    if (op.is_pure()) put(self.alloc, &self.lvn, key, x);
    if (op.is_terminator()) self.dead = true;
    return x;
}

fn fold(self: *HighLowerer, op: Op, t: Index, a: u32, b: u32) ?Ref {
    const unary = op == .neg or op == .not;
    if (!unary and (@intFromEnum(op) < @intFromEnum(Op.add) or @intFromEnum(op) > @intFromEnum(Op.ge))) return null;
    const x: Ref = @enumFromInt(a);
    const y: Ref = if (unary) Ref.of(.unit_value) else @enumFromInt(b);
    if (!x.is_const() or !y.is_const()) return null;
    const sp = self.sp;
    const xv = x.value();
    const yv = y.value();
    if (xv == .bool_true or xv == .bool_false) {
        const p = xv == .bool_true;
        const q = yv == .bool_true;
        if (!unary and yv != .bool_true and yv != .bool_false) return null;
        return Ref.of(if (switch (op) {
            .not => !p,
            .bit_and => p and q,
            .bit_or => p or q,
            .bit_xor, .ne => p != q,
            .eq => p == q,
            else => return null,
        }) .bool_true else .bool_false);
    }
    if (sp.tag(xv) != .int_value or !unary and sp.tag(yv) != .int_value) return null;
    const ot = sp.get(xv).int.ty;
    if (sp.get(ot) != .int_type or (unary or @intFromEnum(op) < @intFromEnum(Op.eq)) and sp.get(t) != .int_type) return null;
    const it = sp.get(ot).int_type;
    const signed = it.signedness == .signed;
    const p = norm(sp.get(xv).int.bits, it);
    const q = if (unary) 0 else norm(sp.get(yv).int.bits, it);
    const sp_: i64 = @bitCast(p);
    const sq: i64 = @bitCast(q);
    const r: u64 = switch (op) {
        .add => p +% q,
        .sub => p -% q,
        .mul => p *% q,
        .bit_and => p & q,
        .bit_or => p | q,
        .bit_xor => p ^ q,
        .neg => 0 -% p,
        .not => ~p,
        .div, .rem => blk: {
            if (q == 0 or signed and sq == -1) return null;
            break :blk if (!signed) (if (op == .div) p / q else p % q) else @bitCast(if (op == .div) @divTrunc(sp_, sq) else @rem(sp_, sq));
        },
        .shl, .shr => blk: {
            if (q >= it.bits) return null;
            const sh: u6 = @intCast(q);
            break :blk if (op == .shl) p << sh else if (signed) @bitCast(sp_ >> sh) else p >> sh;
        },
        .eq, .ne, .lt, .gt, .le, .ge => return Ref.of(if (switch (op) {
            .eq => p == q,
            .ne => p != q,
            .lt => if (signed) sp_ < sq else p < q,
            .gt => if (signed) sp_ > sq else p > q,
            .le => if (signed) sp_ <= sq else p <= q,
            else => if (signed) sp_ >= sq else p >= q,
        }) .bool_true else .bool_false),
        else => return null,
    };
    return self.int(t, norm(r, sp.get(t).int_type));
}

fn norm(v: u64, it: StaticPool.IntType) u64 {
    if (it.bits == 0 or it.bits >= 64) return v;
    const sh: u6 = @intCast(64 - it.bits);
    return if (it.signedness == .signed) @bitCast(@as(i64, @bitCast(v << sh)) >> sh) else v << sh >> sh;
}

fn e2(self: *HighLowerer, op: Op, t: Index, a: Ref, b: Ref) Ref {
    return self.emit(op, t, @intFromEnum(a), @intFromEnum(b));
}

fn block(self: *HighLowerer) u32 {
    self.blocks.push(.{ .sealed = false, .preds = none, .pending = none, .count = 0 });
    return self.blocks.len() - 1;
}

fn edge(self: *HighLowerer, to: u32) void {
    self.edges.push(.{ .from = self.cur, .next = self.blocks.pool.preds.buf[to] });
    self.blocks.pool.preds.buf[to] = self.edges.len() - 1;
    self.blocks.pool.count.buf[to] += 1;
}

fn br(self: *HighLowerer, to: u32) void {
    if (self.dead) return;
    self.edge(to);
    _ = self.emit(.br, .unit_type, to, 0);
}

fn cond(self: *HighLowerer, c: Ref, t: u32, e: u32) void {
    if (self.dead) return;
    if (c.is_const() and (c.value() == .bool_true or c.value() == .bool_false)) return self.br(if (c.value() == .bool_true) t else e);
    self.edge(t);
    self.edge(e);
    _ = self.emit(.cond_br, .unit_type, @intFromEnum(c), self.list(&.{ t, e }));
}

fn enter(self: *HighLowerer, b: u32) void {
    self.cur = b;
    self.lvn.clearRetainingCapacity();
    self.dead = b != 0 and self.blocks.pool.count.buf[b] == 0 and self.blocks.pool.sealed.buf[b];
}

fn goto(self: *HighLowerer, b: u32) void {
    const bs = &self.blocks.pool;
    const is = &self.insts.pool;
    const last = self.insts.len() -% 1;
    if (self.dead and bs.count.buf[b] == 1 and bs.pending.buf[b] == none and last != none and is.op.buf[last] == .br and is.a.buf[last] == b and is.block.buf[last] == self.edges.pool.from.buf[bs.preds.buf[b]]) {
        inline for (@typeInfo(@TypeOf(is.*)).@"struct".fields) |f| @field(is, f.name).head -= 1;
        if (self.cur != is.block.buf[last]) self.lvn.clearRetainingCapacity();
        self.cur = is.block.buf[last];
        bs.count.buf[b] = 0;
        bs.preds.buf[b] = none;
        bs.sealed.buf[b] = true;
        self.dead = false;
        return;
    }
    self.seal(b);
    self.enter(b);
}

fn write(self: *HighLowerer, v: u32, b: u32, x: Ref) void {
    put(self.alloc, &self.defs, @as(u64, v) << 32 | b, x);
}

fn read(self: *HighLowerer, v: u32, b: u32) Ref {
    if (self.defs.get(@as(u64, v) << 32 | b)) |x| return x;
    const t = self.var_ty(v);
    const bs = self.blocks.get(b).?;
    const x = if (!bs.sealed) blk: {
        const p = self.raw(.phi, t, 0, 0, b);
        self.pending.push(.{ .v = v, .phi = @intFromEnum(p), .next = bs.pending });
        self.blocks.pool.pending.buf[b] = self.pending.len() - 1;
        break :blk p;
    } else if (bs.count == 0)
        self.raw(.undef, t, 0, 0, b)
    else if (bs.count == 1)
        self.read(v, self.edges.pool.from.buf[bs.preds])
    else blk: {
        const p = self.raw(.phi, t, 0, 0, b);
        self.write(v, b, p);
        self.operands(v, p);
        break :blk p;
    };
    self.write(v, b, x);
    return x;
}

fn operands(self: *HighLowerer, v: u32, p: Ref) void {
    const mark = self.tmp.head;
    var e = self.blocks.pool.preds.buf[self.insts.pool.block.buf[@intFromEnum(p)]];
    while (e != none) : (e = self.edges.pool.next.buf[e]) {
        const x = self.read(v, self.edges.pool.from.buf[e]);
        self.tmp.push(@intFromEnum(x));
    }
    self.insts.pool.b.buf[@intFromEnum(p)] = self.list(self.tmp.buf[mark..self.tmp.head]);
    self.tmp.head = mark;
}

fn seal(self: *HighLowerer, b: u32) void {
    if (self.blocks.pool.sealed.buf[b]) return;
    var p = self.blocks.pool.pending.buf[b];
    while (p != none) : (p = self.pending.pool.next.buf[p]) self.operands(self.pending.pool.v.buf[p], @enumFromInt(self.pending.pool.phi.buf[p]));
    self.blocks.pool.sealed.buf[b] = true;
}

fn needs_mem(self: *HighLowerer, d: DeclPool.Index) bool {
    return self.taken.contains(d) or self.aggregate(self.apply(self.r.decl_pool.tys()[@intFromEnum(d)]));
}

fn aggregate(self: *HighLowerer, t: Index) bool {
    return t != .none and (self.sp.tag(t) == .record_type or (self.sp.tag(t) == .array_type and !self.is_dyn(t)));
}

fn is_dyn(self: *HighLowerer, t: Index) bool {
    return t != .none and self.sp.get(t) == .array_type and self.sp.get(t).array_type.len == StaticPool.dyn_len;
}

fn alloca(self: *HighLowerer, t: Index) Ref {
    if (self.dead) return .none;
    return self.raw(.alloca, self.ptr(t), none, 0, 0);
}

fn default_value(self: *HighLowerer, t: Index) Ref {
    return if (self.sp.tag(t) == .record_type) self.construct(t, &.{}) else self.emit(.zeroed, t, 0, 0);
}

fn declare_var(self: *HighLowerer, d: DeclPool.Index, x: Ref) void {
    if (d == .none or self.dead) return;
    if (self.global_of.contains(d)) return self.store_var(d, x);
    if (self.needs_mem(d)) {
        const s = self.alloca(self.var_ty(@intFromEnum(d)));
        put(self.alloc, &self.slots, d, s);
        if (x != .none) _ = self.e2(.store, .unit_type, s, x);
    } else self.write(@intFromEnum(d), self.cur, if (x == .none) self.raw(.undef, self.var_ty(@intFromEnum(d)), 0, 0, self.cur) else x);
}

fn load_var(self: *HighLowerer, d: DeclPool.Index) Ref {
    if (self.dead) return .none;
    const t = self.var_ty(@intFromEnum(d));
    if (self.global_of.get(d)) |g| return self.e2(.load, t, Ref.global(g), .none);
    if (self.slots.get(d)) |s| return self.e2(.load, t, s, .none);
    return self.read(@intFromEnum(d), self.cur);
}

fn store_var(self: *HighLowerer, d: DeclPool.Index, x: Ref) void {
    if (self.dead or x == .none) return;
    if (self.global_of.get(d)) |g| {
        _ = self.e2(.store, .unit_type, Ref.global(g), x);
    } else if (self.slots.get(d)) |s| {
        _ = self.e2(.store, .unit_type, s, x);
    } else self.write(@intFromEnum(d), self.cur, x);
}

fn is_ssa(self: *HighLowerer, n: NodeId) bool {
    const d = self.decl(n);
    return switch (self.r.tree.kind(n)) {
        .identifier, .identifier_self => d != .none and !self.global_of.contains(d) and !self.slots.contains(d),
        else => false,
    };
}

fn captures(self: *HighLowerer, d: DeclPool.Index) []const DeclPool.Index {
    if (self.caps_of.get(d)) |c| return self.cap_list.buf[c[0]..][0..c[1]];
    const start = self.cap_list.head;
    self.r.bodies.captures(&self.r.decl_pool, d, &self.cap_list);
    put(self.alloc, &self.caps_of, d, [2]u32{ start, self.cap_list.head - start });
    return self.cap_list.buf[start..self.cap_list.head];
}

fn by_ref(self: *HighLowerer, c: DeclPool.Index) bool {
    return self.r.decl_pool.flags()[@intFromEnum(c)].is_mut or self.aggregate(self.apply(self.r.decl_pool.tys()[@intFromEnum(c)]));
}

fn fn_value(self: *HighLowerer, d0: DeclPool.Index) Ref {
    const d = decls.real(self.r, d0);
    const f = self.func(d);
    const head = self.ir.functions.pool.decl.buf[f];
    const caps = self.captures(head);
    if (caps.len == 0) return Ref.of(self.sp.intern(.{ .function = head }));
    const mark = self.tmp.head;
    for (caps) |c| {
        const x = if (self.by_ref(c)) self.slots.get(c) orelse .none else self.load_var(c);
        self.tmp.push(@intFromEnum(x));
    }
    const at = self.list(self.tmp.buf[mark..self.tmp.head]);
    self.tmp.head = mark;
    return self.emit(.closure, self.apply(self.r.decl_pool.tys()[@intFromEnum(head)]), f, at);
}

fn reset(self: *HighLowerer) void {
    inline for (.{
        &self.insts,
        &self.blocks,
        &self.edges,
        &self.pending,
    }) |s| inline for (@typeInfo(@TypeOf(s.pool)).@"struct".fields) |f| {
        @field(s.pool, f.name).head = 0;
    };

    inline for (.{
        &self.extra,
        &self.tmp,
        &self.alias,
        &self.remap,
        &self.var_types,
        &self.params,
        &self.defers,
        &self.loops,
    }) |b| b.head = 0;

    inline for (.{
        &self.defs,
        &self.lvn,
        &self.slots,
        &self.taken,
    }) |m| m.clearRetainingCapacity();

    self.dead = false;
}

fn scan_taken(self: *HighLowerer) void {
    const b = self.body;
    for (b.lo..b.lo + b.len) |i| {
        const n: NodeId = @intCast(i);
        var target: NodeId = 0;
        if (self.r.tree.kind(n) == .address_of) target = self.r.tree.arg(n, 0);
        if (self.r.tree.kind(n) == .fun_call and self.r.tree.kind(self.r.tree.arg(n, 0)) == .member) {
            const d = self.decl(n);
            if (d != .none and self.r.decl_pool.self_off(d) == 1) target = self.r.tree.arg(self.r.tree.arg(n, 0), 0);
        }
        while (target != 0 and self.r.tree.kind(target) == .capture) target = self.r.tree.arg(target, 0);
        if (target != 0 and self.r.tree.kind(target) == .identifier and !self.is_ptr(self.ty(target))) put(self.alloc, &self.taken, self.decl(target), {});
        const d = self.decl(n);
        if (d != .none and self.r.decl_pool.kinds()[@intFromEnum(d)].is_fn() and self.r.bodies.of.contains(d)) {
            const node = self.r.decl_pool.nodes()[@intFromEnum(d)];
            if (node >= b.lo and node < b.lo + b.len) for (self.captures(d)) |c| if (self.by_ref(c)) put(self.alloc, &self.taken, c, {});
        }
    }
}

fn lower_fn(self: *HighLowerer, d: DeclPool.Index) void {
    self.reset();
    const f = self.fn_of.get(d).?;
    const ft = self.apply(self.r.decl_pool.tys()[@intFromEnum(d)]);
    self.ret_ty = self.sp.get(ft).function_type.ret;
    self.goto(self.block());
    const caps = self.captures(d);
    for (caps, 0..) |c, i| {
        const t = self.var_ty(@intFromEnum(c));
        const p = self.emit(.param, if (self.by_ref(c)) self.ptr(t) else t, @intCast(i), 0);
        if (self.by_ref(c)) put(self.alloc, &self.slots, c, p) else self.write(@intFromEnum(c), self.cur, p);
    }
    for (0..self.sp.get(ft).function_type.params.len) |j| self.params.push(self.emit(.param, self.sp.get(ft).function_type.params[j], @intCast(caps.len + j), 0));
    var m: ?DeclPool.Index = d;
    while (m) |c| : (m = self.next_of.get(c)) if (!self.candidate(c)) break;
    if (!self.dead) _ = self.emit(.@"unreachable", .unit_type, 0, 0);
    self.freeze(f);
}

fn candidate(self: *HighLowerer, m: DeclPool.Index) bool {
    self.body = self.r.bodies.get(m).?;
    self.scan_taken();
    const v = decls.value_node(self.r, m);
    const off = self.r.decl_pool.self_off(m);
    if (off == 1) for (self.body.lo..self.body.lo + self.body.len) |i| {
        const x = self.decl(@intCast(i));
        if (x != .none and self.r.decl_pool.kinds()[@intFromEnum(x)] == .self and self.r.decl_pool.nodes()[@intFromEnum(x)] == v) break self.declare_var(x, self.params.buf[0]);
    };
    const pnodes = syntax.params_of(self.r.tree, v);
    for (pnodes, 0..) |pn, i| self.declare_var(self.decl(pn), self.params.buf[i + off]);
    const fail = self.block();
    var tested = false;
    for (pnodes) |pn| {
        const p = syntax.Param.from_node(self.r.tree, pn);
        if (p.where == 0 or p.@"else" != 0 or p.stc) continue;
        tested = true;
        const ok = self.block();
        self.cond(self.expr_to(p.where, .bool_type), ok, fail);
        self.goto(ok);
    }
    for (pnodes) |pn| {
        const p = syntax.Param.from_node(self.r.tree, pn);
        if (p.where == 0 or p.@"else" == 0 or p.stc) continue;
        const ok = self.block();
        const els = self.block();
        self.cond(self.expr_to(p.where, .bool_type), ok, els);
        self.goto(els);
        if (self.r.tree.kind(p.@"else") == .assign or self.r.tree.kind(p.@"else") == .ret) _ = self.expr(p.@"else") else self.store_var(self.decl(pn), self.expr_to(p.@"else", self.ty(pn)));
        self.br(ok);
        self.goto(ok);
    }
    const body = self.r.tree.arg(v, 1);
    if (self.r.tree.kind(body) == .block) {
        _ = self.expr(body);
        if (!self.dead and !has_value(self.ret_ty)) self.ret(.none) else if (!self.dead and self.r.decl_pool.names()[@intFromEnum(m)] == .main) self.ret(self.int(self.ret_ty, 0)) else if (!self.dead) _ = self.emit(.@"unreachable", .unit_type, 0, 0);
    } else self.ret(self.expr_to(body, self.ret_ty));
    self.goto(fail);
    return tested;
}

fn lower_init(self: *HighLowerer) void {
    self.reset();
    self.body = .{};
    self.ret_ty = .unit_type;
    self.goto(self.block());
    for (self.r.roots) |root| switch (self.r.tree.kind(root)) {
        .assign, .assign_typed, .def_var, .mod_pub, .mod_mut, .mod_stc => self.assign(root),
        else => _ = self.expr(root),
    };
    self.ret(.none);
    self.freeze(self.ir.init_fn);
}

fn ret(self: *HighLowerer, x: Ref) void {
    self.run_defers(0);
    _ = self.emit(.ret, .unit_type, @intFromEnum(if (has_value(self.ret_ty)) x else Ref.none), 0);
}

fn run_defers(self: *HighLowerer, mark: u32) void {
    var i = self.defers.head;
    while (i > mark and !self.dead) {
        i -= 1;
        const df = self.defers.buf[i];
        if (df.val == .none) _ = self.expr(df.node) else self.deinit_at(df.val, df.ty);
    }
}

fn deinit_at(self: *HighLowerer, p: Ref, t: Index) void {
    switch (self.sp.lookup_member(t, .deinit)) {
        .method => |m| _ = self.emit(.call, .unit_type, @intFromEnum(self.fn_value(m)), self.list(&.{@intFromEnum(p)})),
        else => {},
    }
}

fn freeze(self: *HighLowerer, f: u32) void {
    const s = self.insts.sliced();
    const n = s.op.len;
    for (0..n) |_| self.alias.push(none);
    var changed = true;
    while (changed) {
        changed = false;
        for (0..n) |i| if (s.op[i] == .phi and self.alias.buf[i] == none) {
            var same: u32 = none;
            const ops = self.extra.buf[s.b[i] + 1 ..][0..self.extra.buf[s.b[i]]];
            const trivial = for (ops) |o0| {
                const o = self.resolve(o0);
                if (o == i or o == same) continue;
                if (same != none) break false;
                same = o;
            } else true;
            if (!trivial) continue;
            self.alias.buf[i] = if (same != none) same else @intFromEnum(self.raw(.undef, s.ty[i], 0, 0, s.block[i]));
            changed = true;
        };
    }
    const all = self.insts.sliced();
    const bs = self.blocks.sliced();
    const blocks_base = self.ir.blocks.len();
    var live: u32 = 0;
    self.remap.head = 0;
    for (0..bs.count.len) |b| {
        self.remap.push(if (b == 0 or bs.count[b] > 0) live else none);
        if (b == 0 or bs.count[b] > 0) live += 1;
    }
    const counts_at = self.remap.head;
    for (0..live * 3 + 1) |_| self.remap.push(0);
    for (0..all.op.len) |i| {
        const nb = self.remap.buf[all.block[i]];
        if (nb == none or self.alias.buf.len > i and i < n and self.alias.buf[i] != none) continue;
        self.remap.buf[counts_at + 1 + nb * 3 + class(all.op[i], all.a[i])] += 1;
    }
    for (1..live * 3 + 1) |k| self.remap.buf[counts_at + k] += self.remap.buf[counts_at + k - 1];
    const index_at = self.remap.head;
    for (0..all.op.len) |_| self.remap.push(none);
    const order_at = self.remap.head;
    const total = self.remap.buf[counts_at + live * 3];
    for (0..total) |_| self.remap.push(0);
    for (0..all.op.len) |i| {
        const nb = self.remap.buf[all.block[i]];
        if (nb == none or (i < n and self.alias.buf[i] != none)) continue;
        const slot = &self.remap.buf[counts_at + nb * 3 + class(all.op[i], all.a[i])];
        self.remap.buf[index_at + i] = slot.*;
        self.remap.buf[order_at + slot.*] = @intCast(i);
        slot.* += 1;
    }
    const first = self.ir.insts.len();
    for (self.remap.buf[order_at..][0..total]) |i| {
        const sh = all.op[i].shape();
        self.ir.insts.push(.{ .op = all.op[i], .ty = all.ty[i], .a = self.operand(sh[0], all.a[i], index_at), .b = self.operand(sh[1], all.b[i], index_at) });
    }
    var start: u32 = 0;
    for (0..bs.count.len) |b| {
        if (self.remap.buf[b] == none) continue;
        const nb = self.remap.buf[b];
        const len = self.remap.buf[counts_at + nb * 3 + 2] - start;
        const preds = self.ir.extra.head;
        self.ir.extra.push(0);
        var e = bs.preds[b];
        while (e != none) : (e = self.edges.pool.next.buf[e]) {
            self.ir.extra.push(self.remap.buf[self.edges.pool.from.buf[e]]);
            self.ir.extra.buf[preds] += 1;
        }
        self.ir.blocks.push(.{ .start = start, .len = len, .preds = preds });
        start += len;
    }
    const fp = &self.ir.functions.pool;
    fp.first_block.buf[f] = blocks_base;
    fp.blocks.buf[f] = live;
    fp.first_inst.buf[f] = first;
    fp.insts.buf[f] = total;
}

fn class(op: Op, a: u32) u32 {
    return switch (op) {
        .phi, .param => 0,
        .undef => 1,
        .alloca => if (a == none) 1 else 2,
        else => 2,
    };
}

fn resolve(self: *HighLowerer, x0: u32) u32 {
    var x = x0;
    while (x != none and x & (1 << 31) == 0 and x < self.alias.head and self.alias.buf[x] != none) x = self.alias.buf[x];
    return x;
}

fn operand(self: *HighLowerer, kind: Op.Operand, x: u32, index_at: u32) u32 {
    return switch (kind) {
        .none, .imm => x,
        .block => self.remap.buf[x],
        .ref => self.new_ref(x, index_at),
        .refs, .blocks, .cases => blk: {
            const at = self.ir.extra.head;
            const items = self.extra.buf[x + 1 ..][0..self.extra.buf[x]];
            self.ir.extra.push(@intCast(items.len));
            for (items, 0..) |it, k| self.ir.extra.push(if (kind == .blocks or kind == .cases and k % 2 == 0) self.remap.buf[it] else self.new_ref(it, index_at));
            break :blk at;
        },
    };
}

fn new_ref(self: *HighLowerer, x0: u32, index_at: u32) u32 {
    const x = self.resolve(x0);
    return if (x == none or x & (1 << 31) != 0) x else self.remap.buf[index_at + x];
}

fn coerce(self: *HighLowerer, x: Ref, from0: Index, to0: Index) Ref {
    const from = self.apply(from0);
    const to = self.apply(to0);
    if (x == .none or from == to or to == .none or from == .none or !has_value(to)) return x;
    const k = self.sp.coerce(&self.r.abstract_pool, from, to);
    return switch (k) {
        .identity, .unified, .ptr_mut_to_ptr, .never_to_any, .poison, .unit_to_runit, .incompatible => x,
        .case_to_variant => if (self.sp.tag(to) == .variant_type) x else self.emit(.convert, to, @intFromEnum(x), @intFromEnum(StaticPool.CoercionKind.variant_to_union)),
        .payload_to_self_tagged => blk: {
            const case = self.payload_case(to);
            const rec = self.sp.get(self.sp.get(self.sp.get(to).variant_type.cases[case]).variant_case_type.payload).custom_type;
            const agg = self.emit(.aggregate, self.sp.get(self.sp.get(to).variant_type.cases[case]).variant_case_type.payload, 0, self.list(&.{@intFromEnum(self.coerce(x, from, rec.field_types[0]))}));
            break :blk self.emit(.variant_make, to, @intCast(case), @intFromEnum(agg));
        },
        else => self.emit(.convert, to, @intFromEnum(x), @intFromEnum(k)),
    };
}

fn payload_case(self: *HighLowerer, v: Index) u32 {
    const cases = self.sp.get(v).variant_type.cases;
    for (cases, 0..) |c, i| if (self.sp.get(c).variant_case_type.payload != .none) return @intCast(i);
    return 0;
}

fn expr_to(self: *HighLowerer, n: NodeId, t: Index) Ref {
    return self.coerce(self.expr(n), self.ty(n), t);
}

fn constant(self: *HighLowerer, v: Index, t: Index) Ref {
    const sp = self.sp;
    if (t != .none and sp.tag(v) == .int_value and sp.get_tag_prop(t).is_integer) return self.int(t, sp.get(v).int.bits);
    if (t != .none and (sp.tag(v) == .int_value or sp.tag(v) == .float_value) and sp.get_tag_prop(t).is_float) {
        const f: f64 = if (sp.tag(v) == .float_value) sp.get(v).float.value else @floatFromInt(@as(i64, @bitCast(sp.get(v).int.bits)));
        return Ref.of(sp.intern(.{ .float = .{ .ty = t, .value = f } }));
    }
    return Ref.of(v);
}

fn arith(k: Kind) ?Op {
    return switch (k) {
        .binary_add, .binary_add_wrap, .assign_add, .inc_prefix, .inc_postfix => .add,
        .binary_sub, .binary_sub_wrap, .assign_sub, .dec_prefix, .dec_postfix => .sub,
        .binary_mul, .binary_mul_wrap, .assign_mul => .mul,
        .binary_div, .assign_div => .div,
        .binary_mod, .assign_mod => .rem,
        .binary_shift_left => .shl,
        .binary_shift_right => .shr,
        .binary_num_and => .bit_and,
        .binary_num_or => .bit_or,
        .binary_num_xor => .bit_xor,
        .binary_eq => .eq,
        .binary_neq => .ne,
        .binary_less => .lt,
        .binary_greater => .gt,
        .binary_less_eq => .le,
        .binary_greater_eq => .ge,
        else => null,
    };
}

fn expr(self: *HighLowerer, n: NodeId) Ref {
    const t = self.ty(n);
    if (self.static_of(n)) |v| return self.constant(v, t);
    const a0 = self.r.tree.arg(n, 0);
    const a1 = self.r.tree.arg(n, 1);
    const k = self.r.tree.kind(n);
    if (arith(k)) |op| switch (k) {
        .binary_eq, .binary_neq, .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq => return self.compare(op, a0, a1),
        .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod => {
            _ = self.update(a0, op, self.expr_to(a1, self.ty(a0)), false);
            return unit();
        },
        .inc_prefix, .dec_prefix, .inc_postfix, .dec_postfix => return self.update(a0, op, self.int(if (self.is_ptr(t)) .u64_type else t, 1), k == .inc_postfix or k == .dec_postfix),
        .binary_add, .binary_sub => return if (self.is_ptr(t)) blk: {
            const x = self.expr(a0);
            const y = self.expr(a1);
            break :blk if (self.is_ptr(self.ty(a0))) self.advance(t, x, k == .binary_sub, y) else self.advance(t, y, false, x);
        } else self.e2(op, t, self.expr_to(a0, t), self.expr_to(a1, t)),
        else => return self.e2(op, t, self.expr_to(a0, t), self.expr_to(a1, t)),
    };
    return switch (k) {
        .int, .char, .float, .string, .boolean_true, .boolean_false, .neg_num => if (syntax.is_literal(self.r.tree, n) or k == .string or k == .boolean_true or k == .boolean_false)
            self.constant(statics.literal_value(self.r, n, false), t)
        else
            self.e2(.neg, t, self.expr_to(a0, t), .none),
        .identifier, .identifier_self => self.ident(n),
        .capture => self.expr(a0),
        .block => blk: {
            const mark = self.defers.head;
            var last = unit();
            for (self.r.tree.manychildren(n)) |s| last = self.expr(s);
            self.run_defers(mark);
            self.defers.head = mark;
            break :blk last;
        },
        .def_var, .assign, .assign_typed, .mod_pub, .mod_mut, .mod_stc => blk: {
            self.assign(n);
            break :blk unit();
        },
        .binary_logic_and, .binary_logic_or => self.logic(n, k == .binary_logic_and),
        .binary_logic_xor => self.e2(.ne, .bool_type, self.expr_to(a0, .bool_type), self.expr_to(a1, .bool_type)),
        .neg_logic => self.e2(.not, t, self.expr_to(a0, t), .none),
        .fun_call => self.call(n),
        .with => self.with(n),
        .member => self.member(n),
        .array_index => self.e2(.load, t, self.place(n), .none),
        .dereference => self.e2(.load, t, self.expr(a0), .none),
        .address_of => self.place(a0),
        .array, .array_empty => blk: {
            const elem = if (self.sp.get(t) == .array_type) self.sp.get(t).array_type.elem else t;
            const mark = self.tmp.head;
            const kids = if (k == .array) self.r.tree.manychildren(n) else &[_]NodeId{};
            for (kids) |e| {
                const x = self.expr_to(e, elem);
                self.tmp.push(@intFromEnum(x));
            }
            const at = self.list(self.tmp.buf[mark..self.tmp.head]);
            self.tmp.head = mark;
            break :blk self.emit(.aggregate, t, 0, at);
        },
        .as => blk: {
            const from = self.ty(a0);
            const c = self.sp.cast(from, t);
            if (c == .array_narrow or c == .pointer_relength) break :blk self.shrink(n);
            const x = self.expr(a0);
            break :blk if (c == .identity) x else self.emit(.cast, t, @intFromEnum(x), @intFromEnum(c));
        },
        .asbits => if (self.ty(a0) == t) self.expr(a0) else self.emit(.cast, t, @intFromEnum(self.expr(a0)), @intFromEnum(if (self.sp.layout(t).size > self.sp.layout(self.ty(a0)).size) StaticPool.CastKind.bit_extend else StaticPool.CastKind.bit_reinterpret)),
        .if_then, .if_else, .stcif_then, .stcif_else => self.branching(n),
        .@"while", .while_with_repeat_stmt, .stcwhile, .stcwhile_with_repeat_stmt, .for_seq, .for_var_in_seq, .stcfor_seq, .stcfor_var_in_seq, .loop, .loop_with_repeat_stmt, .stcloop, .stcloop_with_repeat_stmt => self.loop(n),
        .match, .stcmatch => self.match(n),
        .ret => blk: {
            const x = self.expr_to(a0, self.ret_ty);
            self.ret(x);
            break :blk .none;
        },
        .ret_void => blk: {
            self.ret(.none);
            break :blk .none;
        },
        .brk, .cont => blk: {
            if (self.loops.head == 0) break :blk .none;
            const l = self.loops.buf[self.loops.head - 1];
            self.run_defers(l.defers);
            self.br(if (k == .brk) l.brk else l.cont);
            break :blk .none;
        },
        .do => blk: {
            _ = self.expr(a0);
            break :blk unit();
        },
        .@"defer" => blk: {
            self.defers.push(.{ .node = a0, .val = .none, .ty = .none });
            break :blk unit();
        },
        .deinit => blk: {
            self.deinit_at(self.place(a0), self.deref_ty(self.ty(a0)));
            break :blk unit();
        },
        .inlined_defer_deinit => blk: {
            const x = self.expr(a0);
            const s = self.alloca(self.ty(a0));
            _ = self.e2(.store, .unit_type, s, x);
            self.defers.push(.{ .node = n, .val = s, .ty = self.ty(a0) });
            break :blk x;
        },
        .selftag_unwrap, .selftag_unwrap_fallback, .selftag_arrow, .labelarrow => self.unwrap(n),
        .oftype => self.emit(.type_test, .bool_type, @intFromEnum(self.expr(a0)), @intFromEnum(self.static_of(a1) orelse self.ty(a1))),
        .def_fun => self.fn_value(self.decl(n)),
        else => if (has_value(t)) self.raw(.undef, t, 0, 0, self.cur) else unit(),
    };
}

fn deref_ty(self: *HighLowerer, t: Index) Index {
    return if (self.is_ptr(t)) self.child(t) else t;
}

fn ident(self: *HighLowerer, n: NodeId) Ref {
    const d = self.decl(n);
    if (d == .none) return .none;
    const kind = self.r.decl_pool.kinds()[@intFromEnum(d)];
    const value = self.r.decl_pool.values()[@intFromEnum(d)];
    if (kind.is_fn()) return self.fn_value(d);
    if (value != .none and (self.r.decl_pool.flags()[@intFromEnum(d)].is_stc or kind == .static_parameter or kind == .parameter or kind == .type_alias or kind == .record or kind == .variant or kind == .trait)) return self.constant(value, self.ty(n));
    return self.load_var(d);
}

fn compare(self: *HighLowerer, op: Op, a: NodeId, b: NodeId) Ref {
    var lt = self.ty(a);
    var rt = self.ty(b);
    if (self.sp.tag(lt) == .meta_type and self.sp.tag(rt) == .meta_type) {
        const same = (self.static_of(a) orelse lt) == (self.static_of(b) orelse rt);
        return Ref.of(if (same == (op == .eq)) .bool_true else .bool_false);
    }
    var l = self.expr(a);
    var r = self.expr(b);
    if (self.sp.join(&self.r.abstract_pool, lt, rt).ty == .none) {
        if (self.is_ptr(lt)) {
            l = self.e2(.load, self.child(lt), l, .none);
            lt = self.child(lt);
        }
        if (self.is_ptr(rt)) {
            r = self.e2(.load, self.child(rt), r, .none);
            rt = self.child(rt);
        }
    }
    const jt = self.sp.join(&self.r.abstract_pool, lt, rt).ty;
    return self.e2(op, .bool_type, self.coerce(l, lt, jt), self.coerce(r, rt, jt));
}

fn update(self: *HighLowerer, target: NodeId, op: Op, rhs: Ref, post: bool) Ref {
    const t = self.ty(target);
    if (self.is_ssa(target)) {
        const old = self.load_var(self.decl(target));
        const new = if (self.is_ptr(t)) self.advance(t, old, op == .sub, rhs) else self.e2(op, t, old, rhs);
        self.store_var(self.decl(target), new);
        return if (post) old else new;
    }
    const p = self.place(target);
    const old = self.e2(.load, t, p, .none);
    const new = if (self.is_ptr(t)) self.advance(t, old, op == .sub, rhs) else self.e2(op, t, old, rhs);
    _ = self.e2(.store, .unit_type, p, new);
    return if (post) old else new;
}

fn store_to(self: *HighLowerer, target: NodeId, x: Ref) void {
    if (self.is_ssa(target) or self.global_of.contains(self.decl(target)) and (self.r.tree.kind(target) == .identifier)) return self.store_var(self.decl(target), x);
    _ = self.e2(.store, .unit_type, self.place(target), x);
}

fn assign(self: *HighLowerer, n0: NodeId) void {
    const parts = Resolver.Stmt.from_node(self.r, n0);
    const n = parts.node;
    if (parts.kind != .variable) return;
    const values = parts.values;
    if (parts.assignees.len == 1 and self.r.name_pool.name_of(self.r.tree, self.r.src_bytes, parts.assignees[0]) == .none) return self.store_to(parts.assignees[0], self.expr_to(values[0], self.ty(parts.assignees[0])));
    const shared = if (values.len == 1) self.expr(values[0]) else Ref.none;
    const mark = self.tmp.head;
    defer self.tmp.head = mark;
    for (parts.assignees, 0..) |id, i| {
        const d = self.decl(id);
        if (d == .none or (self.r.decl_pool.flags()[@intFromEnum(d)].is_stc and self.r.decl_pool.values()[@intFromEnum(d)] != .none)) {
            self.tmp.push(@intFromEnum(Ref.none));
            continue;
        }
        const t = self.var_ty(@intFromEnum(d));
        const x = if (values.len == 0) (if (self.aggregate(t) and !self.global_of.contains(d)) self.default_value(t) else Ref.none) else if (values.len > 1) self.expr_to(values[i], t) else self.coerce(shared, self.ty(values[0]), t);
        self.tmp.push(@intFromEnum(x));
    }
    for (parts.assignees, 0..) |id, i| {
        const d = self.decl(id);
        if (d == .none or (self.r.decl_pool.flags()[@intFromEnum(d)].is_stc and self.r.decl_pool.values()[@intFromEnum(d)] != .none)) continue;
        const x: Ref = @enumFromInt(self.tmp.buf[mark + i]);
        if (self.r.decl_pool.nodes()[@intFromEnum(d)] != n) {
            self.store_var(d, x);
        } else if (self.global_of.get(d)) |g| {
            if (x.is_const()) self.ir.globals.pool.init.buf[g] = x.value() else self.store_var(d, x);
        } else self.declare_var(d, x);
    }
}

fn logic(self: *HighLowerer, n: NodeId, is_and: bool) Ref {
    var budget: u8 = 3;
    if (self.cheap(self.r.tree.arg(n, 1), &budget)) return self.e2(if (is_and) .bit_and else .bit_or, .bool_type, self.expr_to(self.r.tree.arg(n, 0), .bool_type), self.expr_to(self.r.tree.arg(n, 1), .bool_type));
    const res = self.temp(.bool_type);
    const l = self.expr_to(self.r.tree.arg(n, 0), .bool_type);
    self.write(res, self.cur, l);
    const rhs = self.block();
    const done = self.block();
    if (is_and) self.cond(l, rhs, done) else self.cond(l, done, rhs);
    self.goto(rhs);
    const r = self.expr_to(self.r.tree.arg(n, 1), .bool_type);
    if (!self.dead) self.write(res, self.cur, r);
    self.br(done);
    self.goto(done);
    return if (self.dead) .none else self.read(res, self.cur);
}

fn scalar(self: *HighLowerer, t: Index) bool {
    return t == .bool_type or t != .none and (self.sp.get_tag_prop(t).is_integer or self.sp.get_tag_prop(t).is_float or self.is_ptr(t));
}

fn cheap(self: *HighLowerer, n: NodeId, budget: *u8) bool {
    if (!self.scalar(self.ty(n))) return false;
    if (self.static_of(n) != null) return true;
    const k = self.r.tree.kind(n);
    switch (k) {
        .identifier, .identifier_self => return self.is_ssa(n) and !self.r.decl_pool.kinds()[@intFromEnum(self.decl(n))].is_fn(),
        .capture => return self.cheap(self.r.tree.arg(n, 0), budget),
        .int, .char, .float, .string, .boolean_true, .boolean_false => return true,
        .neg_num => if (syntax.is_literal(self.r.tree, n)) return true,
        .if_else => {
            if (budget.* == 0) return false;
            budget.* -= 1;
            const it = self.r.tree.arg(n, 0);
            return self.cheap(self.r.tree.arg(it, 0), budget) and self.cheap(self.r.tree.arg(it, 1), budget) and self.cheap(self.r.tree.arg(n, 1), budget);
        },
        .block => return self.r.tree.manychildren(n).len == 1 and self.cheap(self.r.tree.manychildren(n)[0], budget),
        else => {},
    }
    const binary = switch (k) {
        .binary_add, .binary_sub, .binary_mul, .binary_num_and, .binary_num_or, .binary_num_xor, .binary_eq, .binary_neq, .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq, .binary_logic_and, .binary_logic_or, .binary_logic_xor => true,
        .neg_num, .neg_logic => false,
        else => return false,
    };
    if (budget.* == 0 or self.is_ptr(self.ty(self.r.tree.arg(n, 0))) or binary and self.is_ptr(self.ty(self.r.tree.arg(n, 1)))) return false;
    budget.* -= 1;
    return self.cheap(self.r.tree.arg(n, 0), budget) and (!binary or self.cheap(self.r.tree.arg(n, 1), budget));
}

fn arm(self: *HighLowerer, n: NodeId, t: Index, res: u32, merge: u32) void {
    const x = self.expr(n);
    const bt = self.ty(n);
    if (res != none and !self.dead and has_value(bt)) self.write(res, self.cur, self.coerce(x, bt, t));
    self.br(merge);
}

fn branching(self: *HighLowerer, n: NodeId) Ref {
    const t = self.ty(n);
    const k = self.r.tree.kind(n);
    const has_else = k == .if_else or k == .stcif_else;
    const it = if (has_else) self.r.tree.arg(n, 0) else n;
    if (k == .stcif_then or k == .stcif_else) {
        const taken_then = (self.static_of(self.r.tree.arg(it, 0)) orelse .bool_false) == .bool_true;
        return if (taken_then) self.expr_to(self.r.tree.arg(it, 1), t) else if (has_else) self.expr_to(self.r.tree.arg(n, 1), t) else unit();
    }
    var budget: [2]u8 = .{ 3, 3 };
    if (has_else and self.scalar(t) and self.cheap(self.r.tree.arg(it, 1), &budget[0]) and self.cheap(self.r.tree.arg(n, 1), &budget[1])) {
        const c = self.expr_to(self.r.tree.arg(it, 0), .bool_type);
        if (c.is_const()) return self.expr_to(if (c.value() == .bool_true) self.r.tree.arg(it, 1) else self.r.tree.arg(n, 1), t);
        const x = self.expr_to(self.r.tree.arg(it, 1), t);
        const y = self.expr_to(self.r.tree.arg(n, 1), t);
        return if (x == y) x else self.emit(.select, t, @intFromEnum(c), self.list(&.{ @intFromEnum(x), @intFromEnum(y) }));
    }
    const res = if (has_value(t)) self.temp(t) else none;
    const tb = self.block();
    const eb = if (has_else) self.block() else none;
    const m = self.block();
    self.cond(self.expr_to(self.r.tree.arg(it, 0), .bool_type), tb, if (has_else) eb else m);
    self.goto(tb);
    self.arm(self.r.tree.arg(it, 1), t, res, m);
    if (has_else) {
        self.goto(eb);
        self.arm(self.r.tree.arg(n, 1), t, res, m);
    }
    self.goto(m);
    return if (res == none or self.dead) unit() else self.read(res, self.cur);
}

fn match(self: *HighLowerer, n: NodeId) Ref {
    const t = self.ty(n);
    const arms = self.r.tree.manychildren(self.r.tree.arg(n, 1));
    if (self.r.tree.kind(n) == .stcmatch) for (arms) |a| if ((self.static_of(a) orelse .none) == .bool_true) return self.expr_to(self.r.tree.arg(a, 1), t);
    var st = self.ty(self.r.tree.arg(n, 0));
    var s = self.expr(self.r.tree.arg(n, 0));
    if (self.is_ptr(st) and self.sp.deref(&self.r.abstract_pool, st) != st) {
        s = self.e2(.load, self.child(st), s, .none);
        st = self.child(st);
    }
    const res = if (has_value(t)) self.temp(t) else none;
    const m = self.block();
    if (self.switched(arms, s, st, t, res, m)) {
        self.goto(m);
        return if (res == none or self.dead) unit() else self.read(res, self.cur);
    }
    for (arms) |a| {
        const body = self.block();
        const next = self.block();
        self.pattern(self.r.tree.arg(a, 0), s, st, body, next);
        self.goto(body);
        self.arm(self.r.tree.arg(a, 1), t, res, m);
        self.goto(next);
    }
    if (!self.dead) _ = self.emit(.@"unreachable", .unit_type, 0, 0);
    self.goto(m);
    return if (res == none or self.dead) unit() else self.read(res, self.cur);
}

fn tag_ty(self: *HighLowerer, st: Index, variant: Index) Index {
    if (st != .none and self.sp.tag(st) == .variant_union_type) return self.sp.union_tag_type(st);
    const vt = self.sp.get(variant).variant_type;
    return if (vt.tag_type == .none or vt.tag_type == .poison_type) .u8_type else vt.tag_type;
}

// a union's tag is its member's tag moved into the member's own range (members are flattened, no extra tag byte)
fn tag_of(self: *HighLowerer, st: Index, case: Index) Ref {
    const c = self.sp.get(case).variant_case_type;
    const tt = self.tag_ty(st, c.variant);
    if (st != .none and self.sp.tag(st) == .variant_union_type) return self.int(tt, self.sp.get(c.tag).int.bits + self.sp.union_offset(st, c.variant));
    return self.constant(c.tag, tt);
}

fn owns(self: *HighLowerer, st: Index, case: Index) bool {
    const w = self.sp.get(case).variant_case_type.variant;
    if (st == .none or st == w) return true;
    return switch (self.sp.get(st)) {
        .variant_union_type => |u| std.mem.indexOfScalar(Index, u, w) != null,
        .variant_case_type => |c| c.variant == w,
        .variant_type => false,
        else => true,
    };
}

fn is_case(self: *HighLowerer, v: Ref, st: Index, case: Index) Ref {
    const tag = self.tag_of(st, case);
    return self.e2(.eq, .bool_type, self.e2(.variant_tag, self.ref_ty(tag), v, .none), tag);
}

fn is_key(self: *HighLowerer, p: NodeId, st: Index, tagged: bool) ?bool {
    const pt = self.ty(p);
    const case = pt != .none and self.sp.tag(pt) == .variant_case_type;
    if (case and !self.owns(st, pt)) return null;
    return switch (self.r.tree.kind(p)) {
        .identifier => false,
        .partial__match_case_pattern_or => for (self.r.tree.manychildren(p)) |alt| {
            if ((self.is_key(alt, st, tagged) orelse false) == false) return null;
        } else true,
        .labelarrow => if (self.is_key(self.r.tree.arg(p, 0), st, tagged) == true) true else null,
        .fun_call => if (!case or !tagged) null else for (self.r.tree.manychildren(self.r.tree.arg(p, 1))) |a| {
            if (self.r.tree.kind(syntax.arg_value(self.r.tree, a)) != .identifier) return null;
        } else true,
        .partial__match_case_pattern_typecast, .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl, .string => null,
        else => if (case == tagged and (case or syntax.is_literal(self.r.tree, p) or self.static_of(p) != null)) true else null,
    };
}

fn keys(self: *HighLowerer, p: NodeId, st: Index, b: u32, mark: u32) void {
    switch (self.r.tree.kind(p)) {
        .partial__match_case_pattern_or => for (self.r.tree.manychildren(p)) |alt| self.keys(alt, st, b, mark),
        .labelarrow => self.keys(self.r.tree.arg(p, 0), st, b, mark),
        else => {
            const pt = self.ty(p);
            const v: u32 = @intFromEnum(if (self.sp.tag(pt) == .variant_case_type) self.tag_of(st, pt) else self.constant(self.static_of(p) orelse statics.literal_value(self.r, p, false), st));
            var i = mark + 1;
            while (i < self.tmp.head) : (i += 2) if (self.tmp.buf[i] == v) return;
            self.tmp.push(v);
            self.tmp.push(b);
        },
    }
}

fn bind(self: *HighLowerer, p: NodeId, v: Ref, vt: Index) void {
    switch (self.r.tree.kind(p)) {
        .identifier => if (self.r.name_pool.name_of(self.r.tree, self.r.src_bytes, p) != .underscore) self.declare_var(self.decl(p), v),
        .labelarrow => {
            const ct = self.ty(self.r.tree.arg(p, 0));
            self.bind_label(self.r.tree.arg(p, 1), if (self.sp.tag(ct) == .variant_case_type) self.payload(self.narrow(v, vt, self.sp.get(ct).variant_case_type.variant), ct) else v);
        },
        .fun_call => {
            const c = self.sp.get(self.ty(p)).variant_case_type;
            if (c.payload == .none or self.sp.tag(c.payload) != .record_type) return;
            const container = self.e2(.variant_payload, c.payload, self.narrow(v, vt, c.variant), @enumFromInt(c.case));
            for (self.r.tree.manychildren(self.r.tree.arg(p, 1)), 0..) |a, i| {
                const fi = self.field_index(c.payload, a, i);
                const ft = self.sp.get(c.payload).custom_type.field_types[fi];
                self.bind(syntax.arg_value(self.r.tree, a), self.emit(.extract, ft, @intFromEnum(container), fi), ft);
            }
        },
        else => {},
    }
}

fn switched(self: *HighLowerer, arms: []const NodeId, s: Ref, st: Index, t: Index, res: u32, m: u32) bool {
    const sp = self.sp;
    const tagged = st != .none and (sp.tag(st) == .variant_union_type or sp.tag(st) == .variant_type and sp.get(st).variant_type.tag_mode != .self);
    const st_prop = sp.get_tag_prop(st);
    if (!tagged and (st == .none or !st_prop.is_integer)) return false;
    var count: usize = 0;
    var keyed: usize = 0;
    for (arms) |a| {
        const k = self.is_key(self.r.tree.arg(a, 0), st, tagged) orelse return false;
        count += 1;
        keyed += @intFromBool(k);
        if (!k) break;
    }
    if (keyed < 2) return false;
    const mark = self.tmp.head;
    self.tmp.push(none);
    const first = self.blocks.len();
    for (arms[0..count]) |a| {
        const b = self.block();
        if (self.is_key(self.r.tree.arg(a, 0), st, tagged) == true) self.keys(self.r.tree.arg(a, 0), st, b, mark) else self.tmp.buf[mark] = b;
    }
    const dflt = if (self.tmp.buf[mark] == none) self.block() else self.tmp.buf[mark];
    self.tmp.buf[mark] = dflt;
    const cases = self.tmp.buf[mark..self.tmp.head];
    const key = if (tagged) self.e2(.variant_tag, self.ref_ty(@enumFromInt(cases[1])), s, .none) else s;
    if (key.is_const()) {
        var target = dflt;
        var i: usize = 1;
        while (i < cases.len) : (i += 2) if (cases[i] == @intFromEnum(key)) {
            target = cases[i + 1];
        };
        self.br(target);
    } else if (!self.dead) {
        self.edge(dflt);
        var i: usize = 2;
        while (i < cases.len) : (i += 2) self.edge(cases[i]);
        _ = self.emit(.@"switch", .unit_type, @intFromEnum(key), self.list(cases));
    }
    self.tmp.head = mark;
    for (arms[0..count], 0..) |a, i| {
        self.goto(first + @as(u32, @intCast(i)));
        self.bind(self.r.tree.arg(a, 0), s, st);
        self.arm(self.r.tree.arg(a, 1), t, res, m);
    }
    if (dflt == first + count) {
        self.goto(dflt);
        _ = self.emit(.@"unreachable", .unit_type, 0, 0);
    }
    return true;
}

fn narrow(self: *HighLowerer, v: Ref, st: Index, into: Index) Ref {
    if (st == .none or self.sp.tag(st) != .variant_union_type) return v;
    return self.emit(.cast, into, @intFromEnum(v), @intFromEnum(StaticPool.CastKind.variant_retag));
}

fn field_index(self: *HighLowerer, rec: Index, a: NodeId, i: usize) u32 {
    return calls.field_of(self.r, rec, a, i) orelse @intCast(i);
}

fn pattern(self: *HighLowerer, p: NodeId, v: Ref, vt: Index, ok: u32, fail: u32) void {
    const pt = self.ty(p);
    switch (self.r.tree.kind(p)) {
        .identifier => {
            if (self.r.name_pool.name_of(self.r.tree, self.r.src_bytes, p) != .underscore) self.declare_var(self.decl(p), v);
            self.br(ok);
        },
        .partial__match_case_pattern_or => {
            for (self.r.tree.manychildren(p)) |alt| {
                const next = self.block();
                self.pattern(alt, v, vt, ok, next);
                self.goto(next);
            }
            self.br(fail);
        },
        .partial__match_case_pattern_typecast => {
            const t = self.ty(self.r.tree.arg(p, 1));
            if (vt != .none and self.sp.tag(vt) == .variant_union_type and self.sp.tag(t) == .variant_type) {
                const tt = self.sp.union_tag_type(vt);
                const tag = self.e2(.variant_tag, tt, v, .none);
                const lo = self.sp.union_offset(vt, t);
                const mid = self.block();
                const in = self.block();
                self.cond(self.e2(.ge, .bool_type, tag, self.int(tt, lo)), mid, fail);
                self.goto(mid);
                self.cond(self.e2(.lt, .bool_type, tag, self.int(tt, lo + self.sp.tag_range(t))), in, fail);
                self.goto(in);
                self.declare_var(self.decl(self.r.tree.arg(p, 1)), self.narrow(v, vt, t));
            } else if (vt == t or self.sp.coerce(&self.r.abstract_pool, vt, t) != .incompatible) {
                self.declare_var(self.decl(self.r.tree.arg(p, 1)), self.coerce(v, vt, t));
            } else if (self.sp.tag(t) == .variant_case_type and self.owns(vt, t)) {
                const in = self.block();
                self.cond(self.is_case(v, vt, t), in, fail);
                self.goto(in);
                self.declare_var(self.decl(self.r.tree.arg(p, 1)), self.narrow(v, vt, self.sp.get(t).variant_case_type.variant));
            } else if (vt != .none and self.sp.tag(vt) == .trait_type) {
                const in = self.block();
                self.cond(self.emit(.type_test, .bool_type, @intFromEnum(v), @intFromEnum(t)), in, fail);
                self.goto(in);
                self.declare_var(self.decl(self.r.tree.arg(p, 1)), self.emit(.cast, t, @intFromEnum(v), @intFromEnum(StaticPool.CastKind.trait_narrow)));
            } else return self.br(fail);
            self.br(ok);
        },
        .labelarrow => {
            const mid = self.block();
            self.pattern(self.r.tree.arg(p, 0), v, vt, mid, fail);
            self.goto(mid);
            const ct = self.ty(self.r.tree.arg(p, 0));
            self.bind_label(self.r.tree.arg(p, 1), if (self.sp.tag(ct) == .variant_case_type) self.payload(self.narrow(v, vt, self.sp.get(ct).variant_case_type.variant), ct) else v);
            self.br(ok);
        },
        .fun_call => {
            const is_c = self.sp.tag(pt) == .variant_case_type;
            if (is_c and !self.owns(vt, pt)) return self.br(fail);
            if (is_c) {
                const c1 = self.block();
                self.cond(self.is_case(v, vt, pt), c1, fail);
                self.goto(c1);
            }
            const rec = if (is_c) self.sp.get(pt).variant_case_type.payload else pt;
            const container = if (is_c) self.e2(.variant_payload, rec, self.narrow(v, vt, self.sp.get(pt).variant_case_type.variant), @enumFromInt(self.sp.get(pt).variant_case_type.case)) else v;
            if (rec != .none and self.sp.tag(rec) == .record_type) for (self.r.tree.manychildren(self.r.tree.arg(p, 1)), 0..) |a, i| {
                const fi = self.field_index(rec, a, i);
                const ft = self.sp.get(rec).custom_type.field_types[fi];
                const next = self.block();
                self.pattern(syntax.arg_value(self.r.tree, a), self.emit(.extract, ft, @intFromEnum(container), fi), ft, next, fail);
                self.goto(next);
            };
            self.br(ok);
        },
        .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => {
            const k = self.r.tree.kind(p);
            const has_lo = k == .gen_incl or k == .gen_excl or k == .gen_lowerbound;
            const has_hi = k != .gen_lowerbound;
            if (has_lo) {
                const mid = self.block();
                self.cond(self.e2(.ge, .bool_type, v, self.expr_to(self.r.tree.arg(p, 0), vt)), mid, fail);
                self.goto(mid);
            }
            if (has_hi) {
                const hi = self.expr_to(self.r.tree.arg(p, if (has_lo) 1 else 0), vt);
                self.cond(self.e2(if (k == .gen_incl or k == .gen_upperbound_incl) .le else .lt, .bool_type, v, hi), ok, fail);
            } else self.br(ok);
        },
        else => {
            if (self.sp.tag(pt) == .variant_case_type) return if (self.owns(vt, pt)) self.cond(self.is_case(v, vt, pt), ok, fail) else self.br(fail);
            const lit = self.expr_to(p, vt);
            const text = self.r.tree.kind(p) == .string or (self.is_ptr(vt) and self.child(vt) == .u8_type);
            self.cond(self.e2(if (text) .bytes_eq else .eq, .bool_type, v, lit), ok, fail);
        },
    }
}

fn payload(self: *HighLowerer, v: Ref, case: Index) Ref {
    const c = self.sp.get(case).variant_case_type;
    if (c.payload == .none) return v;
    const p = self.e2(.variant_payload, c.payload, v, @enumFromInt(c.case));
    const fields = self.sp.get(c.payload).custom_type.field_types;
    return if (fields.len == 1) self.emit(.extract, fields[0], @intFromEnum(p), 0) else p;
}

fn bind_label(self: *HighLowerer, label: NodeId, v: Ref) void {
    if (self.r.tree.kind(label) != .partial__destructure) return self.declare_var(self.decl(label), v);
    const vt = self.ref_ty(v);
    for (self.r.tree.manychildren(label), 0..) |id, i| self.declare_var(self.decl(id), self.emit(.extract, self.ty(id), @intFromEnum(v), @intCast(i)));
    _ = vt;
}

fn unwrap(self: *HighLowerer, n: NodeId) Ref {
    const k = self.r.tree.kind(n);
    const t = self.ty(n);
    const v = self.expr(self.r.tree.arg(n, 0));
    const vt = self.sp.deref(&self.r.abstract_pool, self.ty(self.r.tree.arg(n, 0)));
    if (k == .labelarrow) {
        self.bind_label(self.r.tree.arg(n, 1), v);
        return v;
    }
    if (self.sp.tag(vt) != .variant_type) return .none;
    const case = self.sp.get(vt).variant_type.cases[self.payload_case(vt)];
    const test_ = self.is_case(v, vt, case);
    if (k == .selftag_arrow) {
        self.bind_label(self.r.tree.arg(n, 1), self.payload(v, case));
        return test_;
    }
    const ok = self.block();
    const bad = self.block();
    self.cond(test_, ok, bad);
    if (k == .selftag_unwrap) {
        self.goto(bad);
        _ = self.emit(.@"unreachable", .unit_type, 0, 0);
        self.goto(ok);
        return self.payload(v, case);
    }
    const res = self.temp(t);
    const m = self.block();
    self.goto(ok);
    self.write(res, self.cur, self.coerce(self.payload(v, case), control.payload_of(self.r, vt), t));
    self.br(m);
    self.goto(bad);
    self.arm(self.r.tree.arg(n, 1), t, res, m);
    self.goto(m);
    return if (self.dead) .none else self.read(res, self.cur);
}

fn loop(self: *HighLowerer, n: NodeId) Ref {
    if (self.dead) return .none;
    const k = self.r.tree.kind(n);
    const a0 = self.r.tree.arg(n, 0);
    const a1 = self.r.tree.arg(n, 1);
    const t = self.ty(n);
    var out: Ref = if (self.sp.get(t) == .array_type and self.sp.tag(self.sp.get(t).array_type.len) == .int_value) self.alloca(t) else .none;
    const cap: u64 = if (out != .none) self.sp.get(self.sp.get(t).array_type.len).int.bits else 0;
    const dyn = self.is_dyn(t);
    const count = self.temp(.u64_type);
    self.write(count, self.cur, self.int(.u64_type, 0));
    const head = self.block();
    const body_b = self.block();
    const cont = self.block();
    const exit = self.block();
    var body: NodeId = undefined;
    var repeat: NodeId = 0;
    var step: ?struct { v: u32, ty: Index } = null;
    var each: struct { decl: DeclPool.Index = .none, base: Ref = .none, ty: Index = .none } = .{};
    switch (k) {
        .@"while", .stcwhile, .while_with_repeat_stmt, .stcwhile_with_repeat_stmt => {
            const w = if (k == .@"while" or k == .stcwhile) n else a0;
            if (w != n) repeat = a1;
            body = self.r.tree.arg(w, 1);
            self.br(head);
            self.enter(head);
            self.cond(self.expr_to(self.r.tree.arg(w, 0), .bool_type), body_b, exit);
        },
        .loop, .stcloop, .loop_with_repeat_stmt, .stcloop_with_repeat_stmt => {
            body = if (k == .loop or k == .stcloop) a0 else a1;
            self.br(head);
            self.enter(head);
            if (k == .loop_with_repeat_stmt or k == .stcloop_with_repeat_stmt) _ = self.expr(a0);
            self.br(body_b);
        },
        else => {
            const has_var = k == .for_var_in_seq or k == .stcfor_var_in_seq;
            const f = if (has_var) a0 else n;
            const seq = self.r.tree.arg(f, 0);
            body = self.r.tree.arg(f, 1);
            each.decl = self.decl(if (has_var) a1 else f);
            const sk = self.r.tree.kind(seq);
            const st = self.ty(seq);
            const range = switch (sk) {
                .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound_incl, .gen_upperbound_excl => true,
                else => false,
            };
            if (range) {
                const et = self.sp.get(st).array_type.elem;
                const has_lo = sk == .gen_incl or sk == .gen_excl or sk == .gen_lowerbound;
                const i = self.temp(et);
                self.write(i, self.cur, if (has_lo) self.expr_to(self.r.tree.arg(seq, 0), et) else self.int(et, 0));
                const hi: Ref = if (sk == .gen_lowerbound) .none else self.expr_to(self.r.tree.arg(seq, if (has_lo) 1 else 0), et);
                if (dyn and hi != .none) {
                    const lo = self.read(i, self.cur);
                    var span = self.e2(.sub, et, hi, lo);
                    if (sk == .gen_incl or sk == .gen_upperbound_incl) span = self.e2(.add, et, span, self.int(et, 1));
                    out = self.e2(.alloca, self.ptr(self.sp.get(t).array_type.elem), self.to_u64(span, et), .none);
                }
                self.br(head);
                self.enter(head);
                const iv = self.read(i, self.cur);
                if (hi != .none) self.cond(self.e2(if (sk == .gen_incl or sk == .gen_upperbound_incl) .le else .lt, .bool_type, iv, hi), body_b, exit) else self.br(body_b);
                step = .{ .v = i, .ty = et };
            } else if (self.sp.get(self.deref_ty(st)) == .array_type) {
                const at = self.deref_ty(st);
                const et = self.sp.get(at).array_type.elem;
                const base = if (self.is_ptr(st) or self.is_dyn(st)) self.expr(seq) else self.place(seq);
                const len_v = self.sp.get(at).array_type.len;
                const len: Ref = if (self.sp.tag(len_v) == .int_value) self.int(.u64_type, self.sp.get(len_v).int.bits) else self.e2(.len, .u64_type, base, .none);
                const i = self.temp(.u64_type);
                self.write(i, self.cur, self.int(.u64_type, 0));
                if (dyn) out = self.e2(.alloca, self.ptr(self.sp.get(t).array_type.elem), len, .none);
                self.br(head);
                self.enter(head);
                const iv = self.read(i, self.cur);
                self.cond(self.e2(.lt, .bool_type, iv, len), body_b, exit);
                each.base = base;
                each.ty = et;
                step = .{ .v = i, .ty = .u64_type };
            } else {
                const recv = if (self.is_ptr(st)) self.expr(seq) else self.place(seq);
                const rt = self.sp.deref(&self.r.abstract_pool, st);
                self.br(head);
                self.enter(head);
                self.cond(self.method_call(rt, .has_next, recv), body_b, exit);
                each.base = recv;
                each.ty = rt;
            }
        },
    }
    self.goto(body_b);
    if (each.decl != .none) self.declare_var(each.decl, if (step == null) self.method_call(each.ty, .next, each.base) else if (each.base == .none) self.read(step.?.v, self.cur) else self.e2(.load, each.ty, self.e2(.index_ptr, self.ptr(each.ty), each.base, self.read(step.?.v, self.cur)), .none));
    self.loops.push(.{ .brk = exit, .cont = cont, .defers = self.defers.head });
    const x = self.expr(body);
    if (out != .none and !self.dead and has_value(self.ty(body))) {
        const c = self.read(count, self.cur);
        const et = self.sp.get(t).array_type.elem;
        _ = self.e2(.store, .unit_type, self.e2(.index_ptr, self.ptr(et), out, c), self.coerce(x, self.ty(body), et));
        const c1 = self.e2(.add, .u64_type, c, self.int(.u64_type, 1));
        self.write(count, self.cur, c1);
        if (!dyn) {
            const more = self.block();
            self.cond(self.e2(.lt, .bool_type, c1, self.int(.u64_type, cap)), more, exit);
            self.goto(more);
        }
    }
    self.loops.head -= 1;
    self.br(cont);
    self.goto(cont);
    if (repeat != 0) _ = self.expr(repeat);
    if (step) |s| self.write(s.v, self.cur, self.e2(.add, s.ty, self.read(s.v, self.cur), self.int(s.ty, 1)));
    self.br(head);
    self.seal(head);
    self.goto(exit);
    if (dyn and out != .none) return self.emit(.dyn, t, @intFromEnum(out), self.list(&.{ @intFromEnum(self.int(.u64_type, 0)), @intFromEnum(self.read(count, self.cur)) }));
    return if (out != .none) self.e2(.load, t, out, .none) else unit();
}

fn advance(self: *HighLowerer, t: Index, base: Ref, sub: bool, x: Ref) Ref {
    const wide = if (self.ref_ty(x) == .i64_type or self.ref_ty(x) == .u64_type) x else self.emit(.cast, .i64_type, @intFromEnum(x), @intFromEnum(StaticPool.CastKind.int_resize));
    return self.e2(.index_ptr, t, base, if (sub) self.e2(.neg, self.ref_ty(wide), wide, .none) else wide);
}

fn shrink(self: *HighLowerer, n: NodeId) Ref {
    const t = self.ty(n);
    const a0 = self.r.tree.arg(n, 0);
    const at = self.sp.pointee(t);
    const g = syntax.narrowed(self.r.tree, self.r.tree.arg(n, 1));
    const lo = if (g != 0) self.static_of(g) else null;
    const base = if (self.is_ptr(self.ty(a0))) self.expr(a0) else self.place(a0);
    const mutable = !self.is_ptr(self.ty(a0)) or self.sp.get(self.ty(a0)).ptr_type.mutable;
    const at_ptr = if (self.is_ptr(t)) t else self.sp.intern(.{ .ptr_type = .{ .child = at, .mutable = mutable } });
    const first = self.e2(.index_ptr, self.sp.intern(.{ .ptr_type = .{ .child = self.sp.get(at).array_type.elem, .mutable = mutable } }), base, self.int(.u64_type, if (lo) |v| self.sp.get(v).int.bits else 0));
    const p = self.emit(.cast, at_ptr, @intFromEnum(first), @intFromEnum(StaticPool.CastKind.pointer_relength));
    return if (self.is_ptr(t)) p else self.e2(.load, t, p, .none);
}

fn to_u64(self: *HighLowerer, x: Ref, t: Index) Ref {
    return if (t == .u64_type) x else self.emit(.cast, .u64_type, @intFromEnum(x), @intFromEnum(StaticPool.CastKind.int_resize));
}

fn method_call(self: *HighLowerer, t: Index, name: NamePool.Index, recv: Ref) Ref {
    return switch (self.sp.lookup_member(t, name)) {
        .method => |m| self.emit(.call, self.fn_ret(m), @intFromEnum(self.fn_value(m)), self.list(&.{@intFromEnum(recv)})),
        else => .none,
    };
}

fn fn_ret(self: *HighLowerer, d: DeclPool.Index) Index {
    const ft = self.apply(self.r.decl_pool.tys()[@intFromEnum(decls.real(self.r, d))]);
    return if (ft != .none and self.sp.tag(ft) == .function_type) self.sp.get(ft).function_type.ret else .unit_type;
}

fn call(self: *HighLowerer, n: NodeId) Ref {
    const t = self.ty(n);
    const callee = self.r.tree.arg(n, 0);
    const args = self.r.tree.manychildren(self.r.tree.arg(n, 1));
    if (self.realized(n)) |f| return self.fn_value(f);
    const d = self.decl(n);
    if (d != .none and self.r.decl_pool.kinds()[@intFromEnum(d)].is_fn()) return self.direct(d, callee, args, t);
    if (d == .none and self.r.tree.kind(callee) == .member) switch (calls.builtin_of(self.r, callee, self.ty(self.r.tree.arg(callee, 0)), t)) {
        .builtin_init => return self.default_value(t),
        .builtin_deinit => return unit(),
        else => {},
    };
    const ct = self.ty(callee);
    if (self.sp.tag(ct) == .meta_type or self.sp.tag(ct) == .variant_case_type) return self.construct(t, args);
    const f = self.expr(callee);
    const ft = self.sp.get(ct).function_type;
    const mark = self.tmp.head;
    for (args, 0..) |a, i| {
        const x = self.expr_to(syntax.arg_value(self.r.tree, a), self.sp.get(ct).function_type.params[i]);
        self.tmp.push(@intFromEnum(x));
    }
    _ = ft;
    const at = self.list(self.tmp.buf[mark..self.tmp.head]);
    self.tmp.head = mark;
    return self.emit(.call, t, @intFromEnum(f), at);
}

// a stcfun call producing a function stands for its realization
fn realized(self: *HighLowerer, n: NodeId) ?DeclPool.Index {
    if (self.r.tree.kind(n) != .fun_call) return null;
    const g = self.decl(self.r.tree.arg(n, 0));
    return if (g != .none and self.r.decl_pool.kinds()[@intFromEnum(g)] == .static_function and self.decl(n) != .none) self.decl(n) else null;
}

fn direct(self: *HighLowerer, d: DeclPool.Index, callee: NodeId, all: []const NodeId, t: Index) Ref {
    const rd = decls.real(self.r, d);
    const f = self.func(rd);
    const fv = Ref.of(self.sp.intern(.{ .function = self.ir.functions.pool.decl.buf[f] }));
    const ft = self.apply(self.r.decl_pool.tys()[@intFromEnum(rd)]);
    const off = self.r.decl_pool.self_off(rd);
    const pnodes = syntax.params_of(self.r.tree, decls.value_node(self.r, rd));
    const mark = self.tmp.head;
    for (self.captures(self.ir.functions.pool.decl.buf[f])) |c| {
        const x = if (self.by_ref(c)) self.slots.get(c) orelse .none else self.load_var(c);
        self.tmp.push(@intFromEnum(x));
    }
    var args = all;
    var dynamic = false;
    if (off == 1) {
        const bound = self.r.tree.kind(callee) == .member and self.sp.tag(self.ty(self.r.tree.arg(callee, 0))) != .meta_type;
        const recv = if (bound) self.r.tree.arg(callee, 0) else syntax.arg_value(self.r.tree, args[0]);
        const x = if (!bound) self.expr_to(recv, self.sp.get(ft).function_type.params[0]) else if (self.is_ptr(self.ty(recv))) self.expr(recv) else self.place(recv);
        self.tmp.push(@intFromEnum(x));
        if (!bound) args = args[1..];
        dynamic = self.r.decl_pool.kinds()[@intFromEnum(rd)] == .trait_member and self.sp.tag(self.sp.deref(&self.r.abstract_pool, self.ty(recv))) == .trait_type;
    }
    const at = self.tmp.head;
    for (pnodes) |_| self.tmp.push(none);
    for (args, 0..) |a, i| {
        var j = i;
        if (self.r.tree.kind(a) == .partial__fun_call_assigned_param) {
            const name = self.r.name_pool.name_of(self.r.tree, self.r.src_bytes, self.r.tree.arg(a, 0));
            for (pnodes, 0..) |pn, q| if (decls.param_name(self.r, pn, q) == name) {
                j = q;
            };
        }
        const x = self.expr_to(syntax.arg_value(self.r.tree, a), self.sp.get(ft).function_type.params[j + off]);
        self.tmp.buf[at + j] = @intFromEnum(x);
    }
    const saved = self.body;
    if (self.r.bodies.get(rd)) |b| self.body = b;
    for (pnodes, 0..) |pn, j| if (self.tmp.buf[at + j] != none) self.declare_var(self.decl(pn), @enumFromInt(self.tmp.buf[at + j]));
    for (pnodes, 0..) |pn, j| if (self.tmp.buf[at + j] == none) {
        const dflt = syntax.Param.from_node(self.r.tree, pn).default;
        const x = if (dflt != 0) self.expr_to(dflt, self.sp.get(ft).function_type.params[j + off]) else Ref.none;
        self.declare_var(self.decl(pn), x);
        self.tmp.buf[at + j] = @intFromEnum(x);
    };
    self.body = saved;
    const list_at = self.list(self.tmp.buf[mark..self.tmp.head]);
    self.tmp.head = mark;
    return self.emit(if (dynamic) .call_dyn else .call, if (t == .none) self.fn_ret(rd) else t, @intFromEnum(fv), list_at);
}

fn construct(self: *HighLowerer, target: Index, args: []const NodeId) Ref {
    const sp = self.sp;
    const is_c = sp.tag(target) == .variant_case_type;
    const variant = if (is_c) sp.get(target).variant_case_type.variant else target;
    const rec = if (is_c) sp.get(target).variant_case_type.payload else target;
    const case: u32 = if (is_c) sp.get(target).variant_case_type.case else 0;
    if (rec == .none) return self.emit(.variant_make, variant, case, @intFromEnum(Ref.none));
    const fields = types.fields_of(self.r, rec);
    const mark = self.tmp.head;
    for (fields) |_| self.tmp.push(none);
    for (args, 0..) |a, i| {
        const fi = self.field_index(rec, a, i);
        const x = self.expr_to(syntax.arg_value(self.r.tree, a), sp.get(rec).custom_type.field_types[fi]);
        self.tmp.buf[mark + fi] = @intFromEnum(x);
    }
    self.complete(rec, mark);
    const at = self.list(self.tmp.buf[mark..self.tmp.head]);
    self.tmp.head = mark;
    const agg = self.emit(.aggregate, rec, 0, at);
    return if (is_c) self.emit(.variant_make, variant, case, @intFromEnum(agg)) else agg;
}

fn with(self: *HighLowerer, n: NodeId) Ref {
    var bt = self.ty(self.r.tree.arg(n, 0));
    var base = self.expr(self.r.tree.arg(n, 0));
    if (self.is_ptr(bt)) {
        base = self.e2(.load, self.child(bt), base, .none);
        bt = self.child(bt);
    }
    const ft = self.sp.get(bt).custom_type.field_types;
    const mark = self.tmp.head;
    for (0..ft.len) |i| {
        const x = self.emit(.extract, self.sp.get(bt).custom_type.field_types[i], @intFromEnum(base), @intCast(i));
        self.tmp.push(@intFromEnum(x));
    }
    for (self.r.tree.manychildren(self.r.tree.arg(n, 1)), 0..) |a, i| {
        const fi = self.field_index(bt, a, i);
        const x = self.expr_to(syntax.arg_value(self.r.tree, a), self.sp.get(bt).custom_type.field_types[fi]);
        self.tmp.buf[mark + fi] = @intFromEnum(x);
    }
    self.complete(bt, mark);
    const at = self.list(self.tmp.buf[mark..self.tmp.head]);
    self.tmp.head = mark;
    return self.emit(.aggregate, bt, 0, at);
}

// the defaults and `where .. else` of the fields in tmp[mark..], the fields are the locals of the type's body
fn complete(self: *HighLowerer, rec: Index, mark: u32) void {
    const fields = types.fields_of(self.r, rec);
    const saved = self.body;
    defer self.body = saved;
    const bi = self.r.bodies.get(self.sp.get(rec).custom_type.decl);
    if (bi) |b| self.body = b;
    // only the fields a default or guard reads, or a guard repairs, become locals
    var locals: u64 = 0;
    var guarded: u64 = 0;
    if (bi != null) for (fields, 0..) |f, i| {
        const p = syntax.Param.from_node(self.r.tree, f);
        if (p.@"else" != 0) guarded |= @as(u64, 1) << @intCast(i);
        for ([_]NodeId{ if (self.tmp.buf[mark + i] == none) p.default else 0, if (p.@"else" != 0) p.where else 0, p.@"else" }) |x| if (x != 0) {
            const sub = self.r.tree.subtree(x);
            for (sub[0]..sub[1]) |n| {
                const d = @intFromEnum(self.decl(@intCast(n))) -% self.body.first;
                if (self.r.tree.kind(@intCast(n)) == .identifier and d < fields.len) locals |= @as(u64, 1) << @intCast(d);
            }
        };
    };
    locals |= guarded;
    for (0..fields.len) |i| if (locals >> @intCast(i) & 1 != 0 and self.tmp.buf[mark + i] != none) self.declare_var(@enumFromInt(self.body.first + i), @enumFromInt(self.tmp.buf[mark + i]));
    for (fields, 0..) |f, i| if (self.tmp.buf[mark + i] == none) {
        const t = self.sp.get(rec).custom_type.field_types[i];
        const x = if (syntax.Param.from_node(self.r.tree, f).default != 0) self.expr_to(syntax.Param.from_node(self.r.tree, f).default, t) else self.emit(.zeroed, t, 0, 0);
        self.tmp.buf[mark + i] = @intFromEnum(x);
        if (locals >> @intCast(i) & 1 != 0) self.declare_var(@enumFromInt(self.body.first + i), x);
    };
    for (fields, 0..) |f, i| if (guarded >> @intCast(i) & 1 != 0) {
        const p = syntax.Param.from_node(self.r.tree, f);
        if (p.where == 0) continue;
        const ok = self.block();
        const els = self.block();
        self.cond(self.expr_to(p.where, .bool_type), ok, els);
        self.goto(els);
        if (self.r.tree.kind(p.@"else") == .assign) _ = self.expr(p.@"else") else self.store_var(@enumFromInt(self.body.first + i), self.expr_to(p.@"else", self.sp.get(rec).custom_type.field_types[i]));
        self.br(ok);
        self.goto(ok);
    };
    for (0..fields.len) |i| if (guarded >> @intCast(i) & 1 != 0) {
        self.tmp.buf[mark + i] = @intFromEnum(self.load_var(@enumFromInt(self.body.first + i)));
    };
}

fn member(self: *HighLowerer, n: NodeId) Ref {
    const parent = self.r.tree.arg(n, 0);
    const pt = self.ty(parent);
    const name = self.r.name_pool.name_of(self.r.tree, self.r.src_bytes, self.r.tree.arg(n, 1));
    const base_t = if (self.sp.tag(pt) == .meta_type) (self.static_of(parent) orelse return .none) else self.sp.deref(&self.r.abstract_pool, pt);
    return switch (self.sp.lookup_member(base_t, name)) {
        .field => |f| if (self.is_ptr(pt) or self.is_place(parent)) self.e2(.load, f.ty, self.place(n), .none) else self.emit(.extract, f.ty, @intFromEnum(self.expr(parent)), f.index),
        .case => |c| self.construct(c, &.{}),
        .method => |m| self.fn_value(m),
        .trait_method => |m| self.fn_value(@enumFromInt(@intFromEnum(self.sp.get(m.trait).trait_type.decl) + 1 + m.index)),
        .builtin_len => blk: {
            const at = self.deref_ty(pt);
            const len = self.sp.get(at).array_type.len;
            break :blk if (self.sp.tag(len) == .int_value) self.int(.u64_type, self.sp.get(len).int.bits) else self.e2(.len, .u64_type, if (self.is_ptr(pt) or self.is_dyn(pt)) self.expr(parent) else self.place(parent), .none);
        },
        .builtin_tag => if (self.sp.tag(base_t) == .variant_case_type) self.tag_of(base_t, base_t) else self.e2(.variant_tag, self.sp.tag_type_of(base_t), if (self.is_ptr(pt)) self.e2(.load, base_t, self.expr(parent), .none) else self.expr(parent), .none),
        else => .none,
    };
}

fn is_place(self: *HighLowerer, n: NodeId) bool {
    return switch (self.r.tree.kind(n)) {
        .capture => self.is_place(self.r.tree.arg(n, 0)),
        .identifier, .identifier_self => self.global_of.contains(self.decl(n)) or self.slots.contains(self.decl(n)),
        .member => self.is_ptr(self.ty(self.r.tree.arg(n, 0))) or self.is_place(self.r.tree.arg(n, 0)),
        .array_index, .dereference => true,
        else => false,
    };
}

fn place(self: *HighLowerer, n: NodeId) Ref {
    const t = self.ty(n);
    switch (self.r.tree.kind(n)) {
        .capture => return self.place(self.r.tree.arg(n, 0)),
        .identifier, .identifier_self => {
            const d = self.decl(n);
            if (self.global_of.get(d)) |g| return Ref.global(g);
            if (self.slots.get(d)) |s| return s;
        },
        .member => {
            const parent = self.r.tree.arg(n, 0);
            const pt = self.ty(parent);
            const base = if (self.is_ptr(pt)) self.expr(parent) else self.place(parent);
            switch (self.sp.lookup_member(self.sp.deref(&self.r.abstract_pool, pt), self.r.name_pool.name_of(self.r.tree, self.r.src_bytes, self.r.tree.arg(n, 1)))) {
                .field => |f| return self.emit(.field_ptr, self.ptr(f.ty), @intFromEnum(base), f.index),
                else => {},
            }
        },
        .array_index => {
            const ix = self.r.tree.arg(n, 0);
            const it = self.ty(ix);
            const base = if (self.is_ptr(it) or self.is_dyn(it)) self.expr(ix) else self.place(ix);
            return self.e2(.index_ptr, self.ptr(t), base, self.expr(self.r.tree.arg(n, 1)));
        },
        .dereference => return self.expr(self.r.tree.arg(n, 0)),
        else => {},
    }
    const x = self.expr(n);
    const s = self.alloca(t);
    _ = self.e2(.store, .unit_type, s, x);
    return s;
}
