const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const ParseTree = @import("ParseTree.zig");

const NamePool = @import("resolver/NamePool.zig");
const StaticPool = @import("resolver/StaticPool.zig");
const Doctor = @import("resolver/Doctor.zig");
const Interpreter = @import("resolver/Interpreter.zig");
const AbstractPool = @import("resolver/AbstractPool.zig");

const Resolver = @This();
const NodeId = ParseTree.NodeId;
const NodeKind = ParseTree.Node.Kind;

// the resolver answers two questions for every ast node:
//   1. which declaration does this identifier mean?   -> node_decl
//   2. what type does this expression have?           -> node_type
//
// how it works:
//   - one recursive walk per declaration body does everything at once: scoping, name lookup,
//     type checking + inference, mutability, loop context, runit. every node is visited about
//     once while its data is still in cache.
//   - global declarations are resolved lazily: when a body uses a global that is not resolved
//     yet, it is resolved right there and memoized. a state per declaration detects real cycles.
//   - types never have to be written: most are known on the spot (the value's type), and where
//     they are not (induced return types in recursion, `x = []`), a type var stands in and is
//     filled by unification later (see type_system.zig, section 4). one final sweep replaces
//     every var by its result, and is skipped entirely when no var was ever created.
//   - nothing the parse tree already has is copied (defaults, where-clauses, field names are
//     read from the tree when needed). side tables only hold what is computed.
//
// future:
//   - multithreading: bodies are independent once signatures are ready - check them on worker
//     threads with their own type vars and diagnostics, decl states become atomics
//   - incremental: hash every top-level declaration's tokens, reuse results of unchanged ones

// one row per declaration: globals, locals, params, fields, binders.
// stored as struct-of-arrays, so every access pattern touches only the columns it needs:
// looking a name up reads `name` only, checking a use reads `kind`, `flags`, `ty`.
pub const Decl = struct {
    name: NamePool.Index,
    node: ParseTree.NodeId,
    kind: Kind,
    flags: Flags,
    state: State,
    ty: StaticPool.Index,
    value: StaticPool.Index,
    next_overload: Index,

    pub const Kind = enum(u8) {
        variable,
        parameter,
        static_parameter,
        field,
        function,
        static_function,
        inlined_function,
        type_alias,
        record,
        variant,
        variant_case,
        trait,
        trait_member,
        pattern_binder,
        arrow_binder,
        loop_variable,
        self,
        autoins_arg,
        autoins_it,
    };

    pub const Flags = packed struct(u8) {
        is_pub: bool = false,
        is_mut: bool = false,
        is_stc: bool = false,
        is_global: bool = false,
        _pad: u4 = 0,
    };

    //   unresolved -> resolving_signature -> signature_ready -> checking_body -> done   (or failed)
    // signature_ready is published before the body is checked, so a function can call itself or a
    // mutually recursive partner: an induced return type is a type var until the bodies fix it.
    // meeting a declaration in resolving_signature again is a real cycle (a type containing itself
    // by value, a static value defined through itself) and an error.
    pub const State = enum(u8) {
        unresolved,
        resolving_signature,
        signature_ready,
        checking_body,
        done,
        failed,
    };

    pub const Index = enum(u32) { none = std.math.maxInt(u32), _ };
};

// per-body state that would otherwise be globals. lives on the machine stack while a body is
// checked and is passed down by pointer - no table, no allocation.
// ret_type is a type var for induced return types; every `ret` unifies with it.
pub const FnCtx = struct {
    decl: Decl.Index,
    ret_type: StaticPool.Index,
    self_type: StaticPool.Index,
    loop_depth: u16,
    in_static: bool,
};

alloc: std.mem.Allocator,
tree: *ParseTree,
src_bytes: []const u8,
// emitted by `Parser`
roots: []const ParseTree.NodeId,

// identifier string -> NamePool.Index. names are interned when a node is resolved (visited)
name_pool: NamePool,

// where every static (non-runtime) value (from integer values to types) is stored.
static_pool: StaticPool,

// placeholders for types not known yet and what they turned out to be. see type_system.zig.
abstract_pool: AbstractPool,

// ALL declarations
decls: SoD(Decl),

// the two results, one slot per parse tree node, indexed by ParseTree.NodeId.
// plain arrays of u32: 8 bytes per node in total, and the lowerer reads them with no indirection.
node_type: []StaticPool.Index,
node_decl: []Decl.Index,

// global names -> first declaration with that name
// - overloads of the same name handled by `decls.next_overload` for single per-name entry
// - solves: using global before declaring it in a file
globals: std.AutoHashMapUnmanaged(NamePool.Index, Decl.Index),

// the local scope stack. declaring a local pushes (name, decl); a lookup scans `local_names`
// backwards, so the innermost declaration wins and shadowing works for free.
// names and decls are two parallel arrays so the scan reads only a dense run of u32 names -
// for the few dozen locals a body has, that beats any hash map and vectorizes well.
local_names: DynBuf(NamePool.Index),
local_decls: DynBuf(Decl.Index),
// where each open scope starts in the local stack. leaving a scope just truncates the stack
// back to its mark - freeing all its locals at once costs one store.
local_scope_marks: DynBuf(u32),

// stores which nodes have something to report (e.g. warning or error)
// - a single report does not stop resolving
doc: Doctor,

// "static" (compiletime) evaluation of what's static
interpreter: Interpreter,

pub inline fn init(alloc: std.mem.Allocator, tree: *ParseTree, src_bytes: []const u8, roots: []const ParseTree.NodeId) Resolver {
    return Resolver{
        .alloc = alloc,
        .tree = tree,
        .src_bytes = src_bytes,
        .roots = roots,
        .name_pool = .init(alloc),
        .static_pool = .init(alloc),
        .abstract_pool = .init(alloc),
        .decls = .init(alloc, 4096),
        .node_type = alloc.alloc(StaticPool.Index, tree.ast_nodes.len()) catch @panic("OOM"),
        .node_decl = alloc.alloc(Decl.Index, tree.ast_nodes.len()) catch @panic("OOM"),
        .globals = .empty,
        .local_names = .init(alloc, 256),
        .local_decls = .init(alloc, 256),
        .local_scope_marks = .init(alloc, 16),
        .doc = .{ .diagnostics = .init(alloc, 16) },
        .interpreter = .{ .step_budget = 1_000_000 },
    };
}

pub inline fn deinit(self: *Resolver) void {
    self.name_pool.deinit();
    self.static_pool.deinit();
    self.abstract_pool.deinit();
    self.decls.deinit();
    self.alloc.free(self.node_type);
    self.alloc.free(self.node_decl);
    self.globals.deinit(self.alloc);
    self.local_names.deinit();
    self.local_decls.deinit();
    self.local_scope_marks.deinit();
    self.doc.diagnostics.deinit();
}

pub inline fn resolve(self: *Resolver) !void {
    self.s1_collect_globals();
    try self.gate();

    self.s2_check_globals();
    try self.gate();

    self.s3_apply_inferred_types();
    try self.gate();

    self.s4_check_entry_point();
    try self.gate();
}

inline fn gate(self: *Resolver) !void {
    if (self.doc.diagnostics.len() > 0) return error.ResolveFailed;
}

fn s1_collect_globals(self: *Resolver) void {
    @memset(self.node_type, .none);
    @memset(self.node_decl, .none);
    for ([_][]const u8{ "", "_", "$it", "self", "init", "deinit", "main", "len" }) |s| _ = self.name_pool.intern(s);
    for (self.roots) |root| {
        var flags = Decl.Flags{ .is_global = true };
        const n = self.unwrap_mods(root, &flags);
        const parts = self.stmt_parts(n);
        const kind = self.decl_kind(parts.type, parts.value);
        const declares = parts.type != 0 or @as(u8, @bitCast(flags)) != @as(u8, @bitCast(Decl.Flags{ .is_global = true })) or kind != .variable;
        for (parts.ids) |id| {
            const name = self.name_of(id);
            if (name == .none) continue;
            const gop = self.globals.getOrPut(self.alloc, name) catch @panic("OOM");
            if (gop.found_existing and !(is_fn(kind) and is_fn(self.dp(.kind, gop.value_ptr.*).*))) {
                if (declares) _ = self.report(.duplicate_declaration, id, name, gop.value_ptr.*);
                if (declares and self.node_decl[root] == .none) self.node_decl[root] = gop.value_ptr.*;
                continue;
            }
            const d = self.push_decl(name, n, kind, .none, flags);
            // overloads with a where clause come before the ones without, so every group of same-typed
            // overloads reads as a runtime dispatch: its where-clauses in order, the where-less fallback last
            if (gop.found_existing) {
                var at = gop.value_ptr;
                while (at.* != .none and (!self.has_where(d) or self.has_where(at.*))) at = self.dp(.next_overload, at.*);
                self.dp(.next_overload, d).* = at.*;
                at.* = d;
            } else gop.value_ptr.* = d;
            self.node_decl[id] = d;
            if (self.node_decl[root] == .none) self.node_decl[root] = d;
        }
    }
}

fn s2_check_globals(self: *Resolver) void {
    const count = self.decls.len();
    for (0..count) |i| {
        self.h05_ensure_signature(@enumFromInt(i));
        self.h06_check_body(@enumFromInt(i));
    }
    var ctx = FnCtx{ .decl = .none, .ret_type = .none, .self_type = .none, .loop_depth = 0, .in_static = false };
    for (self.roots) |root| if (self.node_decl[root] == .none) {
        _ = self.h09_check_expr(&ctx, root, .none);
    };
}

fn s3_apply_inferred_types(self: *Resolver) void {
    if (self.abstract_pool.count() == 0) return;
    const sp = &self.static_pool;
    for (self.node_type) |*t| if (t.* != .none and sp.has_vars(t.*)) {
        t.* = sp.apply_vars(&self.abstract_pool, t.*);
    };
    for (self.decls.sliced_field(.ty), 0..) |*t, i| if (t.* != .none and sp.has_vars(t.*)) {
        t.* = sp.apply_vars(&self.abstract_pool, t.*);
        if (self.open_type_var(t.*) and !self.length_generic(t.*)) _ = self.report(.uninferable_type, self.decls.pool.node.buf[i], t.*, .none);
    };
}

fn s4_check_entry_point(self: *Resolver) void {
    const main = self.globals.get(.main) orelse return Doctor.h21_report(self, .missing_main, 0, 0, 0);
    const node = self.dp(.node, main).*;
    if (self.dp(.next_overload, main).* != .none) return Doctor.h21_report(self, .duplicate_declaration, self.dp(.node, self.dp(.next_overload, main).*).*, @intFromEnum(NamePool.Index.main), @intFromEnum(main));
    const ty = self.dp(.ty, main).*;
    const sp = &self.static_pool;
    const ok = ty != .none and sp.tag(ty) == .function_type and blk: {
        const f = sp.get(ty).function_type;
        const args_ok = f.params.len == 0 or (f.params.len == 2 and sp.class(f.params[0]).is_integer and sp.class(f.params[1]).is_pointer);
        break :blk args_ok and (f.ret == .unit_type or f.ret == .runit_type or f.ret == .never_type or sp.class(f.ret).is_integer);
    };
    if (!ok) _ = self.report(.type_mismatch, node, ty, .none);
}

// ------------------------------------------------------------------------------------------ //
// scopes and names
// ------------------------------------------------------------------------------------------ //

fn h01_lookup(self: *Resolver, name: NamePool.Index) Decl.Index {
    const names = self.local_names.sliced();
    var i = names.len;
    while (i > 0) {
        i -= 1;
        if (names[i] == name) return self.local_decls.buf[i];
        if (names[i] == .none) break; // barrier: a declaration body never sees its user's locals
    }
    return self.globals.get(name) orelse .none;
}

fn h02_declare_local(self: *Resolver, name: NamePool.Index, node: ParseTree.NodeId, kind: Decl.Kind, ty: StaticPool.Index) Decl.Index {
    const d = self.push_decl(name, node, kind, ty, .{});
    self.local_names.push(name);
    self.local_decls.push(d);
    return d;
}

fn h03_push_scope(self: *Resolver) void {
    self.local_scope_marks.push(self.local_names.head);
}

fn h04_pop_scope(self: *Resolver) void {
    self.local_scope_marks.head -= 1;
    self.local_names.head = self.local_scope_marks.buf[self.local_scope_marks.head];
    self.local_decls.head = self.local_names.head;
}

// ------------------------------------------------------------------------------------------ //
// declarations
// ------------------------------------------------------------------------------------------ //

fn h05_ensure_signature(self: *Resolver, decl: Decl.Index) void {
    const state = self.dp(.state, decl);
    switch (state.*) {
        .unresolved => {},
        .resolving_signature => {
            _ = self.report(.declaration_cycle, self.dp(.node, decl).*, self.dp(.name, decl).*, 0);
            state.* = .failed;
            return;
        },
        else => return,
    }
    state.* = .resolving_signature;
    const sp = &self.static_pool;
    const kind = self.dp(.kind, decl).*;
    const flags = self.dp(.flags, decl).*;
    var ctx = FnCtx{ .decl = decl, .ret_type = .none, .self_type = self.owner_of(decl), .loop_depth = 0, .in_static = flags.is_stc };
    const v = self.value_node(decl);
    self.open_scope(flags.is_global, if (self.self_off(decl) == 1) ctx.self_type else .none, v);
    switch (kind) {
        .function, .static_function, .inlined_function, .trait_member => if (self.nk(v) == .def_fun or self.nk(v) == .def_fun_declaration) {
            // stcfun: the first tuple is static, whatever the body produces is the result (a second tuple belongs to the produced function)
            const ret: StaticPool.Index = if (kind == .static_function) switch (self.nk(self.core(self.arg(v, 1)))) {
                .def_type, .def_type_packed => .type_type,
                .def_variant, .def_variant_unionsized => .variant_type,
                .def_trait, .def_trait_implof => .trait_type,
                .def_fun, .def_fun_declaration => .fun_type,
                else => .poison_type,
            } else if (self.nk(v) == .def_fun_declaration or self.nk(self.arg(v, 0)) == .partial__fun_def_header_ret) .unit_type else self.fresh_var(v);
            const category: StaticPool.FunType.Category = switch (kind) {
                .static_function => .static,
                .inlined_function => .inlined,
                else => .default,
            };
            // a method's first parameter is the induced `*Self`, `init` constructs and has none
            self.dp(.ty, decl).* = self.fun_type(&ctx, v, category, ret, if (self.self_off(decl) == 1) self.self_ptr(ctx.self_type) else .none);
            self.dp(.value, decl).* = if (kind == .static_function)
                sp.intern(.{ .static_fun = .{ .decl = decl, .result_kind = if (sp.tag(ret) == .meta_type) sp.get(ret).meta_type else .stcfun } })
            else
                sp.intern(.{ .function = decl });
        } else {
            // a function produced by a static expression (`fun sub_from_templ = my_templ(i32, false)`)
            const fv = self.h08_eval_static(&ctx, v);
            if (sp.tag(fv) == .function_value) {
                self.dp(.value, decl).* = fv;
                self.dp(.ty, decl).* = self.dp(.ty, sp.get(fv).function).*;
            } else if (fv != .poison_type) _ = self.report(.type_mismatch, v, sp.type_of(fv), .fun_type);
        },
        .record, .variant, .trait => _ = self.h19_check_type_def(&ctx, decl, v),
        .type_alias => {
            const t = self.h07_lower_type(&ctx, v);
            self.dp(.value, decl).* = t;
            self.dp(.ty, decl).* = sp.type_of(t);
        },
        else => _ = self.h11_check_assign(&ctx, self.dp(.node, decl).*),
    }
    self.h04_pop_scope();
    if (self.dp(.state, decl).* == .resolving_signature) self.dp(.state, decl).* = .signature_ready;
}

fn h06_check_body(self: *Resolver, decl: Decl.Index) void {
    const state = self.dp(.state, decl);
    if (state.* != .signature_ready) return;
    const sp = &self.static_pool;
    const kind = self.dp(.kind, decl).*;
    const v = self.value_node(decl);
    const ty = self.dp(.ty, decl).*;
    // stcfun bodies are checked per realization, length-generic ones per length (h20); `main` is realized once, by the runtime
    // LIMITATION: `main` is the only function whose unlengthed parameters are runtime slices instead of per-length realizations
    const generic = self.length_generic(ty) and self.dp(.name, decl).* != .main;
    if (kind == .static_function or !is_fn(kind) or self.nk(v) != .def_fun or generic) {
        state.* = .done;
        return;
    }
    state.* = .checking_body;
    var ctx = FnCtx{ .decl = decl, .ret_type = sp.get(ty).function_type.ret, .self_type = self.owner_of(decl), .loop_depth = 0, .in_static = false };
    self.open_scope(self.dp(.flags, decl).is_global, if (self.self_off(decl) == 1) ctx.self_type else .none, v);
    const off = self.self_off(decl);
    // a where clause sees its own parameter and the ones before it
    for (self.params_of(v), 0..) |pn, i| {
        const p = self.param(pn);
        const pt = sp.get(ty).function_type.params[i + off];
        if (p.default != 0) _ = self.check(&ctx, p.default, pt);
        self.link(p.name, self.h02_declare_local(self.param_name(pn, i), pn, .parameter, pt), pt);
        if (p.where != 0) _ = self.check(&ctx, p.where, .bool_type);
        if (p.@"else" != 0) _ = if (self.nk(p.@"else") == .assign) self.h09_check_expr(&ctx, p.@"else", .none) else self.check(&ctx, p.@"else", pt);
    }
    const body = self.arg(v, 1);
    if (self.nk(body) == .block) {
        _ = self.h09_check_expr(&ctx, body, .none);
        // a `{}` body that never returns a value returns unit
        if (sp.tag(sp.apply_vars(&self.abstract_pool, ctx.ret_type)) == .type_var) _ = sp.unify(&self.abstract_pool, ctx.ret_type, .unit_type);
    } else _ = self.check(&ctx, body, ctx.ret_type);
    self.h04_pop_scope();
    self.dp(.state, decl).* = .done;
}

fn h07_lower_type(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const k = self.nk(node);
    if (@intFromEnum(k) >= @intFromEnum(NodeKind.type_u8) and @intFromEnum(k) <= @intFromEnum(NodeKind.type_bool))
        return @enumFromInt(@intFromEnum(k) - @intFromEnum(NodeKind.type_u8));
    return switch (k) {
        .type_unit => .unit_type,
        .type_type => .type_type,
        .type_trait => .trait_type,
        .type_variant => .variant_type,
        .type_fun => .fun_type,
        .type_stcfun => .stcfun_type,
        .type_inlfun => .inlfun_type,
        .capture => self.h07_lower_type(ctx, self.arg(node, 0)),
        .typeof => blk: {
            const t = self.h09_check_expr(ctx, self.arg(node, 0), .none);
            break :blk if (self.nk(self.arg(node, 0)) == .identifier_self and sp.get(t) == .ptr_type) sp.get(t).ptr_type.child else t;
        },
        .type_ptr, .type_ptrmut => sp.intern(.{ .ptr_type = .{ .child = self.h07_lower_type(ctx, self.arg(node, 0)), .mutable = k == .type_ptrmut } }),
        // an unlengthed array gets a var as its length: inferred from the value, or per call for parameters
        // LIMITATION: in a record field the var is bound by the first value stored, later lengths mismatch
        .type_array_unlengthed => sp.intern(.{ .array_type = .{ .len = self.fresh_var(node), .elem = self.h07_lower_type(ctx, self.arg(node, 0)) } }),
        .type_array => blk: {
            const len = self.h08_eval_static(ctx, self.arg(node, 0));
            const n = if (sp.tag(len) == .int_value) sp.intern(.{ .int = .{ .ty = .u64_type, .bits = sp.get(len).int.bits } }) else if (len == .poison_type) len else self.report(.not_static, self.arg(node, 0), len, 0);
            break :blk sp.intern(.{ .array_type = .{ .len = n, .elem = self.h07_lower_type(ctx, self.arg(node, 1)) } });
        },
        .def_fun_declaration => self.fun_type(ctx, node, .default, .unit_type, .none),
        else => blk: {
            const v = self.h08_eval_static(ctx, node);
            break :blk if (v == .poison_type or sp.class(v).is_type) v else self.report(.not_a_type, node, v, .none);
        },
    };
}

fn h08_eval_static(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    if (self.interpreter.step_budget == 0) return self.report(.static_eval_failed, node, 0, 0);
    self.interpreter.step_budget -= 1;
    const a0 = self.arg(node, 0);
    const a1 = self.arg(node, 1);
    const k = self.nk(node);
    return switch (k) {
        .int, .char, .float, .string, .boolean_true, .boolean_false => self.literal_value(node, false),
        .neg_num => if (self.is_literal(node)) self.literal_value(a0, true) else self.fold(node, .binary_sub, sp.intern(.{ .int = .{ .ty = .i64_type, .bits = 0 } }), self.h08_eval_static(ctx, a0)),
        .neg_logic => self.fold(node, .binary_eq, self.h08_eval_static(ctx, a0), .bool_false),
        .capture, .ret, .do => self.h08_eval_static(ctx, a0),
        .identifier, .identifier_self, .identifier_init, .identifier_deinit, .identifier_main => blk: {
            const d = self.h01_lookup(self.name_of(node));
            if (d == .none) break :blk self.report(.undefined_name, node, self.name_of(node), 0);
            self.node_decl[node] = d;
            self.h05_ensure_signature(d);
            const v = self.dp(.value, d).*;
            break :blk if (v != .none) v else if (self.dp(.state, d).* == .failed) .poison_type else self.report(.not_static, node, self.name_of(node), 0);
        },
        .member => blk: {
            const name = self.name_of(a1);
            if (name == .len) { // `arr.len` is static whenever the array length is
                var t = sp.apply_vars(&self.abstract_pool, self.h09_check_expr(ctx, a0, .none));
                if (sp.get(t) == .ptr_type) t = sp.get(t).ptr_type.child;
                if (sp.get(t) == .array_type and sp.tag(sp.get(t).array_type.len) == .int_value) break :blk sp.get(t).array_type.len;
            }
            const pv = self.h08_eval_static(ctx, a0);
            if (pv == .poison_type) break :blk pv;
            if (!sp.class(pv).is_type) break :blk self.report(.not_static, node, 0, 0);
            break :blk switch (sp.lookup_member(pv, name)) {
                .case => |c| c,
                .method => |m| mv: {
                    self.h05_ensure_signature(m);
                    break :mv self.dp(.value, m).*;
                },
                else => self.report(.unknown_member, node, name, pv),
            };
        },
        .sizeof => blk: {
            const t = self.h09_check_expr(ctx, a0, .none);
            const ty = if (sp.tag(t) == .meta_type) self.h08_eval_static(ctx, a0) else t;
            break :blk sp.intern(.{ .int = .{ .ty = .u64_type, .bits = sp.layout(ty).size } });
        },
        .unify_variants => blk: {
            var members: [64]StaticPool.Index = undefined;
            var n: usize = 0;
            for ([_]NodeId{ a0, a1 }) |side| {
                const t = self.h07_lower_type(ctx, side);
                if (sp.tag(t) == .variant_union_type) {
                    const m = sp.get(t).variant_union_type;
                    @memcpy(members[n..][0..m.len], m);
                    n += m.len;
                } else if (sp.tag(t) == .variant_type) {
                    members[n] = t;
                    n += 1;
                } else if (t != .poison_type) _ = self.report(.type_mismatch, side, t, .variant_type);
            }
            break :blk sp.intern(.{ .variant_union_type = members[0..n] });
        },
        .def_type, .def_type_packed, .def_type_assertsize, .def_type_implof, .def_variant, .def_variant_unionsized, .def_variant_tagof, .def_variant_assertsize, .def_variant_implof, .def_trait, .def_trait_implof => blk: {
            const d = self.push_decl(.empty, node, self.type_kind(node), .none, .{});
            self.node_decl[node] = d;
            break :blk self.h19_check_type_def(ctx, d, node);
        },
        .def_fun => blk: {
            _ = self.h09_check_expr(ctx, node, .none);
            break :blk self.dp(.value, self.node_decl[node]).*;
        },
        .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod, .binary_pow, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and, .binary_eq, .binary_neq, .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq, .binary_logic_or, .binary_logic_xor, .binary_logic_and => self.fold(node, k, self.h08_eval_static(ctx, a0), self.h08_eval_static(ctx, a1)),
        .oftype => blk: {
            const v = self.h08_eval_static(ctx, a0);
            const t = self.h07_lower_type(ctx, a1);
            const vt = if (sp.class(v).is_type) v else sp.type_of(v);
            break :blk if (vt == t or sp.type_of(v) == t or sp.implements(vt, t)) .bool_true else .bool_false;
        },
        .as => self.retype(self.h08_eval_static(ctx, a0), self.h07_lower_type(ctx, a1)),
        .fun_call => blk: {
            const cv = self.h08_eval_static(ctx, a0);
            if (sp.tag(cv) != .generic) break :blk if (cv == .poison_type) cv else self.report(.not_static, node, 0, 0);
            const args = self.kids(a1);
            const want = sp.get(self.dp(.ty, sp.get(cv).static_fun.decl).*).function_type.params.len;
            if (args.len != want) break :blk self.report(.wrong_arity, node, args.len, want);
            var vals: [64]StaticPool.Index = undefined;
            for (args, 0..) |a, i| vals[i] = self.h08_eval_static(ctx, self.arg_value(a));
            break :blk self.h20_instantiate(sp.get(cv).static_fun.decl, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = vals[0..args.len] } }));
        },
        .if_then, .stcif_then, .if_else, .stcif_else => blk: {
            const has_else = k == .if_else or k == .stcif_else;
            const it = if (has_else) a0 else node;
            const c = self.h08_eval_static(ctx, self.arg(it, 0));
            if (c == .bool_true) break :blk self.h08_eval_static(ctx, self.arg(it, 1));
            break :blk if (c != .bool_false) self.report(.type_mismatch, self.arg(it, 0), c, .bool_type) else if (has_else) self.h08_eval_static(ctx, a1) else .unit_value;
        },
        .match, .stcmatch => blk: {
            const v = self.h08_eval_static(ctx, a0);
            self.h03_push_scope();
            defer self.h04_pop_scope();
            for (self.kids(a1)) |arm| if (self.static_match(ctx, self.arg(arm, 0), v)) break :blk self.h08_eval_static(ctx, self.arg(arm, 1));
            break :blk self.report(.non_exhaustive_match, node, v, .none);
        },
        // LIMITATION: a static `ret` only ends the block it is directly in, not enclosing ones
        .block => blk: {
            self.h03_push_scope();
            defer self.h04_pop_scope();
            var v: StaticPool.Index = .unit_value;
            for (self.kids(node)) |s| {
                v = self.h08_eval_static(ctx, s);
                if (self.nk(s) == .ret or v == .poison_type) break;
            }
            break :blk v;
        },
        .def_var, .assign, .assign_typed, .mod_pub, .mod_mut, .mod_stc => blk: {
            _ = self.h11_check_assign(ctx, node);
            break :blk .unit_value;
        },
        .inc_prefix, .dec_prefix, .inc_postfix, .dec_postfix, .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod => blk: {
            // static locals keep their current value in the decl row
            const old = self.h08_eval_static(ctx, a0);
            const d = self.node_decl[a0];
            if (old == .poison_type or d == .none) break :blk old;
            const one = sp.intern(.{ .int = .{ .ty = .u64_type, .bits = 1 } });
            const op: NodeKind = switch (k) {
                .inc_prefix, .inc_postfix, .assign_add => .binary_add,
                .dec_prefix, .dec_postfix, .assign_sub => .binary_sub,
                .assign_mul => .binary_mul,
                .assign_div => .binary_div,
                else => .binary_mod,
            };
            const rhs = if (@intFromEnum(k) >= @intFromEnum(NodeKind.assign_add)) self.h08_eval_static(ctx, a1) else one;
            self.dp(.value, d).* = self.retype(self.fold(node, op, old, rhs), sp.type_of(old));
            break :blk if (k == .inc_postfix or k == .dec_postfix) old else self.dp(.value, d).*;
        },
        .array => blk: {
            var vals: [256]StaticPool.Index = undefined;
            const elems = self.kids(node);
            for (elems, 0..) |e, i| vals[i] = self.h08_eval_static(ctx, e);
            break :blk self.aggregate(vals[0..elems.len]);
        },
        .for_seq, .stcfor_seq, .for_var_in_seq, .stcfor_var_in_seq => blk: {
            const has_var = k == .for_var_in_seq or k == .stcfor_var_in_seq;
            const f = if (has_var) a0 else node;
            const seq = self.static_seq(ctx, self.arg(f, 0));
            if (seq == .poison_type) break :blk seq;
            self.h03_push_scope();
            defer self.h04_pop_scope();
            const it = self.h02_declare_local(if (has_var) self.name_of(a1) else .dollar_it, node, .loop_variable, .none);
            var vals: [256]StaticPool.Index = undefined;
            const n = sp.get(seq).aggregate.elems.len;
            for (0..n) |i| {
                self.dp(.value, it).* = sp.get(seq).aggregate.elems[i];
                vals[i] = self.h08_eval_static(ctx, self.arg(f, 1));
            }
            break :blk self.aggregate(vals[0..n]);
        },
        .@"while", .stcwhile => blk: {
            var vals: [256]StaticPool.Index = undefined;
            var n: usize = 0;
            while (n < vals.len) : (n += 1) {
                const c = self.h08_eval_static(ctx, a0);
                if (c != .bool_true) break;
                vals[n] = self.h08_eval_static(ctx, a1);
            }
            break :blk self.aggregate(vals[0..n]);
        },
        // LIMITATION: `loop` / `stcloop` and constructor calls are not interpreted statically
        else => if (is_type_expr(k)) self.h07_lower_type(ctx, node) else self.report(.not_static, node, 0, 0),
    };
}

// ------------------------------------------------------------------------------------------ //
// expressions
// ------------------------------------------------------------------------------------------ //

// LIMITATION: no definite-initialization check yet (`mut u64 x;` read before its first write)
fn h09_check_expr(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const ap = &self.abstract_pool;
    const a0 = self.arg(node, 0);
    const a1 = self.arg(node, 1);
    const k = self.nk(node);
    const t: StaticPool.Index = switch (k) {
        .int, .float, .char, .string, .boolean_true, .boolean_false => self.literal_type(node, expected),
        .identifier, .identifier_self, .identifier_init, .identifier_deinit, .identifier_main => blk: {
            const name = self.name_of(node);
            const d = self.h01_lookup(name);
            if (d == .none) break :blk self.report(.undefined_name, node, name, 0);
            self.node_decl[node] = d;
            self.h05_ensure_signature(d);
            const ty = self.dp(.ty, d).*;
            break :blk if (ty == .none) .poison_type else ty;
        },
        .capture => self.h09_check_expr(ctx, a0, expected),
        .block => blk: {
            self.h03_push_scope();
            defer self.h04_pop_scope();
            var last: StaticPool.Index = .unit_type;
            const stmts = self.kids(node);
            for (stmts, 0..) |s, i| last = self.h09_check_expr(ctx, s, if (i + 1 == stmts.len) expected else .none);
            break :blk last;
        },
        .def_var, .assign, .assign_typed, .mod_pub, .mod_mut, .mod_stc => self.h11_check_assign(ctx, node),
        .assign_add, .assign_sub, .assign_mul, .assign_div, .assign_mod => blk: {
            const lt = self.h18_check_place(ctx, a0);
            _ = self.check(ctx, a1, lt);
            break :blk self.numeric(node, lt, .unit_type);
        },
        .inc_prefix, .dec_prefix, .inc_postfix, .dec_postfix => blk: {
            const lt = self.h18_check_place(ctx, a0);
            break :blk self.numeric(node, lt, lt);
        },
        .binary_add, .binary_sub, .binary_mul, .binary_div, .binary_mod, .binary_pow, .binary_shift_left, .binary_shift_right, .binary_num_or, .binary_num_xor, .binary_num_and => blk: {
            const j = self.pair(ctx, node, a0, a1, if (self.is_numeric(expected)) expected else .none);
            break :blk self.numeric(node, j, j);
        },
        .binary_eq, .binary_neq, .binary_less, .binary_greater, .binary_less_eq, .binary_greater_eq => blk: {
            const j = self.pair(ctx, node, a0, a1, .none);
            break :blk if (j == .poison_type) j else .bool_type;
        },
        .binary_logic_or, .binary_logic_xor, .binary_logic_and => blk: {
            _ = self.check(ctx, a0, .bool_type);
            _ = self.check(ctx, a1, .bool_type);
            break :blk .bool_type;
        },
        .neg_logic => blk: { // `!` is logical on bools and bitwise on integers
            const st = self.h09_check_expr(ctx, a0, expected);
            break :blk if (st == .bool_type or st == .poison_type or sp.class(st).is_integer) st else self.report(.type_mismatch, node, st, .bool_type);
        },
        .neg_num => if (self.is_literal(node)) self.literal_type(node, expected) else self.numeric(node, self.h09_check_expr(ctx, a0, expected), .none),
        .fun_call, .with => self.h12_check_call(ctx, node, expected),
        .member => self.h13_check_member(ctx, node),
        .array_index => blk: {
            var st = sp.apply_vars(ap, self.h09_check_expr(ctx, a0, .none));
            const is_range = is_range_kind(self.nk(a1));
            const it = self.h09_check_expr(ctx, a1, .none);
            if (!is_range and it != .poison_type and !sp.class(it).is_integer) _ = self.report(.type_mismatch, a1, it, .u64_type);
            if (st == .poison_type) break :blk st;
            const through_ptr = sp.get(st) == .ptr_type;
            if (through_ptr) st = sp.get(st).ptr_type.child;
            // pointers index like arrays (`*u8 buf; buf[i]`), arrays auto-deref once
            const elem = if (sp.get(st) == .array_type) sp.get(st).array_type.elem else if (through_ptr) st else break :blk self.report(.type_mismatch, a0, st, .none);
            break :blk if (is_range) sp.intern(.{ .array_type = .{ .len = self.fresh_var(node), .elem = elem } }) else elem;
        },
        .dereference => blk: {
            const st = sp.apply_vars(ap, self.h09_check_expr(ctx, a0, .none));
            break :blk if (sp.get(st) == .ptr_type) sp.get(st).ptr_type.child else if (st == .poison_type) st else self.report(.type_mismatch, node, st, .none);
        },
        .address_of => blk: {
            const exp = if (expected == .none) expected else sp.apply_vars(ap, expected);
            const st = self.h09_check_expr(ctx, a0, if (exp != .none and sp.get(exp) == .ptr_type) sp.get(exp).ptr_type.child else .none);
            break :blk if (st == .poison_type) st else self.self_ptr(st);
        },
        .array, .array_empty => blk: {
            const exp = if (expected == .none) expected else sp.apply_vars(ap, expected);
            var elem: StaticPool.Index = if (exp != .none and sp.get(exp) == .array_type) sp.get(exp).array_type.elem else .none;
            const elems = if (k == .array) self.kids(node) else &[_]NodeId{};
            for (elems) |e| {
                const et = self.h09_check_expr(ctx, e, elem);
                if (elem == .none) elem = et else _ = self.h10_expect(ctx, e, et, elem);
            }
            if (elem == .none) elem = self.fresh_var(node);
            break :blk sp.intern(.{ .array_type = .{ .len = sp.intern(.{ .int = .{ .ty = .u64_type, .bits = elems.len } }), .elem = elem } });
        },
        .as => blk: {
            const to = self.h07_lower_type(ctx, a1);
            const from = sp.apply_vars(ap, self.h09_check_expr(ctx, a0, .none));
            break :blk if (sp.cast(from, to) == .invalid) self.report(.invalid_cast, node, from, to) else to;
        },
        .oftype => blk: {
            _ = self.h09_check_expr(ctx, a0, .none);
            _ = self.h07_lower_type(ctx, a1);
            break :blk .bool_type;
        },
        .typeof => blk: {
            _ = self.h09_check_expr(ctx, a0, .none);
            break :blk .type_type;
        },
        .sizeof => blk: {
            _ = self.h09_check_expr(ctx, a0, .none);
            break :blk .u64_type;
        },
        .if_then, .if_else, .stcif_then, .stcif_else => self.h15_check_branching(ctx, node, expected),
        .@"while", .while_with_repeat_stmt, .stcwhile, .stcwhile_with_repeat_stmt, .for_seq, .for_var_in_seq, .stcfor_seq, .stcfor_var_in_seq, .loop, .loop_with_repeat_stmt, .stcloop, .stcloop_with_repeat_stmt => self.h16_check_loop(ctx, node, expected),
        // ranges are sequences of their bound type, so `for` and slicing treat them like arrays
        .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound, .gen_upperbound_incl, .gen_upperbound_excl => blk: {
            const exp = if (expected == .none) expected else sp.apply_vars(ap, expected);
            const hint = if (exp != .none and sp.get(exp) == .array_type) sp.get(exp).array_type.elem else if (self.is_numeric(exp)) exp else .none;
            const b = if (k == .gen_incl or k == .gen_excl) self.pair(ctx, node, a0, a1, hint) else self.operand(ctx, a0, hint);
            if (b == .poison_type) break :blk b;
            if (!sp.class(b).is_integer) break :blk self.report(.type_mismatch, node, b, .u64_type);
            break :blk sp.intern(.{ .array_type = .{ .len = self.fresh_var(node), .elem = b } });
        },
        .match, .stcmatch => self.h14_check_match(ctx, node, expected),
        .ret => blk: {
            _ = if (ctx.ret_type == .none) self.h09_check_expr(ctx, a0, .none) else self.check(ctx, a0, ctx.ret_type);
            break :blk .never_type;
        },
        .ret_void => if (ctx.ret_type != .none and sp.coerce(ap, .unit_type, ctx.ret_type) == .incompatible) self.report(.ret_type_mismatch, node, .unit_type, ctx.ret_type) else .never_type,
        .brk, .cont => if (ctx.loop_depth > 0) .never_type else self.report(if (k == .brk) .brk_outside_loop else .cont_outside_loop, node, 0, 0),
        .do => blk: {
            _ = self.h09_check_expr(ctx, a0, .none);
            break :blk .runit_type;
        },
        .@"defer" => blk: {
            _ = self.h09_check_expr(ctx, a0, .none);
            break :blk .unit_type;
        },
        .deinit => blk: {
            self.need_deinit(node, self.h09_check_expr(ctx, a0, .none));
            break :blk .unit_type;
        },
        .inlined_defer_deinit => blk: {
            const st = self.h09_check_expr(ctx, a0, expected);
            self.need_deinit(node, st);
            break :blk st;
        },
        .selftag_unwrap, .selftag_unwrap_fallback, .selftag_arrow, .labelarrow => self.h17_check_unwrap(ctx, node, expected),
        .def_fun => blk: { // lambdas and local functions are checked on the spot and see the enclosing locals
            const d = self.push_decl(.empty, node, .function, .none, .{});
            self.node_decl[node] = d;
            self.h05_ensure_signature(d);
            self.h06_check_body(d);
            break :blk self.dp(.ty, d).*;
        },
        // type expressions in value position: the value is a type
        else => if (is_type_expr(k) or k == .unify_variants or self.type_kind(node) != .variable) sp.type_of(self.h08_eval_static(ctx, node)) else .unit_type,
    };
    return self.set(node, t);
}

fn h10_expect(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, actual: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    _ = ctx;
    // a poisoned value settles what it was expected to infer, so the error does not spread
    if (actual == .poison_type and expected != .none and self.static_pool.has_vars(expected)) _ = self.static_pool.unify(&self.abstract_pool, expected, .poison_type);
    if (expected == .none or actual == .poison_type or expected == .poison_type) return actual;
    // literals take the expected type directly (an unbound var: their default, which then binds the var)
    const a = if (self.is_literal(node)) self.set(node, self.literal_type(node, expected)) else actual;
    if (self.static_pool.coerce(&self.abstract_pool, a, expected) != .incompatible) return expected;
    return self.report(if (self.static_pool.unify(&self.abstract_pool, a, expected) == .infinite) .infinite_type else .type_mismatch, node, a, expected);
}

fn h11_check_assign(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    var flags = Decl.Flags{};
    const n = self.unwrap_mods(node, &flags);
    const parts = self.stmt_parts(n);
    const kind = self.decl_kind(parts.type, parts.value);
    if (kind != .variable) { // local function / type / trait
        for (parts.ids) |id| {
            const d = self.declare(id, n, kind, .none, flags);
            self.h05_ensure_signature(d);
            self.h06_check_body(d);
        }
        return .unit_type;
    }
    const values = if (parts.value == 0) &[_]NodeId{} else self.list_at(n, 1, .partial__assign_multival);
    // a write into a place (`p.x = v`, `a[i] = v`, `ptr.* = v`)
    if (parts.ids.len == 1 and self.name_of(parts.ids[0]) == .none) {
        const pt = self.h18_check_place(ctx, parts.ids[0]);
        for (values) |v| _ = self.check(ctx, v, pt);
        return .unit_type;
    }
    const declaring = parts.type != 0 or @as(u8, @bitCast(flags)) != 0;
    var ty: StaticPool.Index = if (parts.type != 0) self.h07_lower_type(ctx, parts.type) else .none;
    // untyped: visible names are assigned, their type is shared by the new ones
    var existing: [64]Decl.Index = undefined;
    for (parts.ids, 0..) |id, i| {
        existing[i] = if (declaring or self.pre_declared(self.node_decl[id], n)) .none else self.h01_lookup(self.name_of(id));
        if (existing[i] == .none) continue;
        const et = self.h18_check_place(ctx, id);
        if (ty == .none) ty = et else if (et != ty and et != .poison_type) _ = self.report(.destructure_type_conflict, id, et, ty);
    }
    if (values.len > 1) {
        var shared = ty;
        for (values, 0..) |v, i| {
            const vt = self.check(ctx, v, if (i < parts.ids.len and existing[i] != .none) self.dp(.ty, existing[i]).* else ty);
            if (shared == .none) shared = vt else if (ty == .none) {
                const j = sp.join(&self.abstract_pool, shared, vt);
                shared = if (j.ty == .none) self.report(.destructure_type_conflict, v, shared, vt) else j.ty;
            }
        }
        ty = shared;
    } else if (values.len == 1) {
        // a fresh var as expectation means "a value is wanted" (loops / ifs as values) without fixing its type
        const got = self.check(ctx, values[0], if (ty != .none) ty else self.fresh_var(n));
        if (ty == .none) ty = sp.apply_vars(&self.abstract_pool, got);
    }
    for (parts.ids, 0..) |id, i| {
        const d = if (existing[i] != .none) existing[i] else self.declare(id, n, .variable, if (ty == .none) .poison_type else ty, flags);
        if (values.len > 0 and (self.dp(.flags, d).is_stc or ctx.in_static))
            self.dp(.value, d).* = self.retype(self.h08_eval_static(ctx, values[@min(i, values.len - 1)]), self.dp(.ty, d).*);
    }
    return .unit_type;
}

fn h12_check_call(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    _ = expected; // arguments get their parameter types as expectation instead
    const sp = &self.static_pool;
    const args = self.kids(self.arg(node, 1));
    if (self.nk(node) == .with) { // a copy of a record, the named arguments must be its fields
        const t = self.deref(self.h09_check_expr(ctx, self.arg(node, 0), .none));
        for (args) |a| {
            const m = if (self.nk(a) == .partial__fun_call_assigned_param and t != .poison_type) sp.lookup_member(t, self.name_of(self.arg(a, 0))) else StaticPool.Member.none;
            _ = if (m == .field) self.check(ctx, self.arg(a, 1), self.named(a, m.field.ty)) else if (t == .poison_type) t else self.report(.unknown_named_argument, a, self.name_of(self.arg(a, 0)), t);
        }
        return t;
    }
    const callee = self.arg(node, 0);
    const ct = self.h09_check_expr(ctx, callee, .none);
    const d = if (self.nk(callee) == .fun_call) .none else self.node_decl[callee];
    // `x.m(..)` binds x as the self argument, `Type.m(x.&, ..)` passes it like any other argument
    const recv = if (self.nk(callee) == .member and sp.tag(self.node_type[self.arg(callee, 0)]) != .meta_type) self.arg(callee, 0) else 0;
    if (ct != .poison_type and d != .none and is_fn(self.dp(.kind, d).*)) return self.call_decl(ctx, node, d, args, recv);
    const target = if (sp.tag(ct) == .meta_type) self.h08_eval_static(ctx, callee) else sp.apply_vars(&self.abstract_pool, ct);
    switch (sp.tag(target)) {
        // type constructors: records (`Person(name = ..)`) and variant cases (`Event.Key(13)`)
        .record_type, .variant_case_type => {
            const rec = if (sp.tag(target) == .variant_case_type) sp.get(target).variant_case_type.payload else target;
            var map: [64]u32 = undefined;
            if (rec == .none and args.len > 0) return self.report(.wrong_arity, node, args.len, 0);
            if (rec != .none and !self.bind_args(self.fields_of(rec), args, &map, false)) return self.bad_args(node, self.fields_of(rec), args);
            for (args, 0..) |a, i| _ = self.check(ctx, self.arg_value(a), self.named(a, sp.get(rec).custom_type.field_types[map[i]]));
            return target;
        },
        // a value of function type (`op(a, b)`, `make_adder(1)(2)`, a lambda called directly)
        .function_type => {
            if (sp.get(target).function_type.params.len != args.len) return self.report(.wrong_arity, node, args.len, sp.get(target).function_type.params.len);
            for (args, 0..) |a, i| _ = self.check(ctx, self.arg_value(a), sp.get(target).function_type.params[i]);
            return sp.get(target).function_type.ret;
        },
        else => {
            for (args) |a| _ = self.h09_check_expr(ctx, self.arg_value(a), .none);
            return if (target == .poison_type) target else self.report(.not_callable, callee, ct, .none);
        },
    }
}

// calls of declared functions: overload resolution, stcfun realization, length-generic realization
fn call_decl(self: *Resolver, ctx: *FnCtx, node: NodeId, first: Decl.Index, all_args: []const NodeId, recv: NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    if (self.dp(.kind, first).* == .static_function) {
        const want = sp.get(self.dp(.ty, first).*).function_type.params.len;
        if (all_args.len != want) return self.report(.wrong_arity, node, all_args.len, want);
        var vals: [64]StaticPool.Index = undefined;
        for (all_args, 0..) |a, i| vals[i] = self.h08_eval_static(ctx, self.arg_value(a));
        const r = self.h20_instantiate(first, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = vals[0..all_args.len] } }));
        const ret = sp.get(self.dp(.ty, first).*).function_type.ret;
        if (sp.tag(r) != .function_value) return if (sp.tag(ret) == .meta_type or ret == .poison_type) sp.type_of(r) else ret;
        self.node_decl[node] = sp.get(r).function;
        return self.dp(.ty, sp.get(r).function).*;
    }
    // the self argument of a method: the receiver, or the first argument when called through the type
    const off = self.self_off(first);
    var args = all_args;
    if (off == 1) {
        const ft = self.dp(.ty, self.real(first)).*;
        const p0 = if (ft != .none and sp.tag(ft) == .function_type) sp.get(ft).function_type.params[0] else StaticPool.Index.poison_type;
        if (recv != 0) {
            const rt = sp.apply_vars(&self.abstract_pool, self.node_type[recv]);
            const child = if (sp.get(p0) == .ptr_type) sp.get(p0).ptr_type.child else p0;
            if (rt != .poison_type and p0 != .poison_type and rt != child and !sp.implements(rt, child) and sp.coerce(&self.abstract_pool, rt, p0) == .incompatible)
                _ = self.report(.type_mismatch, recv, rt, p0);
        } else if (args.len > 0) {
            _ = self.check(ctx, self.arg_value(args[0]), p0);
            args = args[1..];
        } else return self.report(.wrong_arity, node, 0, 1);
    }
    // argument types once, with the first candidate's parameters as expectation
    var tys: [64]StaticPool.Index = undefined;
    var map: [64]u32 = undefined;
    const f0 = self.real(first);
    const f0_ok = self.dp(.ty, f0).* != .none and self.bind_args(self.params_of(self.value_node(f0)), args, &map, false);
    for (args, 0..) |a, i| {
        const hint = if (f0_ok) sp.get(self.dp(.ty, f0).*).function_type.params[map[i] + off] else .none;
        tys[i] = self.h09_check_expr(ctx, self.arg_value(a), hint);
    }
    // most specific candidate: exact > coercion > unlengthed, a where clause beats none
    var best: Decl.Index = .none;
    var best_score: i32 = -1;
    var ambiguous = false;
    var count: u32 = 0;
    var c = first;
    while (c != .none) : (c = self.dp(.next_overload, c).*) {
        count += 1;
        const s = self.score(c, args, tys[0..args.len], off);
        if (s > best_score) {
            best, best_score, ambiguous = .{ c, s, false };
        } else if (s == best_score and s >= 0 and !self.has_where(self.real(c)) and !self.has_where(self.real(best))) ambiguous = true;
    }
    if (best == .none) {
        if (count > 1) return self.report(.no_matching_overload, node, args.len, 0);
        if (!f0_ok) return self.bad_args(node, self.params_of(self.value_node(f0)), args);
        for (args, 0..) |a, i| _ = self.h10_expect(ctx, self.arg_value(a), tys[i], sp.get(self.dp(.ty, f0).*).function_type.params[map[i] + off]);
        return .poison_type;
    }
    if (ambiguous) _ = self.report(.ambiguous_overload, node, best, 0);
    var callee = self.real(best);
    const pnodes = self.params_of(self.value_node(callee));
    _ = self.bind_args(pnodes, args, &map, false);
    if (self.length_generic(self.dp(.ty, callee).*)) {
        // the argument lengths, in parameter order, pick the realization
        var lens: [64]StaticPool.Index = undefined;
        var n: usize = 0;
        for (0..pnodes.len) |j| {
            const p = sp.get(self.dp(.ty, callee).*).function_type.params[j + off];
            if (!sp.has_vars(p)) continue;
            for (0..args.len) |i| if (map[i] == j) {
                lens[n] = self.arg_len(tys[i], p);
                n += 1;
            };
        }
        callee = sp.get(self.h20_instantiate(callee, sp.intern(.{ .aggregate = .{ .ty = .none, .elems = lens[0..n] } }))).function;
        self.node_decl[node] = callee;
    } else {
        for (args, 0..) |a, i| _ = self.h10_expect(ctx, self.arg_value(a), tys[i], self.named(a, sp.get(self.dp(.ty, callee).*).function_type.params[map[i] + off]));
        // the call names the head of its dispatch group: the lowerer walks `next_overload` from there over the
        // overloads with the identical parameter types, tests their where clauses in order, the where-less one last
        // LIMITATION: a group whose where clauses may all fail and that has no where-less fallback is not reported
        var head = first;
        while (!self.same_params(self.dp(.ty, self.real(head)).*, self.dp(.ty, callee).*)) head = self.dp(.next_overload, head).*;
        self.node_decl[node] = self.real(head);
    }
    return sp.get(self.dp(.ty, callee).*).function_type.ret;
}

fn score(self: *Resolver, c: Decl.Index, args: []const NodeId, tys: []const StaticPool.Index, off: usize) i32 {
    const sp = &self.static_pool;
    self.h05_ensure_signature(c);
    const r = self.real(c);
    const ft = self.dp(.ty, r).*;
    if (ft == .none or sp.tag(ft) != .function_type) return -1;
    var map: [64]u32 = undefined;
    const pnodes = self.params_of(self.value_node(r));
    if (!self.bind_args(pnodes, args, &map, false)) return -1;
    var total: i32 = 0;
    for (args, tys, 0..) |a, t, i| {
        const p = sp.get(ft).function_type.params[map[i] + off];
        const v = self.arg_value(a);
        total += if (t == p or t == .poison_type or (self.is_literal(v) and sp.coerce(&self.abstract_pool, self.literal_type(v, p), p) == .identity))
            @as(i32, 6) - @intFromBool(sp.class(p).is_float and !sp.class(t).is_float)
        else if (sp.has_vars(p))
            (if (self.arg_len(t, p) != .none) 2 else return -1)
        else if (sp.coerce(&self.abstract_pool, t, p) != .incompatible) 4 else return -1;
        if (self.param(pnodes[map[i]]).where != 0) total += 1;
    }
    return total;
}

fn h13_check_member(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const parent = self.arg(node, 0);
    const name = self.name_of(self.arg(node, 1));
    const pt = self.h09_check_expr(ctx, parent, .none);
    if (pt == .poison_type) return pt;
    // `Type.Case`, `Type.init`, `Stream(i32).None` are members of the type value
    const on_type = sp.tag(pt) == .meta_type;
    const base = if (on_type) self.h08_eval_static(ctx, parent) else sp.apply_vars(&self.abstract_pool, pt);
    if (base == .poison_type) return base;
    if (sp.tag(base) == .type_var) return self.report(.uninferable_type, parent, base, .none);
    return switch (sp.lookup_member(base, name)) {
        .field => |f| if (on_type) self.report(.unknown_member, node, name, base) else f.ty,
        .method => |m| self.method(node, m),
        .trait_method => |m| self.method(node, @enumFromInt(@intFromEnum(sp.get(m.trait).trait_type.decl) + 1 + m.index)),
        .case => |c| c,
        .builtin_len => .u64_type,
        .builtin_init, .builtin_deinit => sp.intern(.{ .function_type = .{ .category = .default, .params = &.{}, .ret = if (name == .init) base else .unit_type } }),
        .none => self.report(.unknown_member, node, name, base),
    };
}

fn h14_check_match(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const arms = self.kids(self.arg(node, 1));
    const st = self.deref(self.h09_check_expr(ctx, self.arg(node, 0), .none));
    const is_stc = self.nk(node) == .stcmatch;
    // stcmatch on a static scrutinee: only the matching arm is checked
    // LIMITATION: a runtime scrutinee of stcmatch (`stcmatch a` on a parameter) is checked like a match
    if (is_stc) if (self.try_static(ctx, self.arg(node, 0))) |v| {
        self.h03_push_scope();
        defer self.h04_pop_scope();
        for (arms) |arm| if (self.static_match(ctx, self.arg(arm, 0), v)) return self.branch(ctx, self.arg(arm, 1), expected);
        return self.report(.non_exhaustive_match, node, v, .none);
    };
    // variant cases and bools are tracked in a bitset, everything else needs `_` or a binder
    var covered: u64 = 0;
    var catch_all = false;
    var result: StaticPool.Index = .none;
    for (arms) |arm| {
        self.h03_push_scope();
        const pat = self.pattern(ctx, self.arg(arm, 0), st);
        if (catch_all or (!pat.all and pat.mask != 0 and pat.mask & ~covered == 0)) Doctor.h21_report(self, .redundant_match_arm, arm, 0, 0);
        covered |= pat.mask;
        catch_all = catch_all or pat.all;
        const t = self.branch(ctx, self.arg(arm, 1), expected);
        self.h04_pop_scope();
        result = self.merge(arm, result, t, expected);
    }
    // LIMITATION: ints, strings and `||` unions need `_` or a binder, ranges are not proven to cover everything
    const cases: usize = if (st == .bool_type) 2 else if (sp.tag(st) == .variant_type) sp.get(st).variant_type.cases.len else 65;
    if (!catch_all and !is_stc and st != .poison_type and (cases > 64 or covered != @as(u64, std.math.maxInt(u64)) >> @intCast(64 - cases)))
        _ = self.report(.non_exhaustive_match, node, st, .none);
    return if (result == .none) .unit_type else result;
}

fn h15_check_branching(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const k = self.nk(node);
    const has_else = k == .if_else or k == .stcif_else;
    const it = if (has_else) self.arg(node, 0) else node;
    const cond = self.arg(it, 0);
    const then = self.arg(it, 1);
    if (k == .stcif_then or k == .stcif_else) {
        const c = self.h08_eval_static(ctx, cond);
        _ = self.set(cond, .bool_type);
        if (c == .bool_true) return self.branch(ctx, then, expected);
        if (c != .bool_false) return if (c == .poison_type) c else self.report(.type_mismatch, cond, self.static_pool.type_of(c), .bool_type);
        return if (has_else) self.branch(ctx, self.arg(node, 1), expected) else .unit_type;
    }
    // binders of the condition (`x ?<- v`) are visible in the then branch only
    self.h03_push_scope();
    _ = self.check(ctx, cond, .bool_type);
    const tt = self.branch(ctx, then, expected);
    self.h04_pop_scope();
    if (!has_else) {
        const valued = tt != .never_type and tt != .runit_type and tt != .poison_type and tt != .unit_type;
        return if (self.concrete(expected) and valued) self.report(.runit_mixing, node, tt, .unit_type) else self.merge(node, tt, .unit_type, if (valued) .none else expected);
    }
    return self.merge(node, tt, self.branch(ctx, self.arg(node, 1), expected), expected);
}

fn h16_check_loop(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const k = self.nk(node);
    const a0 = self.arg(node, 0);
    const a1 = self.arg(node, 1);
    const exp = if (expected == .none) expected else sp.apply_vars(&self.abstract_pool, expected);
    const elem_hint = if (exp != .none and sp.get(exp) == .array_type) sp.get(exp).array_type.elem else .none;
    self.h03_push_scope();
    defer self.h04_pop_scope();
    const body = switch (k) {
        .@"while", .stcwhile => blk: {
            _ = self.check(ctx, a0, .bool_type);
            break :blk a1;
        },
        .while_with_repeat_stmt, .stcwhile_with_repeat_stmt => blk: {
            _ = self.check(ctx, self.arg(a0, 0), .bool_type);
            _ = self.h09_check_expr(ctx, a1, .none);
            _ = self.set(a0, .unit_type);
            break :blk self.arg(a0, 1);
        },
        .loop, .stcloop => a0,
        .loop_with_repeat_stmt, .stcloop_with_repeat_stmt => blk: {
            _ = self.h09_check_expr(ctx, a0, .none);
            break :blk a1;
        },
        else => blk: { // for: over an array, a range or anything with an Iterable `next`
            const has_var = k == .for_var_in_seq or k == .stcfor_var_in_seq;
            const f = if (has_var) a0 else node;
            var st = sp.apply_vars(&self.abstract_pool, self.h09_check_expr(ctx, self.arg(f, 0), if (elem_hint != .none and is_range_kind(self.nk(self.arg(f, 0)))) exp else .none));
            if (sp.get(st) == .ptr_type) st = sp.get(st).ptr_type.child;
            const elem = switch (sp.lookup_member(st, if (sp.get(st) == .array_type) .len else self.name_pool.intern("next"))) {
                .builtin_len => sp.get(st).array_type.elem,
                .method => |m| self.fn_ret(m),
                .trait_method => |m| self.fn_ret(@enumFromInt(@intFromEnum(sp.get(m.trait).trait_type.decl) + 1 + m.index)),
                else => if (st == .poison_type) st else self.report(.type_mismatch, self.arg(f, 0), st, .none),
            };
            const it = self.h02_declare_local(if (has_var) self.name_of(a1) else .dollar_it, if (has_var) a1 else f, if (has_var) .loop_variable else .autoins_it, elem);
            if (has_var) {
                self.node_decl[a1] = it;
                _ = self.set(a1, elem);
                _ = self.set(f, .unit_type);
            }
            break :blk self.arg(f, 1);
        },
    };
    ctx.loop_depth += 1;
    const bt = self.h09_check_expr(ctx, body, if (expected != .none) elem_hint else .none);
    ctx.loop_depth -= 1;
    // used as a value: an array of the body values; brk ends it without adding one
    if (expected == .none) return .unit_type;
    return sp.intern(.{ .array_type = .{ .len = self.fresh_var(node), .elem = if (bt == .never_type or bt == .runit_type) (if (elem_hint != .none) elem_hint else .unit_type) else bt } });
}

// LIMITATION: binders go to the current scope; directly in a block they stay visible to the following statements
fn h17_check_unwrap(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    const k = self.nk(node);
    const vt = self.static_pool.apply_vars(&self.abstract_pool, self.h09_check_expr(ctx, self.arg(node, 0), if (k == .labelarrow) expected else .none));
    if (k == .labelarrow) {
        self.bind_label(self.arg(node, 1), vt);
        return vt;
    }
    const pt = self.payload_of(vt);
    if (pt == .none) return if (vt == .poison_type) vt else self.report(.type_mismatch, self.arg(node, 0), vt, .none);
    return switch (k) {
        .selftag_unwrap_fallback => blk: {
            _ = self.check(ctx, self.arg(node, 1), pt);
            break :blk pt;
        },
        .selftag_arrow => blk: {
            self.bind_label(self.arg(node, 1), pt);
            break :blk .bool_type;
        },
        else => pt,
    };
}

fn h18_check_place(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    // self is mutable in methods; stc locals are compile-time variables and writable too
    const t = self.h09_check_expr(ctx, node, .none);
    switch (self.writable(node)) {
        .ok => {},
        .immutable => Doctor.h21_report(self, .assign_to_immutable, node, 0, 0),
        .through_ptr => Doctor.h21_report(self, .write_through_immutable_pointer, node, 0, 0),
    }
    return t;
}

// ------------------------------------------------------------------------------------------ //
// types, generics, diagnostics
// ------------------------------------------------------------------------------------------ //

fn h19_check_type_def(self: *Resolver, ctx: *FnCtx, decl: Decl.Index, node: ParseTree.NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    var body: NodeId = 0;
    var size: NodeId = 0;
    var tagof: NodeId = 0;
    var c = node;
    while (true) switch (self.nk(c)) {
        .def_type_implof, .def_variant_implof => {
            body = self.arg(c, 1);
            c = self.arg(c, 0);
        },
        .def_type_assertsize, .def_variant_assertsize => {
            size = self.arg(c, 1);
            c = self.arg(c, 0);
        },
        .def_variant_tagof => {
            tagof = self.arg(c, 1);
            c = self.arg(c, 0);
        },
        else => break,
    };
    const ck = self.nk(c);
    // reserved first (or already by h20), so fields can point back at the type (`*Tree`)
    if (self.dp(.value, decl).* == .none) self.dp(.value, decl).* = sp.reserve_nominal(decl);
    const ty = self.dp(.value, decl).*;
    self.dp(.ty, decl).* = switch (ck) {
        .def_trait, .def_trait_implof => .trait_type,
        .def_variant, .def_variant_unionsized => .variant_type,
        else => .type_type,
    };
    if (self.dp(.state, decl).* == .resolving_signature) self.dp(.state, decl).* = .signature_ready;
    self.h03_push_scope();
    defer self.h04_pop_scope();

    var traits: [32]StaticPool.Index = undefined;
    var nt: usize = 0;
    var own: StaticPool.Index = .none; // the anonymous `!{..}` body
    if (ck == .def_trait or ck == .def_trait_implof) {
        body = c;
    } else if (body != 0) {
        const impls = if (self.nk(body) == .def_trait_implof) self.kids(self.arg(body, 0)) else &[_]NodeId{};
        const members = self.arg(body, if (self.nk(body) == .def_trait_implof) 1 else 0);
        if (self.kids(members).len > 0) {
            own = self.trait_body(ctx, members, .none, ty, &.{});
            traits[0] = own;
            nt = 1;
        }
        for (impls) |t| {
            traits[nt] = self.h07_lower_type(ctx, t);
            nt += @intFromBool(traits[nt] != .poison_type);
        }
    }

    switch (ck) {
        .def_trait, .def_trait_implof => {
            var supers: [32]StaticPool.Index = undefined;
            const impls = if (ck == .def_trait_implof) self.kids(self.arg(c, 0)) else &[_]NodeId{};
            for (impls, 0..) |t, i| supers[i] = self.h07_lower_type(ctx, t);
            own = self.trait_body(ctx, self.arg(c, if (ck == .def_trait_implof) 1 else 0), ty, .none, supers[0..impls.len]);
        },
        .def_variant, .def_variant_unionsized => {
            const params = self.kids(self.arg(c, 0));
            var cases: [256]StaticPool.Index = undefined;
            var payload_case: ?usize = null;
            var payloads: usize = 0;
            var next_tag: u64 = 0;
            for (params, 0..) |pn, i| {
                var q = pn;
                var tag_node: NodeId = 0;
                var payload_node: NodeId = 0;
                if (self.nk(q) == .partial__variant_def_param_tagged) {
                    tag_node = self.arg(q, 1);
                    q = self.arg(q, 0);
                }
                if (self.nk(q) == .partial__variant_def_param_typed) {
                    payload_node = self.arg(q, 1);
                    q = self.arg(q, 0);
                }
                const payload = if (payload_node == 0) .none else self.h19_check_type_def(ctx, self.push_decl(.empty, payload_node, .record, .none, .{}), payload_node);
                if (payload != .none) {
                    payload_case = i;
                    payloads += 1;
                }
                const tv = if (tag_node == 0) sp.intern(.{ .int = .{ .ty = .u64_type, .bits = next_tag } }) else self.h08_eval_static(ctx, tag_node);
                if (sp.tag(tv) == .int_value) next_tag = sp.get(tv).int.bits +% 1;
                cases[i] = self.set(self.arg(q, 0), sp.intern(.{ .variant_case_type = .{ .variant = ty, .case = @intCast(i), .name = self.name_of(self.arg(q, 0)), .tag = tv, .payload = payload } }));
            }
            // variants are always tagged, without tagof by the smallest tag type for their case count
            const mode: StaticPool.VariantTagMode = if (tagof != 0 and self.nk(tagof) == .identifier_self) .self else .int;
            var tag_ty: StaticPool.Index = if (tagof == 0) StaticPool.smallest_tag_type(params.len) else if (mode == .self) .none else self.h07_lower_type(ctx, tagof);
            if (mode == .self) {
                // the one payload type encodes the other cases in bit patterns it never uses
                if (payloads != 1) _ = self.report(.self_tag_without_niche, tagof, payloads, 0) else {
                    const fields = sp.get(sp.get(cases[payload_case.?]).variant_case_type.payload).custom_type.field_types;
                    tag_ty = if (fields.len == 1 and sp.class(fields[0]).is_integer) fields[0] else self.report(.self_tag_without_niche, tagof, 0, 0);
                }
            }
            if (tag_ty != .none and tag_ty != .poison_type) for (params, 0..) |pn, i| {
                const case = sp.get(cases[i]).variant_case_type;
                if ((mode == .int or case.payload == .none) and sp.tag(case.tag) == .int_value and !sp.fits(case.tag, tag_ty)) _ = self.report(.tag_overflow, pn, case.tag, tag_ty);
            };
            sp.complete_nominal(ty, .{ .variant_type = .{ .decl = decl, .tag_mode = mode, .tag_type = tag_ty, .is_unionsized = ck == .def_variant_unionsized, .cases = cases[0..params.len], .traits = traits[0..nt] } });
        },
        else => { // records: `*(..)`, `**(..)` and payload tuples
            const fields = self.fields_of_node(c);
            var names: [64]NamePool.Index = undefined;
            var types: [64]StaticPool.Index = undefined;
            for (fields, 0..) |f, i| {
                const p = self.param(f);
                types[i] = self.h07_lower_type(ctx, p.ty);
                names[i] = if (p.name != 0) self.name_of(p.name) else self.param_name(f, i);
            }
            sp.complete_nominal(ty, .{ .custom_type = .{ .decl = decl, .is_packed = ck == .def_type_packed, .field_names = names[0..fields.len], .field_types = types[0..fields.len], .traits = traits[0..nt] } });
            // defaults and where-clauses see the fields by name
            for (fields, 0..) |f, i| {
                const fd = self.h02_declare_local(names[i], f, .field, types[i]);
                self.dp(.flags, fd).is_mut = self.param(f).is_mut;
                self.link(self.param(f).name, fd, types[i]);
            }
            for (fields, 0..) |f, i| {
                const p = self.param(f);
                if (p.default != 0) _ = self.check(ctx, p.default, types[i]);
                if (p.where != 0) _ = self.check(ctx, p.where, .bool_type);
                if (p.@"else" != 0) _ = if (self.nk(p.@"else") == .assign) self.h09_check_expr(ctx, p.@"else", .none) else self.check(ctx, p.@"else", types[i]);
            }
        },
    }
    // member bodies once the type is complete, then trait conformance
    if (own != .none) {
        const b = @intFromEnum(sp.get(own).trait_type.decl);
        for (0..sp.get(own).trait_type.member_names.len) |i| self.h06_check_body(@enumFromInt(b + 1 + i));
    }
    if (ck != .def_trait and ck != .def_trait_implof) for (traits[0..nt]) |t| if (t != own and sp.tag(t) == .trait_type) self.conform(ty, own, t, node);
    if (ck != .def_trait and ck != .def_trait_implof and sp.layout(ty).state == .infinite) _ = self.report(.recursive_by_value_type, node, ty, .none);
    if (size != 0) {
        const v = self.h08_eval_static(ctx, size);
        const want = if (sp.class(v).is_type) sp.layout(v).size else if (sp.tag(v) == .int_value) sp.get(v).int.bits else 0;
        if (v != .poison_type and sp.layout(ty).size != want) _ = self.report(.assertsize_failed, size, sp.layout(ty).size, want);
    }
    return ty;
}

fn h20_instantiate(self: *Resolver, generic: Decl.Index, args: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const key = StaticPool.AbstractKey{ .generic_tuple = generic, .args_tuple = args };
    if (sp.realized_abstracts.get(key)) |r| return r;
    const node = self.dp(.node, generic).*;
    // a realization that realizes itself forever eats the static budget and stops there
    if (self.interpreter.step_budget < 64 or self.local_scope_marks.head > max_nesting) return self.report(.static_eval_failed, node, generic, 0);
    self.interpreter.step_budget -= 64;
    var argv: [64]StaticPool.Index = undefined;
    const argc = sp.get(args).aggregate.elems.len;
    @memcpy(argv[0..argc], sp.get(args).aggregate.elems);

    if (self.dp(.kind, generic).* != .static_function) {
        // length-generic function: a new declaration per tuple of lengths, the lengths bound in order of appearance
        const d = self.push_decl(self.dp(.name, generic).*, node, self.dp(.kind, generic).*, .none, self.dp(.flags, generic).*);
        const fv = sp.intern(.{ .function = d });
        self.memo(key, fv);
        self.h05_ensure_signature(d);
        var i: usize = 0;
        for (0..sp.get(self.dp(.ty, d).*).function_type.params.len) |j| {
            var p = sp.get(self.dp(.ty, d).*).function_type.params[j];
            if (sp.get(p) == .ptr_type) p = sp.get(p).ptr_type.child;
            if (sp.get(p) != .array_type or !sp.has_vars(sp.get(p).array_type.len) or i >= argc) continue;
            _ = sp.unify(&self.abstract_pool, sp.get(p).array_type.len, argv[i]);
            i += 1;
        }
        self.h06_check_body(d);
        return fv;
    }

    var ctx = FnCtx{ .decl = generic, .ret_type = .none, .self_type = .none, .loop_depth = 0, .in_static = true };
    self.open_scope(true, .none, 0);
    defer self.h04_pop_scope();
    const v = self.value_node(generic);
    const params = self.params_of(v);
    for (params, 0..) |pn, i| {
        const pt = sp.get(self.dp(.ty, generic).*).function_type.params[i];
        const d = self.h02_declare_local(self.param_name(pn, i), pn, .static_parameter, pt);
        self.link(self.param(pn).name, d, pt);
        self.dp(.value, d).* = self.retype(argv[i], pt);
    }
    // LIMITATION: stcwhere is only evaluated here, for stcfun parameters; on regular functions it is only type checked
    for (params) |pn| {
        const w = self.param(pn).where;
        if (w != 0 and self.h08_eval_static(&ctx, w) == .bool_false) _ = self.report(.stcwhere_violated, w, generic, args);
    }
    const unit = self.arg(v, 1);
    const kind = self.type_kind(unit);
    if (kind != .variable) { // a type: memoized before its body, so it can mention itself (`Stream(Child)` inside Stream)
        const d = self.push_decl(.empty, unit, kind, .none, .{});
        self.dp(.value, d).* = sp.reserve_nominal(d);
        self.memo(key, self.dp(.value, d).*);
        return self.h19_check_type_def(&ctx, d, unit);
    }
    if (self.nk(unit) == .def_fun) {
        const d = self.push_decl(self.dp(.name, generic).*, unit, .function, .none, .{});
        const fv = sp.intern(.{ .function = d });
        self.memo(key, fv);
        self.h05_ensure_signature(d);
        self.h06_check_body(d);
        return fv;
    }
    const r = self.h08_eval_static(&ctx, unit);
    self.memo(key, r);
    return r;
}

// ------------------------------------------------------------------------------------------ //
// helpers
// ------------------------------------------------------------------------------------------ //

const max_nesting = 256;
const Param = struct { ty: NodeId = 0, name: NodeId = 0, default: NodeId = 0, where: NodeId = 0, @"else": NodeId = 0, is_mut: bool = false };
const Parts = struct { type: NodeId = 0, ids: []const NodeId = &.{}, value: NodeId = 0 };
const Pat = struct { mask: u64 = 0, all: bool = false };
const Access = enum { ok, immutable, through_ptr };

const dollar_names = blk: {
    @setEvalBranchQuota(100_000);
    var t: [64][]const u8 = undefined;
    for (&t, 0..) |*s, i| s.* = std.fmt.comptimePrint("${d}", .{i});
    break :blk t;
};

inline fn nk(self: *const Resolver, n: NodeId) NodeKind {
    return self.tree.ast_nodes.pool.nk.buf[n];
}

inline fn arg(self: *const Resolver, n: NodeId, i: u1) NodeId {
    const slots: *const [2]NodeId = @ptrCast(&self.tree.ast_nodes.pool.args.buf[n]);
    return slots[i];
}

fn kids(self: *const Resolver, n: NodeId) []const NodeId {
    const a = self.tree.ast_nodes.pool.args.buf[n];
    return self.tree.extra_childrefs.buf[a[0]..][0..a[1]];
}

// child i as a list: the children of a `wrapper` node, or the child alone
fn list_at(self: *const Resolver, n: NodeId, comptime i: u1, comptime wrapper: NodeKind) []const NodeId {
    const slots: *const [2]NodeId = @ptrCast(&self.tree.ast_nodes.pool.args.buf[n]);
    return if (self.nk(slots[i]) == wrapper) self.kids(slots[i]) else slots[i..][0..1];
}

fn text(self: *const Resolver, n: NodeId) []const u8 {
    const span = self.tree.span_store[self.arg(n, 0)];
    return self.src_bytes[span[0]..span[1]];
}

fn name_of(self: *Resolver, n: NodeId) NamePool.Index {
    return switch (self.nk(n)) {
        .identifier => self.name_pool.intern(self.text(n)),
        .identifier_self => .self,
        .identifier_init => .init,
        .identifier_deinit => .deinit,
        .identifier_main => .main,
        else => .none,
    };
}

inline fn dp(self: *Resolver, comptime f: @EnumLiteral(), d: Decl.Index) *@FieldType(Decl, @tagName(f)) {
    return &@field(self.decls.pool, @tagName(f)).buf[@intFromEnum(d)];
}

inline fn set(self: *Resolver, n: NodeId, t: StaticPool.Index) StaticPool.Index {
    self.node_type[n] = t;
    return t;
}

fn report(self: *Resolver, code: Doctor.Disorder, n: NodeId, a: anytype, b: anytype) StaticPool.Index {
    Doctor.h21_report(self, code, n, word(a), word(b));
    return self.set(n, .poison_type);
}

fn word(v: anytype) u32 {
    return switch (@typeInfo(@TypeOf(v))) {
        .@"enum" => @intFromEnum(v),
        .enum_literal => @intFromEnum(@as(StaticPool.Index, v)),
        else => @intCast(v),
    };
}

fn check(self: *Resolver, ctx: *FnCtx, n: NodeId, expected: StaticPool.Index) StaticPool.Index {
    return self.h10_expect(ctx, n, self.h09_check_expr(ctx, n, expected), expected);
}

fn is_fn(kind: Decl.Kind) bool {
    return switch (kind) {
        .function, .static_function, .inlined_function, .trait_member => true,
        else => false,
    };
}

fn is_range_kind(k: NodeKind) bool {
    return switch (k) {
        .gen_incl, .gen_excl, .gen_lowerbound, .gen_upperbound, .gen_upperbound_incl, .gen_upperbound_excl => true,
        else => false,
    };
}

fn is_type_expr(k: NodeKind) bool {
    return (@intFromEnum(k) >= @intFromEnum(NodeKind.type_ptrmut) and @intFromEnum(k) <= @intFromEnum(NodeKind.type_stcfun)) or switch (k) {
        .type_array, .type_array_unlengthed, .def_fun_declaration, .typeof => true,
        else => false,
    };
}

fn push_decl(self: *Resolver, name: NamePool.Index, node: NodeId, kind: Decl.Kind, ty: StaticPool.Index, flags: Decl.Flags) Decl.Index {
    const d: Decl.Index = @enumFromInt(self.decls.len());
    const lazy = flags.is_global or is_fn(kind) or is_type_decl(kind);
    self.decls.push(.{ .name = name, .node = node, .kind = kind, .flags = flags, .state = if (lazy) .unresolved else .done, .ty = ty, .value = .none, .next_overload = .none });
    return d;
}

fn is_type_decl(kind: Decl.Kind) bool {
    return kind == .type_alias or kind == .record or kind == .variant or kind == .trait;
}

// a declared global row is reused, anything else becomes a new local
fn declare(self: *Resolver, id: NodeId, stmt: NodeId, kind: Decl.Kind, ty: StaticPool.Index, flags: Decl.Flags) Decl.Index {
    var d = self.node_decl[id];
    if (!self.pre_declared(d, stmt)) {
        d = self.h02_declare_local(self.name_of(id), stmt, kind, ty);
        self.dp(.flags, d).* = flags;
        self.node_decl[id] = d;
    } else if (ty != .none) self.dp(.ty, d).* = ty;
    _ = self.set(id, if (ty == .none) .unit_type else ty);
    return d;
}

// s1 rows of this very statement are reused instead of declared again
fn pre_declared(self: *Resolver, d: Decl.Index, stmt: NodeId) bool {
    return d != .none and self.dp(.flags, d).is_global and self.dp(.node, d).* == stmt;
}

// a scope for a declaration: globals get a barrier so they never see their user's locals
fn open_scope(self: *Resolver, barrier: bool, self_type: StaticPool.Index, node: NodeId) void {
    self.h03_push_scope();
    if (barrier) {
        self.local_names.push(.none);
        self.local_decls.push(.none);
    }
    if (self_type != .none) self.dp(.flags, self.h02_declare_local(.self, node, .self, self.self_ptr(self_type))).is_mut = true;
}

// methods: the owning type is the value of the nearest trait body row holding the member's statement
// LIMITATION: a per-length realization of a method of a stcfun-generated type takes its most recent realization
fn owner_of(self: *Resolver, decl: Decl.Index) StaticPool.Index {
    if (self.dp(.kind, decl).* != .trait_member) return .none;
    const node = self.dp(.node, decl).*;
    var d = @intFromEnum(decl);
    while (d > 0) {
        d -= 1;
        if (self.decls.pool.kind.buf[d] != .trait) continue;
        var flags = Decl.Flags{};
        for (self.kids(self.decls.pool.node.buf[d])) |s| if (self.unwrap_mods(s, &flags) == node) return self.decls.pool.value.buf[d];
    }
    return .none;
}

fn value_node(self: *Resolver, d: Decl.Index) NodeId {
    const n = self.dp(.node, d).*;
    return switch (self.nk(n)) {
        .assign, .assign_typed => self.arg(n, 1),
        else => n,
    };
}

fn core(self: *const Resolver, n: NodeId) NodeId {
    var c = n;
    while (true) switch (self.nk(c)) {
        .def_type_assertsize, .def_type_implof, .def_variant_tagof, .def_variant_assertsize, .def_variant_implof => c = self.arg(c, 0),
        else => return c,
    };
}

fn type_kind(self: *const Resolver, n: NodeId) Decl.Kind {
    return switch (self.nk(self.core(n))) {
        .def_type, .def_type_packed => .record,
        .def_variant, .def_variant_unionsized => .variant,
        .def_trait, .def_trait_implof => .trait,
        else => .variable,
    };
}

fn decl_kind(self: *const Resolver, type_node: NodeId, value: NodeId) Decl.Kind {
    const tk = self.type_kind(value);
    return switch (self.nk(type_node)) {
        .type_fun => .function,
        .type_stcfun => .static_function,
        .type_inlfun => .inlined_function,
        .type_type => if (tk == .record) .record else .type_alias,
        .type_variant => if (tk == .variant) .variant else .type_alias,
        .type_trait => if (tk == .trait) .trait else .type_alias,
        .none => if (value != 0 and (self.nk(value) == .def_fun or self.nk(value) == .def_fun_declaration)) .function else .variable,
        else => .variable,
    };
}

fn unwrap_mods(self: *const Resolver, n0: NodeId, flags: *Decl.Flags) NodeId {
    var n = n0;
    while (true) : (n = self.arg(n, 0)) switch (self.nk(n)) {
        .mod_pub => flags.is_pub = true,
        .mod_mut => flags.is_mut = true,
        .mod_stc => flags.is_stc = true,
        else => return n,
    };
}

fn stmt_parts(self: *const Resolver, n: NodeId) Parts {
    return switch (self.nk(n)) {
        .def_var => .{ .type = self.arg(n, 0), .ids = self.list_at(n, 1, .partial__destructure) },
        .assign_typed => .{ .type = self.arg(self.arg(n, 0), 0), .ids = self.list_at(self.arg(n, 0), 1, .partial__destructure), .value = self.arg(n, 1) },
        .assign => .{ .ids = self.list_at(n, 0, .partial__destructure), .value = self.arg(n, 1) },
        else => .{},
    };
}

fn param(self: *const Resolver, n0: NodeId) Param {
    var p = Param{};
    var n = n0;
    while (true) {
        switch (self.nk(n)) {
            .partial__fun_def_param_named, .partial__type_def_param_named => p.name = self.arg(n, 1),
            .partial__fun_def_param_default, .partial__type_def_param_default => p.default = self.arg(n, 1),
            .partial__fun_def_param_where, .partial__type_def_param_where, .partial__fun_def_param_stcwhere => p.where = self.arg(n, 1),
            .partial__fun_def_param_where_else, .partial__type_def_param_where_else => p.@"else" = self.arg(n, 1),
            .partial__type_def_param_mut => p.is_mut = true,
            .partial__fun_def_param, .partial__type_def_param => {
                p.ty = self.arg(n, 0);
                return p;
            },
            else => {
                p.ty = n;
                return p;
            },
        }
        n = self.arg(n, 0);
    }
}

// unnamed parameters and fields are `$0`, `$1`, ...
fn param_name(self: *Resolver, pn: NodeId, i: usize) NamePool.Index {
    const p = self.param(pn);
    return if (p.name != 0) self.name_of(p.name) else self.name_pool.intern(dollar_names[@min(i, 63)]);
}

fn params_of(self: *const Resolver, v: NodeId) []const NodeId {
    if (self.nk(v) != .def_fun and self.nk(v) != .def_fun_declaration) return &.{};
    return self.kids(self.arg(self.arg(v, 0), 0));
}

fn fields_of_node(self: *const Resolver, c: NodeId) []const NodeId {
    return if (self.nk(c) == .partial__type_def_param_tuple) self.kids(c) else self.kids(self.arg(c, 0));
}

fn fields_of(self: *Resolver, rec: StaticPool.Index) []const NodeId {
    return self.fields_of_node(self.core(self.value_node(self.static_pool.get(rec).custom_type.decl)));
}

fn fun_type(self: *Resolver, ctx: *FnCtx, v: NodeId, category: StaticPool.FunType.Category, ret: StaticPool.Index, self_param: StaticPool.Index) StaticPool.Index {
    const header = self.arg(v, 0);
    const params = self.params_of(v);
    const off = @intFromBool(self_param != .none);
    var buf: [64]StaticPool.Index = undefined;
    buf[0] = self_param;
    for (params, 0..) |p, i| buf[i + off] = self.h07_lower_type(ctx, self.param(p).ty);
    const r = if (self.nk(header) == .partial__fun_def_header_ret) self.h07_lower_type(ctx, self.arg(header, 1)) else ret;
    return self.static_pool.intern(.{ .function_type = .{ .category = category, .params = buf[0 .. params.len + off], .ret = r } });
}

// 1 when the declaration's function type starts with the induced `*Self` (methods except `init`)
fn self_off(self: *Resolver, d: Decl.Index) usize {
    return @intFromBool(self.dp(.kind, d).* == .trait_member and self.dp(.name, d).* != .init);
}

fn same_params(self: *Resolver, a: StaticPool.Index, b: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (a == b) return true;
    if (a == .none or b == .none or sp.tag(a) != .function_type or sp.tag(b) != .function_type) return false;
    return std.mem.eql(StaticPool.Index, sp.get(a).function_type.params, sp.get(b).function_type.params);
}

fn self_ptr(self: *Resolver, t: StaticPool.Index) StaticPool.Index {
    return self.static_pool.intern(.{ .ptr_type = .{ .child = t, .mutable = true } });
}

// a value's type looked through one pointer to a record or variant (`self`, `with` / `match` on such pointers)
fn deref(self: *Resolver, t0: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const t = sp.apply_vars(&self.abstract_pool, t0);
    if (sp.get(t) != .ptr_type) return t;
    const c = sp.get(t).ptr_type.child;
    return if (sp.class(c).is_nominal or sp.class(c).is_variant) c else t;
}

fn fresh_var(self: *Resolver, origin: NodeId) StaticPool.Index {
    return self.static_pool.intern(.{ .abstract_type = self.abstract_pool.fresh(origin) });
}

fn fn_ret(self: *Resolver, d: Decl.Index) StaticPool.Index {
    self.h05_ensure_signature(d);
    const t = self.dp(.ty, d).*;
    return if (t != .none and self.static_pool.tag(t) == .function_type) self.static_pool.get(t).function_type.ret else .poison_type;
}

fn method(self: *Resolver, node: NodeId, m: Decl.Index) StaticPool.Index {
    self.node_decl[node] = m;
    return self.decl_type(m);
}

// the function a declaration stands for (`fun f = my_templ(..)` stands for the realization)
fn real(self: *Resolver, d: Decl.Index) Decl.Index {
    const v = self.dp(.value, d).*;
    return if (v != .none and self.static_pool.tag(v) == .function_value) self.static_pool.get(v).function else d;
}

fn has_where(self: *Resolver, d: Decl.Index) bool {
    for (self.params_of(self.value_node(d))) |pn| if (self.param(pn).where != 0) return true;
    return false;
}

fn length_generic(self: *Resolver, ty: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (ty == .none or sp.tag(ty) != .function_type) return false;
    for (0..sp.get(ty).function_type.params.len) |i| if (sp.has_vars(sp.apply_vars(&self.abstract_pool, sp.get(ty).function_type.params[i]))) return true;
    return false;
}

// the static length an argument gives an unlengthed parameter (`&[5]u32` for `&[]u32`), or none
fn arg_len(self: *Resolver, t0: StaticPool.Index, p0: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    var t = sp.apply_vars(&self.abstract_pool, t0);
    var p = p0;
    if (t == .poison_type) return .none;
    if (sp.get(p) == .ptr_type) {
        if (sp.get(t) != .ptr_type or (sp.get(p).ptr_type.mutable and !sp.get(t).ptr_type.mutable)) return .none;
        t = sp.get(t).ptr_type.child;
        p = sp.get(p).ptr_type.child;
    }
    if (sp.get(t) != .array_type or sp.get(p) != .array_type or sp.get(t).array_type.elem != sp.get(p).array_type.elem) return .none;
    const len = sp.get(t).array_type.len;
    return if (sp.tag(len) == .int_value) len else .none;
}

fn bind_args(self: *Resolver, params: []const NodeId, args: []const NodeId, map: []u32, partial: bool) bool {
    if (args.len > params.len or params.len > 64) return false;
    var bound: u64 = 0;
    for (args, 0..) |a, i| {
        var p: usize = i;
        if (self.nk(a) == .partial__fun_call_assigned_param) {
            const name = self.name_of(self.arg(a, 0));
            p = for (params, 0..) |pn, j| {
                if (self.param_name(pn, j) == name) break j;
            } else return false;
        }
        if (bound >> @intCast(p) & 1 != 0) return false;
        bound |= @as(u64, 1) << @intCast(p);
        map[i] = @intCast(p);
    }
    if (!partial) for (params, 0..) |pn, j| if (bound >> @intCast(j) & 1 == 0 and self.param(pn).default == 0) return false;
    return true;
}

fn link(self: *Resolver, id: NodeId, d: Decl.Index, t: StaticPool.Index) void {
    if (id == 0) return;
    self.node_decl[id] = d;
    self.node_type[id] = t;
}

fn named(self: *Resolver, a: NodeId, t: StaticPool.Index) StaticPool.Index {
    if (self.nk(a) == .partial__fun_call_assigned_param) self.node_type[self.arg(a, 0)] = t;
    return t;
}

fn bad_args(self: *Resolver, node: NodeId, params: []const NodeId, args: []const NodeId) StaticPool.Index {
    for (args) |a| if (self.nk(a) == .partial__fun_call_assigned_param) {
        const name = self.name_of(self.arg(a, 0));
        for (params, 0..) |pn, j| {
            if (self.param_name(pn, j) == name) break;
        } else return self.report(.unknown_named_argument, a, name, .none);
    };
    return self.report(.wrong_arity, node, args.len, params.len);
}

fn arg_value(self: *const Resolver, a: NodeId) NodeId {
    return if (self.nk(a) == .partial__fun_call_assigned_param) self.arg(a, 1) else a;
}

fn open_type_var(self: *Resolver, t: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (t == .none or !sp.has_vars(t)) return false;
    return switch (sp.get(t)) {
        .abstract_type => true,
        .array_type => |a| self.open_type_var(a.elem),
        .ptr_type => |p| self.open_type_var(p.child),
        .function_type => |f| for (f.params) |p| {
            if (self.open_type_var(p)) break true;
        } else self.open_type_var(f.ret),
        else => false,
    };
}

fn concrete(self: *Resolver, t: StaticPool.Index) bool {
    return t != .none and self.static_pool.tag(self.static_pool.apply_vars(&self.abstract_pool, t)) != .type_var;
}

fn is_numeric(self: *Resolver, t: StaticPool.Index) bool {
    return t != .none and (self.static_pool.class(t).is_integer or self.static_pool.class(t).is_float);
}

fn numeric(self: *Resolver, node: NodeId, t: StaticPool.Index, result: StaticPool.Index) StaticPool.Index {
    if (t == .poison_type) return t;
    if (self.is_numeric(t) or self.static_pool.tag(t) == .type_var) return if (result == .none) t else result;
    return self.report(.type_mismatch, node, t, .none);
}

fn operand(self: *Resolver, ctx: *FnCtx, n: NodeId, hint: StaticPool.Index) StaticPool.Index {
    return if (self.is_literal(n)) self.check(ctx, n, hint) else self.h09_check_expr(ctx, n, hint);
}

// both sides of a binary operator: the non-literal side first, so a literal takes its type
fn pair(self: *Resolver, ctx: *FnCtx, node: NodeId, l: NodeId, r: NodeId, hint: StaticPool.Index) StaticPool.Index {
    const swap = self.is_literal(l) and !self.is_literal(r);
    const t1 = self.operand(ctx, if (swap) r else l, hint);
    const t2 = self.operand(ctx, if (swap) l else r, t1);
    if (t1 == .poison_type or t2 == .poison_type) return .poison_type;
    if (self.static_pool.tag(t1) == .meta_type and self.static_pool.tag(t2) == .meta_type) return t1;
    var j = self.static_pool.join(&self.abstract_pool, t1, t2);
    if (j.ty == .none) j = self.static_pool.join(&self.abstract_pool, self.deref(t1), self.deref(t2)); // `self == Toggle.On`
    return if (j.ty == .none) self.report(.type_mismatch, node, t1, t2) else j.ty;
}

// a branch of if / match: unit blocks and nested ifs / matches are runit, a plain unit value is not
fn branch(self: *Resolver, ctx: *FnCtx, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    var t = self.static_pool.apply_vars(&self.abstract_pool, self.h09_check_expr(ctx, node, expected));
    if (t == .unit_type and switch (self.nk(node)) {
        .block, .if_then, .if_else, .stcif_then, .stcif_else, .match, .stcmatch => true,
        else => false,
    }) t = .runit_type;
    if (!self.concrete(expected) or t == .never_type or t == .runit_type or t == .poison_type) return t;
    if (t == .unit_type and expected != .unit_type) return self.report(.runit_mixing, node, t, expected);
    return self.h10_expect(ctx, node, t, expected);
}

fn merge(self: *Resolver, node: NodeId, acc: StaticPool.Index, t: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    if (self.concrete(expected)) return expected;
    if (acc == .none) return t;
    const j = self.static_pool.join(&self.abstract_pool, acc, t);
    if (j.ty != .none) return j.ty;
    // LIMITATION: an untyped declaration wants a value, so `x = if c: 1 else: "s"` is an error, but as a statement
    // (nothing expected) differing branch types are dropped silently
    if (expected == .none) return .unit_type;
    return self.report(if (acc == .unit_type or t == .unit_type) .runit_mixing else .type_mismatch, node, acc, t);
}

fn need_deinit(self: *Resolver, node: NodeId, t0: StaticPool.Index) void {
    const t = self.static_pool.apply_vars(&self.abstract_pool, t0);
    if (t != .poison_type and self.static_pool.lookup_member(t, .deinit) == .none)
        Doctor.h21_report(self, .no_deinit, node, @intFromEnum(t), 0);
}

fn writable(self: *Resolver, node: NodeId) Access {
    return switch (self.nk(node)) {
        .capture => self.writable(self.arg(node, 0)),
        .identifier, .identifier_self, .identifier_init, .identifier_deinit, .identifier_main => blk: {
            const d = self.node_decl[node];
            if (d == .none) break :blk .ok;
            const f = self.dp(.flags, d).*;
            break :blk if (f.is_mut or f.is_stc or self.dp(.kind, d).* == .self) .ok else .immutable;
        },
        .member => blk: {
            const base = self.through(self.arg(node, 0), true);
            break :blk if (base != .ok) base else if (self.field_mut(self.node_type[self.arg(node, 0)], self.name_of(self.arg(node, 1)))) .ok else .immutable;
        },
        .array_index => self.through(self.arg(node, 0), true),
        .dereference => self.through(self.arg(node, 0), false),
        else => .immutable,
    };
}

// writing through a parent: `*T` allows it, `&T` never, anything else if the parent itself is writable
fn through(self: *Resolver, parent: NodeId, or_place: bool) Access {
    const sp = &self.static_pool;
    const pt = self.node_type[parent];
    if (pt == .none or pt == .poison_type) return .ok;
    const t = sp.apply_vars(&self.abstract_pool, pt);
    if (sp.get(t) == .ptr_type) return if (sp.get(t).ptr_type.mutable) .ok else .through_ptr;
    return if (or_place) self.writable(parent) else .immutable;
}

fn field_mut(self: *Resolver, pt: StaticPool.Index, name: NamePool.Index) bool {
    const sp = &self.static_pool;
    if (pt == .none or pt == .poison_type) return true;
    var t = sp.apply_vars(&self.abstract_pool, pt);
    if (sp.get(t) == .ptr_type) t = sp.get(t).ptr_type.child;
    if (sp.tag(t) == .variant_case_type) t = sp.get(t).variant_case_type.payload;
    if (t == .none or sp.tag(t) != .record_type) return false;
    for (sp.get(t).custom_type.field_names, 0..) |n, i| if (n == name) return self.param(self.fields_of(t)[i]).is_mut;
    return false;
}

// what `??` / `?<-` unwrap: the payload of a case, or of the first case that has one
fn payload_of(self: *Resolver, t0: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const t = sp.apply_vars(&self.abstract_pool, t0);
    const case = switch (sp.tag(t)) {
        .variant_case_type => t,
        .variant_type => for (sp.get(t).variant_type.cases) |c| {
            if (sp.get(c).variant_case_type.payload != .none) break c;
        } else return .none,
        else => return .none,
    };
    const p = sp.get(case).variant_case_type.payload;
    if (p == .none) return .none;
    const f = sp.get(p).custom_type.field_types;
    return if (f.len == 1) f[0] else p;
}

// `<- name` binds the value, `<- a, b` destructures a record in field order
fn bind_label(self: *Resolver, label: NodeId, t: StaticPool.Index) void {
    const sp = &self.static_pool;
    if (self.nk(label) != .partial__destructure) {
        self.node_decl[label] = self.h02_declare_local(self.name_of(label), label, .arrow_binder, t);
        _ = self.set(label, t);
        return;
    }
    const rt = sp.apply_vars(&self.abstract_pool, t);
    for (self.kids(label), 0..) |id, i| {
        const ft = if (sp.tag(rt) == .record_type and i < sp.get(rt).custom_type.field_types.len) sp.get(rt).custom_type.field_types[i] else if (t == .poison_type) t else self.report(.type_mismatch, id, t, .none);
        self.node_decl[id] = self.h02_declare_local(self.name_of(id), id, .arrow_binder, ft);
        _ = self.set(id, ft);
    }
}

fn case_bit(self: *Resolver, case: StaticPool.Index, st: StaticPool.Index) u64 {
    const c = self.static_pool.get(case).variant_case_type;
    return if (c.variant == st and c.case < 64) @as(u64, 1) << @intCast(c.case) else 0;
}

fn pattern(self: *Resolver, ctx: *FnCtx, p: NodeId, st: StaticPool.Index) Pat {
    const sp = &self.static_pool;
    switch (self.nk(p)) {
        .identifier => {
            const name = self.name_of(p);
            if (name != .underscore) self.node_decl[p] = self.h02_declare_local(name, p, .pattern_binder, st);
            _ = self.set(p, st);
            return .{ .all = true };
        },
        .partial__match_case_pattern_or => {
            var r = Pat{};
            for (self.kids(p)) |alt| {
                const s = self.pattern(ctx, alt, st);
                r = .{ .mask = r.mask | s.mask, .all = r.all or s.all };
            }
            return r;
        },
        .partial__match_case_pattern_typecast => {
            const t = self.h07_lower_type(ctx, self.arg(p, 0));
            const v = self.arg(p, 1);
            self.node_decl[v] = self.h02_declare_local(self.name_of(v), v, .pattern_binder, t);
            _ = self.set(v, t);
            if (t != st and t != .poison_type and st != .poison_type and sp.coerce(&self.abstract_pool, t, st) == .incompatible) _ = self.report(.type_mismatch, p, t, st);
            return .{ .all = t == st };
        },
        .labelarrow => {
            const r = self.pattern(ctx, self.arg(p, 0), st);
            const ct = self.node_type[self.arg(p, 0)];
            const pt = self.payload_of(ct);
            self.bind_label(self.arg(p, 1), if (pt == .none) ct else pt);
            return r;
        },
        .fun_call => {
            const callee = self.arg(p, 0);
            const ct = self.h09_check_expr(ctx, callee, .none);
            const target = self.set(p, if (sp.tag(ct) == .meta_type) self.h08_eval_static(ctx, callee) else ct);
            if (target == .poison_type) { // binders still exist, as poison
                for (self.kids(self.arg(p, 1))) |a| _ = self.pattern(ctx, self.arg_value(a), target);
                return .{};
            }
            if (target != st and sp.coerce(&self.abstract_pool, target, st) == .incompatible) _ = self.report(.type_mismatch, p, target, st);
            const is_case = sp.tag(target) == .variant_case_type;
            const rec = if (is_case) sp.get(target).variant_case_type.payload else target;
            const args = self.kids(self.arg(p, 1));
            var map: [64]u32 = undefined;
            if (rec == .none or sp.tag(rec) != .record_type or !self.bind_args(self.fields_of(rec), args, &map, true)) {
                if (args.len > 0) _ = self.report(.wrong_arity, p, args.len, 0);
                return .{ .mask = if (is_case and args.len == 0) self.case_bit(target, st) else 0 };
            }
            var all = true;
            for (args, 0..) |a, i| all = self.pattern(ctx, self.arg_value(a), self.named(a, sp.get(rec).custom_type.field_types[map[i]])).all and all;
            return if (is_case) .{ .mask = if (all) self.case_bit(target, st) else 0 } else .{ .all = all };
        },
        else => { // literals, ranges and constant paths (`Toggle.On`)
            const t = self.h09_check_expr(ctx, p, st);
            if (is_range_kind(self.nk(p))) {
                const e = sp.apply_vars(&self.abstract_pool, t);
                if (t != .poison_type and st != .poison_type and sp.get(e) == .array_type and sp.coerce(&self.abstract_pool, sp.get(e).array_type.elem, st) == .incompatible) _ = self.report(.type_mismatch, p, sp.get(e).array_type.elem, st);
                return .{};
            }
            _ = self.h10_expect(ctx, p, t, st);
            if (sp.tag(t) == .variant_case_type) return .{ .mask = self.case_bit(t, st) };
            return .{ .mask = if (st == .bool_type and self.nk(p) == .boolean_true) 1 else if (st == .bool_type and self.nk(p) == .boolean_false) 2 else 0 };
        },
    }
}

fn literal_core(self: *const Resolver, node: NodeId, neg: *bool) NodeId {
    var n = node;
    while (true) switch (self.nk(n)) {
        .capture => n = self.arg(n, 0),
        .neg_num => {
            neg.* = !neg.*;
            n = self.arg(n, 0);
        },
        else => return n,
    };
}

fn is_literal(self: *const Resolver, node: NodeId) bool {
    var neg = false;
    return switch (self.nk(self.literal_core(node, &neg))) {
        .int, .float, .char, .string => true,
        else => false,
    };
}

fn unescape(raw: []const u8, buf: []u8) []const u8 {
    if (raw.len > buf.len) return raw;
    var n: usize = 0;
    var i: usize = 0;
    while (i < raw.len) : (i += 1) {
        var c = raw[i];
        if (c == '\\' and i + 1 < raw.len) {
            i += 1;
            c = switch (raw[i]) {
                'n' => '\n',
                't' => '\t',
                'r' => '\r',
                '0' => 0,
                else => raw[i],
            };
        }
        buf[n] = c;
        n += 1;
    }
    return buf[0..n];
}

// the static value of a literal: ints as u64 (i64 when negated), floats as f64
fn literal_value(self: *Resolver, node: NodeId, negated: bool) StaticPool.Index {
    const sp = &self.static_pool;
    var neg = negated;
    const n = self.literal_core(node, &neg);
    var buf: [4096]u8 = undefined;
    switch (self.nk(n)) {
        .boolean_true => return .bool_true,
        .boolean_false => return .bool_false,
        .string => return sp.intern(.{ .string = unescape(self.text(n), &buf) }),
        .float => {
            const f = std.fmt.parseFloat(f64, self.text(n)) catch return self.report(.type_mismatch, n, .none, .none);
            return sp.intern(.{ .float = .{ .ty = .f64_type, .value = if (neg) -f else f } });
        },
        else => {
            const bits: u64 = if (self.nk(n) == .char) unescape(self.text(n), &buf)[0] else std.fmt.parseInt(u64, self.text(n), 0) catch return self.report(.type_mismatch, n, .none, .u64_type);
            return sp.intern(.{ .int = if (neg) .{ .ty = .i64_type, .bits = 0 -% bits } else .{ .ty = .u64_type, .bits = bits } });
        },
    }
}

// untyped literals take the expected type when they fit, otherwise u32 / i32, then u64 / i64, floats f32
fn literal_type(self: *Resolver, node: NodeId, expected: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    var neg = false;
    const n = self.literal_core(node, &neg);
    const k = self.nk(n);
    if (k == .boolean_true or k == .boolean_false) return .bool_type;
    const v = self.literal_value(n, neg);
    var target = if (expected == .none) expected else sp.apply_vars(&self.abstract_pool, expected);
    if (k == .string and target != .none and sp.get(target) == .array_type and sp.get(target).array_type.elem == .u8_type and
        sp.tag(sp.get(target).array_type.len) == .int_value and sp.get(sp.get(target).array_type.len).int.bits >= sp.get(v).string.len) return target;
    if (v == .poison_type or k == .string) return sp.type_of(v);
    if (target != .none and sp.tag(target) == .variant_type) target = sp.single_payload(target); // `Opt8 x = 42`
    const c = if (target == .none) StaticPool.Class{} else sp.class(target);
    if (k == .float) return if (c.is_float) target else .f32_type;
    if ((c.is_integer or c.is_float) and sp.fits(v, target)) return target;
    return if (neg) (if (sp.fits(v, .i32_type)) .i32_type else .i64_type) else if (sp.fits(v, .u32_type)) .u32_type else .u64_type;
}

fn retype(self: *Resolver, v: StaticPool.Index, ty: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    if (v == .none or ty == .none or sp.tag(v) != .int_value) return v;
    if (sp.class(ty).is_integer) return sp.intern(.{ .int = .{ .ty = ty, .bits = sp.get(v).int.bits } });
    if (!sp.class(ty).is_float) return v;
    const i = sp.get(v).int;
    const signed = sp.get(i.ty) == .int_type and sp.get(i.ty).int_type.signedness == .signed;
    return sp.intern(.{ .float = .{ .ty = ty, .value = if (signed) @floatFromInt(@as(i64, @bitCast(i.bits))) else @floatFromInt(i.bits) } });
}

fn aggregate(self: *Resolver, vals: []const StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const len = sp.intern(.{ .int = .{ .ty = .u64_type, .bits = vals.len } });
    const ty = sp.intern(.{ .array_type = .{ .len = len, .elem = if (vals.len > 0) sp.type_of(vals[0]) else .unit_type } });
    return sp.intern(.{ .aggregate = .{ .ty = ty, .elems = vals } });
}

fn fold(self: *Resolver, node: NodeId, k: NodeKind, l: StaticPool.Index, r: StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    if (l == .poison_type or r == .poison_type) return .poison_type;
    const a = sp.get(l);
    const b = sp.get(r);
    const B = struct {
        fn of(x: bool) StaticPool.Index {
            return if (x) .bool_true else .bool_false;
        }
    };
    if (a == .int and b == .int) {
        const signed = for ([_]StaticPool.Index{ a.int.ty, b.int.ty }) |t| {
            if (sp.get(t) == .int_type and sp.get(t).int_type.signedness == .signed) break true;
        } else false;
        const x = a.int.bits;
        const y = b.int.bits;
        const sx: i64 = @bitCast(x);
        const sy: i64 = @bitCast(y);
        const sh: u6 = @truncate(y);
        if ((k == .binary_div or k == .binary_mod) and y == 0) return self.report(.static_eval_failed, node, l, r);
        const res: u64 = switch (k) {
            .binary_add => x +% y,
            .binary_sub => x -% y,
            .binary_mul => x *% y,
            .binary_div => if (signed) @bitCast(@divTrunc(sx, sy)) else x / y,
            .binary_mod => if (signed) @bitCast(@rem(sx, sy)) else x % y,
            .binary_shift_left => x << sh,
            .binary_shift_right => if (signed) @bitCast(sx >> sh) else x >> sh,
            .binary_num_or => x | y,
            .binary_num_xor => x ^ y,
            .binary_num_and => x & y,
            .binary_pow => blk: {
                var p: u64 = 1;
                for (0..@min(y, 64)) |_| p *%= x;
                break :blk p;
            },
            .binary_eq => return B.of(x == y),
            .binary_neq => return B.of(x != y),
            .binary_less => return B.of(if (signed) sx < sy else x < y),
            .binary_greater => return B.of(if (signed) sx > sy else x > y),
            .binary_less_eq => return B.of(if (signed) sx <= sy else x <= y),
            .binary_greater_eq => return B.of(if (signed) sx >= sy else x >= y),
            else => return self.report(.not_static, node, l, r),
        };
        return sp.intern(.{ .int = .{ .ty = a.int.ty, .bits = res } });
    }
    if ((a == .float or a == .int) and (b == .float or b == .int)) {
        const ty = if (a == .float) a.float.ty else b.float.ty;
        const x = sp.get(self.retype(l, ty)).float.value;
        const y = sp.get(self.retype(r, ty)).float.value;
        const res: f64 = switch (k) {
            .binary_add => x + y,
            .binary_sub => x - y,
            .binary_mul => x * y,
            .binary_div => x / y,
            .binary_eq => return B.of(x == y),
            .binary_neq => return B.of(x != y),
            .binary_less => return B.of(x < y),
            .binary_greater => return B.of(x > y),
            .binary_less_eq => return B.of(x <= y),
            .binary_greater_eq => return B.of(x >= y),
            else => return self.report(.not_static, node, l, r),
        };
        return sp.intern(.{ .float = .{ .ty = ty, .value = res } });
    }
    // bools, types and every other static value compare by identity (they are interned)
    return switch (k) {
        .binary_eq => B.of(l == r),
        .binary_neq => B.of(l != r),
        .binary_logic_and => B.of(l == .bool_true and r == .bool_true),
        .binary_logic_or => B.of(l == .bool_true or r == .bool_true),
        .binary_logic_xor => B.of((l == .bool_true) != (r == .bool_true)),
        else => self.report(.not_static, node, l, r),
    };
}

// a static sequence as an aggregate: ranges with static bounds, or any static array
fn static_seq(self: *Resolver, ctx: *FnCtx, seq: NodeId) StaticPool.Index {
    const sp = &self.static_pool;
    const k = self.nk(seq);
    if (!is_range_kind(k)) {
        const v = self.h08_eval_static(ctx, seq);
        return if (v == .poison_type or sp.tag(v) == .aggregate_value) v else self.report(.not_static, seq, v, 0);
    }
    if (k == .gen_lowerbound) return self.report(.not_static, seq, 0, 0);
    const two = k == .gen_incl or k == .gen_excl;
    const lo = if (two) self.h08_eval_static(ctx, self.arg(seq, 0)) else sp.intern(.{ .int = .{ .ty = .u64_type, .bits = 0 } });
    const hi = self.h08_eval_static(ctx, self.arg(seq, if (two) 1 else 0));
    if (sp.tag(lo) != .int_value or sp.tag(hi) != .int_value) return if (lo == .poison_type or hi == .poison_type) .poison_type else self.report(.not_static, seq, 0, 0);
    const end = sp.get(hi).int.bits + @intFromBool(k == .gen_incl or k == .gen_upperbound_incl);
    var vals: [256]StaticPool.Index = undefined;
    var n: usize = 0;
    var i = sp.get(lo).int.bits;
    while (i < end and n < vals.len) : ({
        i += 1;
        n += 1;
    }) vals[n] = sp.intern(.{ .int = .{ .ty = sp.get(lo).int.ty, .bits = i } });
    return self.aggregate(vals[0..n]);
}

fn static_match(self: *Resolver, ctx: *FnCtx, pat: NodeId, v: StaticPool.Index) bool {
    const sp = &self.static_pool;
    switch (self.nk(pat)) {
        .identifier => {
            const name = self.name_of(pat);
            if (name != .underscore) self.dp(.value, self.h02_declare_local(name, pat, .pattern_binder, sp.type_of(v))).* = v;
            return true;
        },
        .partial__match_case_pattern_or => {
            for (self.kids(pat)) |alt| if (self.static_match(ctx, alt, v)) return true;
            return false;
        },
        else => {
            const pv = self.try_static(ctx, pat) orelse return false;
            return pv == v or (sp.tag(pv) == .int_value and sp.tag(v) == .int_value and sp.get(pv).int.bits == sp.get(v).int.bits);
        },
    }
}

// static evaluation that leaves no diagnostics behind when the node turns out not to be static
fn try_static(self: *Resolver, ctx: *FnCtx, node: NodeId) ?StaticPool.Index {
    const mark = self.doc.diagnostics.len();
    const ty = self.node_type[node];
    const v = self.h08_eval_static(ctx, node);
    if (self.doc.diagnostics.len() == mark and v != .poison_type) return v;
    inline for (@typeInfo(Doctor.Diagnosis).@"struct".fields) |f| @field(self.doc.diagnostics.pool, f.name).head = mark;
    self.node_type[node] = ty;
    return null;
}

fn memo(self: *Resolver, key: StaticPool.AbstractKey, v: StaticPool.Index) void {
    self.static_pool.realized_abstracts.put(self.alloc, key, v) catch @panic("OOM");
}

// a trait body: one row for the body (its value is the self type), then one row per function member,
// contiguous, so member i is row + 1 + i. static members (`stc u32 MASK = ..`) are plain locals of the body.
fn trait_body(self: *Resolver, ctx: *FnCtx, body: NodeId, reserved: StaticPool.Index, self_ty: StaticPool.Index, supers: []const StaticPool.Index) StaticPool.Index {
    const sp = &self.static_pool;
    const b = self.push_decl(.empty, body, .trait, .trait_type, .{});
    const tr = if (reserved != .none) reserved else sp.reserve_nominal(b);
    self.dp(.value, b).* = if (self_ty != .none) self_ty else tr;
    var names: [64]NamePool.Index = undefined;
    var n: usize = 0;
    for (self.kids(body)) |s| {
        var flags = Decl.Flags{};
        const m = self.unwrap_mods(s, &flags);
        const parts = self.stmt_parts(m);
        if (parts.ids.len != 1 or !is_fn(self.decl_kind(parts.type, parts.value))) continue;
        names[n] = self.name_of(parts.ids[0]);
        self.node_decl[parts.ids[0]] = self.push_decl(names[n], m, .trait_member, .none, flags);
        n += 1;
    }
    for (self.kids(body)) |s| {
        var flags = Decl.Flags{};
        const parts = self.stmt_parts(self.unwrap_mods(s, &flags));
        if (parts.ids.len != 1 or !is_fn(self.decl_kind(parts.type, parts.value))) _ = self.h11_check_assign(ctx, s);
    }
    var types: [64]StaticPool.Index = undefined;
    for (0..n) |i| types[i] = self.decl_type(@enumFromInt(@intFromEnum(b) + 1 + i));
    sp.complete_nominal(tr, .{ .trait_type = .{ .decl = b, .member_names = names[0..n], .member_types = types[0..n], .supers = supers } });
    return tr;
}

fn decl_type(self: *Resolver, d: Decl.Index) StaticPool.Index {
    self.h05_ensure_signature(d);
    const t = self.dp(.ty, d).*;
    return if (t == .none) .poison_type else t;
}

// implof: every member of the trait and its supers exists with the same signature (`typeof self` read as the type),
// members with a default implementation may be left out
fn conform(self: *Resolver, ty: StaticPool.Index, own: StaticPool.Index, trait: StaticPool.Index, node: NodeId) void {
    const sp = &self.static_pool;
    for (0..sp.get(trait).trait_type.member_names.len) |i| {
        const tt = sp.get(trait).trait_type;
        if (self.nk(self.value_node(@enumFromInt(@intFromEnum(tt.decl) + 1 + i))) == .def_fun) continue;
        const name = tt.member_names[i];
        const want = tt.member_types[i];
        const m = if (own == .none) StaticPool.Member.none else sp.lookup_member(own, name);
        if (m != .trait_method) {
            Doctor.h21_report(self, .trait_member_missing, node, @intFromEnum(name), @intFromEnum(trait));
            continue;
        }
        const have = sp.apply_vars(&self.abstract_pool, sp.get(own).trait_type.member_types[m.trait_method.index]);
        const w = sp.apply_vars(&self.abstract_pool, want);
        if (!self.same_sig(have, w, trait, ty)) Doctor.h21_report(self, .trait_signature_mismatch, node, @intFromEnum(name), @intFromEnum(trait));
    }
    for (0..sp.get(trait).trait_type.supers.len) |i| self.conform(ty, own, sp.get(trait).trait_type.supers[i], node);
}

fn same_sig(self: *Resolver, have: StaticPool.Index, want: StaticPool.Index, trait: StaticPool.Index, ty: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (have == want or have == .poison_type or want == .poison_type) return true;
    if (sp.tag(have) != .function_type or sp.tag(want) != .function_type) return false;
    const h = sp.get(have).function_type;
    const w = sp.get(want).function_type;
    if (h.params.len != w.params.len) return false;
    for (h.params, w.params) |a, b| if (!self.same_as(a, b, trait, ty)) return false;
    return self.same_as(h.ret, w.ret, trait, ty);
}

// a == b with the trait read as the implementing type, also behind pointers (the induced `*Self`)
// LIMITATION: the trait is only replaced at the top level or behind pointers, not inside arrays or function types
fn same_as(self: *Resolver, a: StaticPool.Index, b: StaticPool.Index, trait: StaticPool.Index, ty: StaticPool.Index) bool {
    const sp = &self.static_pool;
    if (a == b or a == .poison_type or (b == trait and a == ty)) return true;
    return sp.get(a) == .ptr_type and sp.get(b) == .ptr_type and sp.get(a).ptr_type.mutable == sp.get(b).ptr_type.mutable and
        self.same_as(sp.get(a).ptr_type.child, sp.get(b).ptr_type.child, trait, ty);
}
