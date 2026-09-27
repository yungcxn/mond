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
    // walk only the top-level roots (not the whole tree) and register every global declaration
    // in `globals`, so bodies can use globals that are declared further down the file
    // unwrap mod_pub / mod_mut / mod_stc into decl flags here
    // same-named functions are chained into an overload list, anything else with a taken name is duplicate_declaration
    // top-level untyped assigns (`induced = 1337`) are declarations as long as the name is new
    _ = self;
}

fn s2_check_globals(self: *Resolver) void {
    // for every global: h05_ensure_signature, then h06_check_body
    // many are already done at this point because some body needed them on demand - the state skips them
    _ = self;
}

fn s3_apply_inferred_types(self: *Resolver) void {
    // skip entirely when vars.count() == 0
    // otherwise one linear sweep over node_type and decls.ty: pool.apply_vars on every entry that has_vars
    // a var that is still unbound is uninferable_type (e.g. `x = [];` never used with an element)
    _ = self;
}

fn s4_check_entry_point(self: *Resolver) void {
    // `main` exists once and has an accepted signature (no params, or argc / argv; returns unit or an int)
    _ = self;
}

// ------------------------------------------------------------------------------------------ //
// scopes and names
// ------------------------------------------------------------------------------------------ //

fn h01_lookup(self: *Resolver, name: NamePool.Index) Decl.Index {
    // scan local_names from the top down, then fall back to `globals`
    _ = .{ self, name };
    @panic("unimplemented");
}

fn h02_declare_local(self: *Resolver, name: NamePool.Index, node: ParseTree.NodeId, kind: Decl.Kind, ty: StaticPool.Index) Decl.Index {
    // push a decl row and (name, decl) onto the local stack
    _ = .{ self, name, node, kind, ty };
    @panic("unimplemented");
}

fn h03_push_scope(self: *Resolver) void {
    // remember local_names.len in scope_marks
    _ = self;
    @panic("unimplemented");
}

fn h04_pop_scope(self: *Resolver) void {
    // truncate the local stack back to the last mark
    _ = self;
    @panic("unimplemented");
}

// ------------------------------------------------------------------------------------------ //
// declarations
// ------------------------------------------------------------------------------------------ //

fn h05_ensure_signature(self: *Resolver, decl: Decl.Index) void {
    // signature_ready or later -> return, resolving_signature -> declaration_cycle, unresolved -> resolve now
    // functions: parameter types + return type; an induced return type becomes a fresh type var
    // types / variants / traits: h19_check_type_def
    // stc values and aliases (`fun sub_from_templ = my_templ(i32, false)`): h08_eval_static
    // untyped globals (`induced = 1337`): the type of the value, via h09 with no expected type
    // figure out: methods - is the implicit self parameter part of the function type
    // figure out: stcfun with two parameter tuples - the first tuple is static, the second belongs to the produced function
    _ = .{ self, decl };
    @panic("unimplemented");
}

fn h06_check_body(self: *Resolver, decl: Decl.Index) void {
    // set up an FnCtx, push a scope, declare the parameters (and self, $0.. for unnamed ones), h09 on the body, pop
    // `:` bodies are one expression whose value is the return value; `{}` bodies return through `ret`
    // where / where-else / stcwhere: predicates must be bool, stcwhere must evaluate true via h08,
    //   the else value is checked against the param type, or it is a `ret` checked against the return type
    // figure out: may a where expression see later parameters or only the ones before it
    _ = .{ self, decl };
    @panic("unimplemented");
}

fn h07_lower_type(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    // turn a type expression into a pool index: primitives, [n]T, []T, *T, &T, `(..) -> ..` signatures,
    //   `A || B` unions, `typeof x`, names of types, stcfun calls (`Vec2T(i32)`, via h20)
    // array lengths are static expressions - h08; an unlengthed array `[]T` gets a fresh var as its length
    // an unlengthed array anywhere in a parameter type makes the function length-generic: `[]u8 arr` (by value),
    //   `&[]u8 arr` (immutable pointer), `*[]u8 arr` (mutable pointer). it is compiled once per
    //   length used, like a stcfun type-realization, and `arr.len` is a static value inside each generic/template
    _ = .{ self, ctx, node };
    @panic("unimplemented");
}

fn h08_eval_static(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    // tiny interpreter directly over the parse tree for stc values, stcif / stcmatch / stcwhile / stcfor / stcloop,
    //   sizeof, assertsize, stcwhere, array lengths, stcfun arguments
    // every step decrements static_budget
    // figure out: static locals need their own value stack next to the local stack
    _ = .{ self, ctx, node };
    @panic("unimplemented");
}

// ------------------------------------------------------------------------------------------ //
// expressions
// ------------------------------------------------------------------------------------------ //

fn h09_check_expr(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    // the heart: switch on the node kind, check the children, write node_type[node] and return it
    // expected is the type the context wants (or none) - it flows down into literals, `[]`, lambdas, `Opt8 x = 42`
    // every node kind has a home:
    //   int / float / string / char / true / false            -> h10_expect (literal rules live there)
    //   identifier, self / init / deinit / main, $it, $0..     -> h01_lookup, node_decl[node] = found decl
    //   capture `( .. )`                                       -> the inner expression
    //   block                                                  -> push scope, every statement, pop
    //   def_var / assign / assign_typed / mod_* / destructure  -> h11_check_assign
    //   += -= *= /= %=, ++ / -- (pre / post)                   -> h18_check_place + numeric operand
    //   binary arithmetic / bitwise                            -> both sides numeric, result via join of the two
    //   comparisons, and / or / xor / &&, !                    -> bool
    //   neg_num                                                -> numeric, a negated untyped literal is signed (i32 / i64)
    //   fun_call, with                                         -> h12_check_call
    //   member                                                 -> h13_check_member
    //   array_index, .*, .&                                    -> index must be an integer, pointer rules, auto-deref
    //   array, array_empty                                     -> element type from expected, else from the elements, `[]` alone -> fresh var
    //   as / oftype / typeof / sizeof                          -> pool.cast, bool, type value, u64 via h08
    //   if / stcif                                             -> h15_check_branching
    //   while / for / loop (+ stc and repeat forms), ranges    -> h16_check_loop
    //   match / stcmatch                                       -> h14_check_match
    //   ret / ret_void                                         -> h10_expect against ctx.ret_type, type never
    //   brk / cont                                             -> ctx.loop_depth > 0, type never
    //   do                                                     -> check the inner expression, type runit
    //   defer, `x defer deinit`, deinit x                      -> checked in place, deinit needs a deinit member (no_deinit)
    //   ??, ?<-, <-                                            -> h17_check_unwrap
    //   def_fun (lambdas, local functions)                     -> h05 + h06 on the spot
    //   def_fun_declaration                                    -> a function type
    //   def_type / def_variant / def_trait (local)             -> h19_check_type_def
    //   type expressions in value position (`Opt(i32)`, `[4]u8`) -> h07_lower_type, the value is a type
    // figure out: definite initialization (`mut u64 x;` read before write) - a bitset over locals saved / merged at branches
    _ = .{ self, ctx, node, expected };
    @panic("unimplemented");
}

fn h10_expect(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, actual: StaticPool.Index, expected: StaticPool.Index) StaticPool.Index {
    // the one place where "what an expression has" meets "what its context wants"
    // untyped int literal: expected type (range checked with pool.fits), else u32, i32 when negated, u64 / i64 when it does not fit 32 bit
    // untyped float literal: expected type, else f32
    // an unbound var as expected type counts as no expectation: the literal takes its default and the var is bound to it
    // everything else: pool.coerce (which unifies when vars are involved); incompatible -> type_mismatch, node gets poison
    _ = .{ self, ctx, node, actual, expected };
    @panic("unimplemented");
}

fn h11_check_assign(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    // typed: declare with the given type, check the value against it (h10)
    // untyped: name visible -> assign (h18 for mutability), otherwise declare with the value's type (may be a var)
    // destructure: existing names are assigned, new ones declared, all share one type - from an existing name, else from joining the values
    // multi values (`= 1, 2`) pair up with the destructured names, a single value is shared by all (figure out)
    // figure out: existing names with different types in one destructure - destructure_type_conflict or join
    _ = .{ self, ctx, node };
    @panic("unimplemented");
}

fn h12_check_call(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    // callee kinds: function / overload list, type constructor (`Person(name = ..)`), variant case (`Event.Key(13)`),
    //   stcfun (-> h20_instantiate), a value of function type (`op(a, b)`), a lambda called directly
    // match positional + named arguments to parameters, fill missing ones from defaults in the parse tree
    // `x with (name = ..)`: a copy of record x, the named arguments must be fields
    // overloads: keep the candidates whose parameter types accept the arguments, then pick the most specific:
    //   exact type match beats a coercion, fixed length array beats unlengthed (`&[1]u8` over `&[]u8`),
    //   a parameter with where beats the same parameter without
    //   several left that differ only by runtime where-clauses -> dispatch at runtime, most specific first (the lowerer emits the chain)
    //   several left that are equally specific -> ambiguous_overload
    // calling a function whose signature is still in progress uses its type var return type - unify decides later
    // a length-generic function (`[]u8` / `&[]u8` / `*[]u8` param): the argument's array length picks the generic/template realization via h20,
    //   with the lengths as args; overload specificity is decided before instantiating
    _ = .{ self, ctx, node, expected };
    @panic("unimplemented");
}

fn h13_check_member(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    // check the parent, then pool.lookup_member (auto-derefs one pointer level like zig)
    // `Type.Case`, `Type.init` and `Stream(i32).None` are members of a type value, not of an generic/template realization
    // a parent whose type is still an unbound var cannot be looked into yet -> uninferable_type (needs an annotation)
    _ = .{ self, ctx, node };
    @panic("unimplemented");
}

fn h14_check_match(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    // per arm: push a scope, check the pattern against the scrutinee type (declares binders), check the body, pop
    // patterns: literals, `,` / `|` or-lists, ranges, `_`, binders, variant cases with payload binders,
    //   struct patterns with named fields, type-cast patterns (`AnyFixed32 x`), label arrows (`Case <- v`)
    // arm values are joined like if branches (runit rules)
    // exhaustiveness: variants / bools -> a small bitset of covered cases; ints / strings need `_` or a binder
    // redundancy: an arm whose cases are all covered already, or anything after `_`
    // stcmatch: the scrutinee is static, only the matching arm is checked
    // figure out: untagged variants only in stcmatch, type-cast patterns only for homogenic ones
    _ = .{ self, ctx, node, expected };
    @panic("unimplemented");
}

fn h15_check_branching(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    // condition is bool (or a `?<-` / `<-` expression, h17)
    // then branch gets its own scope, so binders of the condition are visible there but hidden in else
    // used as a value: pool.join of both branches; brk / ret / cont (never), nested if / match and blocks
    //   count as runit, a plain unit call needs `do`, plain unit + value is runit_mixing
    // no else and used as a value -> the missing branch is unit
    // stcif: condition via h08, only the chosen branch is checked
    _ = .{ self, ctx, node, expected };
    @panic("unimplemented");
}

fn h16_check_loop(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    // while: bool condition, optional repeat statement; for: a sequence (array, range, Iterable) with $it or a named variable;
    //   loop: optional repeat statement; stc forms run through h08
    // ranges (`1..=10`, `..<n`, `1..`): both bounds one integer type, only valid as a for sequence or a match pattern
    // ctx.loop_depth++ around the body so brk / cont know they are inside
    // used as a value: an array of the body values (`[]i32 arr = while j < 50: j++`)
    // figure out: what a brk yields inside a loop used as a value
    _ = .{ self, ctx, node, expected };
    @panic("unimplemented");
}

fn h17_check_unwrap(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId, expected: StaticPool.Index) StaticPool.Index {
    // `x ??`: x is a self-tagged variant, the result is its payload type
    // `x ?? fallback`: fallback is checked against the payload type (never is fine: `?? ret 1`)
    // `x ?<- name`: bool, declares name with the payload type in the current expression scope
    // `x <- name` / `x <- a, b`: the value itself, declares the names (destructured from a record for several)
    // binders live in their own expression and below it, never in following statements
    _ = .{ self, ctx, node, expected };
    @panic("unimplemented");
}

fn h18_check_place(self: *Resolver, ctx: *FnCtx, node: ParseTree.NodeId) StaticPool.Index {
    // the left side of a write: identifier / member / index / deref chain
    // writable only through `mut` declarations, `mut` fields and `*T` pointers (never `&T`)
    // figure out: is self mutable in methods by default
    _ = .{ self, ctx, node };
    @panic("unimplemented");
}

// ------------------------------------------------------------------------------------------ //
// types, generics, diagnostics
// ------------------------------------------------------------------------------------------ //

fn h19_check_type_def(self: *Resolver, ctx: *FnCtx, decl: Decl.Index, node: ParseTree.NodeId) StaticPool.Index {
    // records (`*(..)`, `**(..)` packed), variants (`+(..)`, `++(..)`), traits (`!{..}`, `implof .. !{..}`)
    // reserve_nominal first, so fields can point back at the type (`*Tree`), then fields / cases / members, then complete_nominal
    // field and payload defaults and where-clauses are checked against the field type
    // variants: tag values must fit the tag type (tag_overflow), `tagof self` needs a niche (self_tag_without_niche)
    // assertsize: compare pool.layout(ty).size with the static value or type size (assertsize_failed)
    // trait body members become methods; implof: every member of every listed trait (and their supers) must exist
    //   with a matching signature, `typeof self` replaced by the type (trait_member_missing / trait_signature_mismatch),
    //   members with a default implementation may be left out
    _ = .{ self, ctx, decl, node };
    @panic("unimplemented");
}

fn h20_instantiate(self: *Resolver, generic: Decl.Index, args: StaticPool.Index) StaticPool.Index {
    // look up StaticPools `realized_abstracts`; on a miss evaluate the stcfun with the static args bound and memoize the result
    // length-generic functions: bind every unlengthed parameter's length to its arg, then check the body as a new declaration
    // the produced function / type is checked like any declaration (h05 / h06 / h19)
    // figure out: recursion limit for realized abstracts that realize themselves forever
    //   (`arr_sum` recursing on `&[arr.len-1]u32` is fine because the `&[0]u32` overload ends it; a missing base case would not end)
    _ = .{ self, generic, args };
    @panic("unimplemented");
}
