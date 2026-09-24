const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;
const DynBuf = @import("ds/dynbuf.zig").DynBuf;
const Lexer = @import("Lexer.zig");
const ParseTree = @import("ParseTree.zig");
const ts = @import("type_system.zig");

const Resolver = @This();

const NodeId = ParseTree.NodeId;
const TypeId = ts.TypeId;
const ValueId = ts.ValueId;
const NameId = ts.NameId;
const DeclId = ts.DeclId;
const Span = ts.Span;

pub const ScopeId = enum(u32) { global = 0, none = std.math.maxInt(u32), _ };
pub const OverloadSetId = enum(u32) { none = std.math.maxInt(u32), _ };
pub const InstanceId = enum(u32) { none = std.math.maxInt(u32), _ };

pub const Role = enum(u8) {
    unclassified,
    value,
    place,
    type_expr,
    static_value,
    pattern,
    binder,
    decl_name,
    member_name,
    arg_name,
    label,
};

pub const NodeFlags = packed struct(u8) {
    is_static: bool = false,
    is_place: bool = false,
    is_mut_place: bool = false,
    diverges: bool = false,
    pruned: bool = false,
    implicit: bool = false,
    poisoned: bool = false,
    _pad: u1 = 0,
};

pub const NodeInfo = struct {
    parent: NodeId,
    slot: u16,
    role: Role,
    flags: NodeFlags,
    scope: ScopeId,
    name: NameId,
    decl: DeclId,
    ty: TypeId,
    static: ValueId,
};

pub const ScopeKind = enum(u8) {
    global,
    static_params,
    params,
    block,
    type_body,
    trait_body,
    variant_body,
    loop_body,
    for_binding,
    match_arm,
    arrow_binding,
};

pub const Scope = struct {
    parent: ScopeId,
    kind: ScopeKind,
    depth: u16,
    owner: NodeId,
    decls: Span,
};

pub const DeclKind = enum(u8) {
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
    implicit_it,
    implicit_positional,
    implicit_self,
    init_fn,
    deinit_fn,
    main_fn,
};

pub const DeclFlags = packed struct(u16) {
    is_pub: bool = false,
    is_mut: bool = false,
    is_stc: bool = false,
    is_global: bool = false,
    is_recursive: bool = false,
    is_declaration_only: bool = false,
    has_induced_type: bool = false,
    is_overloaded: bool = false,
    is_generic: bool = false,
    _pad: u7 = 0,
};

pub const DeclState = enum(u8) {
    unvisited,
    signature_in_progress,
    signature_done,
    body_in_progress,
    body_done,
    failed,
};

pub const Decl = struct {
    name: NameId,
    scope: ScopeId,
    node: NodeId,
    kind: DeclKind,
    flags: DeclFlags,
    state: DeclState,
    order: u32,
    ty: TypeId,
    static: ValueId,
    overload: OverloadSetId,
    params: Span,
};

pub const ParamFlags = packed struct(u8) {
    is_unnamed: bool = false,
    is_static: bool = false,
    has_default: bool = false,
    has_where: bool = false,
    has_stcwhere: bool = false,
    has_where_else: bool = false,
    _pad: u2 = 0,
};

pub const ParamInfo = struct {
    name: NameId,
    ty: TypeId,
    flags: ParamFlags,
    default_node: NodeId,
    where_node: NodeId,
    where_else_node: NodeId,
};

pub const EdgeKind = enum(u8) { signature, body, member_guess };

pub const Component = struct {
    members: Span,
    is_recursive: bool,
};

pub const OverloadSet = struct {
    name: NameId,
    scope: ScopeId,
    members: Span,
    specificity: Span,
};

pub const InstanceState = enum(u8) { queued, checking, done, failed };

pub const Instance = struct {
    generic: DeclId,
    args: ValueId,
    result: ValueId,
    scope: ScopeId,
    state: InstanceState,
};

pub const Guard = struct {
    decl: DeclId,
    param: u32,
    predicate: NodeId,
    else_node: NodeId,
    is_static: bool,
};

pub const DecisionKind = enum(u8) { switch_tag, test_eq, test_range, bind, arm, fail };

pub const Decision = struct {
    kind: DecisionKind,
    scrutinee: NodeId,
    test_value: ValueId,
    on_match: u32,
    on_fail: u32,
};

pub const Severity = enum(u8) { note, warning, @"error" };

pub const DiagCode = enum(u16) {
    undefined_name,
    duplicate_declaration,
    use_before_declaration,
    ambiguous_name,
    unknown_member,
    type_mismatch,
    not_a_type,
    not_callable,
    wrong_arity,
    unknown_named_argument,
    no_matching_overload,
    ambiguous_overload,
    overlapping_overloads,
    invalid_cast,
    runit_mixing,
    recursive_by_value_type,
    unresolved_cycle,
    assertsize_failed,
    tag_overflow,
    self_tag_without_niche,
    trait_member_missing,
    trait_signature_mismatch,
    not_static,
    static_eval_failed,
    stcwhere_violated,
    brk_outside_loop,
    cont_outside_loop,
    ret_type_mismatch,
    unreachable_code,
    non_exhaustive_match,
    redundant_match_arm,
    assign_to_immutable,
    write_through_immutable_pointer,
    use_before_initialization,
    destructure_type_conflict,
    uninferable_type,
    unused_value,
};

pub const Diagnostic = struct {
    code: DiagCode,
    severity: Severity,
    node: NodeId,
    a: u32,
    b: u32,
};

alloc: std.mem.Allocator,
io: std.Io,
tree: *const ParseTree,
src_bytes: []const u8,
roots: []const NodeId,

names: ts.NamePool,
pool: ts.Pool,
metavars: ts.MetaVars,

nodes: SoD(NodeInfo),
postorder: DynBuf(NodeId),

scopes: SoD(Scope),
scope_decls: DynBuf(DeclId),
decls: SoD(Decl),
params: SoD(ParamInfo),

dep_offsets: DynBuf(u32),
dep_targets: DynBuf(DeclId),
dep_kinds: DynBuf(EdgeKind),
decl_component: DynBuf(u32),
components: DynBuf(Component),
component_members: DynBuf(DeclId),
waves: DynBuf(Span),

overload_sets: SoD(OverloadSet),
overload_members: DynBuf(DeclId),
overload_edges: DynBuf(u32),

instances: SoD(Instance),
instance_map: std.AutoHashMapUnmanaged(u64, InstanceId),
instance_queue: DynBuf(InstanceId),

guards: SoD(Guard),
decisions: SoD(Decision),

diagnostics: SoD(Diagnostic),
error_count: u32,

scratch: DynBuf(u32),
worklist: DynBuf(u32),

pub fn init(
    alloc: std.mem.Allocator,
    io: std.Io,
    tree: *const ParseTree,
    src_bytes: []const u8,
    roots: []const NodeId,
) Resolver {
    // allocate every per-node table once, sized to tree.ast_nodes.len(), and fill with none/unclassified
    // figure out: initial capacities for decls, scopes, extra buffers (estimate from node count?)
    // figure out: one arena per phase (freed after gate) vs gpa everywhere
    // figure out: who owns names/pool/metavars - resolver or a longer living compilation context
    _ = .{ alloc, io, tree, src_bytes, roots };
    @panic("unimplemented");
}

pub fn deinit(self: *Resolver) void {
    // free every table, the pools and the instance map
    // figure out: which tables survive into highlowerer and must not be freed here
    _ = self;
    @panic("unimplemented");
}

pub fn resolve(self: *Resolver) !void {
    // figure out: stop at the first failing gate or keep going in "poisoned" mode for more diagnostics
    // figure out: steps 15-18 are demand driven inside a component - do you need a query function instead of fixed order
    // figure out: where the parallel dispatch of waves (step 23) lives - here or inside the step
    self.s01_link_parents();
    self.s02_linearize_postorder();
    self.s03_intern_names();
    self.s04_classify_roles();
    self.s05_flatten_modifiers();
    try self.gate();

    self.s06_build_scopes();
    self.s07_collect_declarations();
    self.s08_index_scopes();
    self.s09_bind_implicit_names();
    self.s10_resolve_lexical_names();
    try self.gate();

    self.s11_build_dependency_graph();
    self.s12_condense_components();
    self.s13_schedule_waves();
    try self.gate();

    self.s14_seed_type_pool();
    for (self.components.sliced()) |component| {
        self.s15_lower_type_expressions(component);
        self.s16_resolve_signatures(component);
        self.s17_evaluate_static_declarations(component);
        self.s18_compute_layouts(component);
    }
    try self.gate();

    self.s19_close_trait_hierarchy();
    self.s20_check_trait_conformance();
    self.s21_build_overload_sets();
    self.s22_order_overload_specificity();
    try self.gate();

    for (self.waves.sliced()) |wave| self.s23_check_bodies(wave);
    while (self.s24_drain_instantiations()) {}
    try self.gate();

    self.s25_check_control_flow();
    self.s26_check_patterns();
    self.s27_check_mutability();
    self.s28_check_definite_initialization();
    self.s29_lower_where_guards();
    try self.gate();

    self.s30_zonk_types();
    self.s31_freeze();
}

fn gate(self: *Resolver) !void {
    // figure out: print diagnostics here per phase or collect all and print once at the end
    // figure out: which diagnostics are fatal for the next phase and which are not (warnings never are)
    if (self.error_count != 0) return error.ResolveFailed;
}

fn s01_link_parents(self: *Resolver) void {
    // walk every node once and write parent + slot for each of its children
    // figure out: generic child iteration via the nk_childc table (one / two / many / data)
    // figure out: slot meaning for list children (list index) vs struct fields (0 / 1), is u16 enough
    // figure out: roots get parent 0 (the `none` node) - is that clean enough to detect top level
    _ = self;
}

fn s02_linearize_postorder(self: *Resolver) void {
    // produce a flat postorder array so all later passes are plain loops instead of recursion
    // figure out: explicit stack type for deep nesting (fixedstack capacity vs dynbuf)
    // figure out: do scopes need preorder too (enter/exit events) or can step 06 work on postorder
    // figure out: are pruned stcif/stcmatch branches skipped here or only later
    _ = self;
}

fn s03_intern_names(self: *Resolver) void {
    // intern every identifier span into a NameId and write node.name
    // figure out: hash function (wyhash vs fxhash) and max load factor of the table
    // figure out: `$0`, `$1` - intern as normal names or decode to a positional index right away
    // figure out: identifier_self/init/deinit/main nodes map to the fixed NameIds without touching bytes
    _ = self;
}

fn s04_classify_roles(self: *Resolver) void {
    // assign every node a role from (parent kind, child slot)
    // figure out: build that mapping as a comptime table next to DefTable field names
    // figure out: ambiguous slots - def_var.type is a type expr but `Opt(i32) x` is a call, fun_call callee may be a type constructor
    // figure out: which identifiers must stay unclassified until step 10 knows if they are types or values
    // figure out: inside match patterns, which identifiers are binders (`x`) vs constants (`CommonCode.Ok`) vs wildcard (`_`)
    _ = self;
}

fn s05_flatten_modifiers(self: *Resolver) void {
    // collapse mod_pub / mod_mut / mod_stc chains into declaration flags
    // figure out: where flags live before decls exist (node flags scratch or directly consumed in step 07)
    // figure out: illegal combinations - pub inside a function body, mut + stc, duplicated modifiers
    // figure out: partial__type_def_param_mut (fields, variant payloads) handled the same way or separately
    _ = self;
}

fn s06_build_scopes(self: *Resolver) void {
    // open a scope for every node kind that introduces names and write node.scope for all nodes
    // figure out: exact list of scope opening kinds (block, fun params, type/trait/variant body, loops, match arms, if-then for `<-` / `?<-`)
    // figure out: stcfun with two parameter tuples = two nested scopes (static_params then params)
    // figure out: may a where / where-else expression see later parameters or only the ones before it
    // a `<-` / `?<-` binder is visible in the rest of its own expression and everything below it (then branch, match arms, loop bodies), never in the following statements of the same scope
    // a binder from an if condition is hidden in the else branch - so the then branch needs its own scope, the else branch stays outside of it
    _ = self;
}

fn s07_collect_declarations(self: *Resolver) void {
    // create a Decl for every name introducing node, with its declaration order index
    // figure out: full list of declaring nodes - def_var, untyped assign, destructure, fun params, fields, variant cases, trait members, pattern binders, for variables
    // an untyped assign `bob = ...` declares bob if no bob is visible yet, otherwise it assigns - so it can only become a decl once step 10 knows what is visible
    // an induced decl gets a metavar type that its assigned value fixes in step 23
    // figure out: create tentative decls here and drop them in step 10, or create them lazily in step 10
    // untyped destructure (`aa, cc = 7, 8`) may mix: existing names are assigned, the others are declared
    // all names of one destructure share one type - if one of them already exists, the new ones take its type
    // figure out: existing names of one destructure with different types - destructure_type_conflict error, or join them
    // figure out: typed decl with a name that already exists in an outer scope - shadowing allowed?
    // figure out: overloaded functions share a name - duplicates allowed only for function kinds
    // figure out: ParamInfo extraction from the partial__fun_def_param_* wrapper chains (named / default / where / stcwhere / else)
    _ = self;
}

fn s08_index_scopes(self: *Resolver) void {
    // sort decls by (scope, name) so every scope owns one contiguous span
    // figure out: radix sort vs std.sort - must be stable to keep declaration order among duplicates
    // figure out: size threshold from which a scope gets its own hash index instead of binary search
    // figure out: duplicate declaration detection happens here (same scope, same name, not overloadable)
    _ = self;
}

fn s09_bind_implicit_names(self: *Resolver) void {
    // bind implicit names - $it in for bodies, $0.. for unnamed params, self in type / trait / variant bodies
    // figure out: $it in nested for loops - innermost only, or a way to reach outer ones
    // figure out: `p.$0` on tuple-like types is a member access, not a lexical name - exclude it here
    // figure out: what self means inside a trait body that has no concrete type yet (`typeof self`)
    _ = self;
}

fn s10_resolve_lexical_names(self: *Resolver) void {
    // resolve every identifier use to a DeclId by walking up the scope chain
    // figure out: order rule - globals are order independent, locals need decl.order < use order
    // figure out: identifiers that name an overload set - store an OverloadSetId instead of a DeclId?
    // figure out: member names and named call arguments (`name = "x"`) are skipped here and resolved in step 23
    // figure out: `_` never resolves, unresolved identifiers in pattern position become binders
    // untyped assigns are decided here in declaration order - visible name -> assign, otherwise -> declare (see step 07)
    _ = self;
}

fn s11_build_dependency_graph(self: *Resolver) void {
    // build csr edges decl -> referenced decls, each tagged signature / body / member_guess
    // figure out: exact split of signature deps (types, defaults, static args) vs body deps
    // figure out: member_guess edges for `x.foo` (all decls named foo) - how coarse is acceptable
    // figure out: an induced return type turns body edges into signature edges for callers
    _ = self;
}

fn s12_condense_components(self: *Resolver) void {
    // strongly connected components over the dependency graph, fill components + decl_component
    // figure out: iterative tarjan / pearce with an explicit stack (no recursion)
    // figure out: which cycles are legal (mutual recursion through bodies) and which are errors (signature cycles, by-value type cycles)
    // figure out: tarjan emits components in reverse topological order - confirm the direction you need
    _ = self;
}

fn s13_schedule_waves(self: *Resolver) void {
    // kahn levels over the component dag, one wave = components without dependencies between each other
    // figure out: only body edges matter for waves or signature edges too
    // figure out: wave granularity vs thread overhead - merge tiny waves, split huge ones
    _ = self;
}

fn s14_seed_type_pool(self: *Resolver) void {
    // intern all primitive types and values so their Index equals the ts.Index enum order
    // figure out: assert this ordering once at startup (debug only)
    _ = self;
}

fn s15_lower_type_expressions(self: *Resolver, component: Component) void {
    // evaluate every type position node of this component into a TypeId
    // figure out: nominal placeholders for recursive types (`*Tree` inside Tree) via fresh_nominal / complete_nominal
    // figure out: array lengths need static evaluation - call into step 17 on demand
    // figure out: type_array_unlengthed - slice, or array whose length is induced from the initializer
    // figure out: variant `||` - flatten nested unions, reject overlapping cases or tag values?
    _ = .{ self, component };
}

fn s16_resolve_signatures(self: *Resolver, component: Component) void {
    // build function types, record fields, variant payloads and trait member types
    // figure out: induced return types - leave a metavar and fill it after the body check
    // figure out: default values checked here (need expected type) or in step 23
    // figure out: methods - is the implicit self parameter part of the function type or not
    _ = .{ self, component };
}

fn s17_evaluate_static_declarations(self: *Resolver, component: Component) void {
    // run the comptime interpreter for stc decls, stcfun calls in signatures, assertsize, sizeof
    // figure out: interpret the ast directly or compile static code to a small bytecode first
    // figure out: memo key = (generic decl, interned argument tuple), detect infinite instantiation (depth limit?)
    // figure out: evaluation budget (like zig's branch quota) and how errors inside static code are reported
    // figure out: forbid reading runtime values in static context - enforce via node flags
    _ = .{ self, component };
}

fn s18_compute_layouts(self: *Resolver, component: Component) void {
    // compute size, alignment and field offsets of every type in this component
    // figure out: bool as 1 byte, or 1 bit inside packed types
    // figure out: tag placement and tag type inference when no `tagof` is given
    // figure out: `tagof self` niche search - which payload bit patterns are invalid and can encode the other cases
    // figure out: `++(` vs `+(` size rules, and assertsize against a type (`assertsize u32`) vs a number
    _ = .{ self, component };
}

fn s19_close_trait_hierarchy(self: *Resolver) void {
    // transitive closure of implof per type and per trait, stored as bitsets
    // figure out: bitset width bound by trait count, or a sparse fallback for huge programs
    // figure out: generic trait instances (`Comparable(Money)`) are separate traits in the closure
    _ = self;
}

fn s20_check_trait_conformance(self: *Resolver) void {
    // check that every type provides each trait member with a matching signature
    // figure out: signature matching with `typeof self` / self type substitution
    // figure out: default implementations - copied into the type or referenced from the trait
    // figure out: two traits requiring members with the same name
    _ = self;
}

fn s21_build_overload_sets(self: *Resolver) void {
    // group same-named functions of one scope into overload sets
    // figure out: local functions - shadow a global set or join it
    // figure out: may a non-function share its name with an overload set
    _ = self;
}

fn s22_order_overload_specificity(self: *Resolver) void {
    // order overloads by specificity using parameter types and where predicates
    // figure out: how smart predicate implication is (syntactic equality, intervals over comparisons, smt later?)
    // figure out: array length overloads (&[0]u8, &[1]u8, &[]u8) - exact length beats unlengthed
    // figure out: incomparable overlaps - error statically or fall back to declaration order
    _ = self;
}

fn s23_check_bodies(self: *Resolver, wave: Span) void {
    // type check every body in the wave - check against an expected type when there is one, infer otherwise
    // untyped int literal - takes the expected type if there is one (range checked with fits), otherwise u32, or i32 when directly negated
    // untyped float literal - expected type or f32
    // figure out: expected type propagation into lambdas, `[]` and payload shorthand (`Opt8 x = 42`)
    // an untyped int literal that does not fit into 32 bit is upcast to u64, or i64 when negated
    // figure out: member lookup order - field, own method, trait method, variant case, builtin (len), with zig-like auto-deref
    // figure out: overload resolution at calls - static where picks at compile time, runtime where builds a dispatch chain
    // runit - brk / ret / cont and nested if / match in a valued if / match are auto runit, a plain unit call must be wrapped in `do`
    // figure out: typing of loops that produce arrays
    // figure out: typing of `?<-`, `??`, `<-` (binder scopes are fixed in step 06)
    // untyped destructure - the shared type comes from an existing name, otherwise from joining the assigned values
    // figure out: parallel execution - per thread metavars and diagnostics, merged into the global tables afterwards
    _ = .{ self, wave };
}

fn s24_drain_instantiations(self: *Resolver) bool {
    // check the bodies of queued stcfun instances until the queue is empty, return true on progress
    // figure out: instances created while draining - same loop or next iteration
    // figure out: dedupe identical instantiations requested from different threads
    _ = self;
    return false;
}

fn s25_check_control_flow(self: *Resolver) void {
    // check brk / cont are inside loops, ret types match, detect unreachable code
    // figure out: what a brk yields inside an assigned loop (`[]i32 a = while ...`)
    // figure out: may defer bodies contain ret / brk
    // runit - a branch of a valued if / match that is plain unit (no do, not brk / ret / cont / if / match) is a runit_mixing error
    _ = self;
}

fn s26_check_patterns(self: *Resolver) void {
    // check exhaustiveness and redundancy of every match and build its decision tree
    // figure out: start with maranget usefulness matrices, move to lower your guards later
    // figure out: int patterns with ranges (interval sets), string patterns, struct patterns with named fields
    // figure out: stcmatch - scrutinee must be static, mark all other arms as pruned
    // figure out: untagged variants only in stcmatch, type-cast patterns only for homogenic ones
    _ = self;
}

fn s27_check_mutability(self: *Resolver) void {
    // check that writes only hit mutable places and go through mutable pointers
    // figure out: place computation through member / index / deref chains
    // figure out: is self mutable inside methods by default, or does that need a marker
    // figure out: where-else that repairs a parameter (`else p = 50`) - does that make the param implicitly mutable
    _ = self;
}

fn s28_check_definite_initialization(self: *Resolver) void {
    // dataflow - every read sees an initialized variable
    // figure out: declarations without value (`mut u64 x;`), joins at branches and loops
    // figure out: arrays declared by length and assigned later (`arr4 = for ...`)
    _ = self;
}

fn s29_lower_where_guards(self: *Resolver) void {
    // turn where / where-else clauses into guard rows, prove stcwhere statically
    // figure out: guards decide the overload (dispatch) vs guards only validate the chosen one
    // figure out: typing of the else value - must match the param type, or the return type when it is `ret x`
    _ = self;
}

fn s30_zonk_types(self: *Resolver) void {
    // replace every metavar in node types and decl types by its final binding
    // still unbound metavars are an uninferable_type error, there is no defaulting (literals never stay unbound)
    _ = self;
}

fn s31_freeze(self: *Resolver) void {
    // shrink the tables and expose read-only views for highlowerer
    // figure out: what exactly the lowerer needs (node types, decl ids, instances, guards, decisions)
    // figure out: free scratch, worklist and metavars here
    _ = self;
}
