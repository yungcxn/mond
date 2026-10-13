const std = @import("std");
const mond = @import("mond");
const Lexer = mond.Lexer;
const ParseTree = mond.ParseTree;
const Resolver = mond.Resolver;
const DeclPool = mond.DeclPool;
const DynamicBuffer = mond.DynamicBuffer;
const Completion = @import("Completion.zig");
const Analysis = @import("Analysis.zig");
const positions = @import("positions.zig");
const symbol_classes = @import("symbol_classes.zig");
const Range = Analysis.Range;
const Type = Analysis.Type;
const StaticIndex = std.meta.Child(@FieldType(Resolver, "node_types"));
const none = Analysis.none;
const undefined_name = Analysis.undefined_name;

// the links: every declaration by the token naming it and every name by the declaration it means

pub fn link(analysis: *Analysis, lexer: *Lexer, resolver: *Resolver) void {
    const tree = resolver.tree;
    const spans = lexer.tokens.column(.span);
    const declaration_count = resolver.decl_pool.entries.columns().kind.len;
    const node_count = tree.ast_nodes.len();
    analysis.token_meaning = analysis.allocate_unset(spans.len);
    analysis.declaration_token = analysis.allocate_unset(declaration_count);
    analysis.node_parent = analysis.allocate_unset(node_count);
    analysis.node_scope = analysis.allocate_unset(node_count);
    analysis.node_first_token = analysis.allocate_unset(node_count);
    analysis.node_declaration = analysis.allocate_unset(node_count);
    analysis.token_leaf = analysis.allocate_unset(spans.len);
    for (resolver.roots) |root| descend(analysis, tree, root);

    declare_resolved(analysis, resolver, spans);
    declare_from_earlier_passes(analysis, spans);
    declare_unchecked(analysis, resolver, lexer);

    link_resolved_names(analysis, resolver);
    link_names_of_earlier_passes(analysis);
    link_pattern_alternatives(analysis, resolver);
    link_named_arguments(analysis, resolver);
    mark_undefined_names(analysis, resolver);
    link_remaining_names(analysis, resolver, spans);

    // a binder of a quote pattern holds a tree, used or not
    for (analysis.token_leaf, 0..) |leaf, token| {
        if (leaf != none and binds_tree(analysis, tree, leaf)) analysis.token_class[token] = .macro;
    }

    for (analysis.token_meaning, spans) |meaning, span| {
        if (meaning == none or meaning == undefined_name) continue;
        const name_range = positions.range(analysis, span[0], span[1]);
        const start = name_range.start;
        analysis.links.push(.{ start.line, start.character, name_range.end.character, meaning });
    }
}

// the last pass has no trace of the names splices spelled and of stcfuns it does not run again
pub fn remember_pass(analysis: *Analysis, resolver: *Resolver) void {
    const declarations = resolver.decl_pool.entries.columns();
    const naming_tokens = analysis.allocate_unset(declarations.kind.len);
    for (naming_tokens, 0..) |*naming_token, i| {
        const node = origin(resolver, i);
        naming_token.* = named(resolver, node, declarations.name[i]) orelse continue;
        remember_declaration(analysis, resolver, i, node, naming_token.*);
    }

    for (0..resolver.tree.ast_nodes.len()) |i| {
        const token = name_token(resolver, @intCast(i)) orelse continue;
        const declaration = resolver.node_declarations[i];
        if (declaration == .none) continue;
        analysis.earlier_naming_token[token] = naming_tokens[@intFromEnum(declaration)];
    }
}

// the declaration named at `naming_token` as this pass found it, the latest pass overwrites it
fn remember_declaration(
    analysis: *Analysis,
    resolver: *Resolver,
    declaration: usize,
    node: u32,
    naming_token: u32,
) void {
    const declarations = resolver.decl_pool.entries.columns();
    const past_index = &analysis.past_declaration_index[naming_token];
    if (past_index.* == none) {
        past_index.* = @intCast(analysis.past_declarations.items().len);
        analysis.past_declarations.push(undefined);
    }

    const name = resolver.name_pool.text_of(declarations.name[declaration]);
    const detail = type_text(analysis, resolver, declared_type(resolver, declaration));
    const class = symbol_classes.shown_class(resolver, declaration);
    const modifiers = symbol_classes.declaration_modifiers(resolver, declaration);
    analysis.past_declarations.items()[past_index.*] = .{
        .name = name,
        .detail = detail,
        .class = class,
        .modifiers = modifiers,
        .extent = resolver.tree.extent(node),
    };
}

// the parent, first token and scope of every node below `node`
fn descend(analysis: *Analysis, tree: *ParseTree, node: u32) void {
    if (tree.token(node)) |token| {
        analysis.node_first_token[node] = token;
        // code that landed is written at the splice that made it, it is no leaf there
        if (tree.arg(node, 1) == 0) analysis.token_leaf[token] = node;
    }

    const opens_scope = tree.kind(node) == .block or tree.kind(node) == .partial__match_case;
    for (tree.children(node)) |child| {
        if (child == 0) continue;
        analysis.node_parent[child] = node;
        analysis.node_scope[child] = if (opens_scope) node else analysis.node_scope[node];
        descend(analysis, tree, child);
        const first_token = &analysis.node_first_token[node];
        first_token.* = @min(first_token.*, analysis.node_first_token[child]);
    }
}

// every declaration of the resolver at the token naming it
fn declare_resolved(analysis: *Analysis, resolver: *Resolver, spans: []const Lexer.TextSpan) void {
    const declarations = resolver.decl_pool.entries.columns();
    for (analysis.declaration_token, 0..) |*declaration_token, i| {
        const node = origin(resolver, i);
        declaration_token.* = named(resolver, node, declarations.name[i]) orelse continue;
        const token = declaration_token.*;
        if (analysis.token_meaning[token] != none) continue;

        const class = symbol_classes.class_of_kind(declarations.kind[i]);
        const flags = declarations.flags[i];
        const is_local_value = class == .variable or class == .parameter;
        const name = resolver.name_pool.text_of(declarations.name[i]);
        const detail = type_text(analysis, resolver, declared_type(resolver, i));
        const shown_class = symbol_classes.shown_class(resolver, i);
        declare(analysis, token, .{
            .name = name,
            .detail = detail,
            .class = shown_class,
            .modifiers = symbol_classes.modifiers(class, flags),
            .outlined = !is_local_value or flags.is_global,
            .global = flags.is_global,
            .extent = resolver.tree.extent(node),
            .name_span = spans[token],
        });
        analysis.node_declaration[node] = analysis.token_meaning[token];
    }
}

// a type shows what it is, a value its type
fn declared_type(resolver: *Resolver, declaration: usize) StaticIndex {
    const declarations = resolver.decl_pool.entries.columns();
    if (declarations.kind[declaration].is_type_declaration()) {
        return declarations.static_value[declaration];
    }
    return declarations.value_type[declaration];
}

// what only a pass before the last declared: the locals of a stcfun it does not run again
fn declare_from_earlier_passes(analysis: *Analysis, spans: []const Lexer.TextSpan) void {
    for (analysis.past_declaration_index, 0..) |past_index, token| {
        if (past_index == none or analysis.token_meaning[token] != none) continue;
        const past = analysis.past_declarations.items()[past_index];
        declare(analysis, @intCast(token), .{
            .name = past.name,
            .detail = past.detail,
            .class = past.class,
            .modifiers = past.modifiers,
            .outlined = false,
            .global = false,
            .extent = past.extent,
            .name_span = spans[token],
        });
    }
}

// the resolver declares no cases and no parameters of unchecked signatures (`fun f = (&u8 x);`)
fn declare_unchecked(analysis: *Analysis, resolver: *Resolver, lexer: *Lexer) void {
    const tree = resolver.tree;
    for (1..tree.ast_nodes.len()) |i| {
        const node: u32 = @intCast(i);
        const identifier, const class: Type = switch (tree.kind(node)) {
            .partial__variant_def_param => .{
                tree.laidout_children(.partial__variant_def_param, node).name,
                .enumMember,
            },
            .partial__fun_def_param_named => .{ tree.arg(node, 1), .parameter },
            .partial__type_def_param_named => .{ tree.arg(node, 1), .property },
            else => continue,
        };
        if (tree.kind(identifier) != .identifier) continue;
        const token = tree.arg(identifier, 0);
        if (analysis.token_meaning[token] != none) continue;

        const outer = outermost_case_part(analysis, tree, node);
        const is_case = class == .enumMember;
        const parameter = if (is_case) ParseTree.Param{} else ParseTree.Param.from_node(tree, node);
        const is_written_code = parameter.ty != 0 and written_as_code(tree, parameter.ty);
        const name = resolver.name_pool.text_of(resolver.name_pool.name_of_node(identifier));
        const detail = if (is_case)
            ""
        else
            written_type(analysis, resolver, lexer, parameter.ty, token);
        const readonly = symbol_classes.modifier_bit(.readonly, !parameter.is_mut);
        declare(analysis, token, .{
            .name = name,
            .detail = detail,
            .class = if (is_written_code) .macro else class,
            .modifiers = if (is_case) 0 else readonly,
            .outlined = class != .parameter,
            .global = false,
            .extent = tree.extent(outer),
            .name_span = tree.span(identifier),
        });
        analysis.node_declaration[outer] = analysis.token_meaning[token];
    }
}

// a case spans its payload and tag (`Circle(f32 r)`)
fn outermost_case_part(analysis: *Analysis, tree: *ParseTree, node: u32) u32 {
    var outer = node;
    while (true) {
        const parent = analysis.node_parent[outer];
        if (parent == none) return outer;
        const kind = tree.kind(parent);
        const is_case_part =
            kind == .partial__variant_def_param_typed or kind == .partial__variant_def_param_tagged;
        if (!is_case_part) return outer;
        outer = parent;
    }
}

const Declaring = struct {
    name: []const u8,
    detail: []const u8,
    class: Type,
    modifiers: u32,
    // outside the outline a declaration has no kind
    outlined: bool,
    global: bool,
    extent: ?Lexer.TextSpan,
    name_span: Lexer.TextSpan,
};

fn declare(analysis: *Analysis, token: u32, declaring: Declaring) void {
    analysis.token_meaning[token] = @intCast(analysis.declarations.items().len);
    analysis.declaration_sites.push(.{
        .token = token,
        .global = declaring.global,
        .class = declaring.class,
        .modifiers = declaring.modifiers,
    });

    const name_span = declaring.name_span;
    const extent = declaring.extent orelse name_span;
    const whole_start = @min(extent[0], name_span[0]);
    const whole_end = @max(extent[1], name_span[1]);
    analysis.declarations.push(.{
        .name = declaring.name,
        .detail = declaring.detail,
        .kind = if (declaring.outlined) symbol_classes.symbol_kind(declaring.class) else 0,
        .range = positions.range(analysis, whole_start, whole_end),
        .selectionRange = positions.range(analysis, name_span[0], name_span[1]),
    });
}

fn link_resolved_names(analysis: *Analysis, resolver: *Resolver) void {
    for (0..resolver.tree.ast_nodes.len()) |i| {
        const node: u32 = @intCast(i);
        const token = name_token(resolver, node) orelse continue;
        const declaration = resolver.node_declarations[node];
        if (declaration == .none) continue;
        analysis.token_meaning[token] = meaning_of_declaration(analysis, resolver, declaration);
    }
}

// a positional parameter has no name of its own (`(i32, i32)`), its function declares it
fn meaning_of_declaration(
    analysis: *Analysis,
    resolver: *Resolver,
    declaration: DeclPool.Index,
) u32 {
    const declaration_token = analysis.declaration_token[@intFromEnum(declaration)];
    const template = resolver.generics.template_of.get(declaration) orelse declaration;
    if (declaration_token != none) return analysis.token_meaning[declaration_token];

    const declarations = resolver.decl_pool.entries.columns();
    const template_name = resolver.name_pool.text_of(declarations.name[@intFromEnum(template)]);
    if (!positional(template_name)) return none;
    return enclosing_declaration(analysis, declarations.node[@intFromEnum(template)]);
}

// a name only an earlier pass resolved: one a splice spelled, one in a stcfun not run again
fn link_names_of_earlier_passes(analysis: *Analysis) void {
    for (analysis.earlier_naming_token, analysis.token_meaning) |naming_token, *meaning| {
        if (meaning.* != none or naming_token == none) continue;
        meaning.* = analysis.token_meaning[naming_token];
    }
}

// alternatives bind the same names (`A(x) | B(x)`), one a stcfun did not match means the same
fn link_pattern_alternatives(analysis: *Analysis, resolver: *Resolver) void {
    const tree = resolver.tree;
    for (1..tree.ast_nodes.len()) |i| {
        if (tree.kind(@intCast(i)) != .partial__match_case_pattern_or) continue;
        const subtree = tree.subtree(@intCast(i));
        for (subtree[0]..subtree[1]) |binder| for (subtree[0]..subtree[1]) |other| {
            adopt_alternative_meaning(analysis, resolver, @intCast(binder), @intCast(other));
        };
    }
}

fn adopt_alternative_meaning(
    analysis: *Analysis,
    resolver: *Resolver,
    binder: u32,
    other: u32,
) void {
    const binder_token = name_token(resolver, binder) orelse return;
    const other_token = name_token(resolver, other) orelse return;
    if (resolver.tree.kind(binder) != .identifier) return;

    const meanings = analysis.token_meaning;
    if (meanings[binder_token] != none or meanings[other_token] == none) return;
    if (resolver.name_pool.name_of_node(binder) != resolver.name_pool.name_of_node(other)) return;
    meanings[binder_token] = meanings[other_token];
}

// a named argument means the parameter or field within what is called (`p with (x = 1)`)
fn link_named_arguments(analysis: *Analysis, resolver: *Resolver) void {
    const tree = resolver.tree;
    for (0..tree.ast_nodes.len()) |i| {
        const node: u32 = @intCast(i);
        const kind = tree.kind(node);
        if (kind != .fun_call and kind != .with) continue;
        const arguments = tree.arg(node, 1);
        if (tree.kind(arguments) != .partial__fun_call_param_tuple) continue;

        const callee = tree.arg(node, 0);
        const callee_type = type_declaration(analysis, resolver, callee);
        const called = if (kind == .fun_call) meaning_of_name(analysis, resolver, callee) else none;
        for (tree.laidout_children(.partial__fun_call_param_tuple, arguments)) |argument| {
            const identifier = tree.arg_name(argument);
            if (identifier == 0 or tree.kind(identifier) != .identifier) continue;
            const name = resolver.name_pool.text_of(resolver.name_pool.name_of_node(identifier));
            const meaning = named_argument_meaning(analysis, callee_type, called, name);
            analysis.token_meaning[tree.arg(identifier, 0)] = meaning;
        }
    }
}

fn meaning_of_name(analysis: *Analysis, resolver: *Resolver, node: u32) u32 {
    const token = name_token(resolver, node) orelse return none;
    return analysis.token_meaning[token];
}

fn named_argument_meaning(
    analysis: *Analysis,
    callee_type: ?Range,
    called: u32,
    name: []const u8,
) u32 {
    if (callee_type) |type_range| return within(analysis, type_range, name);
    if (called != none) return within_overloads(analysis, called, name);
    return none;
}

// a name the resolver reported undefined stays so
fn mark_undefined_names(analysis: *Analysis, resolver: *Resolver) void {
    const diagnostics = resolver.doctor.diagnostics.columns();
    for (diagnostics.code, diagnostics.node) |code, node| {
        if (code != .undefined_name) continue;
        const token = resolver.tree.token(node) orelse continue;
        analysis.token_meaning[token] = undefined_name;
    }
}

// the other names in source order
fn link_remaining_names(
    analysis: *Analysis,
    resolver: *Resolver,
    spans: []const Lexer.TextSpan,
) void {
    // names code the resolver did not check has not met before
    var unmet: DynamicBuffer(u32) = .init(analysis.allocator, 16);
    for (analysis.token_leaf, 0..) |leaf, token| {
        if (leaf == none or resolver.tree.kind(leaf) != .identifier) continue;
        if (analysis.token_meaning[token] != none) continue;
        link_remaining_name(analysis, resolver, spans, &unmet, leaf, @intCast(token));
    }
}

// a field or case lies within its base's type, a positional field (`A.$1`) is declared by it
// other members and named arguments go by their unique name, the other names by scope
fn link_remaining_name(
    analysis: *Analysis,
    resolver: *Resolver,
    spans: []const Lexer.TextSpan,
    unmet: *DynamicBuffer(u32),
    leaf: u32,
    token: u32,
) void {
    const tree = resolver.tree;
    const name = resolver.name_pool.text_of(resolver.name_pool.name_of_node(leaf));
    const parent = analysis.node_parent[leaf];
    const is_member = parent != none and
        tree.kind(parent) == .member and
        tree.arg(parent, 1) == leaf;
    const is_named_argument = parent != none and
        tree.kind(parent) == .partial__fun_call_assigned_param and
        tree.arg(parent, 0) == leaf;
    const goes_by_parent = is_member or is_named_argument;

    const meaning = &analysis.token_meaning[token];
    const base_type = if (is_member)
        type_declaration(analysis, resolver, tree.arg(parent, 0))
    else
        null;
    if (base_type) |type_range| {
        meaning.* = within(analysis, type_range, name);
        if (meaning.* == none and positional(name)) meaning.* = spanning(analysis, type_range);
    }
    if (meaning.* == none) {
        meaning.* = if (goes_by_parent) unique(analysis, name) else scoped(analysis, leaf, name);
    }
    const is_intrinsic = name.len > 0 and name[0] == '$';
    if (meaning.* == none and is_intrinsic) meaning.* = intrinsic(analysis, name, spans[token]);
    if (meaning.* != none or goes_by_parent) return;

    // unchecked code declares a name where it first appears (`Res.Ok(v) => v` never matched)
    var same_name: DynamicBuffer(u32) = .init(analysis.allocator, 4);
    for (unmet.items()) |unmet_token| {
        const unmet_name = resolver.name_pool.name_of_node(analysis.token_leaf[unmet_token]);
        if (unmet_name == resolver.name_pool.name_of_node(leaf)) same_name.push(unmet_token);
    }
    const nearest_index = nearest(analysis, leaf, same_name.items()) orelse {
        unmet.push(token);
        return;
    };

    const first_token = same_name.items()[nearest_index];
    if (analysis.token_meaning[first_token] == none) {
        const holds_tree = binds_tree(analysis, tree, analysis.token_leaf[first_token]);
        declare(analysis, first_token, .{
            .name = name,
            .detail = "",
            .class = if (holds_tree) .macro else .variable,
            .modifiers = 0,
            .outlined = false,
            .global = false,
            .extent = null,
            .name_span = spans[first_token],
        });
    }
    analysis.token_meaning[token] = analysis.token_meaning[first_token];
}

// the declaration made by `node` or by a node enclosing it
fn enclosing_declaration(analysis: *Analysis, node: u32) u32 {
    var ancestor = node;
    while (ancestor != none and analysis.node_declaration[ancestor] == none) {
        ancestor = analysis.node_parent[ancestor];
    }
    if (ancestor == none) return none;
    return analysis.node_declaration[ancestor];
}

// a positional name: `$0`, `$1`
fn positional(name: []const u8) bool {
    return name.len > 1 and name[0] == '$' and std.ascii.isDigit(name[1]);
}

// a builtin (`$len`) is declared nowhere, its uses share one declaration
fn intrinsic(analysis: *Analysis, name: []const u8, use: Lexer.TextSpan) u32 {
    for (analysis.declarations.items(), 0..) |declaration, i| {
        if (declaration.selectionRange != null) continue;
        if (std.mem.eql(u8, declaration.name, name)) return @intCast(i);
    }

    analysis.declaration_sites.push(.{
        .token = none,
        .global = false,
        .class = .property,
        .modifiers = 0,
    });
    analysis.declarations.push(.{
        .name = name,
        .detail = builtin_detail(analysis, name),
        .kind = 0,
        .range = positions.range(analysis, use[0], use[1]),
        .selectionRange = null,
    });
    return @intCast(analysis.declarations.items().len - 1);
}

// one the completion knows is described by it
fn builtin_detail(analysis: *Analysis, name: []const u8) []const u8 {
    const entry = Completion.described(name) orelse return "builtin";
    const format = "{s}  # {s}";
    const arguments = .{ entry.ty, entry.doc };
    return std.fmt.allocPrint(analysis.allocator, format, arguments) catch @panic("OOM");
}

// the token of `x` or of the `x` in `p.x`, a name a macro made is written at no token
pub fn name_token(resolver: *Resolver, node: u32) ?u32 {
    const tree = resolver.tree;
    const identifier = switch (tree.kind(node)) {
        .identifier => node,
        .member => tree.arg(node, 1),
        else => return null,
    };
    if (tree.kind(identifier) != .identifier or tree.arg(identifier, 1) != 0) return null;
    return tree.arg(identifier, 0);
}

// the node declaring `declaration`, a realization is declared where its template is
fn origin(resolver: *Resolver, declaration: usize) u32 {
    const index: DeclPool.Index = @enumFromInt(declaration);
    const template = resolver.generics.template_of.get(index) orelse index;
    return resolver.decl_pool.get(template, .node);
}

// the token of the first identifier called `name` in the subtree of `node`
fn named(resolver: *Resolver, node: u32, name: anytype) ?u32 {
    const tree = resolver.tree;
    const subtree = tree.subtree(node);
    for (subtree[0]..subtree[1]) |i| {
        const candidate: u32 = @intCast(i);
        if (tree.kind(candidate) != .identifier or tree.arg(candidate, 1) != 0) continue;
        if (resolver.name_pool.name_of_node(candidate) == name) return tree.arg(candidate, 0);
    }
    return null;
}

// the first declaration called `name` within `outer`, but not the one spanning `outer`
fn within(analysis: *Analysis, outer: Range, name: []const u8) u32 {
    for (analysis.declarations.items(), 0..) |declaration, i| {
        const name_range = declaration.selectionRange orelse continue;
        if (!std.mem.eql(u8, declaration.name, name)) continue;
        if (std.meta.eql(declaration.range, outer)) continue;
        if (positions.before(name_range.start, outer.start)) continue;
        if (positions.before(outer.end, name_range.end)) continue;
        return @intCast(i);
    }
    return none;
}

fn spanning(analysis: *Analysis, outer: Range) u32 {
    for (analysis.declarations.items(), 0..) |declaration, i| {
        if (std.meta.eql(declaration.range, outer)) return @intCast(i);
    }
    return none;
}

// within `function` or within another overload of it (`mixed(1, b = 2)`)
fn within_overloads(analysis: *Analysis, function: u32, name: []const u8) u32 {
    const declarations = analysis.declarations.items();
    const function_name = declarations[function].name;
    var found = within(analysis, declarations[function].range, name);
    for (declarations) |declaration| {
        if (found != none) return found;
        if (declaration.selectionRange == null) continue;
        if (!std.mem.eql(u8, declaration.name, function_name)) continue;
        found = within(analysis, declaration.range, name);
    }
    return found;
}

// the only member, field, case or function called `name`
fn unique(analysis: *Analysis, name: []const u8) u32 {
    var found: u32 = none;
    for (analysis.declarations.items(), 0..) |declaration, i| {
        if (!is_member_kind(declaration.kind) or !std.mem.eql(u8, declaration.name, name)) continue;
        if (found != none) return none;
        found = @intCast(i);
    }
    return found;
}

fn is_member_kind(kind: u8) bool {
    return kind == symbol_classes.symbol_kind(.method) or
        kind == symbol_classes.symbol_kind(.property) or
        kind == symbol_classes.symbol_kind(.function) or
        kind == symbol_classes.symbol_kind(.enumMember);
}

// the nearest declaration of `name` before `node` within a node enclosing it, else a global one
fn scoped(analysis: *Analysis, node: u32, name: []const u8) u32 {
    var candidates: DynamicBuffer(u32) = .init(analysis.allocator, 8);
    var candidate_tokens: DynamicBuffer(u32) = .init(analysis.allocator, 8);
    const sites = analysis.declaration_sites.items();
    for (analysis.declarations.items(), sites, 0..) |declaration, site, i| {
        if (declaration.selectionRange == null) continue;
        if (!std.mem.eql(u8, declaration.name, name)) continue;
        candidates.push(@intCast(i));
        candidate_tokens.push(site.token);
    }

    if (nearest(analysis, node, candidate_tokens.items())) |i| return candidates.items()[i];
    for (candidates.items()) |candidate| {
        if (sites[candidate].global) return candidate;
    }
    return none;
}

// of the tokens `candidates`, the nearest one before `node` within a node enclosing it
fn nearest(analysis: *Analysis, node: u32, candidates: []const u32) ?usize {
    var ancestor = analysis.node_parent[node];
    while (ancestor != none) : (ancestor = analysis.node_parent[ancestor]) {
        var best: ?usize = null;
        for (candidates, 0..) |token, i| {
            const is_inside = token >= analysis.node_first_token[ancestor];
            const is_before = token < analysis.node_first_token[node];
            if (!is_inside or !is_before or !sees(analysis, node, token)) continue;
            if (best) |best_index| {
                if (token <= candidates[best_index]) continue;
            }
            best = i;
        }
        if (best != null) return best;
    }
    return null;
}

// a binder of a quote pattern holds a tree (`quote: @x + 0 => x`)
fn binds_tree(analysis: *Analysis, tree: *ParseTree, node: u32) bool {
    if (node == none) return false;
    const parents = analysis.node_parent;
    if (parents[node] == none or tree.kind(parents[node]) != .unquote) return false;

    var quote = parents[node];
    while (quote != none and tree.kind(quote) != .quote) quote = parents[quote];
    if (quote == none) return false;

    const arm = parents[quote];
    return arm != none and tree.kind(arm) == .partial__match_case and tree.arg(arm, 0) == quote;
}

// whether a name declared at `token` is seen at `node`: one in a block or match arm only within it
fn sees(analysis: *Analysis, node: u32, token: u32) bool {
    const leaf = analysis.token_leaf[token];
    const scope = if (leaf == none) none else analysis.node_scope[leaf];
    if (scope == none) return true;

    var ancestor = node;
    while (ancestor != none and ancestor != scope) ancestor = analysis.node_parent[ancestor];
    return ancestor == scope;
}

// where the type of `node` is declared, a type stands for itself
fn type_declaration(analysis: *Analysis, resolver: *Resolver, node: u32) ?Range {
    const declaration = resolver.node_declarations[node];
    // a static value can be a type (`Q = Opt(u8)`)
    const static_value: StaticIndex = if (declaration == .none)
        .none
    else
        resolver.decl_pool.get(declaration, .static_value);
    const type_value = if (symbol_classes.is_type(resolver, node))
        resolver.node_static_values[node]
    else
        .none;
    for ([_]StaticIndex{ static_value, type_value, resolver.node_types[node] }) |candidate| {
        if (type_owner(analysis, resolver, candidate)) |owner_range| return owner_range;
    }

    // a value made by a call is made within what it calls (`Q = Opt(wide)` only interpreted)
    if (declaration == .none) return null;
    const tree = resolver.tree;
    for (tree.children(resolver.decl_pool.get(declaration, .node))) |child| {
        if (child == 0 or tree.kind(child) != .fun_call) continue;
        const callee_token = name_token(resolver, tree.arg(child, 0)) orelse continue;
        const meaning = analysis.token_meaning[callee_token];
        if (meaning == none or meaning == undefined_name) continue;
        return analysis.declarations.items()[meaning].range;
    }
    return null;
}

// where a type is declared, an anonymous one too (`ret ++(Some(t), None)`)
fn type_owner(analysis: *Analysis, resolver: *Resolver, type_index: StaticIndex) ?Range {
    if (type_index == .none) return null;
    const declaration = switch (resolver.static_pool.get(type_index)) {
        .pointer_type => |pointer| return type_owner(analysis, resolver, pointer.pointee),
        .record_type => |record| record.declaration,
        .variant_type => |variant| variant.declaration,
        .variant_case_type => |case| return case_owner(analysis, resolver, case),
        .int_type,
        .float_type,
        .simple_type,
        .meta_type,
        .array_type,
        .function_type,
        .variant_union_type,
        .trait_type,
        .static_function,
        .template_type,
        .type_variable,
        .ast_type,
        .int_value,
        .float_value,
        .simple_value,
        .string_value,
        .aggregate_value,
        .variant_value,
        .function_value,
        .tree_value,
        => return null,
    };
    if (declaration == .none) return null;

    const template = resolver.generics.template_of.get(declaration) orelse declaration;
    const declaration_token = analysis.declaration_token[@intFromEnum(template)];
    const meaning = if (declaration_token == none)
        none
    else
        analysis.token_meaning[declaration_token];
    if (meaning != none and meaning != undefined_name) {
        return analysis.declarations.items()[meaning].range;
    }

    const extent = resolver.tree.extent(resolver.decl_pool.get(template, .node)) orelse return null;
    return positions.range(analysis, extent[0], extent[1]);
}

// a case lies within its variant
fn case_owner(analysis: *Analysis, resolver: *Resolver, case: anytype) ?Range {
    const variant_range = type_owner(analysis, resolver, case.variant) orelse return null;
    const case_declaration = within(analysis, variant_range, resolver.name_pool.text_of(case.name));
    if (case_declaration == none) return null;
    return analysis.declarations.items()[case_declaration].range;
}

// the type of a parameter as written before its name (`&u8 fmt`), when it is not evaluated
fn written_type(
    analysis: *Analysis,
    resolver: *Resolver,
    lexer: *Lexer,
    type_node: u32,
    parameter_name: u32,
) []const u8 {
    const evaluated = resolver.node_static_values[type_node];
    if (evaluated != .none) return type_text(analysis, resolver, evaluated);

    const tokens = lexer.tokens.columns();
    var start = parameter_name;
    var depth: u32 = 0;
    while (start > 0) : (start -= 1) {
        switch (tokens.tk[start - 1]) {
            .@"pct_)", .@"pct_]" => depth += 1,
            .@"pct_(", .@"pct_[" => {
                if (depth == 0) break;
                depth -= 1;
            },
            .@"pct_," => if (depth == 0) break,
            else => {},
        }
    }
    if (start == parameter_name) return "";
    return analysis.source[tokens.span[start][0]..tokens.span[parameter_name - 1][1]];
}

fn type_text(analysis: *Analysis, resolver: *Resolver, type_index: StaticIndex) []const u8 {
    var text: std.Io.Writer.Allocating = .init(analysis.allocator);
    if (type_index != .none and type_index != .poison_type) {
        const pool = &resolver.static_pool;
        pool.format(&resolver.name_pool, type_index, &text.writer) catch @panic("OOM");
    }
    return text.written();
}

// a type written with `ast` in it, of a parameter the resolver did not check
fn written_as_code(tree: *ParseTree, type_node: u32) bool {
    const subtree = tree.subtree(type_node);
    for (subtree[0]..subtree[1]) |i| {
        if (tree.kind(@intCast(i)) == .type_ast) return true;
    }
    return false;
}
