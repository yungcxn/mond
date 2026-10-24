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
const fallbacks = @import("fallbacks.zig");
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

    // every declaration of the resolver at the token naming it
    const declarations = resolver.decl_pool.entries.columns();
    for (analysis.declaration_token, 0..) |*declaration_token, i| {
        // a realization is declared where its template is
        const index: DeclPool.Index = @enumFromInt(i);
        const template = resolver.generics.template_of.get(index) orelse index;
        const node = resolver.decl_pool.get(template, .node);
        declaration_token.* = named(resolver, node, declarations.name[i]) orelse continue;
        const token = declaration_token.*;
        if (analysis.token_meaning[token] != none) continue;

        const class = symbol_classes.class_of_kind(declarations.kind[i]);
        const flags = declarations.flags[i];
        const is_local_value = class == .variable or class == .parameter;
        const name = resolver.name_pool.text_of(declarations.name[i]);
        // a type shows what it is, a value its type
        const declared_type = if (declarations.kind[i].is_type_declaration())
            declarations.static_value[i]
        else
            declarations.value_type[i];
        const detail = type_text(analysis, resolver, declared_type);
        declare(analysis, token, .{
            .name = name,
            .detail = detail,
            .class = class,
            .modifiers = symbol_classes.modifiers(class, flags),
            .outlined = !is_local_value or flags.is_global,
            .global = flags.is_global,
            .extent = resolver.tree.extent(node),
            .name_span = spans[token],
        });
        analysis.node_declaration[node] = analysis.token_meaning[token];
    }

    // what only a pass before the last declared: the locals of a stcfun it does not run again
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

    // the resolver declares no cases and no parameters of unchecked signatures (`fun f = (&u8 x);`)
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
        // landed code is written at the token of its splice, it names nothing there
        if (tree.kind(identifier) != .identifier or tree.arg(identifier, 1) != 0) continue;
        const token = tree.arg(identifier, 0);
        if (analysis.token_meaning[token] != none) continue;

        // a case spans its payload and tag (`Circle(f32 r)`)
        var outer = node;
        while (true) {
            const parent = analysis.node_parent[outer];
            if (parent == none) break;
            const kind = tree.kind(parent);
            const is_case_part = kind == .partial__variant_def_param_typed or
                kind == .partial__variant_def_param_tagged;
            if (!is_case_part) break;
            outer = parent;
        }
        const is_case = class == .enumMember;
        const parameter = if (is_case) ParseTree.Param{} else ParseTree.Param.from_node(tree, node);
        const name = resolver.name_pool.text_of(resolver.name_pool.name_of_node(identifier));
        // the type of a parameter as written before its name (`&u8 fmt`), when it is not evaluated
        const detail = if (is_case) "" else blk: {
            const evaluated = resolver.node_static_values[parameter.ty];
            if (evaluated != .none) break :blk type_text(analysis, resolver, evaluated);

            const tokens = lexer.tokens.columns();
            var start = token;
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
            if (start == token) break :blk "";
            break :blk analysis.source[tokens.span[start][0]..tokens.span[token - 1][1]];
        };
        const readonly = symbol_classes.modifier_bit(.readonly, !parameter.is_mut);
        declare(analysis, token, .{
            .name = name,
            .detail = detail,
            .class = class,
            .modifiers = if (is_case) 0 else readonly,
            .outlined = class != .parameter,
            .global = false,
            .extent = tree.extent(outer),
            .name_span = tree.span(identifier),
        });
        analysis.node_declaration[outer] = analysis.token_meaning[token];
    }

    // the top-level names of the included files where they are written, read once one is needed,
    // and the entries in `declarations` made for them
    var included: ?std.StringHashMapUnmanaged(Analysis.Elsewhere) = null;
    var declared_elsewhere: std.AutoHashMapUnmanaged(u32, u32) = .empty;
    // the names of the tree, then those only an earlier pass met that mean a global without a
    // naming token (`derive` of `<derive(..)>`, from an included file)
    var usages: std.ArrayList(struct { u32, DeclPool.Index }) = .empty;
    const in_tree = analysis.allocator.alloc(bool, spans.len) catch @panic("OOM");
    @memset(in_tree, false);
    for (0..resolver.tree.ast_nodes.len()) |i| {
        const node: u32 = @intCast(i);
        const token = name_token(resolver, node) orelse continue;
        const declaration = resolver.node_declarations[node];
        if (declaration == .none) continue;
        usages.append(analysis.allocator, .{ token, declaration }) catch @panic("OOM");
        in_tree[token] = true;
    }
    for (analysis.earlier_names, in_tree, 0..) |name, is_in_tree, token| {
        if (name.len == 0 or is_in_tree) continue;
        const global = resolver.scopes.globals.get(resolver.name_pool.intern(name)) orelse continue;
        usages.append(analysis.allocator, .{ @intCast(token), global }) catch @panic("OOM");
    }
    for (usages.items) |usage| {
        const token, const declaration = usage;
        // a positional parameter has no name of its own (`(i32, i32)`), its function declares it
        analysis.token_meaning[token] = blk: {
            const declaration_token = analysis.declaration_token[@intFromEnum(declaration)];
            const template = resolver.generics.template_of.get(declaration) orelse declaration;
            if (declaration_token != none) break :blk analysis.token_meaning[declaration_token];

            const template_name =
                resolver.name_pool.text_of(declarations.name[@intFromEnum(template)]);
            if (!positional(template_name)) {
                const index = @intFromEnum(template);
                if (declared_elsewhere.get(index)) |made| break :blk made;
                if (included == null) included = read_included(analysis, resolver);
                // ``x`name`` landed from a namespace's file, ``name`1`` a private name made fresh
                const tick = std.mem.indexOfScalar(u8, template_name, '`');
                const name = if (tick) |at| name: {
                    const after = template_name[at + 1 ..];
                    const is_fresh = std.mem.indexOfNone(u8, after, "0123456789") == null;
                    break :name if (is_fresh) template_name[0..at] else after;
                } else template_name;
                const where = included.?.get(name) orelse break :blk none;
                const made: u32 = @intCast(analysis.declarations.items().len);
                const class = symbol_classes.class_of_kind(declarations.kind[index]);
                analysis.declaration_sites.push(.{
                    .token = none,
                    .global = true,
                    .class = class,
                    .modifiers = symbol_classes.declaration_modifiers(resolver, index),
                });
                const declared_type = if (declarations.kind[index].is_type_declaration())
                    declarations.static_value[index]
                else
                    declarations.value_type[index];
                analysis.declarations.push(.{
                    .name = name,
                    .detail = type_text(analysis, resolver, declared_type),
                    .kind = 0,
                    .range = where.range,
                    .selectionRange = null,
                });
                analysis.elsewhere.push(.{ .decl = made, .uri = where.uri, .range = where.range });
                declared_elsewhere.put(analysis.allocator, index, made) catch @panic("OOM");
                break :blk made;
            }
            // the declaration made by the template's node or by a node enclosing it
            var ancestor = declarations.node[@intFromEnum(template)];
            while (ancestor != none and analysis.node_declaration[ancestor] == none) {
                ancestor = analysis.node_parent[ancestor];
            }
            if (ancestor == none) break :blk none;
            break :blk analysis.node_declaration[ancestor];
        };
    }

    // a name only an earlier pass resolved: one a splice spelled, one in a stcfun not run again
    for (analysis.earlier_naming_token, analysis.token_meaning) |naming_token, *meaning| {
        if (meaning.* != none or naming_token == none) continue;
        meaning.* = analysis.token_meaning[naming_token];
    }

    // alternatives bind the same names (`A(x) | B(x)`), one a stcfun did not match means the same
    for (1..tree.ast_nodes.len()) |i| {
        if (tree.kind(@intCast(i)) != .partial__match_case_pattern_or) continue;
        const subtree = tree.subtree(@intCast(i));
        for (subtree[0]..subtree[1]) |binder_index| for (subtree[0]..subtree[1]) |other_index| {
            const binder: u32 = @intCast(binder_index);
            const other: u32 = @intCast(other_index);
            const binder_token = name_token(resolver, binder) orelse continue;
            const other_token = name_token(resolver, other) orelse continue;
            if (resolver.tree.kind(binder) != .identifier) continue;

            const meanings = analysis.token_meaning;
            if (meanings[binder_token] != none or meanings[other_token] == none) continue;
            const binder_name = resolver.name_pool.name_of_node(binder);
            if (binder_name != resolver.name_pool.name_of_node(other)) continue;
            meanings[binder_token] = meanings[other_token];
        };
    }

    // a named argument means the parameter or field within what is called (`p with (x = 1)`)
    for (0..tree.ast_nodes.len()) |i| {
        const node: u32 = @intCast(i);
        const kind = tree.kind(node);
        if (kind != .fun_call and kind != .with) continue;
        const arguments = tree.arg(node, 1);
        if (tree.kind(arguments) != .partial__fun_call_param_tuple) continue;

        const callee = tree.arg(node, 0);
        const callee_type = type_declaration(analysis, resolver, callee);
        const callee_token = if (kind == .fun_call) name_token(resolver, callee) else null;
        const called = if (callee_token) |token| analysis.token_meaning[token] else none;
        for (tree.laidout_children(.partial__fun_call_param_tuple, arguments)) |argument| {
            // a part of a field (`pos.x = ..`) names the field at its root, members after it
            var identifier = tree.arg_name(argument);
            while (kind == .with and identifier != 0 and
                (tree.kind(identifier) == .member or tree.kind(identifier) == .array_index))
            {
                identifier = tree.arg(identifier, 0);
            }
            if (identifier == 0 or tree.kind(identifier) != .identifier) continue;
            const name = resolver.name_pool.text_of(resolver.name_pool.name_of_node(identifier));
            // within `called` or within another overload of it (`mixed(1, b = 2)`)
            const meaning = if (callee_type) |type_range|
                within(analysis, type_range, name)
            else if (called != none) blk: {
                const function_name = analysis.declarations.items()[called].name;
                var found = within(analysis, analysis.declarations.items()[called].range, name);
                for (analysis.declarations.items()) |declaration| {
                    if (found != none) break :blk found;
                    if (declaration.selectionRange == null) continue;
                    if (!std.mem.eql(u8, declaration.name, function_name)) continue;
                    found = within(analysis, declaration.range, name);
                }
                break :blk found;
            } else none;
            analysis.token_meaning[tree.arg(identifier, 0)] = meaning;
        }
    }

    // a name the resolver reported undefined stays so
    const diagnostics = resolver.doctor.diagnostics.columns();
    for (diagnostics.code, diagnostics.node) |code, node| {
        if (code != .undefined_name) continue;
        const token = resolver.tree.token(node) orelse continue;
        analysis.token_meaning[token] = undefined_name;
    }

    // the other names in source order
    // names code the resolver did not check has not met before
    var unmet: DynamicBuffer(u32) = .init(analysis.allocator, 16);
    for (analysis.token_leaf, 0..) |leaf, token| {
        if (leaf == none or resolver.tree.kind(leaf) != .identifier) continue;
        if (analysis.token_meaning[token] != none) continue;

        // a field or case lies within its base's type, a positional one (`A.$1`) is declared by it
        // other members and named arguments go by their unique name, the other names by scope
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
            if (meaning.* == none and positional(name)) {
                for (analysis.declarations.items(), 0..) |declaration, i| {
                    if (!std.meta.eql(declaration.range, type_range)) continue;
                    meaning.* = @intCast(i);
                    break;
                }
            }
        }
        if (meaning.* == none) {
            meaning.* = if (goes_by_parent) unique(analysis, name) else blk: {
                // the nearest one before `leaf` within a node enclosing it, else a global one
                var candidates: DynamicBuffer(u32) = .init(analysis.allocator, 8);
                var candidate_tokens: DynamicBuffer(u32) = .init(analysis.allocator, 8);
                const sites = analysis.declaration_sites.items();
                for (analysis.declarations.items(), sites, 0..) |declaration, site, i| {
                    if (declaration.selectionRange == null) continue;
                    if (!std.mem.eql(u8, declaration.name, name)) continue;
                    candidates.push(@intCast(i));
                    candidate_tokens.push(site.token);
                }

                if (nearest(analysis, leaf, candidate_tokens.items())) |i| {
                    break :blk candidates.items()[i];
                }
                for (candidates.items()) |candidate| {
                    if (sites[candidate].global) break :blk candidate;
                }
                break :blk none;
            };
        }
        const is_intrinsic = name.len > 0 and name[0] == '$' or std.mem.startsWith(u8, name, "__");
        // a builtin (`__os`) is declared nowhere, its uses share one declaration
        if (meaning.* == none and is_intrinsic) meaning.* = blk: {
            const use = spans[token];
            for (analysis.declarations.items(), 0..) |declaration, i| {
                if (declaration.selectionRange != null) continue;
                if (std.mem.eql(u8, declaration.name, name)) break :blk @intCast(i);
            }

            analysis.declaration_sites.push(.{
                .token = none,
                .global = false,
                .class = .property,
                .modifiers = 0,
            });
            // one the completion knows is described by it
            var detail: []const u8 = "builtin";
            if (Completion.described(name)) |entry| {
                const format = "{s}  # {s}";
                const arguments = .{ entry.ty, entry.doc };
                detail = std.fmt.allocPrint(analysis.allocator, format, arguments) catch
                    @panic("OOM");
            }
            analysis.declarations.push(.{
                .name = name,
                .detail = detail,
                .kind = 0,
                .range = positions.range(analysis, use[0], use[1]),
                .selectionRange = null,
            });
            break :blk @intCast(analysis.declarations.items().len - 1);
        };
        if (meaning.* != none or goes_by_parent) continue;

        // unchecked code declares a name where it first appears (`Res.Ok(v) => v` never matched)
        var same_name: DynamicBuffer(u32) = .init(analysis.allocator, 4);
        for (unmet.items()) |unmet_token| {
            const unmet_name = resolver.name_pool.name_of_node(analysis.token_leaf[unmet_token]);
            if (unmet_name == resolver.name_pool.name_of_node(leaf)) same_name.push(unmet_token);
        }
        const nearest_index = nearest(analysis, leaf, same_name.items()) orelse {
            unmet.push(@intCast(token));
            continue;
        };

        const first_token = same_name.items()[nearest_index];
        if (analysis.token_meaning[first_token] == none) {
            declare(analysis, first_token, .{
                .name = name,
                .detail = "",
                .class = .variable,
                .modifiers = 0,
                .outlined = false,
                .global = false,
                .extent = null,
                .name_span = spans[first_token],
            });
        }
        analysis.token_meaning[token] = analysis.token_meaning[first_token];
    }

    fallbacks.link(analysis, lexer, resolver);
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
        // a realization is declared where its template is
        const index: DeclPool.Index = @enumFromInt(i);
        const template = resolver.generics.template_of.get(index) orelse index;
        const node = resolver.decl_pool.get(template, .node);
        naming_token.* = named(resolver, node, declarations.name[i]) orelse continue;

        // the declaration named at `naming_token` as this pass found it, a later pass overwrites it
        const past_index = &analysis.past_declaration_index[naming_token.*];
        if (past_index.* == none) {
            past_index.* = @intCast(analysis.past_declarations.items().len);
            analysis.past_declarations.push(undefined);
        }

        const name = resolver.name_pool.text_of(declarations.name[i]);
        // a type shows what it is, a value its type
        const declared_type = if (declarations.kind[i].is_type_declaration())
            declarations.static_value[i]
        else
            declarations.value_type[i];
        const detail = type_text(analysis, resolver, declared_type);
        const class = symbol_classes.class_of_kind(declarations.kind[i]);
        const modifiers = symbol_classes.declaration_modifiers(resolver, i);
        analysis.past_declarations.items()[past_index.*] = .{
            .name = name,
            .detail = detail,
            .class = class,
            .modifiers = modifiers,
            .extent = resolver.tree.extent(node),
        };
    }

    for (0..resolver.tree.ast_nodes.len()) |i| {
        const token = name_token(resolver, @intCast(i)) orelse continue;
        const declaration = resolver.node_declarations[i];
        if (declaration == .none) continue;
        const naming_token = naming_tokens[@intFromEnum(declaration)];
        analysis.earlier_naming_token[token] = naming_token;
        if (naming_token != none) continue;
        // the names of this pass are gone with it
        const name = resolver.name_pool.text_of(resolver.decl_pool.get(declaration, .name));
        analysis.earlier_names[token] = analysis.allocator.dupe(u8, name) catch @panic("OOM");
    }
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

// the top-level declarations of the files a program includes by name, in the first file declaring
// each: its uri and the range of the name there
fn read_included(
    analysis: *Analysis,
    resolver: *Resolver,
) std.StringHashMapUnmanaged(Analysis.Elsewhere) {
    const allocator = analysis.allocator;
    var names: std.StringHashMapUnmanaged(Analysis.Elsewhere) = .empty;
    for (resolver.session.files.items) |file| {
        const text = resolver.tree.text_bytes.items()[file.at..][0..file.len];
        var lexer = Lexer{ .src_bytes = text, .tokens = .init(allocator, 1024) };
        lexer.gen_tokens() catch continue;
        var parser = mond.Parser.init(allocator, lexer.tokens, text, lexer.tokens.column(.span));
        parser.build_ast() catch continue;

        var uri: std.ArrayList(u8) = .empty;
        uri.appendSlice(allocator, "file://") catch @panic("OOM");
        for (file.path) |byte| switch (byte) {
            'a'...'z', 'A'...'Z', '0'...'9', '/', '-', '_', '.', '~' => {
                uri.append(allocator, byte) catch @panic("OOM");
            },
            else => uri.print(allocator, "%{X:0>2}", .{byte}) catch @panic("OOM"),
        };
        const tree = &parser.tree;
        for (parser.global_store.items()) |root| {
            var declared = root;
            while (true) switch (tree.kind(declared)) {
                .mod_pub, .mod_mut, .mod_stc => declared = tree.arg(declared, 0),
                else => break,
            };
            const name_node = switch (tree.kind(declared)) {
                .assign_typed => tree.arg(tree.arg(declared, 0), 1),
                .assign => tree.arg(declared, 0),
                .def_var => tree.arg(declared, 1),
                else => continue,
            };
            if (tree.kind(name_node) != .identifier) continue;
            const entry = names.getOrPut(allocator, tree.text(name_node, text)) catch @panic("OOM");
            if (entry.found_existing) continue;
            // a line and a column in utf-16 code units, as `positions` counts the document
            const span = tree.span(name_node);
            const line_start = if (std.mem.lastIndexOfScalar(u8, text[0..span[0]], '\n')) |at|
                at + 1
            else
                0;
            const line: u32 = @intCast(std.mem.count(u8, text[0..span[0]], "\n"));
            const start = positions.utf16_length(text[line_start..span[0]]);
            const end = start + positions.utf16_length(text[span[0]..span[1]]);
            entry.value_ptr.* = .{ .decl = none, .uri = uri.items, .range = .{
                .start = .{ .line = line, .character = start },
                .end = .{ .line = line, .character = end },
            } };
        }
    }
    return names;
}

// a positional name: `$0`, `$1`
fn positional(name: []const u8) bool {
    return name.len > 1 and name[0] == '$' and std.ascii.isDigit(name[1]);
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

// the only member, field, case or function called `name`
fn unique(analysis: *Analysis, name: []const u8) u32 {
    var found: u32 = none;
    for (analysis.declarations.items(), 0..) |declaration, i| {
        const is_member_kind = declaration.kind == symbol_classes.symbol_kind(.method) or
            declaration.kind == symbol_classes.symbol_kind(.property) or
            declaration.kind == symbol_classes.symbol_kind(.function) or
            declaration.kind == symbol_classes.symbol_kind(.enumMember);
        if (!is_member_kind or !std.mem.eql(u8, declaration.name, name)) continue;
        if (found != none) return none;
        found = @intCast(i);
    }
    return found;
}

// of the tokens `candidates`, the nearest one before `node` within a node enclosing it
fn nearest(analysis: *Analysis, node: u32, candidates: []const u32) ?usize {
    var ancestor = analysis.node_parent[node];
    while (ancestor != none) : (ancestor = analysis.node_parent[ancestor]) {
        var best: ?usize = null;
        for (candidates, 0..) |token, i| {
            const is_inside = token >= analysis.node_first_token[ancestor];
            const is_before = token < analysis.node_first_token[node];
            if (!is_inside or !is_before) continue;
            // a name declared in a block or match arm is seen only within it
            const leaf = analysis.token_leaf[token];
            const scope = if (leaf == none) none else analysis.node_scope[leaf];
            if (scope != none) {
                var scope_ancestor = node;
                while (scope_ancestor != none and scope_ancestor != scope) {
                    scope_ancestor = analysis.node_parent[scope_ancestor];
                }
                if (scope_ancestor != scope) continue;
            }
            if (best) |best_index| {
                if (token <= candidates[best_index]) continue;
            }
            best = i;
        }
        if (best != null) return best;
    }
    return null;
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
        .variant_subset_type => |subset| return type_owner(analysis, resolver, subset.whole),
        .int_type,
        .float_type,
        .simple_type,
        .meta_type,
        .array_type,
        .slice_type,
        .function_type,
        .unified_variant_type,
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

pub fn type_text(analysis: *Analysis, resolver: *Resolver, type_index: StaticIndex) []const u8 {
    var text: std.Io.Writer.Allocating = .init(analysis.allocator);
    if (type_index != .none and type_index != .poison_type) {
        const pool = &resolver.static_pool;
        pool.format(&resolver.name_pool, type_index, &text.writer) catch @panic("OOM");
    }
    return text.written();
}
