const std = @import("std");
const mond = @import("mond");
const Lexer = mond.Lexer;
const Resolver = mond.Resolver;
const DynamicBuffer = mond.DynamicBuffer;
const Completion = @import("Completion.zig");
const Analysis = @import("Analysis.zig");
const linking = @import("linking.zig");
const positions = @import("positions.zig");
const symbol_classes = @import("symbol_classes.zig");
const Type = Analysis.Type;
const Kind = Lexer.Token.Kind;
const none = Analysis.none;
const undefined_name = Analysis.undefined_name;

// the semantic tokens: every token classed by its kind, then by what the resolver and links found

// the class of a token kind by its name in the lexer, so new keywords and operators are colored too
const class_of_token_kind = blk: {
    @setEvalBranchQuota(10_000);
    var table: [256]?Type = @splat(null);
    for (@typeInfo(Kind).@"enum".fields) |field| {
        if (std.mem.startsWith(u8, field.name, "kw_")) table[field.value] = .keyword;
        if (std.mem.startsWith(u8, field.name, "xpct_")) table[field.value] = .operator;
    }
    for (@intFromEnum(Kind.kw_u8)..@intFromEnum(Kind.kw_bool) + 1) |i| table[i] = .type;
    // the syntax between code and the code it writes: a quote, a reflection, a hole
    table[@intFromEnum(Kind.kw_quote)] = .macro;
    table[@intFromEnum(Kind.kw_refl)] = .macro;
    table[@intFromEnum(Kind.@"xpct_@")] = .macro;
    table[@intFromEnum(Kind.identifier)] = .variable;
    table[@intFromEnum(Kind.val_string)] = .string;
    table[@intFromEnum(Kind.val_char)] = .string;
    table[@intFromEnum(Kind.val_int)] = .number;
    table[@intFromEnum(Kind.val_float)] = .number;
    break :blk table;
};

// the keywords a declaration starts with, what the name after them is
const class_after_keyword = blk: {
    var table: [256]?Type = @splat(null);
    for ([_]Kind{ .kw_fun, .kw_stcfun, .kw_inlfun }) |kind| table[@intFromEnum(kind)] = .function;
    table[@intFromEnum(Kind.kw_type)] = .type;
    table[@intFromEnum(Kind.kw_variant)] = .@"enum";
    table[@intFromEnum(Kind.kw_trait)] = .interface;
    break :blk table;
};

// the tokens a bracket opens with: `(`, `*(`, `!{`, ..
const opens_bracket = blk: {
    var table: [256]bool = @splat(false);
    for (@typeInfo(Kind).@"enum".fields) |field| {
        const name = field.name;
        const ends_in_opening = std.mem.endsWith(u8, name, "(") or
            std.mem.endsWith(u8, name, "[") or
            std.mem.endsWith(u8, name, "{");
        table[field.value] = ends_in_opening;
    }
    break :blk table;
};

// `_` is no name, a builtin is what it is, a declared name what its keyword declares (in quotes)
// the meta syntax (`quote`, `refl`, the `<..>` of a splice, `@`) is a macro, what it holds is code
pub fn classify_lexically(analysis: *Analysis, lexer: *Lexer) void {
    const tokens = lexer.tokens.columns();
    analysis.token_class = analysis.allocator.alloc(?Type, tokens.tk.len) catch @panic("OOM");
    analysis.token_modifiers = analysis.allocator.alloc(u32, tokens.tk.len) catch @panic("OOM");
    @memset(analysis.token_modifiers, 0);

    // the bracket depth at every `<` opening a splice still open
    var open_splices: DynamicBuffer(u32) = .init(analysis.allocator, 4);
    var depth: u32 = 0;
    for (tokens.tk, tokens.span, analysis.token_class, 0..) |kind, span, *class, i| {
        class.* = class_of_token_kind[@intFromEnum(kind)];
        if (kind == .identifier) {
            const name = analysis.source[span[0]..span[1]];
            class.* = blk: {
                if (Completion.described(name)) |entry| {
                    if (entry.class == .function) break :blk .function;
                    break :blk .property;
                }
                if (i > 0) {
                    const after_keyword = class_after_keyword[@intFromEnum(tokens.tk[i - 1])];
                    if (after_keyword) |declared| break :blk declared;
                }
                if (std.mem.eql(u8, name, "_")) break :blk .keyword;
                break :blk .variable;
            };
        }

        if (opens_bracket[@intFromEnum(kind)]) depth += 1;
        switch (kind) {
            .@"pct_)", .@"pct_]", .@"pct_}" => depth -|= 1,
            // a `<` where no operand ends opens a splice
            .@"xpct_<" => if (i == 0 or !ends_operand(analysis.token_class, tokens.tk, i - 1)) {
                class.* = .macro;
                open_splices.push(depth);
            },
            // the first `>` outside the brackets in a splice closes it
            .@"xpct_>" => if (open_splices.last() == depth) {
                class.* = .macro;
                open_splices.len -= 1;
            },
            .@"xpct_.." => if (i > 0 and tokens.tk[i - 1] == .@"xpct_@") {
                class.* = .macro;
            },
            else => {},
        }
    }
}

// a token an operand ends with, a `<` after it compares
fn ends_operand(token_class: []const ?Type, kinds: []const Kind, index: usize) bool {
    return switch (kinds[index]) {
        .identifier,
        .val_string,
        .val_int,
        .val_float,
        .val_char,
        .@"pct_)",
        .@"pct_]",
        .kw_true,
        .kw_false,
        .@"xpct_.*",
        .@"xpct_.&",
        => true,
        .@"xpct_>" => token_class[index] == .macro,
        else => false,
    };
}

// names by their declaration, fields, cases and children of trees without one (`e.lhs`)
pub fn classify_resolved(resolver: *Resolver, token_class: []?Type, token_modifiers: []u32) void {
    const tree = resolver.tree;
    for (0..tree.ast_nodes.len()) |i| {
        const node: u32 = @intCast(i);
        const identifier, const undeclared_class: ?Type = switch (tree.kind(node)) {
            .identifier => .{ node, null },
            .member => .{ tree.arg(node, 1), member_class(resolver, tree.arg(node, 0)) },
            // the names in `tree with (lhs = x)` are children of the tree
            .with => {
                const copied = tree.arg(node, 0);
                const arguments = tree.arg(node, 1);
                if (!resolver.static_pool.is_tree(resolver.node_types[copied])) continue;
                if (tree.kind(arguments) != .partial__fun_call_param_tuple) continue;

                for (tree.manychildren(arguments)) |argument| {
                    const token = linking.name_token(resolver, tree.arg_name(argument)) orelse
                        continue;
                    token_class[token] = .property;
                }
                continue;
            },
            .partial__variant_def_param => .{
                tree.laidout_children(.partial__variant_def_param, node).name,
                .enumMember,
            },
            else => continue,
        };

        // a name a macro made is written at no token, landed code is at the splice that made it
        if (tree.kind(identifier) != .identifier or tree.arg(identifier, 1) != 0) continue;
        const token = tree.arg(identifier, 0);

        const declaration = resolver.node_declarations[node];
        if (declaration == .none) {
            // a builtin (`$src`) stays what it is, a later pass may know more of other names
            if (undeclared_class) |class| {
                const span = tree.span(identifier);
                const name = resolver.src_bytes[span[0]..span[1]];
                if (Completion.described(name) == null) token_class[token] = class;
            }
            continue;
        }

        const declaration_index = @intFromEnum(declaration);
        const kind = resolver.decl_pool.get(declaration, .kind);
        token_class[token] = symbol_classes.class_of_kind(kind);
        token_modifiers[token] = symbol_classes.declaration_modifiers(resolver, declaration_index);
    }
}

// a member of a type is a case, of any other value (a tree too) a field
fn member_class(resolver: *Resolver, base: u32) Type {
    const is_type = symbol_classes.is_type(resolver, base) or resolver.tree.kind(base) == .type_ast;
    return if (is_type) .enumMember else .property;
}

// encodes every token by its class, lsp wants each relative to the one before
pub fn encode(analysis: *Analysis, lexer: *Lexer) void {
    const tokens = lexer.tokens.columns();
    // a name no pass resolved (in a stcfun no pass ran, in a quote) is classed by what it links to
    if (analysis.token_meaning.len > 0) {
        for (
            tokens.tk,
            tokens.span,
            analysis.token_class,
            analysis.token_modifiers,
            analysis.token_meaning,
        ) |kind, span, *class, *modifiers, meaning| {
            if (kind != .identifier or class.* != .variable or modifiers.* != 0) continue;
            if (meaning == none or meaning == undefined_name) continue;

            const declaration_name = analysis.declarations.items()[meaning].name;
            if (!std.mem.eql(u8, declaration_name, analysis.source[span[0]..span[1]])) continue;

            const site = analysis.declaration_sites.items()[meaning];
            class.* = site.class;
            modifiers.* = site.modifiers;
        }
    }

    var previous_end: u32 = 0;
    for (
        tokens.span,
        tokens.tk,
        analysis.token_class,
        analysis.token_modifiers,
    ) |span, kind, class, modifiers| {
        // the span of a string or char leaves its quotes out
        const quote_width: u32 = @intFromBool(kind == .val_string or kind == .val_char);
        const start = span[0] - quote_width;
        // only whitespace and comments are between tokens, a comment runs from `#` to its line end
        const up_to_gap_end = analysis.source[0..start];
        var cursor = previous_end;
        while (std.mem.indexOfScalarPos(u8, up_to_gap_end, cursor, '#')) |comment_start| {
            const line_end = std.mem.indexOfScalarPos(u8, up_to_gap_end, comment_start, '\n');
            cursor = @intCast(line_end orelse start);
            push_token(analysis, @intCast(comment_start), cursor, .comment, 0);
        }
        previous_end = span[1] + quote_width;
        if (class) |token_class| push_token(analysis, start, previous_end, token_class, modifiers);
    }
    // and the comments after the last token
    const gap_end: u32 = @intCast(analysis.source.len);
    const up_to_gap_end = analysis.source[0..gap_end];
    var cursor = previous_end;
    while (std.mem.indexOfScalarPos(u8, up_to_gap_end, cursor, '#')) |comment_start| {
        const line_end = std.mem.indexOfScalarPos(u8, up_to_gap_end, comment_start, '\n');
        cursor = @intCast(line_end orelse gap_end);
        push_token(analysis, @intCast(comment_start), cursor, .comment, 0);
    }
}

// one token per line, editors draw none across lines
fn push_token(analysis: *Analysis, start: u32, end: u32, class: Type, modifiers: u32) void {
    var piece_start = start;
    var pieces = std.mem.splitScalar(u8, analysis.source[start..end], '\n');
    while (pieces.next()) |piece| : (piece_start += @intCast(piece.len + 1)) {
        if (piece.len == 0) continue;

        const piece_position = positions.position(analysis, piece_start);
        const previous = analysis.last_token_start;
        const character_delta = if (piece_position.line == previous.line)
            piece_position.character - previous.character
        else
            piece_position.character;
        analysis.token_data.append(&.{
            piece_position.line - previous.line,
            character_delta,
            positions.utf16_length(piece),
            @intFromEnum(class),
            modifiers,
        });
        analysis.last_token_start = piece_position;
    }
}
