const std = @import("std");
const mond = @import("mond");
const DynamicBuffer = mond.DynamicBuffer;
const Analysis = @import("Analysis.zig");
const positions = @import("positions.zig");
const Outline = Analysis.Outline;
const Symbol = Analysis.Symbol;

// the outline: the declarations with a kind, each holding the ones within it

pub fn build(analysis: *Analysis) []const Outline {
    const declarations = analysis.declarations.items();
    var outlined: DynamicBuffer(u32) = .init(analysis.allocator, 64);
    for (declarations, 0..) |declaration, i| {
        if (declaration.kind != 0) outlined.push(@intCast(i));
    }

    std.mem.sort(u32, outlined.items(), declarations, starts_first);

    var next: usize = 0;
    return nest(analysis, outlined.items(), &next, null);
}

// an enclosing declaration starts first, of two starting together the longer one encloses
fn starts_first(declarations: []const Symbol, left: u32, right: u32) bool {
    const left_range = declarations[left].range;
    const right_range = declarations[right].range;
    if (positions.before(left_range.start, right_range.start)) return true;
    const start_together = std.meta.eql(left_range.start, right_range.start);
    return start_together and positions.before(right_range.end, left_range.end);
}

// the declarations from `next.*` on that end before `enclosing_end`, each with the ones within it
fn nest(
    analysis: *Analysis,
    outlined: []const u32,
    next: *usize,
    enclosing_end: ?Analysis.Position,
) []const Outline {
    var nested: DynamicBuffer(Outline) = .init(analysis.allocator, 8);
    while (next.* < outlined.len) {
        const declaration = outlined[next.*];
        const declaration_end = analysis.declarations.items()[declaration].range.end;
        if (enclosing_end) |end| {
            if (positions.before(end, declaration_end)) break;
        }

        next.* += 1;
        const children = nest(analysis, outlined, next, declaration_end);
        nested.push(.{ .decl = declaration, .children = children });
    }
    return nested.items();
}
