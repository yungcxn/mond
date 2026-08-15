const std = @import("std");
const SoD = @import("ds/dynbuf.zig").SoD;

const anywspace = [_]u8{ ' ', '\t', '\r', '\n' };

pub const TextSpan = @Vector(2, u32);

pub const Token = struct {
    tk: Kind,
    span: TextSpan,

    pub const Kind = enum(u8) {
        none,

        // keywords, must be of form kw_...
        kw_return,
        kw_u8,
        kw_u32,
        kw_f32,
        kw_bool,
        kw_mut,
        kw_true,
        kw_false,
        kw_if,
        kw_else,

        // punctuators, must be of form @"pct_..." or for unclear: @"xpct_..."
        @"pct_$",
        @"pct_\n",
        @"pct_(",
        @"pct_)",
        @"pct_[",
        @"pct_]",
        @"pct_{",
        @"pct_}",
        @"pct_,",

        @"xpct_=",
        @"xpct_!",
        @"xpct_+",
        @"xpct_-",
        @"xpct_*",
        @"xpct_%",
        @"xpct_/",
        @"xpct_&",
        @"xpct_|",
        @"xpct_^",
        @"xpct_<",
        @"xpct_>",

        @"xpct_==",
        @"xpct_+=",
        @"xpct_-=",
        @"xpct_*=",
        @"xpct_/=",
        @"xpct_++",
        @"xpct_--",
        @"xpct_**",
        @"xpct_||",
        @"xpct_^^",
        @"xpct_&&",
        @"xpct_!=",
        @"xpct_<=",
        @"xpct_>=",

        @"xpct_&&=",

        // everything below this needs a textspan //

        identifier,

        // values, must be of form val_...
        val_string,
        val_int,
        val_float,
        val_char,

        fn xpcts(comptime len: u32) []const struct { []const u8, Token.Kind } {
            return comptime blk: {
                var list: []const struct { []const u8, Token.Kind } = &.{};
                for (@typeInfo(@This()).@"enum".fields) |field| {
                    if (!std.mem.startsWith(u8, field.name, "xpct_") or field.name.len != 5 + len) continue;
                    list = list ++ .{.{ field.name[5 .. 5 + len], @field(@This(), field.name) }};
                }
                break :blk list;
            };
        }

        fn keywords() []const struct { []const u8, Token.Kind } {
            return comptime blk: {
                var list: []const struct { []const u8, Token.Kind } = &.{};
                for (@typeInfo(@This()).@"enum".fields) |field| {
                    if (!std.mem.startsWith(u8, field.name, "kw_")) continue;
                    list = list ++ .{.{ field.name[3..field.name.len], @field(@This(), field.name) }};
                }
                break :blk list;
            };
        }

        const xpct_tbl: []const []const struct { []const u8, Token.Kind } = &.{
            xpcts(1),
            xpcts(2),
            xpcts(3),
        };

        const kw_tbl: []const struct { []const u8, Token.Kind } = keywords();

        pub inline fn xpct_from_str(xpct_str: []const u8) ?Token.Kind {
            for (xpct_tbl[xpct_str.len - 1]) |xpct_pair| {
                if (std.mem.eql(u8, xpct_str, xpct_pair[0])) return xpct_pair[1];
            }
            return null;
        }

        pub inline fn kw_from_str(kw_str: []const u8) ?Token.Kind {
            for (kw_tbl) |kw_pair| {
                if (std.mem.eql(u8, kw_str, kw_pair[0])) return kw_pair[1];
            }
            return null;
        }
    };
};

src_bytes: []u8,
cursor: u32 = 0,

tokens: SoD(Token),

// -> `null`: outside of `src_bytes`
inline fn at_set(self: *@This(), comptime charset: anytype) ?bool {
    const viewed = self.peek_srcbyte() orelse return null;
    inline for (charset) |char| {
        if (viewed == char) return true;
    }
    return false;
}

// -> `false`: outside of `src_bytes`
inline fn safe_skip_set(self: *@This(), comptime charset: anytype) bool {
    while (self.at_set(charset)) |is_at| {
        if (is_at) {
            self.cursor += 1;
        } else {
            return true;
        }
    }
    return false;
}

// -> `false`: outside of `src_bytes`
// esc: escaped, exc: exclusive (cursor is at `char` + 1)
inline fn take_esc(self: *@This(), char: u8) bool {
    var c0: u8 = 0;
    while (self.peek_srcbyte()) |c| : (self.cursor += 1) {
        if (char == c and c0 != '\\') return true;
        c0 = c;
    }
    return false;
}

inline fn adv_until(self: *@This(), char: u8) !void {
    while (self.peek_srcbyte()) |c| : (self.cursor += 1) {
        if (char == c) return;
    }
    return error.EOF;
}

inline fn peek_srcbyte(self: *@This()) ?u8 {
    if (self.cursor < self.src_bytes.len) {
        @branchHint(.likely);
        return self.src_bytes[self.cursor];
    } else {
        @branchHint(.unlikely);
        return null;
    }
}

inline fn pop_srcbyte(self: *@This()) ?u8 {
    defer self.cursor += 1;
    return self.peek_srcbyte();
}

inline fn push_tok(self: *@This(), tok: Token.Kind, opt_cursor0: ?u32) void {
    self.tokens.push(.{
        .tk = tok,
        .span = if (opt_cursor0) |c0| .{ c0, self.cursor } else .{ 0, 0 },
    });
}

// we assume to always start on "something worth to scan" (no whitespace)
// therefore, we scan and advance cursor until next "worthy-to-scan" char
// -> `false`: outside of `src_bytes`
inline fn gen_next_tok(self: *@This()) !bool {
    if (self.pop_srcbyte()) |c0| {
        switch (c0) {
            '#' => { // comment... skip until newline (inclusively)
                self.adv_until('\n') catch return false;
            },
            '0'...'9' => { // val_int or val_float
                const cursor0 = self.cursor - 1;
                var has_dot = false;
                while (self.peek_srcbyte()) |c| : (self.cursor += 1) switch (c) {
                    '.' => {
                        if (has_dot) return error.LexingError_2DotsInNumeric;
                        has_dot = true;
                    },
                    '0'...'9' => continue,
                    else => break,
                };
                self.push_tok(if (has_dot) .val_float else .val_int, cursor0);
            },
            '\'' => { // val_char
                const cursor0 = self.cursor;

                const c1 = self.pop_srcbyte() orelse return error.LexingError_CharScanEOF;
                switch (c1) {
                    '\'' => return error.LexingError_IllegalEmptyChar,
                    '\\' => {
                        const c2 = self.pop_srcbyte() orelse return error.LexingError_CharScanEOF;
                        if (c2 == '\'') return error.LexingError_CharNothingAfterEscape;
                    },
                    else => {},
                }

                if ((self.pop_srcbyte() orelse return error.LexingError_CharScanEOF) != '\'') {
                    return error.LexingError_CharScanEOF;
                }

                self.cursor -= 1;
                self.push_tok(.val_char, cursor0);
                self.cursor += 1;
            },
            '"' => { // val_string
                const cursor0 = self.cursor;
                if (self.take_esc('"')) {
                    self.push_tok(.val_string, cursor0);
                } else return error.LexingError_StringScanEOF;
                self.cursor += 1;
            },
            'a'...'z', 'A'...'Z', '_' => { // literal or keyword
                const cursor0 = self.cursor - 1;

                while (self.peek_srcbyte()) |c| : (self.cursor += 1) switch (c) {
                    'a'...'z', 'A'...'Z', '_', '0'...'9' => continue,
                    else => break,
                };

                if (Token.Kind.kw_from_str(self.src_bytes[cursor0..self.cursor])) |found_kw| {
                    self.push_tok(found_kw, null);
                } else {
                    self.push_tok(.identifier, cursor0);
                }
            },
            // clear punctuators (@"pct_...")
            '\n' => {
                // TODO
                // if (self.tokens.peek()) |last_tok| if (last_tok.tok != .@"pct_\n") {
                //     self.push_tok(.@"pct_\n"); // reduces overall token count if \n\n\n...
                // };
            },
            '$' => self.push_tok(.@"pct_$", null),
            '(' => self.push_tok(.@"pct_(", null),
            ')' => self.push_tok(.@"pct_)", null),
            '[' => self.push_tok(.@"pct_[", null),
            ']' => self.push_tok(.@"pct_]", null),
            '{' => self.push_tok(.@"pct_{", null),
            '}' => self.push_tok(.@"pct_}", null),
            ',' => self.push_tok(.@"pct_,", null),

            else => { // unclear punctuators (@"pct_...")
                const cursor0 = self.cursor - 1;
                var longest_valid_punct: ?Token.Kind = null;
                var longest_punctc: u32 = 0;

                inline for (1..4) |i| {
                    if (self.cursor >= self.src_bytes.len) break;

                    if (Token.Kind.xpct_from_str(self.src_bytes[cursor0..self.cursor])) |found_punct| {
                        longest_valid_punct = found_punct;
                        longest_punctc = i;
                    } else break;

                    self.cursor += 1;
                }

                if (longest_valid_punct) |punct| {
                    self.cursor = cursor0 + longest_punctc;
                    self.push_tok(punct, null);
                } else return error.LexingError_InvalidPunctuator;
            },
        }

        return self.safe_skip_set(anywspace);
    }
    return false;
}

pub fn gen_tokens(self: *@This()) !void {
    if (!self.safe_skip_set(anywspace)) return error.LexingError_EmptyFile;
    while (try self.gen_next_tok()) {}
}

pub fn dbg_print_tokens(self: *@This(), io: std.Io) void {
    std.Io.File.stdout().writeStreamingAll(io, "[DBG LEXER TOKENS]\n\n") catch @panic("print failed");

    var i: u32 = 0;
    while (i < self.tokens.len()) : (i += 1) {
        const spanned_tok = self.tokens.get(i) orelse unreachable;
        const tk = spanned_tok.tk;
        const span = spanned_tok.span;
        std.Io.File.stdout().writeStreamingAll(io, @tagName(tk)) catch @panic("print failed");
        if (span[0] != 0 and span[1] != 0) {
            const txt: []const u8 = self.src_bytes[span[0]..span[1]];

            std.Io.File.stdout().writeStreamingAll(io, " := ") catch @panic("print failed");
            std.Io.File.stdout().writeStreamingAll(io, txt) catch @panic("print failed");

            i += 4;
        }

        std.Io.File.stdout().writeStreamingAll(io, "\n") catch @panic("print failed");
    }

    std.Io.File.stdout().writeStreamingAll(io, "\n[END DBG LEXER TOKENS]\n") catch @panic("print failed");
}
