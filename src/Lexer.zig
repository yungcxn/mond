const std = @import("std");
const DynBuf = @import("ds/dynbuf.zig").DynBuf;

const vertwspace = [_]u8{ ' ', '\t' };
const anywspace = [_]u8{ ' ', '\t', '\r', '\n' };
const TextSpan = @Vector(2, u32);

const Token = enum(u8) {
    // keywords, must be of form kw_...
    kw_main,
    kw_u32,
    kw_mut,
    kw_true,
    kw_false,

    // punctuators, must be of form @"punct_..."
    //   just @"..." means it's an clear punctuator
    @"$",
    @"\n",
    @"(",
    @")",
    @"[",
    @"]",
    @"<",
    @">",
    @"{",
    @"}",

    @"punct_=",
    @"punct_+",
    @"punct_-",
    @"punct_*",
    @"punct_/",

    @"punct_==",
    @"punct_+=",
    @"punct_-=",
    @"punct_*=",
    @"punct_/=",
    @"punct_++",
    @"punct_--",
    @"punct_**",

    @"punct_&&=",

    // everything below this needs a textspan //

    identifier,

    // values, must be of form val_...
    val_string,
    val_int,
    val_float,
    val_char,

    fn puncts(comptime len: usize) []const struct { []const u8, Token } {
        return comptime blk: {
            var list: []const struct { []const u8, Token } = .{};
            for (@typeInfo(@This()).@"enum".fields) |field| {
                if (!std.mem.startsWith(u8, field.name, "punct_") or field.name.len != 6 + len) continue;
                list = list ++ .{ field.name[6 .. 6 + len], @field(@This(), field.name) };
            }
            break :blk list;
        };
    }

    fn keywords() []const struct { []const u8, Token } {
        return comptime blk: {
            var list: []const struct { []const u8, Token } = .{};
            for (@typeInfo(@This()).@"enum".fields) |field| {
                if (!std.mem.startsWith(u8, field.name, "kw_")) continue;
                list = list ++ .{ field.name[3..], @field(@This(), field.name) };
            }
            break :blk list;
        };
    }

    const punct_tbl: []const []const struct { []const u8, Token } = .{
        puncts(1),
        puncts(2),
        puncts(3),
    };

    pub inline fn punct_from_str(punct_str: []const u8) ?Token {
        inline for (punct_tbl[punct_str.len]) |punct_pair| {
            if (std.mem.eq(u8, punct_str, punct_pair[0])) return punct_pair[1];
        }
        return null;
    }

    pub inline fn kw_from_str(kw_str: []const u8) ?Token {
        inline for (keywords()) |kw_pair| {
            if (std.mem.eq(u8, kw_str, kw_pair[0])) return kw_pair[1];
        }
        return null;
    }

    // pub inline fn needs_textspan(tok: Token) bool {
    //     return @intFromEnum(tok) >= @intFromEnum(.identifier);
    // }
};

// if `tok` needs a textspan, the next 4 bytes are a ref in `spans`
const AmbigToken = union {
    tok: Token,
    idx_part: u8,
};

src_code: []u8,
cursor: usize = 0,

tokens: DynBuf(AmbigToken),
spans: DynBuf(TextSpan),

// -> `null`: outside of `src_code`
inline fn at_set(self: *@This(), comptime charset: []const u8) ?bool {
    const viewed = self.peek() orelse return null;
    inline for (charset) |char| {
        if (viewed == char) return true;
    }
    return false;
}

// -> `false`: outside of `src_code`
inline fn safe_skip_set(self: *@This(), comptime charset: []const u8) bool {
    while (self.at_set(charset)) |is_at| {
        if (is_at) {
            self.cursor += 1;
        } else {
            return true;
        }
    }
    return false;
}

// -> `false`: outside of `src_code`
// esc: escaped, exc: exclusive (cursor is at `char` + 1)
inline fn take_esc_exc(self: *@This(), char: u8) bool {
    var c0: u8 = 0;
    while (self.pop_srcbyte()) |c| {
        if (char == c and c0 != '\\') return true;
        c0 = c;
    }
    return false;
}

inline fn take_exc(self: *@This(), char: u8) bool {
    while (self.pop_srcbyte()) |c| {
        if (char == c) return true;
    }
    return false;
}

inline fn peek_srcbyte(self: *@This()) ?u8 {
    if (self.cursor < self.src_code.len) {
        @branchHint(.likely);
        return self.src_code[self.cursor];
    } else {
        @branchHint(.unlikely);
        return null;
    }
}

inline fn pop_srcbyte(self: *@This()) ?u8 {
    defer self.cursor += 1;
    return self.peek_srcbyte();
}

inline fn push_tok(self: *@This(), tok: Token) void {
    self.tokens.push(.{ .tok = tok });
}

inline fn push_spanned_tok(self: *@This(), from: usize, tok: Token) void {
    const newspan_idx = self.spans.head;
    const idx_bytes: [4]u8 = @bitCast(newspan_idx);
    self.spans.push(.{ from, self.cursor });

    const newtok: AmbigToken = .{ .tok = tok };
    self.tokens.push(newtok);
    inline for (idx_bytes) |b| {
        const newidx: AmbigToken = .{ .idx_part = b };
        self.tokens.push(newidx);
    }
}

// we assume to always start on "something worth to scan" (no whitespace)
// therefore, we scan and advance cursor until next "worthy-to-scan" char
// -> `false`: outside of `src_code`
inline fn gen_next_tok(self: *@This()) !bool {
    if (self.pop_srcbyte()) |c0| switch (c0) {
        '0'...'9' => { // val_int or val_float
            const cursor0 = self.cursor - 1;
            var has_dot = false;
            while (self.pop_srcbyte()) |c| switch (c) {
                '.' => {
                    if (has_dot) return error.LexingError_2DotsInNumeric;
                    has_dot = true;
                },
                '0'...'9' => continue,
                else => break,
            };
            self.push_spanned_tok(cursor0, if (has_dot) .val_float else .val_int);
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

            self.push_spanned_tok(cursor0, .val_char);
        },
        '"' => { // val_string
            const cursor0 = self.cursor;
            if (self.take_esc_exc('"')) {
                self.push_spanned_tok(cursor0, .val_string);
            } else return error.LexingError_StringScanEOF;
        },
        'a'...'z', 'A'...'Z', '_' => { // literal or keyword
            const cursor0 = self.cursor - 1;

            while (self.pop_srcbyte()) |c| switch (c) {
                'a'...'z', 'A'...'Z', '_' => continue,
                else => break,
            };

            if (Token.kw_from_str(self.src_code[cursor0..self.cursor])) |found_kw| {
                self.push_tok(found_kw);
            } else {
                self.push_spanned_tok(cursor0, .identifier);
            }
        },
        // clear punctuators (@"...")
        '$' => self.push_tok(.@"$"),
        '\n' => self.push_tok(.@"\n"),
        '(' => self.push_tok(.@"("),
        ')' => self.push_tok(.@"("),
        '[' => self.push_tok(.@"["),
        ']' => self.push_tok(.@"]"),
        '<' => self.push_tok(.@"<"),
        '>' => self.push_tok(.@">"),
        '{' => self.push_tok(.@"{"),
        '}' => self.push_tok(.@"}"),
        else => { // unclear punctuators (@"punct_...")
            const cursor0 = self.cursor - 1;
            var longest_valid_punct: ?Token = null;
            inline for (1..4) |_| {
                if (self.cursor >= self.src_code.len) break;

                if (Token.punct_from_str(self.src_code[cursor0..self.cursor])) |found_punct| {
                    longest_valid_punct = found_punct;
                } else break;

                self.cursor += 1;
            }

            if (longest_valid_punct) |punct| {
                self.push_tok(punct);
            } else return error.LexingError_InvalidPunctuator;
        },
        '#' => { // comment... skip until newline (inclusively)
            self.take_exc('\n');
        },
    };
    return self.skip_set(vertwspace);
}

pub fn gen_tokens(self: *@This()) void {
    self.skip_set(anywspace);
    while (self.gen_next_tok()) {}
}
