const std = @import("std");
const StructOfArrays = @import("containers.zig").StructOfArrays;

const anywspace = [_]u8{ ' ', '\t', '\r', '\n' };

pub const TextSpan = @Vector(2, u32);

pub const LexingError = error{
    InvalidEscape,
    CharScanEOF,
    IllegalEmptyChar,
    CharNothingAfterEscape,
    StringScanEOF,
    InvalidPunctuator,
    ReservedName,
    EmptyFile,
};

pub const Token = struct {
    tk: Kind,
    span: TextSpan,

    pub const Kind = enum(u8) {
        none,

        // keywords, must be of form kw_...
        kw_assertsize,
        kw_with,
        kw_do,
        kw_self,
        kw_tagof,
        kw_tagtype,
        kw_notagtype,
        kw_and,
        kw_xor,
        kw_or,
        kw_as,
        kw_asbits,
        kw_oftype,
        kw_implof,
        kw_ret,
        kw_typeof,
        kw_isstc,
        kw_sizeof,
        kw_alignof,
        kw_lenof,
        kw_where,
        kw_pub,
        kw_inlfun,
        kw_fun,
        kw_stcfun,
        kw_in,
        kw_u8,
        kw_u16,
        kw_u32,
        kw_u64,
        kw_i8,
        kw_i16,
        kw_i32,
        kw_i64,
        kw_f16,
        kw_f32,
        kw_f64,
        kw_ast,
        kw_bool,
        kw_mut,
        kw_true,
        kw_false,
        kw_match,
        kw_if,
        kw_else,
        kw_for,
        kw_while,
        kw_loop,
        kw_brk,
        kw_cont,
        kw_defer,
        kw_type,
        kw_variant,
        kw_trait,
        kw_deinit,
        kw_stc,
        // `stc?` before a parameter: static when the argument is (no `kw_` name, so no keyword)
        stc_maybe,
        kw_stcif,
        kw_stcmatch,
        kw_stcwhile,
        kw_stcfor,
        kw_stcloop,
        kw_stcwhere,
        kw_quote,
        kw_refl,
        kw_include,
        kw_includeraw,
        kw_crash,
        kw_asm,
        kw_syscall,
        kw_fresh,

        // punctuators, must be of form @"pct_..." or for unclear: @"xpct_..."
        @"pct_(",
        @"pct_)",
        @"pct_[",
        @"pct_]",
        @"pct_{",
        @"pct_}",
        @"pct_,",
        @"pct_:",
        @"pct_;",

        @"xpct_.",
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
        @"xpct_@",
        @"xpct_~",

        @"xpct_==",
        @"xpct_++",
        @"xpct_--",
        @"xpct_||",
        @"xpct_!=",
        @"xpct_<=",
        @"xpct_>=",
        @"xpct_>>",
        @"xpct_<<",
        @"xpct_<-",
        @"xpct_+=",
        @"xpct_-=",
        @"xpct_*=",
        @"xpct_/=",
        @"xpct_%=",
        @"xpct_&&",
        @"xpct_*(",
        @"xpct_+(",
        @"xpct_!{",

        @"xpct_->", // for func ret type
        @"xpct_=>", // for `expr_match`
        @"xpct_.*",
        @"xpct_.&",
        @"xpct_??", // for selftag unwrap expression
        @"xpct_..",

        @"xpct_..<", // for `expr_genseq`
        @"xpct_..=", // for `expr_genseq`
        @"xpct_?<-", // for selftag arrow
        @"xpct_++(",
        @"xpct_**(",
        @"xpct_|||",

        // everything below this needs a textspan //

        identifier,

        // values, must be of form val_...
        val_string,
        val_int,
        val_float,
        val_char,

        fn xpcts(comptime len: u32) []const struct { []const u8, Token.Kind } {
            @setEvalBranchQuota(10000);
            return comptime blk: {
                var list: []const struct { []const u8, Token.Kind } = &.{};
                for (@typeInfo(@This()).@"enum".field_names) |fname| {
                    if (!std.mem.startsWith(u8, fname, "xpct_") or fname.len != 5 + len) continue;
                    list = list ++ .{.{ fname[5 .. 5 + len], @field(@This(), fname) }};
                }
                break :blk list;
            };
        }

        // the keywords of length `len`, a name is compared with the ones of its length only
        fn keywords(comptime len: u32) []const struct { []const u8, Token.Kind } {
            return comptime blk: {
                var list: []const struct { []const u8, Token.Kind } = &.{};
                for (@typeInfo(@This()).@"enum".field_names) |fname| {
                    if (!std.mem.startsWith(u8, fname, "kw_") or fname.len != 3 + len) continue;
                    list = list ++ .{.{ fname[3..fname.len], @field(@This(), fname) }};
                }
                break :blk list;
            };
        }

        const xpct_tbl: []const []const struct { []const u8, Token.Kind } = &.{
            xpcts(1),
            xpcts(2),
            xpcts(3),
        };

        const kw_tbl = blk: {
            @setEvalBranchQuota(100_000);
            var t: [16][]const struct { []const u8, Token.Kind } = undefined;
            for (&t, 0..) |*l, i| l.* = keywords(i);
            break :blk t;
        };

        pub inline fn xpct_from_str(xpct_str: []const u8) ?Token.Kind {
            for (xpct_tbl[xpct_str.len - 1]) |xpct_pair| {
                if (std.mem.eql(u8, xpct_str, xpct_pair[0])) return xpct_pair[1];
            }
            return null;
        }

        pub inline fn kw_from_str(kw_str: []const u8) ?Token.Kind {
            if (kw_str.len >= kw_tbl.len) return null;
            for (kw_tbl[kw_str.len]) |kw_pair| {
                if (std.mem.eql(u8, kw_str, kw_pair[0])) return kw_pair[1];
            }
            return null;
        }
    };
};

src_bytes: []u8,
cursor: u32 = 0,

tokens: StructOfArrays(Token),

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
// esc: escaped, exc: exclusive (cursor is at `char`)
inline fn take_esc(self: *@This(), char: u8) !bool {
    while (self.pop_srcbyte()) |c| {
        if (c == '\\') {
            try self.escape(self.pop_srcbyte() orelse return false);
        } else if (c == char) {
            self.cursor -= 1;
            return true;
        }
    }
    return false;
}

// the byte after a `\`, `x` takes two hex digits
inline fn escape(self: *@This(), c: u8) !void {
    switch (c) {
        'n', 't', 'r', '0', '\\', '\'', '"' => {},
        'x' => for (0..2) |_| switch (self.pop_srcbyte() orelse return LexingError.InvalidEscape) {
            '0'...'9', 'a'...'f', 'A'...'F' => {},
            else => return LexingError.InvalidEscape,
        },
        else => return LexingError.InvalidEscape,
    }
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
    const c = self.peek_srcbyte() orelse return null;
    self.cursor += 1;
    return c;
}

// a span is always stored for user-debug purposes, but really needed only for certain token-types
inline fn push_tok(self: *@This(), tok: Token.Kind, c0: u32) void {
    self.tokens.push(.{
        .tk = tok,
        .span = .{ c0, self.cursor },
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

                if (c0 == '0') switch (self.peek_srcbyte() orelse 0) {
                    'x', 'X', 'b', 'B', 'o', 'O' => {
                        self.cursor += 1;
                        while (self.peek_srcbyte()) |c| : (self.cursor += 1) switch (c) {
                            '0'...'9', 'a'...'f', 'A'...'F', '_' => continue,
                            else => break,
                        };
                        self.push_tok(.val_int, cursor0);
                        return self.safe_skip_set(anywspace);
                    },
                    else => {},
                };

                var last_dot_at: ?u32 = null;
                while (self.peek_srcbyte()) |c| : (self.cursor += 1) switch (c) {
                    '.' => {
                        if (last_dot_at) |ld| {
                            if (self.cursor == ld + 1) {
                                // detected '..' which could be a punctuator
                                // -> go one back, cursor is on first dot, then push int and resume
                                self.cursor -= 1;
                                self.push_tok(.val_int, cursor0);
                                return true;
                            } else {
                                self.push_tok(.val_float, cursor0);
                                return true;
                            }
                        }
                        last_dot_at = self.cursor;
                    },
                    '0'...'9', '_' => continue,
                    else => break,
                };
                self.push_tok(if (last_dot_at != null) .val_float else .val_int, cursor0);
            },
            '\'' => { // val_char
                const cursor0 = self.cursor;

                const c1 = self.pop_srcbyte() orelse return LexingError.CharScanEOF;
                switch (c1) {
                    '\'' => return LexingError.IllegalEmptyChar,
                    '\\' => {
                        const c2 = self.pop_srcbyte() orelse return LexingError.CharScanEOF;
                        if (c2 == '\'' and self.peek_srcbyte() != '\'') return LexingError.CharNothingAfterEscape;
                        try self.escape(c2);
                    },
                    else => {},
                }

                if ((self.pop_srcbyte() orelse return LexingError.CharScanEOF) != '\'') {
                    return LexingError.CharScanEOF;
                }

                self.cursor -= 1;
                self.push_tok(.val_char, cursor0);
                self.cursor += 1;
            },
            '"' => { // val_string
                const cursor0 = self.cursor;
                if (try self.take_esc('"')) {
                    self.push_tok(.val_string, cursor0);
                } else return LexingError.StringScanEOF;
                self.cursor += 1;
            },
            'a'...'z', 'A'...'Z', '_', '$' => { // literal or keyword
                const cursor0 = self.cursor - 1;

                while (self.peek_srcbyte()) |c| : (self.cursor += 1) switch (c) {
                    'a'...'z', 'A'...'Z', '_', '0'...'9' => continue,
                    else => break,
                };
                const name = self.src_bytes[cursor0..self.cursor];
                const is_positional = name.len > 1 and
                    std.mem.indexOfNone(u8, name[1..], "0123456789") == null;
                if (name[0] == '$' and !is_positional and !std.mem.eql(u8, name, "$it")) {
                    return LexingError.ReservedName;
                }

                const is_stc_maybe = std.mem.eql(u8, name, "stc") and self.peek_srcbyte() == '?';
                if (is_stc_maybe) {
                    self.cursor += 1;
                    self.push_tok(.stc_maybe, cursor0);
                } else if (Token.Kind.kw_from_str(name)) |found_kw| {
                    self.push_tok(found_kw, cursor0);
                } else {
                    self.push_tok(.identifier, cursor0);
                }
            },
            // clear punctuators (@"pct_...")
            '(' => self.push_tok(.@"pct_(", self.cursor - 1),
            ')' => self.push_tok(.@"pct_)", self.cursor - 1),
            '[' => self.push_tok(.@"pct_[", self.cursor - 1),
            ']' => self.push_tok(.@"pct_]", self.cursor - 1),
            '{' => self.push_tok(.@"pct_{", self.cursor - 1),
            '}' => self.push_tok(.@"pct_}", self.cursor - 1),
            ',' => self.push_tok(.@"pct_,", self.cursor - 1),
            ':' => self.push_tok(.@"pct_:", self.cursor - 1),
            ';' => self.push_tok(.@"pct_;", self.cursor - 1),

            else => { // unclear punctuators (@"xpct_...")
                const cursor0 = self.cursor - 1;
                const max_len: u32 = @min(3, @as(u32, @intCast(self.src_bytes.len - cursor0)));

                var len = max_len;
                const found: ?Token.Kind = while (len >= 1) : (len -= 1) {
                    if (Token.Kind.xpct_from_str(self.src_bytes[cursor0 .. cursor0 + len])) |k| {
                        break k;
                    }
                    if (len == 1) break null;
                } else null;

                if (found) |punct| {
                    self.cursor = cursor0 + len;
                    self.push_tok(punct, cursor0);
                } else return LexingError.InvalidPunctuator;
            },
        }

        return self.safe_skip_set(anywspace);
    }
    return false;
}

pub fn gen_tokens(self: *@This()) LexingError!void {
    if (!self.safe_skip_set(anywspace)) return LexingError.EmptyFile;
    while (try self.gen_next_tok()) {}
}

pub fn handle_err(self: *@This(), io: std.Io, path: []const u8, e: anyerror) noreturn {
    const at: u32 = @intCast(self.cursor -| 1);
    print_error(io, path, self.src_bytes, .{ at, at + 1 }, @errorName(e));
    return std.process.exit(1);
}

pub fn print_error(io: std.Io, path: []const u8, src: []const u8, problem_span: TextSpan, name: []const u8) void {
    const src_len: u32 = @intCast(src.len);

    var lstart_cur: u32 = @min(problem_span[0], src_len);
    while (lstart_cur != 0) {
        if (src[lstart_cur - 1] == '\n') break;

        lstart_cur -= 1;
    }

    var rend_cur: u32 = @min(@max(problem_span[1], lstart_cur), src_len);
    while (rend_cur != src_len) {
        if (src[rend_cur] == '\n') break;

        rend_cur += 1;
    }

    var lc: u32 = 1;
    for (src[0..lstart_cur]) |b| {
        if (b == '\n') lc += 1;
    }

    var buf: [4096]u8 = undefined;
    var linebuf: [1024]u8 = undefined;
    const shown_end = @min(rend_cur, lstart_cur + @as(u32, linebuf.len));
    const mark_start = @min(problem_span[0] -| lstart_cur, @as(u32, linebuf.len));
    const mark_end = @min(@max(problem_span[1] -| lstart_cur, mark_start + 1), @as(u32, linebuf.len));
    for (linebuf[0..mark_start], src[lstart_cur..][0..mark_start]) |*m, b| m.* = if (b == '\t') '\t' else ' ';
    @memset(linebuf[mark_start..mark_end], '~');

    const colored = std.Io.File.stderr().isTty(io) catch false;
    const red, const cyan, const reset = if (colored) .{ "\x1b[1;31m", "\x1b[36m", "\x1b[0m" } else .{ "", "", "" };
    const err_msg = std.fmt.bufPrint(
        &buf,
        "{s}:{d}:{d}: {s}{s}{s}\n{s}\n{s}{s}{s}\n",
        .{ path, lc, problem_span[0] -| lstart_cur + 1, red, name, reset, src[lstart_cur..shown_end], cyan, linebuf[0..mark_end], reset },
    ) catch @panic("OOM, could not print error");

    std.Io.File.stderr().writeStreamingAll(io, err_msg) catch @panic("print failed");
}
