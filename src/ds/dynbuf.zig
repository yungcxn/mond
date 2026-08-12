const std = @import("std");

pub fn DynBuf(T: type) type {
    return struct {
        pub const Elem = T;

        alloc: std.mem.Allocator,
        buf: []T,
        head: u32 = 0,
        cap: u32,

        pub fn init(alloc: std.mem.Allocator, initial_cap: u32) @This() {
            if (initial_cap == 0) @panic("Zero cap'd dynbuf");
            return @This(){
                .alloc = alloc,
                .buf = alloc.alloc(T, initial_cap) catch @panic("OOM"),
                .cap = initial_cap,
            };
        }

        pub fn deinit(self: *@This()) void {
            self.alloc.free(self.buf);
        }

        inline fn grow(self: *@This()) void {
            self.cap *= 2;
            self.buf = self.alloc.realloc(self.buf, self.cap) catch @panic("OOM");
        }

        pub inline fn get(self: *@This(), idx: u32) ?T {
            if (idx >= self.head) return null;
            return self.buf[idx];
        }

        pub inline fn peek(self: *@This()) ?T {
            return self.get(self.head - 1);
        }

        pub inline fn push(self: *@This(), value: T) void {
            if (self.head >= self.cap) self.grow();

            self.buf[self.head] = value;
            self.head += 1;
        }

        pub inline fn sliced(self: *const @This()) []T {
            return self.buf[0..self.head];
        }
    };
}

fn PoolType(StructT: type) type {
    const fields = @typeInfo(StructT).@"struct".fields;
    const n = fields.len;

    comptime var names: [n][]const u8 = undefined;
    comptime var types: [n]type = undefined;

    inline for (fields, 0..) |f, i| {
        names[i] = f.name;
        types[i] = DynBuf(f.type);
    }

    return @Struct(.auto, null, &names, &types, &@splat(.{}));
}

pub fn SoD(StructT: type) type {
    const Pool = PoolType(StructT);
    const fields = @typeInfo(StructT).@"struct".fields;

    return struct {
        pool: Pool,

        pub fn init(alloc: std.mem.Allocator, initial_cap: u32) @This() {
            var pool: Pool = undefined;
            inline for (fields) |f| {
                @field(pool, f.name) = DynBuf(f.type).init(alloc, initial_cap);
            }
            return @This(){
                .pool = pool,
            };
        }

        pub fn deinit(self: *@This()) void {
            inline for (fields) |f| {
                @field(self.pool, f.name).deinit();
            }
        }

        pub fn push(self: *@This(), value: StructT) void {
            inline for (fields) |f| {
                @field(self.pool, f.name).push(@field(value, f.name));
            }
        }

        pub fn get(self: *@This(), idx: u32) ?StructT {
            var result: StructT = undefined;
            inline for (fields) |f| {
                const v = @field(self.pool, f.name).get(idx) orelse return null;
                @field(result, f.name) = v;
            }
            return result;
        }

        pub fn peek(self: *@This()) ?StructT {
            const head = @field(self.pool, fields[0].name).head;
            if (head == 0) return null;
            return self.get(head - 1);
        }

        pub fn get_field(
            self: *@This(),
            comptime field: @EnumLiteral(),
            idx: u32,
        ) ?@TypeOf(@field(self.pool, @tagName(field))).Elem {
            return @field(self.pool, @tagName(field)).get(idx);
        }

        pub fn peek_field(
            self: *@This(),
            comptime field: @EnumLiteral(),
        ) ?@TypeOf(@field(self.pool, @tagName(field))).Elem {
            return @field(self.pool, @tagName(field)).peek();
        }

        pub fn len(self: *const @This()) u32 {
            return @field(self.pool, fields[0].name).head;
        }

        pub const Sliced = blk: {
            var slice_names: [fields.len][]const u8 = undefined;
            var slice_types: [fields.len]type = undefined;
            for (fields, 0..) |f, i| {
                slice_names[i] = f.name;
                slice_types[i] = []f.type;
            }
            break :blk @Struct(.auto, null, &slice_names, &slice_types, &@splat(.{}));
        };

        pub fn sliced(self: *const @This()) Sliced {
            var result: Sliced = undefined;
            inline for (fields) |f| {
                @field(result, f.name) = @field(self.pool, f.name).sliced();
            }
            return result;
        }

        pub fn sliced_field(
            self: *const @This(),
            comptime field: @EnumLiteral(),
        ) []@TypeOf(@field(self.pool, @tagName(field))).Elem {
            return @field(self.pool, @tagName(field)).sliced();
        }
    };
}
