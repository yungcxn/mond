# Basics

## Program

A file is a list of declarations. `main` is the entry point and must exist exactly once.

```mond
fun square = (u32 x) -> u32: ret x * x;

main = () -> u32: ret square(7);
```

`main` takes nothing, or C's pair of the arguments' count and a pointer to them (`u32 argc, &&u8 argv`, any integer type for the count). It returns nothing, an integer (the exit code), a variant that is one integer (self-tagged by an integer, exiting with its bits, or without payloads, exiting with its tag) or `never`, and falling off the end returns `0`. Any other signature is `invalid_main`.

```mond
main = (u32 argc, &&u8 argv) -> u8 { ret argc as u8; }
```

A statement ends with `;` unless its last token is `}`. There are no empty statements (`;;`). A statement may discard a value (`stack.push(1);`).

## Comments and names

`#` runs to the end of the line. There are no block comments.

A name is `[A-Za-z_][A-Za-z0-9_]*`. The compiler names some things itself: what it puts into scope starts with `$` (`$it` in loops, `$0`, `$1`, .. for unnamed parameters and fields), and any other `$` name is the lexing error `ReservedName`; the constants it provides start with `__` (`__os`, `__arch`); `main` and the methods it calls (`init`, `deinit`, `has_next`, `next`) are plain names. `self` is the receiver in methods. After `.` a keyword is a name too (`x.deinit()`), and `deinit = ..` declares one. Keywords:

`fun` `stcfun` `inlfun` `type` `variant` `trait` `mut` `stc` `pub` `ret` `brk` `cont` `defer` `deinit` `if` `else` `stcif` `match` `stcmatch` `while` `stcwhile` `for` `stcfor` `loop` `stcloop` `in` `do` `where` `stcwhere` `implof` `tagof` `tagtype` `assertsize` `as` `asbits` `oftype` `typeof` `sizeof` `alignof` `lenof` `with` `and` `or` `xor` `true` `false` `self` `quote` `refl` `include` `includeraw` `crash` `asm` `syscall` `fresh` `ast` `bool` `u8` `u16` `u32` `u64` `i8` `i16` `i32` `i64` `f16` `f32` `f64`

## Literals

| kind | examples | default type |
|---|---|---|
| int | `42` `0xFF` `0b1010` `0o755` `1_000` | `u32`, else `u64`; negated: `i32`, else `i64` |
| float | `2.5` `3.` `1_0.25` | `f32` |
| char | `'a'` `'\n'` `'\x41'` | `u32`, fits `u8` when one is expected |
| string | `"hi\n"` | `[n]u8` (no terminating zero) |
| bool | `true` `false` | `bool` |
| unit | `{}` | `()` |

Escapes: `\n \t \r \0 \\ \' \" \xHH`. A float has no exponent and no leading dot.

A literal takes the type that is expected, if its value fits:

```mond
stc f32 F = 3;             #= F 3
stc u8 W = 200 + 100;      #= W 44
stc u32 X = 200 + 100;     #= X 300
stc C = 'z' - 'a';         #= C 25
u8 too_big = 256;          #! type_mismatch
```

## Types

| type | meaning |
|---|---|
| `u8 u16 u32 u64` `i8 i16 i32 i64` | integers, wrapping |
| `f16 f32 f64` | IEEE floats |
| `bool` | 1 byte |
| `()` | unit, written as a type only in function types |
| `[N]T` | array, `N` is a static integer |
| `[]T` | length taken from the value; behind a pointer or in a field it is a runtime length, only the address of the first element |
| `*T` / `&T` | writable / read-only pointer (`**u8`, `&*u8`, ...) |
| `type` | a type as a value (static only) |

Two types appear only in messages: `never` (the type of `ret`, `brk`, `cont`, or a `loop` without `brk`) and `runit` (an `if` or block used as a statement-like branch). Both disappear when joined with another type.

`[]T` means different things by position. A parameter `[]T` / `&[]T` / `*[]T` is realized for each length (see [functions.md](functions.md#length-generic-functions)). A `&[]T` or `*[]T` field or result is a runtime-length array: like a pointer in C, only the address of its first element (`sizeof` 8), and it only fits pointer parameters. A length is always static, so a runtime-length array has no `lenof`, no `for` over it and no `==` (each `not_static`); keep its length yourself, or cast it to a length (`p as &[4]u8`) to have one again. Its elements index as usual, unchecked.

```mond
[]u32 a = [1, 2, 3];       #: a [3]u32
stc u64 N = lenof a;        #= N 3
stc u64 S = sizeof u64;    #= S 8
type Text = *(&[]u8 bytes, u64 count);
fun first = (Text t) -> u8: ret t.bytes.*[0];
fun count = (Text t) -> u64: ret lenof t.bytes;          #! not_static
fun word = (Text t) -> u64: ret lenof (t.bytes as &[4]u8);
stc u64 AL = alignof a;    #= AL 4
typeof N m = 4;            #: m u64
```

### Arrays

`[a, b, c]` builds an array, and trailing commas are fine. The element type comes from the expected type, else from the join of the elements. Arrays are values: they are copied, and `==` compares them element by element. An array without a value is zero-filled. `lenof a` is its length, a static `u64`, also through a pointer to an array of a static length; `lenof` of anything else is `invalid_operand`. Arrays of different lengths don't join as values (`if c: "ab" else: "other"` is a `type_mismatch`), but runtime-length arrays do: a function returning `&[]u8` may return `"ab".&` or `"other".&`.

```mond
fun last = ([3]u32 xs) -> u32: ret xs[2];
stc u32 L = last([4, 5, 6]);      #= L 6
stc [4]u8 BYTES = [1, 2, 3, 4];
stc []u8 HEAD = BYTES as [2]u8;  #= HEAD [1, 2]
```

A range as an index is not allowed (`a[1..]` is `genexpr_index`). A part of an array is a cast: `a as [lo..<hi]T`.

### Pointers

`x.&` takes the address of any value, also of a literal (`"abc".&`). It is `*T` if `x` is writable, else `&T`. `p.*` dereferences. `*T` coerces to `&T`, and a pointer to `[n]T` coerces to a pointer to `T` or to `[]T`. An element pointer moves with `+ - ++ --` and indexes with `p[i]`. There is no null literal and no pointer difference. Integers and pointers convert only through bits: `p asbits u64`, `0 asbits *u8`.

```mond
fun bump = (*u32 p) { p.* += 1; }
fun run = () -> u32 {
    mut u32 n = 41;
    bump(n.&);
    ret n;
}
stc u32 R = run();   #= R 42
```

## Operators

Lowest to highest precedence, and `·` separates levels within a row. All binary operators are left associative.

| | |
|---|---|
| `+= -= *= /= %=` | compound assignment (a statement) |
| `or` · `xor` · `and` / `&&` | bool only, `and` and `or` short-circuit |
| `\|` · `^` · `&` | bitwise |
| `== !=` · `< > <= >=` | comparisons, not chained |
| `<< >>` | shifts (`>>` is arithmetic on signed types) |
| `+ -` · `* / %` | arithmetic (`/` truncates, `%` keeps the dividend's sign and takes integers only) |
| prefix | `- ! ++ -- typeof sizeof alignof lenof tagof crash asm syscall fresh` |
| postfix | `f(..) a[i] .m .* .& x++ x-- as asbits oftype ?? <- ?<- with ..` (unwrapping and labels: [control.md](control.md#unwrapping)) |

`crash`, `asm`, `syscall` and `fresh` take one operand, or several in parentheses: `crash "too big"`, `syscall (WRITE, 1, p, n)`. `!` is logical not on `bool` and bitwise not on integers. Unary `-` on an unsigned value wraps. The operands of a shift join like any others, so `u8 << u32` is a `u32`. `||` and `|||` are not logical or: they make unified variants (see [types.md](types.md#unified-variants-a--b-a--b)). There is no `**`, and no `<<=` or similar.

```mond
stc u32 A = 1 << 2 + 1;          #= A 8
stc i32 B = -7 / 2;              #= B -3
stc i8 C = 127 + 1;              #= C -128
stc f32 R = 5.5 % 2.0;           #! type_mismatch
stc u8 D = !0x0F as u8;          #= D 240
stc bool E = false and false xor true;  #= E true
```

Both operands of an operator must join to one type: `u8 + i8`, or an int with a float variable, is `type_mismatch`.

## Conversions

Implicit conversions only widen: same signedness to a wider type, unsigned to a strictly wider signed type, `f16` to `f32` to `f64`, `*T` to `&T`, `[n]T` to `[]T`, a case to its variant, and a type to a trait it implements. Everything else needs a cast.

`v as T`:
- int to int truncates or reinterprets the sign
- float to int rounds toward zero and saturates
- bool and int convert to number types
- a payload-free case converts to its tag
- pointer casts reinterpret
- array casts take a head or a sub-range

`v asbits T` reinterprets the bytes. `T` must be at least as large, and the extra bytes are zero. Mind the literal's default type: `1.5 asbits u64` reinterprets an `f32`, so write `(1.5 as f64) asbits u64` instead.

```mond
stc u8 T1 = 300 as u8;           #= T1 44
stc i16 T2 = 65535 as i16;       #= T2 -1
stc u8 T3 = 255.9 as u8;         #= T3 255
stc u32 T4 = 1.0 asbits u32;     #= T4 1065353216
stc u16 T5 = (300 as u8) as u16; #= T5 44
bool no = 1 as bool;             #! invalid_cast
```

Casts don't chain without parentheses: `x as u8 as u16` parses as `x as (u8 as u16)`.

## Machine code

`asm ".."` puts machine code where it stands, as a statement. Its text is a static `[]u8` in the assembler syntax of the target (AT&T on x86-64), and it only runs at run time. The compiler doesn't know what the code touches, so it counts as reading and writing all memory and every register: values live across it in memory or are saved around it, and it is never moved or removed. `__os` and `__arch` are static text naming the target (`"macos"`, `"linux"`; `"aarch64"`, `"x86_64"`), so a `stcmatch` picks the code for it:

```mond
fun relax = () {
    asm (stcmatch __arch { "aarch64" => "yield", "x86_64" => "pause", _ => "nop" });
}
stc u64 WORD = stcmatch __arch { "aarch64" => 8, "x86_64" => 8, _ => 4 };   #= WORD 8
stcfun at_compile_time = () -> u32 { asm "nop"; ret 1; }   #! not_static
stc u32 NO = at_compile_time();
```

`syscall (number, ..)` calls the kernel with up to six integers, `bool`s or pointers, each passed as one 64-bit register. It returns an `i64`: the kernel's result, or the negated error number when the call failed, on Linux as on macOS. The numbers are the system's own (`SYS_write` of its headers), picked with `stcmatch`:

```mond
stc u64 WRITE = stcmatch __os {
    "linux" => stcmatch __arch { "x86_64" => 1, _ => 64 },
    "macos" => 4,
    _ => 0,
};
fun print = (&[]u8 text) -> i64: ret syscall (WRITE, 1, text, lenof text);
fun twice = (f32 x) -> i64: ret syscall (WRITE, x);   #! type_mismatch
```

## Declarations

```mond
fun forms = () -> u32 {
    u32 a = 1;          # typed
    b = 2;              # untyped: declares, immutable, type inferred
    mut u32 c = 3;      # writable
    stc u32 d = 4;      # compile-time variable (writable at compile time)
    u32 e, f = 5, 6;    # several at once
    mut x, y = 1, 2;
    x, y = y, x;        # values are computed before any write: a swap
    c += a + b + d + e + f;
    ret c + x * 10;
}
stc u32 FORMS = forms();  #= FORMS 41
```

- `pub` marks what an `include` lets the program name, `includeraw` lets it name everything (see [metaprogramming.md](metaprogramming.md#crash-at-a-tree-include)).
- `x++` / `x--` give the old value, `++x` / `--x` the new one.
- Operands and arguments are evaluated left to right. An assignment evaluates its value before its place: in `a[i()] += f()`, `f()` runs first.
- `name = v` writes the visible `name`, or declares it if there is none. A typed or modified declaration (`mut`, `stc`, `pub`) always declares, and may shadow.
- A function, type, variant or trait is declared with its keyword: `f = () {}` is `missing_keyword`. `name = <include "f">` declares a namespace (see [metaprogramming.md](metaprogramming.md#crash-at-a-tree-include)). Only `main` and the methods the compiler calls by name (`init`, `deinit`, `has_next`, `next`) are written without `fun`; with it they are `redundant_fun`.
- Everything is immutable unless declared `mut`. A write needs every part writable: a `mut` field of a writable owner, an element of a writable array, or a write through a `*` pointer.
- A scalar declared without a value must be written on every path before it is read. Arrays and records without a value are zeroed.
- Globals see each other regardless of order. Locals are visible from their declaration on. Each `{}` opens a scope.

```mond
fun limits = (u32 p) {
    p = 3;                 #! assign_to_immutable
    u32 x;
    u32 y = x;             #! use_before_initialization
    u32 p = p + 1;         # a typed declaration shadows
    u32 p = 0;             #! duplicate_declaration
}
```

## Blocks

`{ a; b; }` has the value of its last statement, and `{}` is unit. Single statements use `:`: `if c: a else: b`, `while c: s`, `(x): x + 1`. A block directly after `:` is an error. An expression ends at a closing `}`, so put parentheses around a block that is used as an operand.

```mond
stc u32 V = ({ 7; }) + 1;                        #= V 8
stc u32 W = (if true { 1; } else { 2; }) * 10;   #= W 10
```
