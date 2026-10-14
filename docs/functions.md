# Functions

## Definition

```mond
fun add = (u32 a, u32 b) -> u32: ret a + b;   # `:` takes one statement or expression
fun twice = (u32 x): x * 2;                   # the result type is inferred
fun sum3 = (u32 a, u32 b, u32 c) -> u32 {     # a block returns only through `ret`
    ret a + b + c;
}
inc = (u32 x): x + 1;                         # no keyword needed
fun first = (u32, u32): $0;                   # unnamed parameters are $0, $1, ..
stc u32 R = add(1, 2) + twice(3) + sum3(1, 1, 1) + inc(0) + first(5, 6);  #= R 18
```

- Without `->` the result is the join of all `ret` values. A `{}` body without a value-`ret` returns `()`.
- A block body whose last value is not `ret`'d is `missing_ret`. `ret;` returns unit.
- Parameters are immutable. `fun f = (..) -> R;` without a body declares a signature only.
- A function-typed result needs an alias: `type IntFn = (i32) -> i32;`.

```mond
fun no_ret = () -> u32 { 5; }   #! missing_ret
```

## Parameters

`Type [name] [= default] [where cond [else value | else ret value]] [stcwhere cond]`

```mond
fun chain = (u32 a, u32 b = a + 1, u32 c = b * 2) -> u32: ret a * 100 + b * 10 + c;
fun safe_div = (u32 a, u32 b where b != 0 else ret 0) -> u32: ret a / b;
fun at_least = (u32 x where x >= 10 else 10) -> u32: ret x;
fun nonzero = (u32 d stcwhere d != 0) -> u32: ret 100 / d;

stc u32 C1 = chain(1);               #= C1 124
stc u32 C2 = chain(1, c = 9);        #= C2 129
stc u32 D0 = safe_div(9, 0);         #= D0 0
stc u32 L = at_least(3);             #= L 10
stc u32 N = nonzero(4);              #= N 25
stc u32 Z = nonzero(0);              #! stcwhere_violated
```

- A default sees the parameters before it.
- A `type T` parameter takes a static type: `fun size = (type T) -> u64: ret sizeof T;`. Later parameters can't use `T`. For that, see generic functions below.
- `where c else v` replaces the argument with `v`, and `else ret v` returns `v` from the function. `where c` without `else` makes the overload rejectable (see dispatch below).
- `stcwhere` is checked at compile time at every call, so the arguments it reads must be static.
- Arguments go by position or by name, in any order. A positional argument fills its own slot. Trailing commas are fine.

## Overloads

One name, several parameter lists. Each argument scores: exact 6, into a template-typed parameter such as `Box b` 5, coercion 4, length-generic 2, plus 1 for each `where`. The highest total wins. Methods can't be overloaded.

```mond
fun show = (u8 x) -> u32: ret 1;
fun show = (f32 x) -> u32: ret 2;
fun len = (&[]u8 s) -> u32: ret 10;
fun len = (&[3]u8 s) -> u32: ret 3;
stc u32 A = show(7) * 10 + show(7.0);  #= A 12
stc [3]u8 BYTES = [1, 2, 3];
stc u32 B = len(BYTES.&);             #= B 3
```

A tie is `ambiguous_overload`, and no fit at all is `no_matching_overload`. Used as a value, an overloaded name is the overload whose type is expected: `(u8) -> u32 f = show;`. A different result type alone doesn't make a new overload (`duplicate_declaration`).

### `where` dispatch

Overloads with the same parameters form a group. The guarded ones (`where` without `else`) are tried in order, and the unguarded one is the fallback. A static call picks at compile time, a runtime call tests at runtime. They share one result type, a member giving another is `ret_type_mismatch`.

```mond
fun sign = (i32 x where x < 0) -> i32: ret -1;
fun sign = (i32 x where x == 0) -> i32: ret 0;
fun sign = (i32 x) -> i32: ret 1;
stc []i32 S = [sign(-5), sign(0), sign(9)];   #= S [-1, 0, 1]
```

## Function values, lambdas, closures

The type is `(T1, T2) -> R`. Function values match exactly (no variance), take positional arguments only, and have no defaults.

```mond
type IntFn = (i32) -> i32;
fun make_mul = (i32 n) -> IntFn: ret (i32 x): x * n;
fun apply = (IntFn f, i32 v) -> i32: ret f(v);
stc i32 M = apply(make_mul(6), 7);   #= M 42

stcfun sees_later = () -> i32 {
    mut i32 x = 1;
    get = (): x;          # mutable locals are captured by reference
    x = 5;
    ret get();
}
stc i32 SL = sees_later();   #= SL 5
```

- Captures: mutable locals, records and arrays are captured by reference, other immutable locals by copy. Globals are not captured.
- At run time a function value is a function and the environment holding its captures (`sizeof` 16). The environment lives in the frame that made the closure. A closure that outlives that call (returned, stored, or passed where it may be kept, like `make_mul` above) keeps its environment, and the variables it captures by reference, on the heap; that memory is never freed.
- `f = (..): ..` declares a local function from that point on. `fun f = ..` in a body is hoisted to its whole block.
- `brk` and `cont` don't cross a function boundary.
- There's no UFCS: `x.f()` works only for methods.

## Generic functions

Write a generic function as a `stcfun` (or a `fun`) whose first tuple takes only the types and whose second takes the values. Each type argument builds a function at compile time, which runtime code can call. The second tuple takes defaults and named arguments like any function. Type arguments are never inferred.

```mond
stcfun swap = (type T): (*T a, *T b) { T t = a.*; a.* = b.*; b.* = t; }
stcfun largest = (type T): (&[]T xs) -> T {
    mut T m = xs[0];
    for x in xs: if x > m: m = x;
    ret m;
}
stcfun demo = () -> u32 {
    mut u32 x = 1;
    mut u32 y = 2;
    swap(u32)(x.&, y.&);
    ret x * 10 + y;
}
stc u32 SW = demo();                      #= SW 21
stc [3]i16 XS = [4, -9, 7];
stc i16 MX = largest(i16)(XS.&);          #= MX 7
fun at_runtime = (&[3]i16 p) -> i16: ret largest(i16)(p);
fun bad = (type T, T v) -> T: ret v;      #! undefined_name undefined_name
```

## `stcfun`, `inlfun`

`stcfun` runs at compile time on every call. Its arguments must be static, and results are memoized per argument tuple. It can return values, types and functions. See [static.md](static.md).

```mond
stcfun Word = (u32 bits) -> type: ret if bits <= 8: u8 else: u64;
stcfun scaler = (u32 k): (u32 x) -> u32: ret x * k;   # a second tuple makes a function
fun triple = scaler(3);
stc u64 W = sizeof Word(16);    #= W 8
stc u32 T = triple(14);         #= T 42
```

`inlfun` declares a function meant for inlining. Today it behaves like `fun`, except that its values don't fit plain function types.

A function declared without a body is external: `fun malloc = (u64 n) -> *u8;`.

## Length-generic functions

A parameter `[]T`, `&[]T` or `*[]T` is realized (compiled as a copy of its own) once per argument length, and `.$len` is static inside. The element type must match exactly.

```mond
fun total = (&[]u32 a) -> u32 {
    mut u32 s = 0;
    for x in a: s += x;
    ret s;
}
stc [3]u32 XS = [1, 2, 3];
stc [2]u32 YS = [10, 20];
stc u32 TOT = total(XS.&) + total(YS.&);   #= TOT 36
```

## Methods

These are declared in a type's `!{ }`; see [types.md](types.md#methods).
