# Compile-time evaluation

The compiler has an interpreter, so any code can run at compile time as long as everything it reads is static.

## What is static

- Static: literals, `stc` declarations, `stcfun` results, `sizeof`, `typeof`, `lenof` of fixed arrays, types, and calls of plain `fun`s with static arguments.
- Not static (`not_static`): runtime locals and parameters, non-`stc` and `mut` globals, ranges as values, body-less functions, and pointers that leave the evaluation.

```mond
stc u32 KIB = 1024;
stc u32 A = B + 1;            # order doesn't matter
stc u32 B = 2;
fun sq = (u32 x) -> u32: ret x * x;
stc u32 S = sq(KIB / 256);    #= S 16
[KIB / 256]u8 buf;            #: buf [4]u8
stc type T = typeof S;
u32 plain = 5;
stc u32 NOPE = plain;         #! not_static
```

## `stc` locals and static control flow

`stc` locals are compile-time variables, even inside runtime functions. `stcif`, `stcmatch`, `stcfor`, `stcwhile` and `stcloop` run at compile time, and only the branch that is taken gets checked. That makes them the way to prune code per type or per platform.

```mond
stc u32 Z = stcif true: 1 else: this_is_never_checked;     #= Z 1
stc type W = stcmatch sizeof u16 { 1 => u8, 2 => u16, _ => u64 };   #= W u16
stc []u32 POW = stcfor i in 0..<5: 1 << i;                   #= POW [1, 2, 4, 8, 16]
stc u32 N = 0;
stc []u32 STEPS = stcwhile N < 20, N += 7: N;                #= STEPS [0, 7, 14]

fun sq = (u32 x) -> u32: ret x * x;
fun pick = (u32 n) -> u32 {
    stc u32 K = sq(4);
    ret stcif sizeof u32 == 4: n + K else: 0;
}
```

Inside a `stcfun` everything is static already, so the `stc..` forms there are `redundant_stc`. Elsewhere a plain loop's variable is not static: `stc []u32 T = for i in 0..<3: sq(i);` with a `stcfun sq` is `not_static`, so use `stcfor`.

## stcfun

Every call runs at compile time and is memoized per argument tuple, which makes `stcfun`s pure: writing a global from one is `impure_stcfun`. A `stcfun` can return anything static: numbers, arrays, records, types and functions.

```mond
stcfun fib = (u32 n) -> u64: ret if n < 2: n else: fib(n - 1) + fib(n - 2);
stcfun Int = (u32 bits) -> type: ret if bits <= 8: u8 else: if bits <= 16: u16 else: u64;
stcfun table = (u32 n) -> []u32: ret for i in 0..<n: i * i;

stc u64 F = fib(20);              #= F 6765
stc Int(12) small = 4000;         #: small u16
stc []u32 TBL = table(4);         #= TBL [0, 1, 4, 9]
stc []u32 TB2 = table(2);         #= TB2 [0, 1]

fun runtime = (u32 n) -> u64: ret fib(n);   #! not_static
```

- The body is checked separately for each call, with its arguments known, and only the branches taken are checked. A `stcfun` nobody calls is never checked.
- In `stcmatch` on types, write a named type in parentheses (`(Money) =>`), because a bare name is a binder.
- Results are memoized across evaluations, so a call cached once costs nothing later.
- A second parameter tuple produces a function: `stcfun scaler = (u32 k): (u32 x) -> u32: ret x * k;`. Templates are `stcfun`s too (see [types.md](types.md#templates)).

## crash

`crash "text"` is the compile error `crash` with that text, wherever the compiler meets it. Runtime code is checked once, so it throws in any branch there, also in a function nobody calls and in each instantiation. Static code throws when it is evaluated: a `stc` value, the taken branch of a `stcif` or `stcmatch`, a `stcfun` running into it. A branch that isn't taken is never checked, so a static branch makes it a condition. The text is any static text: a `[]u8`, a `[N]u8` (also a field) or a `&u8`. It has the type `never`, so it fits where any value is expected. The error points at the `crash`, a `stcfun` reports it once; `crash (at, "text")` points at the tree `at` instead (see [metaprogramming.md](metaprogramming.md#crash-at-a-tree-include)).

```mond
stcfun Int = (u32 bits) -> type: ret if bits <= 64: u64 else: crash "at most 64 bits";   #! crash
stc Int(12) small = 7;                                   #: small u64
stc type HUGE = Int(65);                                 # runs into the crash above
stcif sizeof u32 != 4: crash "u32 must be 4 bytes";    # not taken, never checked
fun wide = (type T) -> u32: ret stcif sizeof T <= 8: 1 else: crash "too wide";
stc u32 W = wide(u32);                                   #= W 1
fun never_called = () { crash "checked all the same"; }   #! crash
```

## Interpreter rules

- Values are copied: assignment, parameters, returns and loop variables all copy, and a pointer is the only way to share. Pointers work inside an evaluation but can't escape it.
- Integers wrap, `/` truncates toward zero, and `>>` is arithmetic on signed types. Floats are rounded to their type at every step.
- These fail with `static_eval_failed`: `/ 0`, `% 0`, a shift of at least the width, an index out of bounds, a failing `x??`, more than 1,000,000 steps per top-level evaluation (a loop iteration costs a few), and 256 nested calls. A read out of bounds through a pointer is `not_static`.

```mond
stc i8 WR = 127 + 1;                   #= WR -128
stc f32 HALF = 1.0 / 2.0;              #= HALF 0.5
stc u32 BAD = 7 / 0;                   #! static_eval_failed
stcfun down = (u32 n) -> u32: ret if n == 0: 0 else: down(n - 1);   #! static_eval_failed
stc u32 DEEP = down(300);              # 300 frames: reported at the recursion
stc []u32 FOREVER = stcloop 1;         #! static_eval_failed
```
