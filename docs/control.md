# Control flow

Everything is an expression. Every construct has two forms: `head: one statement` and `head { block }`.

## if

```mond
fun grade = (u32 s) -> u8: ret if s >= 90: 'A' else: if s >= 80: 'B' else: 'F';
stc u8 G = grade(85);        #= G 66
stc i32 C = if 1 > 0: 100 else 200;
```

- The condition must be a `bool`. The value is the join of both branches, and an untyped literal takes the other branch's type.
- An `if` without `else` is `()`. A unit call used as a branch next to a value is `runit_mixing`, so use `do f()` (evaluate and discard) or a block.

```mond
fun unit_fn = () {}
fun mix = (bool c) {
    i32 a = if c: 1 else: do unit_fn();
    i32 b = if c: unit_fn() else: 2;   #! runit_mixing
}
```

## Loops

| form | |
|---|---|
| `while c: s` · `while c, step: s` | `step` runs after every iteration, also after `cont` |
| `for xs: s` | the element is `$it` |
| `for x in xs: s` | `x` is an immutable copy |
| `loop s` · `loop pre: s` | endless; `pre` runs before every iteration |
| `stcwhile` `stcfor` `stcloop` | run at compile time, see [static.md](static.md) |

`brk` and `cont` act on the innermost loop, also from inside a `match` used as a value. They take no value and no label. The step of `while c, step` is one statement.

A sequence is a range, an array, a string, a pointer to an array, or any value with `has_next() -> bool` and `next() -> T`.

```mond
stcfun demo = () -> u32 {
    mut u32 s = 0;
    mut u32 i = 0;
    while i < 10, i += 1 { if i % 2 == 0: cont; s += i; }   # 25
    for x in [1, 2, 3]: s += x * 100;                       # +600
    for 0..<4: s += $it * 1000;                             # +6000
    mut u32 k = 0;
    loop { k += 1; if k > 3: brk; }
    ret s + k;
}
stc u32 D = demo();   #= D 6629
```

```mond
type Countdown = *(mut u32 n) !{
    has_next = () -> bool: ret self.n > 0;
    next = () -> u32 { self.n -= 1; ret self.n; }
}
stcfun drain = () -> u32 {
    mut u32 s = 0;
    for x in Countdown(4): s = s * 10 + x;
    ret s;
}
stc u32 DR = drain();   #= DR 3210
```

### Ranges

`a..<b` excludes `b`, `a..=b` includes it, `a..` has no end, and `..<b` / `..=b` start at 0. Ranges appear in `for`, in patterns and in array casts. A range is never a static value, and indexing with a range is `genexpr_index`.

### Loops as values

A loop that is expected to produce an array collects its body values. `cont` skips a value, and `brk` ends the array. The length is static for a `for` over static bounds without `brk`/`cont`.

```mond
stc [4]u32 SQ = for i in 0..<4: i * i;                                   #= SQ [0, 1, 4, 9]
stcfun evens = () -> []u32: ret for i in 0..<10: if i % 2 == 1: cont else: i;
stc []u32 EV = evens();                                                  #= EV [0, 2, 4, 6, 8]
stc [][2]u32 GRID = for i in 0..<2: for j in 0..<2: i * 2 + j;           #= GRID [[0, 1], [2, 3]]
```

In runtime code, a `while`, a `loop` or an open-ended `for` used as a value needs a declared length (`[5]i32 v = while ..`).

A `loop` without `brk` has the type `never`, so it fits any type: `fun serve = () -> u32: loop {};`. A `while true` loop is not `never`.

## match

```mond
variant Res = +(Ok(i32), Err(u8 code, u8 extra), Empty);
type Pt = *(i32 x, i32 y);

stcfun describe = (Res r) -> i32: ret match r {
    Res.Ok(0) => 0,                  # payload pattern
    Res.Ok(v) => v,                  # binder
    Res.Err(code = 1) | Res.Empty => -1,
    Res.Err <- e => -(e.code as i32), # label: the payload
};
stcfun quadrant = (Pt p) -> u8: ret match p {
    Pt(0, 0) => 0,
    Pt(x = 1.., y = 1..) => 1,
    Pt(..<0, _) => 2,
    _ => 3,
};
stc i32 D1 = describe(Res.Ok(7));           #= D1 7
stc i32 D2 = describe(Res.Err(4, 0));       #= D2 -4
stc u8 Q = quadrant(Pt(3, 5));              #= Q 1
```

| pattern | matches |
|---|---|
| `_` | anything |
| `name` | anything and binds it. A bare name is always a binder, even if a constant has that name |
| `3` `'a'` `"ab"` `true` `K + 0` | by equality (any expression other than a name) |
| `1..=9` `..<0` `10..` | integer intervals |
| `V.Case` · `V.Case(p, f = p)` · `Rec(p, f = p)` | a case or a record, fields by position or name; missing fields are `_` |
| `p1 \| p2` | either one (only at the top of an arm); both must bind the same names |
| `T x` | a value that is a `T` (a member of a unified variant, a trait implementer, a case), bound as `T` |
| `p <- x` · `p <- a, b` | matches `p` and binds its payload: a single field directly, several fields as a record, or `a, b` in order |
| `quote: ..` | tree shapes, see [metaprogramming.md](metaprogramming.md#quote-patterns) |

- There are no tuples. To match on two values at once, wrap them in a record; exhaustiveness is checked across both:

```mond
variant S = +(Idle, Moving(u32 to));
variant Ev = +(Call(u32 floor), Tick);
type Step = *(S s, Ev e);
fun next = (S s, Ev e) -> u32: ret match Step(s, e) {
    Step(S.Idle, Ev.Call(f)) => f,
    Step(S.Idle, Ev.Tick) => 0,
    Step(S.Moving(t), _) => t,
};
stc u32 NX = next(S.Idle, Ev.Call(3));   #= NX 3
```

- A match must be exhaustive (`non_exhaustive_match`). Integers need their whole range covered, variants every case, and floats, arrays and pointers need a catch-all.
- An arm already covered by the arms above it is a `redundant_match_arm` warning.

```mond
fun check = (i8 x) -> u8: ret match x { -127..=127 => 0 };   #! non_exhaustive_match
fun again = (bool b) -> u8: ret match b { _ => 0, true => 1 };   #! redundant_match_arm
```

## Unwrapping

| | |
|---|---|
| `x ?? fallback` | the payload of the first payload case (so declare the success case first), else `fallback` (which may be `ret ..`) |
| `x??` | the payload; failing it is an error |
| `x ?<- v` | `bool`; binds the payload as `v` in the then-branch or the `while` body |
| `e <- v` · `e <- a, b` | the value is `e`; binds `v` to it, or `a, b` to its fields, for the rest of the statement |

```mond
variant Opt = +(Some(i32), None);
stcfun or_zero = (Opt o) -> i32: ret o ?? 0;
stcfun bound = (Opt o) -> i32: ret if o ?<- v: v * 2 else: -1;
type P = *(i32 a, i32 b);
stcfun parts = () -> i32: ret (P(3, 4) <- a, b).a + a * b;
stc i32 U = or_zero(Opt.Some(5)) + bound(Opt.None) + parts();   #= U 19
```

## defer, deinit

`defer s` runs `s` when the enclosing block ends, latest first, on every exit (fall-through, `ret`, `brk`, `cont`). A `ret` value is computed before the defers run. `deinit x` runs `x`'s `deinit`, after which `x` counts as unwritten. `e defer deinit` deinitializes a copy at the end of the block.

```mond
stcfun order = () -> u32 {
    mut u32 t = 0;
    { defer t = t * 10 + 1; defer t = t * 10 + 2; t = 3; }
    ret t;
}
stc u32 O = order();   #= O 321
```

## Initialization and returns

- A scalar local declared without a value must be `mut`, and it must be written on every path before it's read. `if` without `else`, loop bodies and `_ => {}` don't count as writing. A `never` branch (such as `else: ret`) does count.
- A block body that declares a result must end every path with `ret` or `never`; otherwise it's `missing_ret`. `main` and unit functions may fall off the end.

```mond
fun maybe = (bool c) -> u32 {
    mut u32 x;
    if c: x = 1;
    ret x;          #! use_before_initialization
}
fun half = (bool c) -> i32 { if c { ret 1; } }   #! missing_ret
```
