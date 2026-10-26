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

A sequence is a range, an array, a string, a pointer to an array, a slice, or any value with `has_next() -> bool` and `next() -> T`.

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
    Res.Err e => -(e.code as i32),   # the case itself
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
| `p where c` | `p`, when `c` holds for what it bound (only at the top of an arm, after `\|` alternatives) |
| `bits(u7 0x13, u5 rd, ..rest)` | an integer's bits from the lowest up: each field a width and a pattern on those bits, seen as that width's type; `..rest` binds the bits left (unsigned), `..` ignores them (only at the top of an arm or of an alternative) |
| `T x` | a value that is a `T` (a member of a unified variant, a trait implementer, a case), bound as `T` |
| `p <- x` · `p <- (a, b)` | matches `p` and names the part of the scrutinee it matched `x` (the place itself, see [unwrapping](#unwrapping)), as the type it is matched as, or its fields `a, b` in order |
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

- Without `..` the widths of a `bits(..)` pattern add up to the integer's own (`bits_width`). An arm of bits covers every value only when each of its parts does; otherwise it covers nothing, like a guarded arm:

```mond
fun decode = (u32 insn) -> u32: ret match insn {
    bits(u7 0x33, u5 rd, u3 0, u5 rs1, u5 rs2, u7 0) => rd as u32 + rs1 as u32 + rs2 as u32,
    bits(u7 0x13, u5 rd, u3 _, ..immediate) => rd as u32 + immediate,
    _ => 0,
};
stc u32 DEC = decode(0x00A00093);                       #= DEC 321
fun halves = (i8 x) -> i64: ret match x { bits(i4 low, i4 high) => low as i64 * 100 + high };
stc i64 H = halves(-2);                                   #= H -201
fun short = (u8 x) -> u8: ret match x { bits(u4 a) => a, _ => 0 };   #! bits_width
```

- A `where` guard runs after its pattern matched, with the pattern's names bound; when it doesn't hold, the arms below are tried. A guarded arm covers nothing: it never makes the match exhaustive or a later arm redundant.

```mond
variant Tok = +(Num(i64), Op(u8), End);
fun kind = (Tok t) -> u32: ret match t {
    Tok.Num(n) where n > 0 => 1,
    Tok.Num(n) where n < 0 => 2,
    Tok.Op(c) where c == '+' or c == '-' => 3,
    _ => 4,
};
stc []u32 KINDS = [kind(Tok.Num(5)), kind(Tok.Num(-5)), kind(Tok.Op('-')), kind(Tok.Num(0))];   #= KINDS [1, 2, 3, 4]
fun sign = (i8 x) -> i8: ret match x { y where y < 0 => -1, 0 => 0 };   #! non_exhaustive_match
```

- A bare name that takes what the arms above left is of the scrutinee without the cases they took whole (`V.A`, `V.A(x, _)`, `V.A <- v`, `T x`): a subset (see [types.md](types.md#subsets-v----vcase)), so it fits where those cases are not allowed.

```mond
variant IoErr = +(NotFound, Timeout, Denied);
type Config = *(u32 port);
fun load = (u32 x) -> Config || IoErr: ret if x == 0: IoErr.NotFound else: Config(x);
fun load_or_default = (u32 x) -> Config || (IoErr -- IoErr.NotFound): ret match load(x) {
    IoErr.NotFound => Config(80),
    rest => rest,          # Config || IoErr -- IoErr.NotFound
};
stc u32 PORT = match load_or_default(0) { Config c => c.port, _ => 0 };   #= PORT 80
```

- A match must be exhaustive (`non_exhaustive_match`). Integers need their whole range covered, variants every case, and floats, arrays and pointers need a catch-all.
- An arm already covered by the arms above it is a `redundant_match_arm` warning.

```mond
fun check = (i8 x) -> u8: ret match x { -127..=127 => 0 };   #! non_exhaustive_match
fun again = (bool b) -> u8: ret match b { _ => 0, true => 1 };   #! redundant_match_arm
```

## Unwrapping

`<-` names, `?` asks for the success payload: the payload of the first case that has one (so declare the success case first). Of a unified variant it is the first of its members, in the order written, with a payload: a member's case, or a member that is one case (a record, a number) as itself, so `Config || IoErr` succeeds as a `Config`. A `|||` parameter is realized per member, so there it is decided while compiling: the member that is the success always is, one holding the success case tests for it, any other never succeeds. Through a pointer (`&V`, `*V`) they read the variant it points to.

| | |
|---|---|
| `e <- v` · `e <- (a, b)` | the value is `e`, named `v` (an alias, of `e`'s type), or `a, b` naming its fields in order |
| `x ?<- v` | `bool`: whether `x` holds the success payload, named `v` where it does |
| `x ?? fallback` | the success payload, else `fallback` (which may be `ret ..`); `if x ?<- v: v else: fallback` |
| `x??` | the success payload, else `ret` of the result's fallback; outside a function body (also in a default of a parameter or field) failing is `static_eval_failed` |

An arrow names all on its left that binds tighter than `|`, `and`, `or` and `xor` (`a * 2 <- d > 4` is `(a * 2 <- d) > 4`, `c and o ?<- v` is `c and (o ?<- v)`). Its name lives to the end of the statement holding it, the branches, arms, guards and loop bodies in it included, and is read where it is surely bound: a `<-` name everywhere after it, a `?<-` name where its test held (the then-branch, a `while` body, the right of `and`, a `true =>` arm, the else of `!(x ?<- v)`). Elsewhere reading it is `use_before_initialization`, also when it hides an outer name. In a `while` condition `?<-` tests and binds anew on each round, while a `<-` stays an alias of one value: its operand runs the first time the condition reaches it.

```mond
variant Opt = +(Some(i32), None);
stcfun or_zero = (Opt o) -> i32: ret o ?? 0;
stcfun bound = (Opt o) -> i32: ret if o ?<- v: v * 2 else: -1;
type P = *(i32 a, i32 b);
stcfun parts = () -> i32: ret (P(3, 4) <- (a, b)).a + a * b;
stc i32 U = or_zero(Opt.Some(5)) + bound(Opt.None) + parts();   #= U 19
stcfun twice = (i32 a) -> i32: ret if a * 2 <- d > 4: d else: -d;
stcfun failed = (Opt o) -> i32: ret if !(o ?<- v): 0 else: v;
stcfun steps = (i32 n) -> i32 { mut i32 i = 0; while i < (n * 2 <- end) { i += 1; } ret i; }
stc []i32 N = [twice(3), twice(1), failed(Opt.Some(4)), steps(3)];   #= N [6, -2, 4, 6]
fun unbound = (Opt o) -> i32: ret if o ?<- v: v else: v;   #! use_before_initialization
```

Arrows never copy: a name an arrow binds is the place it names, the variable, field or element on its left, and `?<-` the payload inside the variant there (through a pointer, inside the variant it points to). Reading it reads that place as it is now, writing it writes there. It may be written where the place may be: in a mutable variable, through a `*` pointer, a field only when it is `mut`. A value that lives nowhere (`a + b <- s`) is a place of its own, read-only. A payload written into a niche makes the value that niche's case. The names `|` alternatives share, the bits of `bits(..)` parts, and the payloads of variants a strategy (`tagtype ranges(..)`) or a bit-packed layout (`++(..)`) store are values, read-only as well. Hovering a name in the editor shows `(writable)` where it writes.

```mond
variant Cell = +(Some(mut i32), None);
variant Byte = +(Some(mut u8), None = 0xFF) tagtype self;
stcfun bump = () -> i32 { mut Cell c = Cell.Some(3); if c ?<- v { v += 10; } ret c ?? -1; }
stcfun niche = () -> i32 { mut Byte b = Byte.Some(3); if b ?<- v { v = 255; } ret (b ?? 7) as i32; }
stcfun live = () -> i32 { mut i32 x = 1; if (x <- y) > 0 { x = 8; ret y; } ret 0; }
stcfun matched = () -> i32 { mut Cell c = Cell.Some(1); match c { Cell.Some(_ <- k) => { k = 5; }, _ => {} } ret c ?? -1; }
stc []i32 W = [bump(), niche(), live(), matched()];   #= W [13, 7, 8, 5]
fun reads = (&Cell p) { if p ?<- v { v = 1; } }   #! assign_to_immutable
```

The fallback of the result, which a failed `x??` returns (hovering `??` in the editor shows it):

- nothing for a unit result, `0`, `0.0` and `false` for numbers and `bool`, every element of an array, every field of a record its default (run where `x??` fails) or else its fallback
- of a variant a case without payload, else the case `x` holds if it is one of the result's, else any; tagged 0 or else the smallest tag first, a payload its fallback. So `Res.Err(7)??` returns `Res.Err(0)` from a function returning `Res`. A unified variant picks among its cases alike
- pointers, functions, `never`, types and variants without tag have none: `no_fallback`
- the innermost function returns: a lambda, a method, a realization of a template or trait default; a parameter's `where .. else x??` returns from its function, quoted code from where it lands
- a token after `??` that can start an expression starts a fallback: `x?? - 1` is `x ?? -1`, so write `(x??) - 1`. A `{` doesn't (`match x?? {`), a block fallback is in parentheses

```mond
variant Opt = +(Some(i32), None);
variant Res = +(Ok(i32), Err(u8));
type Point = *(i32 x = 1, i32 y);
stcfun more = (Opt o) -> i32: ret o?? + 2;
stcfun at = (Opt o) -> Point { i32 v = o??; ret Point(v, v); }
stcfun again = (Res r) -> Res { i32 v = r??; ret Res.Ok(v + 1); }
stcfun some = (Res r) -> Opt { i32 v = r??; ret Opt.Some(v); }
stc i32 T = more(Opt.None) + at(Opt.None).x * 10 + at(Opt.None).y;   #= T 10
stc bool A = again(Res.Err(7)) == Res.Err(0) and some(Res.Err(7)) == Opt.None;   #= A true
fun name = (Opt o) -> &u8 { i32 v = o??; ret "x"; }   #! no_fallback
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
