# Metaprogramming

Code is data. A tree (`ast`) is a value that exists only at compile time. Its source text is `.src`, and its parts are [views](#views). You make one with `quote`, put one into the program with a splice `<..>`, and read or rewrite declarations with `refl`. A macro is just a function that returns a tree and is called in a splice, usually a `stcfun`.

```mond
stcfun unless = (ast(bool) c, ast body) -> ast(()): ret quote { if !@c { @body; } };
fun clamp = (i32 x) -> i32 {
    <unless(quote: x < 100, quote: ret 100)>;
    ret x;
}
stc i32 CL = clamp(250);   #= CL 100
stc i32 CK = clamp(50);    #= CK 50
```

## Tree types

| type | holds |
|---|---|
| `ast` | any tree |
| `ast(T)` | code producing a `T` (`ast(i32)`, `ast(())` for statements) |
| `ast(fun)` `ast(type)` `ast(variant)` `ast(trait)` | a declaration or type expression |
| `ast.Kind` | a tree with that root kind (`ast.Identifier`, `ast.BinaryAdd`, ...) |
| `[]ast..` | a list of trees; it grows with `+=` |
| `*ast..` / `&ast..` | a shared tree, writable / read-only |

Trees convert unless both sides say what they produce and the two differ: `ast(u32)` converts to `ast`, but `ast(bool)` doesn't convert to `ast(u32)`. Any variable holding a tree is static.

## quote

`quote: expr | statement | declaration` or `quote { statements }`. A quote's type comes from its code: a block is `ast(())`, a function is `ast(fun)`, a type is `ast(type)`, and a typable expression is `ast(T)`. Anything with free names is plain `ast`.

```mond
stc q_add = quote: 1 + 2;            #: q_add ast(u32)
stc q_fun = quote: (i32 x): x + 1;   #: q_fun ast(fun)
stc q_type = quote: *(i32 a);        #: q_type ast(type)
stc q_free = quote: unknown + 1;     #: q_free ast
stc ast(i32) bad = quote: true;      #! type_mismatch
```

### Holes

| hole | puts in |
|---|---|
| `@x` | the tree `x` (a copy). A known static value is lifted to code. An unknown `x` stays the plain name `x` (unhygienic, so it reaches the caller's names) |
| `@(expr)` | the same, for any expression |
| `@..xs` | the items of a `[]ast`, spread into a list: arguments, array elements, statements, match arms (an arm is `quote: pattern => body`) |
| `name_@(x)` | one identifier pasted together from text or a name |

Holes also work in member, type and pattern position: `a.@(f.name)`, `(@(t.name) a)`, `@(v.name).@(c.name) => ..`.

Values lift to code: bools, ints (negative ones too), floats (also `inf` and `nan`), `[]u8` text, and types (`*T`, `[N]T`, `Box(u64)`, ...). Records don't lift (`not_static`).

```mond
stcfun add = (ast(i32) a, ast(i32) b) -> ast(i32): ret quote: @a + @b;
stcfun lifted = (u32 n) -> ast(u32): ret quote: @n * 2;
stcfun all = ([]ast parts) -> ast: ret quote: [@..parts];
stcfun getter = ([]u8 field) -> ast: ret quote: fun get_@(field) = () -> u32: ret 9;

stc i32 SUM = <add(quote: 20, quote: 22)>;                 #= SUM 42
stc u32 DBL = <lifted(21)>;                                #= DBL 42
stc []u32 ARR = <all([quote: 1, quote: 2, quote: 3])>;     #= ARR [1, 2, 3]
stc u64 SZ = <quote: sizeof @(u32)>;                       #= SZ 4
<getter("nine")>;
stc u32 NINE = get_nine();                                 #= NINE 9
```

## Splices `<..>`

`<expr>` expands a static tree in place. It can stand in expression, type, statement or top-level position, or as a declaration's value.

```mond
stcfun int_type = (u32 bits) -> ast(type): ret if bits <= 8: quote: u8 else: quote: u64;
stcfun maker = (u32 k) -> ast(fun): ret quote: (u32 x) -> u32: ret x * @k;
stcfun helpers = () -> ast(()): ret quote { fun one = () -> u32: ret 1; fun two = (): 2; };

type Sized = *(<int_type(8)> small, <int_type(64)> big);   # type position
fun times3 = <maker(3)>;                                     # a declaration's value
<helpers()>;                                                 # top level: declares
stc u32 T3 = times3(one() + two());                          #= T3 9
stc u64 SS = sizeof Sized;                                   #= SS 16
```

- `ast(T)` gives a `T`, plain `ast` fits anywhere, and a macro returning `()` puts in nothing.
- In statement position the statements of a block spread into the block around the splice. `brk` and `defer` then apply where they land.
- The tree must be static: `<make(n)>` with a runtime `n` is `not_static`.
- In a generic body a splice is expanded once per realization: `stcfun sz = (type T): () -> u64: ret <quote: sizeof @(T)>;`.
- Code that lands is checked in the next pass, and its errors are reported at the splice.
- A *top splice* is a splice at top level, including one in a top-level declaration's value (`stc X = <m()>`). Top splices run before anything else is resolved.
- Inside a splice, `>` closes it, so a comparison needs parentheses (`<if (a > b): ..>`). `>>` is a shift, so write `> >`.

## Hygiene

- **Fresh names:** a variable declared inside a quote that is written in a function (a macro, or a caller's quote passed to it) gets a fresh name each time it lands, so it never captures or leaks. That covers `x = ..` and `T x`, function parameters, loop variables and binders. So `quote: s = s + 1` passed to a macro declares a new `s`; write `s += 1` instead. A quote written at top level, outside any function, keeps its names: `<quote { stc u32 LIMIT = 8; }>;` declares `LIMIT`.
- **Pasted names** (`get_@(x)`) are kept.
- **Kept names:** functions, types, members, fields and case names keep their written names.
- **Free names** mean what they mean where the code lands.
- **Sharing:** all quotes written in one function share their names.
- **Caller's names:** a macro writes the caller's variable through a hole: `quote { @target = v; }` with `target` given as `quote: x`.
- **`fresh "v"`** makes a name no one else can write.

```mond
stcfun swap_add = (ast a, ast b) -> ast(()): ret quote { tmp = @a; @a = @b + tmp; };
fun use = () -> u32 {
    mut u32 x = 1;
    mut u32 tmp = 10;            # not captured by the macro's `tmp`
    <swap_add(quote: x, quote: tmp)>;
    ret x + tmp;
}
stc u32 HY = use();              #= HY 21
stcfun set_to = (ast target, ast(u32) v) -> ast(()): ret quote { @target = @v; };
fun assign = () -> u32 {
    mut u32 y = 1;
    <set_to(quote: y, quote: 100)>;   # writes the caller's y
    <quote { y = 7; }>;                # declares a fresh y of its own
    ret y;
}
stc u32 AS = assign();           #= AS 100
fun leak = () -> u32 {
    <quote { secret = 1; }>;
    ret secret;                  #! undefined_name
}
```

## Inspecting trees

A tree is a value you can match, read and rebuild.

```mond
stcfun op = (ast e) -> u64: ret match e {
    ast.BinaryAdd(lhs, rhs) => 1,             # kinds as patterns
    ast.BinaryMultiply(rhs = r) => lenof r.src,
    ast.IntegerValue | ast.FloatingPointValue => 7,
    _ => 0,
};
stc u64 O1 = op(quote: a + b);                #= O1 1
stc u64 O2 = op(quote: a * bee);              #= O2 3
stc i32 SW = <(quote: 10 - 4) with (lhs = quote: 4, rhs = quote: 10)>;   #= SW -6
stc i32 MK = <ast.BinaryMultiply(quote: 6, ast.IntegerValue("7"))>;      #= MK 42
stcfun kind = (ast e) -> u32: ret if e oftype ast(fun): 1 else: if e oftype ast.Identifier: 2 else: 0;
stc u32 K = kind(quote: name);                #= K 2
```

- Every kind and its children are listed in [trees.md](trees.md).
- Children go by position, or by field name (`e.lhs`, `e.cond`).
- `x with (field = tree)` makes a copy with some children replaced.
- `ast.Kind(children..)` builds a node. Data kinds take text, as in `ast.Identifier("x")`.
- `oftype` tests the root only, so `oftype ast(u32)` is false for every expression.

### Quote patterns

`quote: shape => ..` matches by shape. `@x` binds a subtree, `@_` matches any, and `@..xs` binds the items in between as `[]ast`. Names and literals compare by text.

```mond
stcfun shape = (ast e) -> []u8: ret match e {
    quote: @x + 0 => x.src,
    quote: @_ * @_ => "product",
    quote: f(@first, @..rest) => first.src,
    _ => "none",
};
stc []u8 S1 = shape(quote: (a * b) + 0);      #= S1 "a * b"
stc []u8 S3 = shape(quote: f(y, 2, 3));       #= S3 "y"
stcfun same = (ast e) -> u32: ret match e { quote: @a + @a => 1, _ => 0 };   #! duplicate_declaration
stc u32 SM = same(quote: 1 + 1);
```

Each name binds once in a pattern, so `@a + @a` is not an equality test.

## Views

`tree.view` reads part of a node. Its value is an `ast`. Through a `*ast` a view can also be assigned (`f.body = ..`), and list elements are then `*ast`; write `c.*` where an `ast` is expected.

| view | of | |
|---|---|---|
| `src` | any | source text `[]u8` (read only) |
| `children` | any | all children |
| `name` `type` `defval` `guard` `ismut` | declarations, parameters, fields | `ismut` is a read-only `bool` |
| `assigned` | declaration | what it declares |
| `params` `rettype` `body` | function | |
| `fields` · `cases` · `methods` · `traits` | record · variant · type · type | lists, `+=` appends (and creates a missing `!{}` / `implof`) |
| `decls` | block, `include`, bare `refl` | top-level statements |

List views are `[]ast` (`[]*ast` on a `*ast`), and `lenof` counts them. A view the node doesn't have is `unknown_member`.

- Views of declarations are on the declaration: `(refl Pt).fields`, `(refl f).params`.
- A case has `name`. Its payload fields are the children of its `def_type`.
- A node without a view of a name reaches its child of that name: the `body` of a loop, the `type` of an `as`.
- `src` is the text as written. A declaration's `src` starts at its name, and on trees a macro built, changed or included it is not meaningful.

```mond
variant Sh = +(Circle(u32 r), Rect(u32 w, u32 h), Dot);
stc []u8 CN = (refl Sh).cases[1].name.src;                           #= CN "Rect"
stc u64 PF = lenof (refl Sh).cases[1].def_type.children;              #= PF 2
stc []u8 F0 = (refl Sh).cases[1].def_type.children[0].name.src;    #= F0 "w"
stc []u8 AS = (quote: 300 as u8).type.src;                           #= AS "u8"
```

## refl: reading and writing the program

`refl name` gives the declaration's tree as a `*ast(fun | type | variant | trait)`, unresolved. A bare `refl` is the whole file: `refl.decls`. Writes are allowed while a splice is evaluated, and only to declarations that are not resolved yet.

```mond
fun scale = (u32 v, u32 by = 2) -> u32: ret v * by;
stc []u8 NAME = (refl scale).name.src;    #= NAME "scale"
stc u64 NP = lenof (refl scale).params;     #= NP 2

fun legacy = (i16 x) -> i16: ret x + 1;
stcfun upgrade = (*ast(fun) f) {
    f.name = ast.Identifier("upgraded");
    f.params[0].type = quote: u32;
    f.rettype = quote: u32;
    f.body = quote: ret @(f.body.subnode) * 10;   # `subnode`: the value of `ret`
}
<upgrade(refl legacy)>;
stc u32 UP = upgraded(4);                   #= UP 50
```

- `refl.decls` lists the top-level declarations. Appending to it or replacing an entry rewrites the program.
- Write `(refl x).name`, with the parentheses: `refl x.name` reflects `x.name`.
- Writing outside a splice, or writing an already resolved declaration (including the macro itself), is `frozen_declaration`.
- Renaming (`name =`) doesn't update the uses of the old name.
- Top splices run first, in order. What they write is seen everywhere, even by code written before them.

## crash at a tree, include

`crash (at, "text")` stops expansion with `crash`, reported where the tree `at` was written. `at` is an `ast`, so dereference a `refl` tree (`d.*`); the error then points at that declaration. The text is fixed: there is no string concatenation. `include "path"` reads the top-level declarations of a file (relative to the file the `include` is written in, the path any static `[]u8`) as a block tree. `<include "lib/math.mn">;` declares them. To edit them first, take a writable tree: `mut ast lib = include "f.mn"; *ast b = lib.&;` then change `b.decls` and splice `<lib>`. A library is only included and needs no `main`. The declarations without `pub` come along under names of their own: the library's code uses them, the including program can't name them. `includeraw "path"` gives the same tree with every name as written: the program can name all of it, and a name it declares itself is a `duplicate_declaration`. Other free names in included code resolve in the including program. A program declares a file once, like a module: a top-level `<include "f">` of a file it already declared, directly or through a library that includes it too, lands nothing, whether plain or raw (the first one counts). Inside a body each include declares its own locals, and `include "f"` as a tree always reads the file. A missing or broken file is `include_failed`.

```mond
stcfun positive = (ast(i32) e) -> ast(i32): ret match e {
    quote: -@_ => crash (e, "must not be negated"),
    _ => e,
};
stc i32 OK = <positive(quote: 5)>;      #= OK 5
```

```mond
<include "../examples/lib/nested/fractions.mn">;   # includes ../math.mn, relative to itself
<include "../examples/lib/math.mn">;               # declared already: nothing more
stc u32 R = reduced_denominator(6, 8);            #= R 4
stc u32 G = gcd(12, 18);                          #= G 6
```

`name = <include "f">` at top level declares a namespace instead: no value, a name that reaches what the file shows as `name.x`, its `pub` declarations (all of them for `includeraw`), functions, types, cases, values and macros alike. None of the file's names is a global name, so they clash with nothing; its C functions keep their names for the linker. A namespace of a file another namespace has reaches the same declarations, and its name is taken like any global name. The file's own namespaces are reached through it when they are `pub` (`pub inner = <include "x.mn">;` gives `name.inner.x`), and a plain `<include>` inside the file still declares globally. A namespace is declared at top level only, in a body it is `include_failed`, and its name is taken everywhere: a global, parameter, local or binder of it is a `duplicate_declaration`.

```mond
math = <include "../examples/lib/math.mn">;   # a library of the examples
fun gcd = () -> u32: ret 1;                    # no clash with math.gcd
stc u32 G = math.gcd(12, 18);                  #= G 6
stc u32 H = math.hidden();                     #! undefined_name
```

```mond
stcfun positive = (ast(i32) e) -> ast(i32): ret match e { quote: -@_ => crash (e, "negated"), _ => e };
stc i32 NO = <positive(quote: -5)>;     #! crash
stc ast lib = include "missing.mn";     #! include_failed
```

## Passes and limits

The compiler runs in passes: top-level splices first, then everything is checked and body splices expand. Then the program is rebuilt with what was expanded, and the next pass starts. A splice produced by an expansion runs in the next pass, so each level of generation costs one pass.

| limit | |
|---|---|
| 64 passes in total | more is `endless_expansion`, which also covers chains 64 deep |
| a failed splice ends the passes | the other splices of that pass still report, but the code they landed is checked only once the error is fixed |
| a stray `@` outside a quote | `stray_unquote` stops the compile before anything else is reported |
| the same pass | what a top splice declares (a function, a macro from an include) doesn't exist yet for the other top splices of that pass; defer with `<quote: <..> >` or use it in a body |
| unchecked macros | a `stcfun` nobody calls is never checked |
| no generic walk | `children[i] =` is `not_static`; a rewriter rebuilds each kind it handles with `with` or `ast.Kind(..)` |
| quotes hold mond | a DSL must reuse mond syntax (`when(c, b);`, not `when c: b`) |
| no text functions | no concatenation or comparison of `[]u8`; write a `stcfun` for it |
| text is code-free | `src`, `ismut` and `children[i] =` can't be written (`not_static`) |
| lifted literals type where they land | `<quote: @('a')>` is a `u32` |
| a block inserted with `@b` is nested | its names end with it; use `@..b` to spread its statements |

```mond
stcfun forever = () -> ast: ret quote: <forever()>;
stc u32 E = <forever()>;     #! endless_expansion
```
