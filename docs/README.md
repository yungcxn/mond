# mond

A systems language with functional and OOP concepts, where code can run and be written at compile time.

```mond
variant Shape = +(Circle(u32 r), Rect(u32 w, u32 h));
type Canvas = *(mut u32 painted) !{
    fun paint = (Shape s) {
        self.painted += match s { Shape.Circle(r) => 3 * r * r, Shape.Rect(w, h) => w * h };
    }
}
stcfun area_sum = () -> u32 {               # runs at compile time
    mut Canvas c = Canvas(0);
    for s in [Shape.Circle(2), Shape.Rect(3, 4)]: c.paint(s);
    ret c.painted;
}
stc u32 TOTAL = area_sum();                 #= TOTAL 24

stcfun unroll = (u32 n, ast body) -> ast(()) {   # a macro: makes n copies of body
    mut []ast copies = [];
    for 0..<n: copies += body;
    ret quote { @..copies; };
}
$main = () -> u32 {
    mut u32 x = 1;
    <unroll(3, quote: x *= 2)>;             # x *= 2; x *= 2; x *= 2;
    ret x + TOTAL;
}
```

| page | covers |
|---|---|
| [basics](basics.md) | program, literals, types, operators, casts, declarations |
| [functions](functions.md) | parameters, overloads, dispatch, lambdas, closures, generic lengths |
| [types](types.md) | records, methods, variants, unions, traits, templates |
| [control](control.md) | if, loops, match and patterns, unwrapping, defer, initialization |
| [static](static.md) | compile-time evaluation |
| [metaprogramming](metaprogramming.md) | quotes, splices, hygiene, trees, `refl`, `include`, limits |
| [trees](trees.md) | every tree kind, how it is written, its children |
| [tooling](tooling.md) | CLI, tests, editor, every diagnostic |

## What a program can do today

The compiler builds native executables through LLVM (see [tooling](tooling.md)). There is no standard library: no I/O, heap, or string functions. A function declared without a body (`fun puts = (&u8 s) -> i32;`) is external and links against the C library; records and arrays go to it by value, and variadic C functions like `printf` aren't supported. Arrays have a fixed length, strings are `[n]u8` (string literals get a hidden terminating zero for C), and only lists of trees grow.

The code on these pages is compiled by `zig build test`. In the examples, `#= name value` shows a static value, `#: name type` a type, and `#! code` the diagnostic a line reports.
