# Types

## Records `*( )`

`type Name = *(fields) [assertsize N] [implof Traits] [!{ members }]`. A record has at least one field (`*()` is a parse error).

A field is `[mut] Type [name] [= default] [where c else v]`. `**( )` is packed (no padding). Records are nominal: two equal `*(..)` declarations are different types.

```mond
type Pt = *(i32 x, i32 y = 0);
type D = *(u32 a, u32 b = a * 2);           # a default sees earlier fields
type Cap = *(u8 v where v < 5 else 5);

stc Pt P = Pt(3);                            #= P [3, 0]
stc Pt Q = Pt(y = 2, x = 1);                 #= Q [1, 2]
stc Pt U = P with (y = 9);                   #= U [3, 9]
stc D DD = D(4);                             #= DD [4, 8]
stc Cap C = Cap(9);                          #= C [5]
stc i32 X = P.x;                             #= X 3
```

- `x with (f = v)` is a copy with the named fields replaced.
- Unnamed fields are `$0`, `$1`, ...
- `T(..)` needs every field that has no default, even an array (a missing one is `wrong_arity`). `T.init()` builds a value with every field defaulted or zeroed, so `T.init() with (f = v)` sets just some fields. An unknown name is `unknown_named_argument`.
- Writing `p.x = ..` needs a `mut` field and a writable `p` (or a `*` pointer to it).
- The layout is C order with natural alignment. `assertsize N` (bytes) or `assertsize T` checks it, `alignof` gives the alignment in bytes.
- A record can't contain itself by value (`recursive_by_value_type`). Use a pointer.

```mond
type A = *(u8 a, u32 b);
type Pk = **(u8 a, u32 b);
type Node = *(i32 value, *Node next);
stc u64 SA = sizeof A;     #= SA 8
stc u64 SP = sizeof Pk;    #= SP 5
stc u64 AA = alignof A;    #= AA 4
stc u64 AP = alignof Pk;   #= AP 1
stc u64 AF = alignof (i32) -> i32;   #= AF 8
type Big = *(u64 a) assertsize 4;   #! assertsize_failed
```

## Methods

Members go in `!{ }`. Inside them `self` is a `*Self`, and fields are reached only through `self.f`.

```mond
type Acc = *(mut i64 total) !{
    init = (i64 start) -> Acc: ret Acc(start);
    fun add = (i64 v) -> i64 { self.total += v; ret self.total; }
    fun peek = () -> i64: ret self.total;
    fun reset = () { self.* = Acc(0); }
}
stcfun use = () -> i64 {
    mut Acc a = Acc.init(10);
    a.add(5);
    ret a.peek() + Acc.peek(a.&);
}
stc i64 U = use();   #= U 30
```

- A method that writes `self` (directly or by calling a method that does) needs a writable receiver. Others accept `&T`.
- `Type.m` is a function value `(*Type, ..) -> R`.
- Methods may take `type T` parameters (`b.size_of(u16)`), and a template's methods see its parameters.
- Builtin members:
  - `T.init()` is the user's `init`, or else defaults and zeros.
  - `x.deinit()` / `deinit x` is the user's `deinit`, or else a no-op.
  - `next`/`has_next` make a value iterable (see [control.md](control.md#loops)).
- `init`, `deinit`, `has_next` and `next` are written without `fun` (`fun init = ..` is `redundant_fun`). Outside a type these names are ordinary: a function `next` needs `fun`.

## Variants `+( )`

`variant Name = +(cases) [tagtype IntType | tagtype self] [implof ..] [!{ .. }]`

A case is `Name`, `Name(payload fields)` or `Name = tag`. Tags count up from 0, or from the last explicit tag. Without `tagtype`, the tag type is the smallest unsigned type that fits.

```mond
variant Shape = +(Circle(u32 r), Rect(u32 w, u32 h), Dot);
variant Seq = +(A, B = 10, C);
variant Opt8 = +(Some(u8), None = 0xFF) tagtype self;   # None lives in the unused byte values

fun area = (Shape s) -> u32: ret match s {
    Shape.Circle(r) => 3 * r * r,
    Shape.Rect(w, h) => w * h,
    Shape.Dot => 0,
};
stc u32 AR = area(Shape.Rect(2, 5));   #= AR 10
stc u8 TC = tagof Seq.C;                #= TC 11
stc u64 SZ = sizeof Opt8;              #= SZ 1
stc Opt8 O = 42;                        # a single-payload variant takes its payload
```

- A case value has the case type `Shape.Rect`, which coerces to `Shape`. A payload field is a member of a case value (`r.w`).
- Casts:
  - `v as V.Case` retags within the variant.
  - `x as V.Case` wraps a payload.
  - A payload-free case `as u32` gives its tag.
- `tagof v` is the tag of a variant value (`tagof Seq.C`); of anything else, a type too, it is `invalid_operand`.
- `tagtype self` needs exactly one single-integer payload case (else `self_tag_without_niche`), and a tag must fit its tag type (else `tag_overflow`). A payload equal to another case's tag is that case: `Opt8.Some(255)` is `Opt8.None`.
- Pattern matching and `??` unwrapping are in [control.md](control.md#match).

### Unions `A || B`

A union is a variant made of other variants. Their tags are renumbered one after another, and members and their cases coerce into it.

```mond
variant A = +(X, Y);
variant B = +(Z(u32), W);
variant AB = A || B;
fun which = (AB v) -> u32: ret match v { A a => 1, B.Z(k) => k, B b => 50 };
stc u32 WH = which(A.X) + which(B.Z(7)) + which(B.W);   #= WH 58
```

## Traits

`trait T = [implof Supers] !{ signatures and defaults }`. In a signature, `typeof self` means the implementing type.

```mond
trait Named = !{
    fun id = () -> u32;
    fun twice = () -> u32: ret self.id() * 2;   # a default
}
type Cat = *(u32 v) implof Named !{ fun id = () -> u32: ret self.v; }
type Dog = *(u32 v) implof Named !{
    fun id = () -> u32: ret self.v;
    fun twice = () -> u32: ret 77;              # overrides the default
}
fun call = (&Named n) -> u32: ret n.twice();
stc Cat CAT = Cat(4);
stc Dog DOG = Dog(1);
stc u32 TR = call(CAT.&) + call(DOG.&);         #= TR 85
stc bool IS = CAT oftype Named;                 #= IS true
```

```mond
trait Named = !{ fun id = () -> u32; }
type Cat = *(u32 v) implof Named !{ fun id = () -> u32: ret self.v; }
fun pick = () -> Named: ret Cat(1);            #! trait_outside_parameter
type Slot = *(&Named any);                     # opaque: an address of some implementer
fun peek = (Slot s) -> u32: ret (s.any as &Cat).id();
fun guess = (Slot s) -> u32: ret s.any.id();   #! unstorable_dereference
```

- A missing member is `trait_member_missing`, and a different signature is `trait_signature_mismatch`.
- A trait is only a parameter type (`Named n`, `&Named n`, `*Named n`). Like a template, the function is realized for each argument type, so calls are static and no trait value exists at run time. Defaults are realized per implementer through `self`. A trait type anywhere else (a local, field, result, array element, or inside a parameter type) is `trait_outside_parameter`; for a closed set of types use a variant. Behind a pointer it is allowed everywhere (`&Named`, `[]*Named`): an address of some implementer, used after a cast to its type (`p as &Cat`). Calling or dereferencing through it is `unstorable_dereference`, as for a pointer to a template or to a runtime-length array.
- Inside the function the parameter reaches only the trait's members.
- `T oftype Named` also works on types, which makes it a constraint for generics: `stcfun max_of = (type T where T oftype Cmp(T)): (T a, T b) -> T: ..`.
- Only declared types implement traits; built-in types like `u32` can't.
- A generic trait looks like `trait Cmp = (type T): !{ fun cmp = (T o) -> i32; }` and is implemented as `implof Cmp(Money)`.

## Templates

A type, variant or trait with static parameters. A realization is memoized: `Box(i32)` is always the same type.

```mond
type Box = (type T): *(mut T value) !{ fun get = () -> T: ret self.value; };
variant Maybe = (type T): +(Just(T), Nothing);
type Stack = (type T, u32 CAP stcwhere CAP > 0): *(mut [CAP]T items, mut u32 len = 0);
stcfun Grid = (u32 n): ret *([n]u8 cells);   # a stcfun can make a type too

stc Box(u32) BX = Box(u32)(7);
stc u32 G = BX.get();                        #= G 7
stc u64 SS = sizeof Stack(u16, 4);           #= SS 12
stc u64 SG = sizeof Grid(3);                 #= SG 3
```

- The arguments must be static, and they are not inferred (`Box(value = 3)` is `wrong_arity`). A failing `stcwhere` of a template is reported at the template.
- A template used as a parameter type, `(Box b)`, realizes the function for each argument. Only the members whose type doesn't depend on the parameters are reachable (`generic_member`). `match b { Box(u8) x => .. }` narrows it to one realization, where everything is reachable.
- A bare template where a concrete type is needed is `unrealized_template`. Behind a pointer (`*Box`) it is an address only, like a pointer to a trait: used after a cast to a realization (`p as *Box(u32)`).

## Aliases and local types

`type A = <type>` is an alias, the same type. Types and traits may be declared inside function bodies. They see the function's types and stcfuns, but never its locals.

```mond
type Bytes = [4]u8;
fun local = () -> u64 {
    type Pair = *(u32 a, u32 b);
    ret sizeof Pair;
}
stc u64 LT = local() + sizeof Bytes;   #= LT 12
```
