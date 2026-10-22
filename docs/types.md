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

`variant Name = +(cases) [tagtype IntType | tagtype self | tagtype _] [implof ..] [!{ .. }]`

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
- `tagtype self` needs exactly one payload case, of one scalar field: an integer, `bool`, float or pointer (else `self_tag_without_niche`). Its tag type is that integer, or the unsigned integer of the field's size, and a tag is a bit pattern of the field: `+(None, Some(&u8)) tagtype self` is 8 bytes, `None` the null address. A tag must fit its tag type (else `tag_overflow`). A payload equal to another case's tag is that case: `Opt8.Some(255)` is `Opt8.None`.
- `tagtype _` has no tag: the cases share the room of the widest payload, like a C union. A value is read through a cast to a case (`v as V.Case`), which reinterprets its bytes, while compiling as well (bytes a smaller case leaves are zero then). Matching a case, `tagof`, `==`, `??` and a case `as` an int need a tag (`untagged_variant`), only a binder takes any value, and a written tag doesn't fit (`tag_overflow`). `stcmatch` tells the case of a static value.
- Pattern matching and `??` unwrapping are in [control.md](control.md#match).

```mond
variant Word = +(Int(u32), Float(f32)) tagtype _;
stc Word ONE = Word.Float(1.0);
stc u32 BITS = (ONE as Word.Int).$0;   #= BITS 1065353216
stc u64 SW = sizeof Word;              #= SW 4
fun tag = (Word w) -> u8: ret tagof w;   #! untagged_variant
```

### Packed variants `++( )`

A doubled sigil packs: `**( )` drops the padding between fields, `++( )` the padding up to the widest case. A case of a packed variant is its tag and its own payload, so each case has a size of its own (`sizeof Msg.Ping`) and the variant has none (`sizeof Msg` is `invalid_operand`). Like a trait it is only a parameter type: the function is realized for each case it is called with, its methods for each case `self` is, and `match` picks the arm while compiling. Anywhere else it is `unstorable_outside_parameter`. Behind a pointer it is the address of some case: `tagof p` reads its tag, anything else needs a cast to a case (`p as &Msg.Ping`). Tags work as for `+( )`; `tagtype _` leaves them out.

```mond
variant Msg = ++(Ping(u8 seq), Data(u64 a, u64 b), Quit);
fun weight = (Msg m) -> u64: ret match m {
    Msg.Ping(s) => s as u64,
    Msg.Data(a, b) => a + b,
    Msg.Quit => 0,
};
fun kind = (&Msg m) -> u8: ret tagof m;
stc u64 WT = weight(Msg.Data(3, 4));   #= WT 7
stc u64 SP = sizeof Msg.Ping;          #= SP 2
stc u64 SD = sizeof Msg.Data;          #= SD 24
Msg stored = Msg.Quit;                 #! unstorable_outside_parameter
```

### Unified variants `A || B`, `A ||| B`

`||` unifies types into a variant whose cases are the types. A member variant with tags brings its cases, renumbered one after another (a self-tagged one keeps its tags, the next member starts after them); any other type, an untagged variant too, is one case. The smallest tag tells them apart and the room of the widest holds the value, so it is stored like any variant. A value of a member's own type or of a case coerces into it (`[1, 2]` is a `[2]u32`, no `[2]u8`), a number literal takes the first number member it fits (`u8 || i64 v = -4` holds an `i64`), and `T x` and record patterns tell them apart. `||` binds looser than any prefix (`&u8 || [2]u8`), a member appears once and a single member is the type itself (`u32 || u32` is `u32`). A member needs a size (`unstorable_outside_parameter`). A template makes unified variants of type parameters: `variant Either = (type A, type B): A || B;` (as a `stcfun` would compute it).

```mond
variant A = +(X, Y);
variant B = +(Z(u32), W);
variant AB = A || B;
fun which = (AB v) -> u32: ret match v { A a => 1, B.Z(k) => k, B b => 50 };
stc u32 WH = which(A.X) + which(B.Z(7)) + which(B.W);   #= WH 58
variant Number = u32 || f32;
fun twice = (Number n) -> f32: ret match n { u32 i => i as f32 * 2.0, f32 f => f * 2.0 };
stc f32 TW = twice(3) + twice(0.5);    #= TW 7
stc u64 SN = sizeof Number;            #= SN 8
```

`|||` is packed and untagged, the unnamed form of `++(..) tagtype _`: a parameter type realized for each member it is called with (for a case, its variant).

```mond
fun scaled = (u32 ||| f32 x) -> f32: ret match x { u32 i => i as f32 * 10.0, f32 f => f * 10.0 };
stc f32 SC = scaled(2) + scaled(0.5);   #= SC 25
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
fun pick = () -> Named: ret Cat(1);            #! unstorable_outside_parameter
type Slot = *(&Named any);                     # opaque: an address of some implementer
fun peek = (Slot s) -> u32: ret (s.any as &Cat).id();
fun guess = (Slot s) -> u32: ret s.any.id();   #! unstorable_dereference
```

- A missing member is `trait_member_missing`, and a different signature is `trait_signature_mismatch`.
- A trait is only a parameter type (`Named n`, `&Named n`, `*Named n`). Like a template, the function is realized for each argument type, so calls are static and no trait value exists at run time. Defaults are realized per implementer through `self`. A trait type anywhere else (a local, field, result, array element, or inside a parameter type) is `unstorable_outside_parameter`; for a closed set of types use a variant. Behind a pointer it is allowed everywhere (`&Named`, `[]*Named`): an address of some implementer, used after a cast to its type (`p as &Cat`). Calling or dereferencing through it is `unstorable_dereference`, as for a pointer to a template or to a runtime-length array.
- Inside the function the parameter reaches only the trait's members. `match n { Cat c => .., _ => .. }` tells implementers apart (the set is open, so it needs `_`); each realization takes only the arm of its own type.
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
type Pair = (type T): [2]T;                  # a type expression: computed like a stcfun

stc Box(u32) BX = Box(u32)(7);
stc u32 G = BX.get();                        #= G 7
stc u64 SS = sizeof Stack(u16, 4);           #= SS 12
stc u64 SG = sizeof Grid(3);                 #= SG 3
stc Pair(u8) PR = [1, 2];                    #= PR [1, 2]
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
