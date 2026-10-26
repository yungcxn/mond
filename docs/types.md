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
type Line = *(Pt from, [2]Pt via);
stc Line L = Line(P, [P, Q]) with (from.y = 5, via[1].x = 7);
stc Pt LV = L.via[1];                        #= LV [7, 2]
stc D DD = D(4);                             #= DD [4, 8]
stc Cap C = Cap(9);                          #= C [5]
stc i32 X = P.x;                             #= X 3
```

- `x with (f = v)` is a copy with the named fields replaced, of a case value its payload's (it stays that case, or becomes the niche's it lands on). A part of a field is named by its path, fields of the records and elements of the arrays it holds (`pos.x = v`, `trail[i].y = v`, not through a pointer). The replacements apply in order, each value before its place, and the `where .. else` of every record on the way runs again, as in `x with (pos = x.pos with (x = v))`.
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

A packed record with an integer of a width without a keyword (`u3`, `u12`) packs to the bit: each field starts right after the one before it, from the lowest bit of the first byte up, an integer taking its width and anything else its bytes. Its size is the bytes its bits fill, its alignment 1. A field sharing a byte with another is read and written through those bytes, so it has no address (`bit_field_address`), and only integers and bools may share one (`unaligned_field`).

```mond
type Insn = **(mut u7 opcode, mut u5 rd, u3 f3, u5 rs1, u12 imm);
stc u64 SI = sizeof Insn;                          #= SI 4
stcfun with_rd = () -> u64 {
    mut Insn i = Insn(0x13, 1, 0, 2, 300);
    i.rd += 30;
    ret i.rd as u64 * 1000 + i.imm;
}
stc u64 RD = with_rd();                            #= RD 31300
fun rd_of = (*Insn i) -> &u5: ret i.rd.&;          #! bit_field_address
type Mixed = **(u4 low, [2]u8 bytes, u4 high);     #! unaligned_field
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

`variant Name = +(cases) [tagtype IntType | tagtype self | tagtype self.field | tagtype strategy | notagtype] [implof ..] [!{ .. }]`

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
- `tagtype self.field` does the same with a payload of several fields: the field it names is the one whose unused bit patterns are the other cases, and the variant is laid out as that payload. A value of another case is zeros with its tag in that field. The field may be deeper (`self.o.inner.code`), and a name reaches into the one record a payload or field holds (`+(Some(Node), None = 0) tagtype self.next`). A payload case whose own tag another case has written takes the smallest free one.

```mond
variant List = +(Cons(u64 head, &List tail), Nil) tagtype self.tail;   # Nil is a null tail
variant Slot = +(Used(u32 value, u8 kind), Free = 255) tagtype self.kind;
stc u64 LS = sizeof List * 100 + sizeof Slot;     #= LS 1608
stc bool SAME = Slot.Used(9, 255) == Slot.Free;   #= SAME true
fun length = (&List l) -> u64: ret match l.* { List.Cons(_, rest) => 1 + length(rest), List.Nil => 0 };
variant Two = +(A(u8 x, u8 y), B(u8 z), C) tagtype self.y;   #! self_tag_without_niche
```
- `tagtype` of a static record with the fields `storage` (an integer type), `wrap`, `case_of` and `unwrap` is a strategy: every value is stored in `storage` as `wrap(tag, payload bits)` makes it, `case_of(stored)` gives its tag back and `unwrap(stored, tag)` its payload's bits (as `u64`s, a tag as `u32`). A case has no payload or one scalar field. When the variant is declared, the round trip of every case is run on payloads 0, 1, all ones, alternating bits and the top bit, on every payload of up to 16 bits, and the stored bits must fit `storage` (else `tag_strategy_failed`). Such a variant is no member of `||` (`strategy_member`). [examples/lib/tags.mn](../examples/lib/tags.mn) has the record and a strategy.

```mond
type Tagging = *(type storage, (u32, u64) -> u64 wrap, (u64) -> u32 case_of, (u64, u32) -> u64 unwrap);
stcfun ranges = (u64 width) -> Tagging: ret Tagging(
    storage = u16,
    wrap = (u32 tag, u64 payload) -> u64: ret tag as u64 * width + payload,
    case_of = (u64 stored) -> u32: ret (stored / width) as u32,
    unwrap = (u64 stored, u32 tag) -> u64: ret stored % width,
);
variant Small = +(Low(u8), High(u8), Zero) tagtype ranges(256);      # 2 bytes, no tag bits
stc u64 SS = sizeof Small;                                             #= SS 2
fun high = (Small s) -> u8: ret match s { Small.High(h) => h, _ => 0 };
stc u8 HI = high(Small.High(9));                                       #= HI 9
variant Lossy = +(A(u16), B) tagtype ranges(1000);                     #! tag_strategy_failed
```
- `notagtype` has no tag: the cases share the room of the widest payload, like a C union. A value is read through a cast to a case (`v as V.Case`), which reinterprets its bytes, while compiling as well (bytes a smaller case leaves are zero then). Matching a case, `tagof`, `==`, `??` and a case `as` an int need a tag (`untagged_variant`), only a binder takes any value, and a written tag doesn't fit (`tag_overflow`). `stcmatch` tells the case of a static value.
- Pattern matching and `??` unwrapping are in [control.md](control.md#match).

```mond
variant Word = +(Int(u32), Float(f32)) notagtype;
stc Word ONE = Word.Float(1.0);
stc u32 BITS = (ONE as Word.Int).$0;   #= BITS 1065353216
stc u64 SW = sizeof Word;              #= SW 4
fun tag = (Word w) -> u8: ret tagof w;   #! untagged_variant
```

### Packed variants `++( )`

A doubled sigil packs: `**( )` drops the padding between fields, `++( )` the padding up to the widest case. A case of a packed variant is its tag and its own payload, so each case has a size of its own (`sizeof Msg.Ping`) and the variant has none (`sizeof Msg` is `invalid_operand`). Like a trait it is only a parameter type: the function is realized for each case it is called with, its methods for each case `self` is, and `match` picks the arm while compiling. Anywhere else it is `unstorable_outside_parameter`. Behind a pointer it is the address of some case: `tagof p` reads its tag, anything else needs a cast to a case (`p as &Msg.Ping`). Tags work as for `+( )`; `notagtype` leaves them out.

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

`|||` is packed and untagged, the unnamed form of `++(..) notagtype`: a parameter type realized for each member it is called with (for a case, its variant).

```mond
fun scaled = (u32 ||| f32 x) -> f32: ret match x { u32 i => i as f32 * 10.0, f32 f => f * 10.0 };
stc f32 SC = scaled(2) + scaled(0.5);   #= SC 25
```

### Subsets `V -- V.Case`

`A -- B` is the variant `A` without the cases of `B`: a case, a member of a unified variant, `||` of them in parentheses, or another subset. It keeps the layout and the tags of `A`'s whole, so a value of it is a value of the whole as it is: it goes into the whole, or into a subset keeping all its cases, without any cost. A value of the whole goes into it only through a `match` (see [control.md](control.md#match)). `--` binds tighter than `||`, so `A || B -- B.X` is `A || (B -- B.X)`, and `A -- A.X -- A.Y` removes both. Unifying keeps cases out: `Config || (IoErr -- IoErr.NotFound)` is the same type as `(Config || IoErr) -- IoErr.NotFound`. Without any case left it is `never`.

```mond
variant IoErr = +(NotFound, Timeout, Denied);
type Config = *(u32 port);
type Loaded = Config || (IoErr -- IoErr.NotFound);
stc u64 SL = sizeof Loaded;                       #= SL 8
stc bool SAME = Loaded == (Config || IoErr) -- IoErr.NotFound;   #= SAME true
fun code = (Loaded l) -> u32: ret match l { Config c => c.port, IoErr.Timeout => 1, IoErr.Denied => 2 };
fun widen = (IoErr -- IoErr.Denied e) -> IoErr: ret e;
stc u32 CODE = code(IoErr.Timeout);               #= CODE 1
fun lost = () -> IoErr -- IoErr.NotFound: ret IoErr.NotFound;   #! type_mismatch
type Wrong = u32 -- u32;                          #! type_mismatch
```

- The left side must be a variant with tags: an untagged or packed variant has no cases to tell apart (`type_mismatch`), and the right side must be parts of it.
- `tagof`, `==`, `??`, casts and methods work as on the whole; `??` unwraps the first payload case the subset keeps, and the fallback of a subset result is one of its cases.
- A subset whose all-zero value is a case it leaves out is not zeroed: a record or array holding one, declared without a value, must be written before it is read, as a scalar, and a field of it without a default makes `T.init()` an error (`use_before_initialization`).

### Testing a case: `oftype`

`x oftype T` is whether `x` is a value of `T`: of its own type, of a trait it implements, and for a value of a variant, of the type its case is. That is the case itself, a subset keeping it, the variant, or a unified variant holding it; of a unified variant, also the member the value is. Where the type alone answers, the answer is static (a `Shape -- Shape.Dot` is never a `Shape.Dot`). Otherwise the value's tag is tested at run time, so `stcif` and `stc` can't take it (`not_static`). `oftype` doesn't narrow `x`; a `match` does. A cast chains with it like `as`: `7 as u32 oftype Num`.

```mond
variant Shape = +(Dot, Box(u32 side), Ring(u32 r));
type Num = u32 || f32 || Shape;
fun round = (Shape s) -> bool: ret s oftype Shape -- Shape.Box;
fun is_box = (Num n) -> bool: ret n oftype Shape.Box;
stc []bool TESTS = [round(Shape.Ring(1)), is_box(Shape.Box(2)), is_box(1.5 as f32)];   #= TESTS [true, true, false]
stc bool MEMBER = 7 as u32 oftype Num;              #= MEMBER true
fun never = (Shape -- Shape.Dot s) -> bool { stc bool NO = s oftype Shape.Dot; ret NO; }
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
