# Compiler bugs, holes and limits found by the new tests

Found while writing `examples/general-purpose/` and the new `examples/negative/` files.
Every workaround is tagged in the test files with `# BUG:` (compiler bug) or `# LIMIT:` (language limit).
Search with `grep -rn "# BUG\|# LIMIT" examples`.

## Compiler bugs

### Crashes

1. `x as &[n]u8` with a runtime `n` panics in `has_vars` instead of reporting `not_static` (`strings.mn:179`).
2. A record pattern that omits a field and has only literal sub-patterns (`Ent(hp = 255)`) panics in `has_vars` (`edge_patterns.mn:54`).
3. `b[2..<4].&` passed to a `&[]u8` parameter panics the checker (`run_tokenizer.mn:39`).
   ```
   fun g = (&[]u8 x) -> u64: ret x.$len;
   fun f = () -> u64 { mut [16]u8 b; ret g(b[2..<4].&); }
   ```
4. A runtime call of a stcfun with more static than runtime arguments panics `HighLowerer.direct` (`matrix_templates.mn:76`).
   ```
   stcfun f = (type T, type U): (T a) -> T: ret a;
   $main = () { x = f(u8, u8)(1); }
   ```

### Wrong results in the interpreter

5. A callee that writes through a pointer into a caller's array built from a string literal frees the thawed cells on return; later calls clobber element 0 (`strings.mn:50`).
6. Storing a whole record through a pointer in a callee (`p.* = Node(..)`, `ns.*[i] = Node(..)`) leaves a dangling block that later calls clobber (`containers.mn:108`).
   ```
   fun put = (*[3]Node ns, u64 at, i32 v, u32 nx) { ns.*[at] = Node(v, nx); }
   put(n.&, 0, 1, 6); put(n.&, 1, 2, 0);   # n[0].next is now 0, expected 6
   ```
7. A trait default method called through a trait value ignores the implementing type's override; a direct call is correct (`traits_oop.mn:8`).
8. `match self { … }` and `self == Case` in a variant method are not dereferenced when executed (`non_exhaustive_match` / `false`); `self.*` works (`edge_variants.mn:1`).
9. `where … else` on a type field is never applied at construction: `Temp(-50).kelvin` stays `-50`. On function parameters it works (`edge_types.mn:1`).
10. A `for` as the body of a value `for` (`for i in 0..<3: for j in 0..<2: i * 2 + j`) yields no array element (`edge_values.mn:93`).
11. `stc []u8 X = stcfor 0..<256: 7;` gives `type_mismatch` (found `u32`, expected `u8`); `[]u16` works (`tokenizer_state.mn:66`).
12. `for T in [u8, u16]: t += sizeof T;` inside a fun or stcfun gives no diagnostic but every static evaluation is poison (`layout_shapes.mn:48`).
13. A `match` on an element of a zero-initialised variant array that was never written is `not_static` (`constant_fold.mn:335`).
14. An or-pattern whose alternatives bind the same names is `not_static` when executed (`edge_patterns.mn:70`).
15. A stcfun called with the variable of a `stcfor` (also `stcmatch` on it) reports `not_static` although the value is computed (`edge_globals.mn:3`, `static_tables.mn:98`, `generic_algos.mn:165`).

### Wrong diagnostics, typing and parsing

16. Named arguments do not choose between overloads of the same arity; only the first candidate is tried, e.g. `pair(0, c = 1)` and `h(1, d = 9)` report `wrong_arity` (`overloads.mn:17`).
17. A template applied to its own parameters inside its own body is a different type: `Pair(B, A)` swapped gives `not_callable`, and `Poly(N)` is unequal to the realised `Poly(8)` with identical printed types (`generics.mn:4`, `polynomials.mn:1`).
18. A stcfun parameter type built from a template with static value params never equals the caller's realisation (`matrix_templates.mn:18`).
   ```
   type B1 = (u32 N): *([N]u8 a);
   stcfun f = (u32 N): (B1(N) b) -> u32: ret N;
   fun t = () -> u32 { B1(2) a = B1(2)(a = [1, 2]); ret f(2)(a); }   # type_mismatch
   ```
19. A generic `&[]T` parameter rejects `*[N]T` (`generics.mn:39`); a typed declaration `&[]u32 q = a.&` and `f(S.&)` for a `[]u32` static also fail (`edge_globals.mn:44`); a stcfun `&[]u8` parameter rejects `*[N]u8` from a static call (`text_algorithms.mn:203`, `compression.mn:380`). Plain `fun` arguments accept them.
20. `-10..=-2` parses as `-(10..=-2)` and reports `type_mismatch`; `(-10)..=-2` works (`edge_patterns.mn:7`).
21. A template value parameter in a field default (`mut u32 sets = N`) gives `undefined_name` (`graphs.mn:131`).
22. A wrong kind of template argument (`Stack(u8, u8)`, `Stack(4, u8)`) is reported at the template declaration, never at the argument (`template_args.mn:4`).
23. Nested payload exhaustiveness is per outer case, so nested arms need a `_` arm (`nested_templates.mn:25`).

## Invalid code the compiler accepts

Recorded as comments at the top of the negative files.

### Mutability and pointers (`safety.mn`, `generic_safety.mn`)

- `*i32 p = imm.&;` and `*i32 p = param.&;`: a mutable pointer to an immutable variable.
- `*i32 p = ip.x.&;`, `mp.x.&`, `ip.y.&`: a mutable pointer to a non-mut field, or to a mut field of an immutable value.
- `takes_mut(rp.y.&)`, `takes_mut(rq.minner.y.&)`: a mutable pointer taken through `&P` / `&Q`.
- `*P d = ip.&;`, `*P d = rq.minner.&;`: a mutable pointer to an immutable record.
- `ip.bump();`, `rp.bump();`, `rp.set_arr();`: a method that writes `self` called on an immutable variable or through `&P`.
- `*u8 s = "text".&;`: a mutable pointer to a string literal.
- `*i32 t = (imm + 1).&;`: the address of a temporary.
- `for x in arr { *i32 p = x.&; }`: a mutable pointer to the loop copy.
- A closure reading a never-initialised variable, and use of a value after `deinit`.

Note: `small.mn` itself takes `*u32` from an immutable local, so the first group may be intended.

### Declarations and checks (`edge_errors.mn`, `template_args.mn`, `trait_generics.mn`, `table_failures.mn`)

- Duplicate field `*(i32 a, i32 a)`, duplicate variant case `+(A, B(u8), A)`, duplicate parameter `(u32 a, u32 a)`.
- A function that does not return on every path, also `-> i32 { }`.
- `V u = V.B;`: a payload case used without its payload.
- Constant out-of-range index `arr[7]` / `arr[-1]` on `[3]i32` (only caught when executed).
- Template value arguments that do not fit: `Buf(-1)`, `Buf(5000000000)` for `(u32 N)`.
- Wrong array length from generators: `stc [4]u32 T = stcfor 0..<5: $it;`, `[4]u32 a = for i in 0..<5: i;`.
- A default trait method overridden with a different arity, parameter type or return type.
- `stc u8 X = 200 + 100` gives 300, `stc u32 A = 1 << 32` gives 4294967296, `u8 g = 200 + 100;` is accepted.

## Language limits (by design or grammar)

- No `~`, `>>=`, `<<=`, `&=`, `|=`, `^=`, `[x; n]` arrays, `\x41` escapes; decimal `1_000` is not a literal (only `0x` `0b` `0o` take `_`); `brk value` is not supported.
- `&`, `^`, `|` bind looser than `==`; `as` does not bind into the right operand of `*` `/` `%`; `<-` labels only the operand right before it.
- A condition or range ending in a parenthesised group before `{` or `:` parses as a lambda, e.g. `if a or (b) {`, `for i in 0..<(n - 1) {`.
- A one-element array literal needs a trailing comma (`[7,]`); `[]` alone is not inferable.
- Local functions are not hoisted (no local mutual recursion); `fun f = (type T, T a)` needs `stcfun`.
- A `&u8` cannot be indexed.
- Escaping capturing closures cannot be evaluated at compile time (`not_static`).
- The compile-time interpreter cannot order pointers (`p < q`), keep a pointer in a variant payload, cast a variant value to an integer (`c as u32`, use `c.$tag`), or call a method on a case constant (`Light.Green.next()`).
- A variant field of a zeroed record has no value (`mut Elevator e;`), reading it is `not_static`.
- Exhaustiveness is per case: `Door(true)` plus `Door(false)` does not cover `Door`.
- Field defaults cannot name other fields.
- Interpreter budget: 1,000,000 nodes per top level `stc`, call depth 256.
