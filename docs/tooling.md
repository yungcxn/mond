# Tooling

The compiler checks and lowers programs. It has no code generation yet: the output is the resolved tree and an SSA IR.

```sh
zig build                         # builds ./mond
./mond -b app.mn                  # check: the resolved tree, then the lowered IR
./mond -b app.mn -d               # the declarations instead of the tree
./mond -b app.mn -i add '#3' ':12'  # inspect declarations by name, index or line
zig build test [-- filter]        # examples and docs
zig build bench -- 10             # time the pipeline over all examples
zig build lsp                     # the language server, into lsp/vscode and lsp/vim
```

## Tests

Every `.mn` file under `examples/` and every ```` ```mond ```` block in `docs/` must report exactly the diagnostics it marks and pass its checks. A doc block without `$main` gets an empty one appended.

| comment | checks |
|---|---|
| `#! code ..` | this line reports these diagnostics |
| `#= name value` | the static value of `name`, declared on this line |
| `#: name type` | the type of `name` |

These markers count anywhere in a comment. Values print as they are stored: a variant as `+(..).Case[payload]`, a computed `[]u8` as numbers, a string literal as text. Files in `examples/negative/` must mark at least one diagnostic. The docs must name every keyword, tree kind and diagnostic in backticks, so a new feature fails the tests until it is documented.

## Editor

`mond-lsp` provides highlighting, diagnostics, go to definition, references, outline, hover and completion (also for `ast.` kinds and `$` views). Setup is described in `lsp/vscode/README.md` and `lsp/vim/README.md`.

A file that another file includes isn't asked for a `$main`.

## Diagnostics

Lexing and parsing stop at the first error (`LexingError_*`, `Expected*`, `Illegal*`, `NoRuleFound`), and then nothing is resolved, so a test file with a parse error reports only that error. Resolving reports everything it finds. Only `redundant_match_arm` is a warning; everything else is an error.

| code | when |
|---|---|
| `undefined_name` | a name is not visible |
| `duplicate_declaration` | a name is declared twice in one scope (overloads aside) |
| `unknown_member` | there is no such field, case, method or view |
| `type_mismatch` | a value doesn't fit the expected type |
| `infinite_type` | an inferred type contains itself (`fun f = (): ret [f()];`) |
| `uninferable_type` | nothing fixes a type (`[]`, a runtime loop length, mutual recursion) |
| `not_a_type` | a type was expected |
| `not_callable` | something that isn't a function is called |
| `wrong_arity` | the wrong number of arguments, children or fields |
| `unknown_named_argument` | no parameter or field has that name |
| `no_matching_overload` / `ambiguous_overload` | no overload fits / several fit equally |
| `invalid_cast` | `as` or `asbits` between incompatible types |
| `runit_mixing` | a unit call used as a branch next to values |
| `declaration_cycle` | declarations depend on each other in a cycle |
| `recursive_by_value_type` | a type contains itself without a pointer |
| `assertsize_failed` | the size differs from `assertsize` |
| `tag_overflow` | a tag doesn't fit the tag type |
| `self_tag_without_niche` | `tagof self` with no single-integer payload case |
| `trait_member_missing` / `trait_signature_mismatch` | an implementation lacks a member / differs from the trait |
| `no_deinit` | `deinit` on a value without one |
| `not_static` | a compile-time value depends on runtime |
| `static_eval_failed` | compile-time evaluation failed (division by zero, bounds, budget, depth) |
| `stcwhere_violated` | a `stcwhere` condition is false |
| `redundant_stc` | a `stc..` form where everything is static already |
| `genexpr_index` | a range used as an index |
| `generic_member` | a template-dependent member of an unopened template value |
| `missing_ret` / `redundant_ret` | a path doesn't return / `ret` before a template's definition |
| `redundant_fun` | `fun` on a predefined name (`$main`, `$init`, ...) |
| `unrealized_template` | a template where a concrete type is needed |
| `impure_stcfun` | a `stcfun` writes state outside itself |
| `brk_outside_loop` / `cont_outside_loop` | a jump outside a loop |
| `ret_type_mismatch` | `ret` disagrees with the result type |
| `non_exhaustive_match` | some value matches no arm |
| `redundant_match_arm` | (warning) an arm can never be reached first |
| `assign_to_immutable` | a write to something not `mut` |
| `write_through_immutable_pointer` | a write through `&T` |
| `use_before_initialization` | a read before every path wrote it |
| `destructure_type_conflict` | the names of a multi-assignment need different types |
| `missing_main` | there is no `$main` |
| `stray_unquote` | `@` outside a quote |
| `frozen_declaration` | a write to a declaration that is already resolved, or a write outside a splice |
| `macro_error` | a macro called `$error` |
| `include_failed` | the file can't be read, lexed or parsed |
| `endless_expansion` | more than 64 expansion passes |
