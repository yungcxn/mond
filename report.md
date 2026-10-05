# test suite expansion: report

state: `zig build test` → 399 passed, 0 failed (181 positive, 218 negative files, before: 139). `./mond` runs `huge.mn` cleanly.
nothing is left open.

## tests added (260 files)

| area | files | prefix |
|---|---|---|
| lexer / parser errors, one per file | 62 | `negative/lex_*`, `negative/parse_*` |
| syntax forms, precedence, literals, limits | 19 | `positive/syntax_*` |
| names, scoping, redeclaration, cycles, `$main` | 31 | `scope_*` |
| typing, coercions, casts, literals, overflow, joins | 26 | `typing_*` |
| control flow, definite init, exhaustiveness, redundancy | 20 | `flow_*` |
| records, variants, traits, layouts, tags | 28 | `data_*` |
| calls, overloads, where dispatch, methods, closures, pointers | 32 | `fn_*` |
| compile-time evaluation, templates | 17 | `ctfe_*` |
| whole programs | 18 | `general-purpose/prog_*`, `prog_*` |
| lowering stress (ssa joins, defers, match, closures, aggregates) | 5 | `positive/ir_*` |
| misc | 2 | `assign_swap`, `edge_rare_diagnostics` |

every diagnostic code is reached at least 3 times, every reachable lexer/parser error has its own file, every `#=` value was checked independently (python).

## compiler fixes

- lexer / parser: cursor only advances on success (wrong eof line, panic in `handle_err`), `'\''`, `a *(b)` / `a +(b)`, parenthesized range in `for` heads, `if` inside named arguments, `[x] {` in heads, 64-entry buffers (method params + self, trait members, unions, implof)
- typing: literal branches take the other branches' type, float `%`, bitwise/shift only on integers, string literals never `*u8`, malformed literals report once, function values coerce to `fun`, lambdas take the expected result type
- data: defaults see earlier fields only, implof/supers must be traits, implicit tags keep the explicit tag's type, self tag without payload no longer crashes, case field access / retag / builtin `$init` `$deinit` at compile time and in lowering, `sizeof` of unlengthed arrays
- calls: length-generic parameters no longer leak a length from a rejected call, stcwhere sees static arguments, record/case values are not constructors, `writes` spreads to methods calling writers, duplicate overloads without `where`
- flow: induced return types re-check earlier branches, endless loops are `never`, jagged loop values, runtime `0..` loops are uninferable, poisoned static cycles stay quiet
- interpreter: return values coerce to the signature, `??` only unwraps the payload case, stcfun args that escape are not static, static parameters may be addressed

## language decisions (implemented and pinned by tests)

- `**` power removed everywhere (lexer, tree, checker, interpreter, lowerer, ir)
- multi-assign evaluates all values first: `a, b = b, a` swaps
- unknown escapes and malformed `\x` are `LexingError_InvalidEscape`
- `1 + 1..=4` stays `1 + (1..=4)`
- array literals and untyped multi values join their elements, literals last (`[1, -2, 3]` is `[3]i32`)
- redeclaration in the same scope is `duplicate_declaration`, duplicate binders in one pattern too (`small.mn` renamed its second `myvar`)
- an overloaded function as a value picks the overload of the expected type
- local types see only the types and stcfuns of their function, never its locals
- `redundant_match_arm` fires for every arm the earlier arms cover (usefulness check); a typed binder after full coverage counts like `_` (`small.mn` / `huge.mn` dropped the arm before it so the showcase stays reachable)
- `huge.mn`: `ByteStream` / `tokenize` take `&u8`, since string literals are immutable

## design limits kept (tagged `# LIMIT:` in the tests)

- at most 64 cases / fields / params per list (parser `StackOverflow`)
- the 65th uninitialized scalar is not tracked by definite initialization
- `&&` is one token, `& &T` needs a space
- a static recursion overflow is reported at the recursive call, not at the `stc` that started it
