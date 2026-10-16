# Tooling

The compiler checks a program, lowers it to an SSA IR, and builds a native executable of it with LLVM and the linker built in (lld). Nothing else is linked unless asked for: the program starts in mond's own `_start`, and `-lc` links the C library.

```sh
zig build                           # builds ./mond (needs llvm and lld, see below)
./mond --help                       # the flags and modes
./mond -b app.mn                    # builds ./app
./mond -b app.mn -o out -m default  # builds ./out, optimized
./mond -b app.mn io.c libz.a        # compiles io.c with the c compiler, links both in
./mond -b app.mn -lc -lm            # with the C library and libm
./mond -b app.mn -p tree,ir,llvm    # also prints stages: tree, decls, ir, llvm
./mond -b app.mn -i add '#3' ':12'  # inspect declarations by name, index or line
zig build test [-- filter]          # examples, docs, then the backend tests
zig build test-backend [-- filter]  # only the programs of examples/backend
zig build lsp                       # the language server, into lsp/vscode and lsp/vim
```

| flag | |
|---|---|
| `-b` `--build` | the source, then files to link with it: `.o` `.a` `.so` `.dylib` as they are, any other (`.c` `.cpp` `.s` ..) compiled first by `<cc> -c file -o <out>.file.o`, with the mode's `-O` flag, and `-g` under `-d`. The objects are deleted after linking (kept with `-d` on macOS) |
| `-c` `--cc` | the c compiler and its flags (`--cc "clang -Iinclude"`), else `$CC`, else `cc` |
| `-o` `--out` | the executable, by default the source's name without `.mn` |
| `-m` `--mode` | how to optimize: `none` (the default, `-O0`) and `safe` (`-O2`) keep the runtime checks; `less` `default` `aggressive` (`-O1` `-O2` `-O3`), `size` and `minsize` (`-Os` `-Oz`) drop them |
| `-d` `--debug` | DWARF for a debugger: functions, source lines and frame pointers. On macOS the object file stays next to the executable, lldb reads the DWARF from it. Code from `include` and macros is placed at the line that splices it |
| `-l<name>` `-L<dir>` | a library, and where libraries are, as cc takes them |
| `-lc` | the C library: the program starts through C's startup, which calls `$main` |
| `-w` `--with` | further linker inputs, comma separated: `-w -framework,Cocoa` |
| `-p` `--print` | `tree` the resolved tree, `decls` the declarations, `ir` the SSA IR, `llvm` the optimized LLVM IR |
| `-i` `--inspect` | declarations by name, `#index` or `:line`; nothing is built |
| `-h` `--help` | the flags and modes; also shown when `mond` gets no arguments |

Diagnostics go to stderr as `file:line:column: code operands`, which editors and vim's `:make` jump to; a lexing or parse error shows its line below, the token marked with `~`. One in included code names the included file and then the include as `file:line:column: included here`. Colors only go to a terminal. `$main` returns the exit code, and takes nothing or `(argc, &&u8 argv)` (see [basics](basics.md#program)).

Records, arrays and variants live in memory: they are passed by address and returned through a pointer the caller gives. LLVM's passes promote small ones to registers in every mode but `none`.

The runtime checks stop the program with a trap (a debugger shows the line) on a division or remainder by zero (and of the smallest integer by `-1`), a shift by the width or more, an index past the end of an array, and on reaching code that can't be reached, like a failing `x??`. Without them these are undefined behavior. At compile time the same operations have no value (`static_eval_failed`). Debug symbols (`-d`) are independent of the mode: `-m none -d` is what other compilers call a debug build.

### C functions

A function declared without a body is a C function, linked from the files listed after the source or from libraries (`-lc` for the C library). Its values cross as C passes them on this machine (aarch64 or x86-64): ints, floats, `bool` and pointers as themselves, records by value in registers or as a copy in memory, a runtime-length array (`&[]u8`) as the address of its first element, and a static function value as a C function pointer. A C function declared with several parameter lists is variadic (`printf`): the parameters all lists share are fixed, the others get C's promotions.

```mond
fun printf = (&u8 format, i64 number) -> i32;
fun printf = (&u8 format, &u8 text) -> i32;
fun qsort = (*u8 items, u64 count, u64 size, (&u8, &u8) -> i32 compare);
```

### Without the C library

Without `-lc` nothing is linked that the program doesn't name. On Linux the executable is static: the kernel jumps to `_start`, which passes the arguments to `$main` and ends the process with its result through a system call, and mond adds the few C functions its code calls itself (`memcpy`, `memset`, `memmove`, `memcmp`, `strcmp`). On macOS every program is started by dyld, which needs libSystem, so that is linked and `_start` is called like `main`.

### Building mond

`build.zig` asks `llvm-config` where LLVM is (LLVM 19 or newer). It takes the first one in `PATH`, or else where Homebrew, Debian and Fedora install it. `-Dllvm-config=/path/to/llvm-config` picks one. lld's headers and libraries are looked for next to LLVM and in Homebrew's `opt/lld`, or `-Dlld-prefix=..`. On Linux, `-Dcrt-dir=..` names where `Scrt1.o` and libc are if they aren't found. `-Doptimize=Debug` builds mond with stack traces for compiler bugs. The language server and the example tests don't need LLVM.

## Tests

Every `.mn` file under `examples/` and every ```` ```mond ```` block in `docs/` must report exactly the diagnostics it marks and pass its checks. A doc block without `$main` gets an empty one appended.

| comment | checks |
|---|---|
| `#! code ..` | this line reports these diagnostics |
| `#= name value` | the static value of `name`, declared on this line |
| `#: name type` | the type of `name` |
| `#> text` | (backend tests) the next line the program prints |
| `#+ arguments` | (backend tests) what the program is built with instead of `-lc lib/clib.c` |
| `#? exit N` | (backend tests) the exit code, else `0` |
| `#? trap` | (backend tests) a runtime check stops the program, in the modes that keep the checks |
| `#? args a b` | (backend tests) the arguments the program is run with |

These markers count anywhere in a comment. Values print as they are stored: a variant as `+(..).Case[payload]`, a computed `[]u8` as numbers, a string literal as text. Files in `examples/negative/` must mark at least one diagnostic. The docs must name every keyword, tree kind and diagnostic in backticks, so a new feature fails the tests until it is documented.

The programs in `examples/backend/` are built and run after that, in the modes `none`, `safe`, `default`, `aggressive` and `minsize`: each must print exactly its `#> text` lines, in order, and end as its `#?` lines say. A `#? trap` program is run only in the modes that keep the checks; in the others its failing check is undefined behavior, so it is only built. `examples/backend/lib/raw.mn` writes unbuffered through `$syscall`, for programs that trap (C's buffered output would be lost) or are built without the C library. `examples/backend/lib/out.mn` gives them output through the C library: each is built with `-lc examples/backend/lib/clib.c`, or with the arguments after its `#+` marker (files relative to `examples/backend`).

## Editor

`mond-lsp` provides highlighting, diagnostics, go to definition, references, outline, hover and completion (also for `ast.` kinds and `$` views). Setup is described in `lsp/vscode/README.md` and `lsp/vim/README.md`.

A file that another file includes isn't asked for a `$main`.

## Diagnostics

Lexing and parsing stop at the first error (a `LexingError` like `InvalidPunctuator`, or `Expected*`, `Illegal*`, `NoRuleFound`), and then nothing is resolved, so a test file with a parse error reports only that error. Resolving reports everything it finds. Only `redundant_match_arm` is a warning; everything else is an error.

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
| `crash` | a `$crash` was checked or evaluated, with its text |
| `stcwhere_violated` | a `stcwhere` condition is false |
| `redundant_stc` | a `stc..` form where everything is static already |
| `genexpr_index` | a range used as an index |
| `generic_member` | a template-dependent member of an unopened template value |
| `missing_ret` / `redundant_ret` | a path doesn't return / `ret` before a template's definition |
| `redundant_fun` | `fun` on a predefined name (`$main`, `$init`, ...) |
| `unrealized_template` | a template where a concrete type is needed |
| `trait_outside_parameter` | a trait type is used other than as a parameter type or behind a pointer |
| `unstorable_dereference` | a pointer to a trait, a template or a runtime-length array is used as what it points to: dereferenced, called through, or indexed directly instead of through `.*` |
| `impure_stcfun` | a `stcfun` writes state outside itself |
| `escaping_closure` | a closure, or a value that may hold one, outlives its frame (returned, stored outside it, given to C) |
| `brk_outside_loop` / `cont_outside_loop` | a jump outside a loop |
| `ret_type_mismatch` | `ret` disagrees with the result type |
| `non_exhaustive_match` | some value matches no arm |
| `redundant_match_arm` | (warning) an arm can never be reached first |
| `assign_to_immutable` | a write to something not `mut` |
| `write_through_immutable_pointer` | a write through `&T` |
| `use_before_initialization` | a read before every path wrote it |
| `destructure_type_conflict` | the names of a multi-assignment need different types |
| `missing_main` | there is no `$main` |
| `invalid_main` | `$main` has another signature than `()` or `(argc, &&u8 argv)`, or another result than nothing, an integer or `never` |
| `stray_unquote` | `@` outside a quote |
| `frozen_declaration` | a write to a declaration that is already resolved, or a write outside a splice |
| `asterr` | a macro called `$asterr` |
| `include_failed` | the file can't be read, lexed or parsed |
| `endless_expansion` | more than 64 expansion passes |
