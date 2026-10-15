# mond

multi-purpose system programming language with functional and oop concepts

w.i.p.

The [docs](docs/README.md) are always in sync with the compiler source and its feature set: their code is compiled by `zig build test`.

## Philosophy

1. Ideally, features should be used by intuition rather than introducing "cool toy semantics" that are unsatisfying to use for experienced users of other common programming languages. 
2. Expressiveness is something I miss all the time. Short notations are nice.
3. FP does a lot of things well, especially metaprogramming.

## Roadmap:

1. DONE: Build a basic compiler that transpiles into as-primitive-as-possible C
2. DONE: Replace the backend with a custom IR
3. DONE: Add LLVM as Backend and finally compile working executables
4. Self-hosting
