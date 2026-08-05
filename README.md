# mond

multi-purpose system programming language with functional and oop concepts

w.i.p.

## Philosophy

I really love Zig, and would define some of the philosophic ideas of this language with regards to Zig features, as it's a bit near to my goals: 

1. Ideally, features should be used by intuition rather than introducing "cool toy semantics" that are unsatisfying to use for experienced users of other common programming languages. 
2. Feature spectrum should not be huge to disallow hundred equally-adequate solutions to a problem solvable through 1-3 good ways.
3. What can be done in compile-time should be done in compile-time -> compile-time templates (for functions and types) and -control-flow must supported.  
4. Type construction does not need to be complex -> no complex type construction like in Zig.
5. force good code practices by error -> force constants, force dead code removal...
6. Types are nice, type inference is ugly (in most cases).
7. Zig's "`anytype`" arguments provoke laziness (probably use 1-2 types on that parameter at max.) and abuse (use some unsupported, unchecked type) -> functions should be always fully typed (but templates are supported)
8. Zig's "`anytype`" does not allow Java's excellent type restrictions/boundaries -> support structure polymorphism and interfaces/traits in a Zig/Rust and not C++/Java way.
9. structures are *just structures* and not file imports, namespaces for functions etc... 
10. Zig does not truly support closures and lambdas -> I want lambdas.
11. I like functional programming and concise notation for control flow -> Also sprinkle a bit "FP" in here.

## Roadmap:

1. Build a basic compiler that transpiles into as-primitive-as-possible C
2. Replace the backend with true x86 code gen
3. ?
