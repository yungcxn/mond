# lsp

The mond language server and its editor plugins: highlighting (semantic tokens), diagnostics, go to definition, references, outline and hover, straight from the compiler.
`zig build lsp` builds `mond-lsp` into `vscode/` and `vim/`, each folder's readme says how to install it.

- `main.zig`: `mond-lsp` serves the editor, `mond-lsp analyze` is its worker
- `Server.zig`: json-rpc on stdio, the open documents, one worker per analysis
- `Analysis.zig`: the worker, runs the compiler on a source and turns its tokens, resolved names and diagnostics into lsp results
- the compiler comes in as the module `mond` (`src/main.zig`)

The compiler runs in the worker process, so a crash or a hang (killed after 5s) of the w.i.p. compiler shows up as a diagnostic and the server lives on.
Changes are analyzed once the editor is quiet or asks something, a burst of keystrokes is one analysis.
Every name links to the token that declares it: a field or case to the one within its type's declaration, a named argument to the parameter or field it sets.

Nothing here lists the language: tokens are colored by their kind's name in the lexer (`kw_`, `xpct_`, `val_`), names by the kind of declaration the resolver binds them to.
New keywords, operators or declaration kinds need no change in `lsp/`.
The worker is spawned from the server's binary on disk, so after `zig build lsp` the next edit already runs the new compiler, only changes to `lsp/` itself need a server restart.
