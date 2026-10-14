# lsp

The mond language server and its editor plugins: highlighting (semantic tokens), diagnostics, go to definition, references, outline, hover and completion, straight from the compiler.
`zig build lsp` builds `mond-lsp` into `vscode/` and `vim/`, and one per platform (`mond-lsp-linux-aarch64`, `mond-lsp-macos-aarch64`, ..): a plugin runs the one of the machine it runs on, so a folder shared with another machine (a vm, a remote host) works from both. Each folder's readme says how to install it.

- `main.zig`: `mond-lsp` serves the editor, `mond-lsp analyze` is its worker
- `Server.zig`: json-rpc on stdio, the open documents, one worker per analysis
- `Analysis.zig`: the worker, runs the compiler on a source and turns its tokens, resolved names and diagnostics into lsp results
- `includers.zig`: whether another file of the workspace (up to the nearest `.git` or `build.zig`) includes a file: such a library is shown without `missing_main`, compiling it on its own still reports it
- `Completion.zig`: what the editor offers after `x.`, `ast.` and `$`: the api of trees (views, children, kinds, builtins), by the types the last analysis that knew the names found
- the compiler comes in as the module `mond` (`src/main.zig`)

The compiler runs in the worker process, so a crash or a hang (killed after 5s) of the w.i.p. compiler shows up as a diagnostic and the server lives on.
Changes are analyzed once the editor is quiet or asks something, a burst of keystrokes is one analysis.
Every name links to the token that declares it: a field or case to the one within its type's declaration, a named argument to the parameter or field it sets.

Nothing here lists the language: tokens are colored by their kind's name in the lexer (`kw_`, `xpct_`, `val_`), names by the kind of declaration the resolver binds them to.
Macros are colored as written, not as expanded: only the meta syntax is a macro (`quote`, `refl`, the `<..>` of a splice, `@`, `@..`), what it holds is colored by its role (a tree held in a parameter is a parameter, a function making trees a function, views and children of trees are properties), so code that writes code reads like code; the VS Code extension shows macros in the `keyword.control` color, apart from the other keywords. Names a splice spelled and the code of stcfuns are colored by the pass that ran them (the last pass has no trace of them), names no pass resolved (a stcfun never run, the names of a quote) by the declaration the links find.
New keywords, operators or declaration kinds need no change in `lsp/`, neither do new node kinds or views of trees (`Macros.views`).
The worker is spawned from the server's binary on disk, so after `zig build lsp` the next edit already runs the new compiler, only changes to `lsp/` itself need a server restart.
