# vim

This folder is a plugin for neovim (0.11+, its own client) and vim (9, through [yegappan/lsp](https://github.com/yegappan/lsp)).

1. `zig build lsp` (puts `mond-lsp` here)
2. load the folder as a package:

```sh
mkdir -p ~/.local/share/nvim/site/pack/mond/start && ln -s "$PWD/lsp/vim" ~/.local/share/nvim/site/pack/mond/start/mond   # neovim
mkdir -p ~/.vim/pack/mond/start && ln -s "$PWD/lsp/vim" ~/.vim/pack/mond/start/mond                                        # vim
```

Vim also needs semantic highlighting turned on in yegappan/lsp (it is off by default):

```vim
autocmd User LspSetup call LspOptionsSet(#{semanticHighlight: v:true})
```

Neovim: `:checkhealth vim.lsp` shows the server, `:LspRestart` after changing `lsp/` itself.
Its defaults do the rest: `<C-]>` and ctrl-click go to the definition, `grr` lists references, `gO` the outline, `K` hovers.

Vim: `:LspGotoDefinition`, `:LspShowReferences`, `:LspDocumentSymbol`, `:LspHover`, ctrl-click with `setlocal tagfunc=lsp#lsp#TagFunc`.
