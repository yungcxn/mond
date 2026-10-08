" vim has no language client of its own, this registers mond-lsp with yegappan/lsp, neovim reads lsp/mond.lua
if has('nvim')
  finish
endif

let s:server = expand('<sfile>:p:h:h') .. '/mond-lsp'
autocmd User LspSetup call LspAddServer([#{name: 'mond', filetype: ['mond'], path: s:server, args: []}])
