" vim has no language client of its own, this registers mond-lsp with yegappan/lsp, neovim reads lsp/mond.lua
if has('nvim')
  finish
endif

" the server of the machine vim runs on (`zig build lsp` builds one per platform), else the one built here
let s:dir = expand('<sfile>:p:h:h')
let s:os = get({'Darwin': 'macos', 'Linux': 'linux'}, trim(system('uname -s')), '')
let s:server = s:dir .. '/mond-lsp-' .. s:os .. '-' .. substitute(trim(system('uname -m')), '^arm64$', 'aarch64', '')
if !executable(s:server)
  let s:server = s:dir .. '/mond-lsp'
endif
autocmd User LspSetup call LspAddServer([#{name: 'mond', filetype: ['mond'], path: s:server, args: []}])
