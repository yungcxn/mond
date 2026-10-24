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

" `:MondExpansions [pass]`: the program before and after a macro pass (the last one when none is
" given) side by side, as the server's worker analyzes the buffer
function! s:expansions(pass) abort
  let l:command = shellescape(s:server) .. ' analyze ' .. shellescape(expand('%:p'))
  let l:answer = system(l:command, getline(1, '$'))
  let l:passes = v:shell_error ? [] : get(json_decode(l:answer), 'passes', [])
  if empty(l:passes)
    echomsg 'mond: no macro expands anything here'
    return
  endif
  let l:pass = empty(a:pass) ? len(l:passes) - 1 : str2nr(a:pass)
  if l:pass < 1 || l:pass >= len(l:passes)
    echomsg printf('mond: the passes are 1 to %d', len(l:passes) - 1)
    return
  endif
  let l:name = expand('%:t')
  tabnew
  for l:step in [l:pass - 1, l:pass]
    if l:step == l:pass
      rightbelow vnew
    endif
    call setline(1, split(l:passes[l:step], "\n"))
    setlocal buftype=nofile bufhidden=wipe noswapfile nomodifiable
    execute 'file' fnameescape(printf('%s, %s', l:name, l:step == 0 ? 'source' : 'pass ' .. l:step))
    diffthis
  endfor
endfunction
command! -nargs=? MondExpansions call s:expansions(<q-args>)
