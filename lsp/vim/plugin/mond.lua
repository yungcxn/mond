vim.lsp.enable('mond')
-- the values of `stc` variables show at the end of their lines (inlay hints)
vim.api.nvim_create_autocmd('LspAttach', {
  callback = function(args)
    local client = vim.lsp.get_client_by_id(args.data.client_id)
    if client and client.name == 'mond' then vim.lsp.inlay_hint.enable(true, { bufnr = args.buf }) end
  end,
})
-- `:MondExpansions [pass]`: the program before and after a macro pass (the last one when none is
-- given) side by side, a diff of what the pass expanded and wrote
vim.api.nvim_create_user_command('MondExpansions', function(command)
  local client = vim.lsp.get_clients({ bufnr = 0, name = 'mond' })[1]
  if not client then return vim.notify('mond: no language server here', vim.log.levels.WARN) end
  local params = { textDocument = vim.lsp.util.make_text_document_params(0) }
  local response = client:request_sync('mond/expansions', params, 10000, 0)
  local passes = response and response.result or {}
  if #passes == 0 then return vim.notify('mond: no macro expands anything here') end
  local pass = tonumber(command.args) or #passes - 1
  if pass < 1 or pass >= #passes then
    return vim.notify(('mond: the passes are 1 to %d'):format(#passes - 1), vim.log.levels.WARN)
  end
  local name = vim.fn.expand('%:t')
  vim.cmd('tabnew')
  for side, step in ipairs({ pass - 1, pass }) do
    if side == 2 then vim.cmd('rightbelow vnew') end
    local buffer = vim.api.nvim_get_current_buf()
    vim.api.nvim_buf_set_lines(buffer, 0, -1, false, vim.split(passes[step + 1], '\n', { trimempty = true }))
    vim.api.nvim_buf_set_name(buffer, ('%s, %s'):format(name, step == 0 and 'source' or 'pass ' .. step))
    vim.bo[buffer].buftype, vim.bo[buffer].bufhidden, vim.bo[buffer].modifiable = 'nofile', 'wipe', false
    vim.cmd('diffthis')
  end
end, { nargs = '?', desc = 'the program before and after a mond macro pass' })
