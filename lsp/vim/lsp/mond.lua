-- neovim's own client reads this config, mond-lsp sits next to the plugin: `zig build lsp` puts it there
local plugin = vim.fs.dirname(vim.fs.dirname(debug.getinfo(1, 'S').source:sub(2)))

return {
  cmd = { plugin .. '/mond-lsp' },
  filetypes = { 'mond' },
  root_markers = { '.git' },
}
