-- neovim's own client reads this config, mond-lsp sits next to the plugin: `zig build lsp` puts it there
local plugin = vim.fs.dirname(vim.fs.dirname(debug.getinfo(1, 'S').source:sub(2)))
-- the server of the machine neovim runs on (`zig build lsp` builds one per platform), else the one built here
local u = vim.uv.os_uname()
local sys = ({ Darwin = 'macos', Linux = 'linux' })[u.sysname] or u.sysname:lower()
local exe = plugin .. '/mond-lsp-' .. sys .. '-' .. (u.machine == 'arm64' and 'aarch64' or u.machine)

return {
  cmd = { vim.uv.fs_stat(exe) and exe or plugin .. '/mond-lsp' },
  filetypes = { 'mond' },
  root_markers = { '.git' },
}
