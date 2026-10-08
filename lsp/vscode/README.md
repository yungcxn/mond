# vscode

This folder is the extension, no npm and no dependencies: `extension.js` speaks the protocol with `mond-lsp` itself.

1. `zig build lsp` (puts `mond-lsp` here)
2. link the folder into the extensions, a running vscode picks it up on its own:

```sh
ln -s "$PWD/lsp/vscode" ~/.vscode-server/extensions/mond.mond-0.0.1   # vscode connected to wsl / ssh
ln -s "$PWD/lsp/vscode" ~/.vscode/extensions/mond.mond-0.0.1          # local vscode
```

Server output (and compiler panics) is in the `mond` output channel.
After changing `lsp/` itself: `Developer: Restart Extension Host`.
