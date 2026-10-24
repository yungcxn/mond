# vscode

This folder is the extension, no npm and no dependencies: `extension.js` speaks the protocol with `mond-lsp` itself.

1. `zig build lsp` (puts `mond-lsp` here, and one per platform)
2. link the folder into the extensions, a running vscode picks it up on its own:

```sh
ln -s "$PWD/lsp/vscode" ~/.vscode-server/extensions/mond.mond-0.0.1   # vscode connected to wsl / ssh
ln -s "$PWD/lsp/vscode" ~/.vscode/extensions/mond.mond-0.0.1          # local vscode
```

Installed locally, the extension runs on this machine also in a window connected to wsl / ssh (its documents' paths are taken as paths here, a folder shared under the same path resolves `include`), else on the remote host.
`mond: Step Through Macro Expansions` (command palette) shows the program before and after a macro pass side by side, hovering a splice shows what each pass expanded it to.
Server output (and compiler panics) is in the `mond` output channel.
After changing `lsp/` itself: `Developer: Restart Extension Host`.
