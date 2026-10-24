// a language client without dependencies: runs mond-lsp and speaks the language server protocol with it
const vscode = require('vscode')
const path = require('path')
const fs = require('fs')
const { spawn } = require('child_process')

let stop = () => {}

exports.activate = (context) => {
  // the server of the machine the extension runs on (`zig build lsp` builds one per platform), else the one built here
  const os = { darwin: 'macos', win32: 'windows' }[process.platform] ?? process.platform
  const arch = { arm64: 'aarch64', x64: 'x86_64' }[process.arch] ?? process.arch
  const exe = [`mond-lsp-${os}-${arch}`, 'mond-lsp'].map((n) => path.join(context.extensionPath, n)).find((p) => fs.existsSync(p))
  const server = spawn(exe ?? path.join(context.extensionPath, 'mond-lsp'))
  const log = vscode.window.createOutputChannel('mond')
  const diagnostics = vscode.languages.createDiagnosticCollection('mond')
  const pending = new Map()
  let id = 0
  let input = Buffer.alloc(0)
  let alive = true

  const send = (msg) => {
    const body = Buffer.from(JSON.stringify({ jsonrpc: '2.0', ...msg }))
    if (alive) server.stdin.write(Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`), body]))
  }
  // a failed request or a gone server answers null
  const request = (method, params) => new Promise((resolve) => {
    if (!alive) return resolve(null)
    pending.set(++id, resolve)
    send({ id, method, params })
  })
  const notify = (method, params) => send({ method, params })

  const range = (r) => new vscode.Range(r.start.line, r.start.character, r.end.line, r.end.character)
  const location = (l) => new vscode.Location(vscode.Uri.parse(l.uri), range(l.range))
  // lsp symbol kinds count from file = 1, vscode ones from file = 0
  const symbol = (s) => Object.assign(new vscode.DocumentSymbol(s.name, s.detail, s.kind - 1, range(s.range), range(s.selectionRange)), { children: s.children.map(symbol) })
  // lsp severities count from error = 1, vscode ones from error = 0
  const diagnostic = (d) => Object.assign(new vscode.Diagnostic(range(d.range), d.message, d.severity - 1), { source: d.source })
  const hint = (h) => Object.assign(new vscode.InlayHint(new vscode.Position(h.position.line, h.position.character), h.label), { paddingLeft: h.paddingLeft })
  // lsp completion kinds count from text = 1, vscode ones from text = 0
  const completion = (c) => Object.assign(new vscode.CompletionItem(c.label, c.kind - 1), { detail: c.detail, documentation: c.documentation, range: range(c.textEdit.range), insertText: c.textEdit.newText })

  const receive = (msg) => {
    if (pending.has(msg.id)) {
      pending.get(msg.id)(msg.result ?? null)
      pending.delete(msg.id)
    } else if (msg.method === 'textDocument/publishDiagnostics') {
      diagnostics.set(vscode.Uri.parse(msg.params.uri), msg.params.diagnostics.map(diagnostic))
    }
  }

  // messages are a `Content-Length` header and that many bytes of json
  server.stdout.on('data', (chunk) => {
    input = Buffer.concat([input, chunk])
    for (let end; (end = input.indexOf('\r\n\r\n')) >= 0;) {
      const len = Number(/content-length: *(\d+)/i.exec(input.subarray(0, end))[1])
      if (input.length < end + 4 + len) return
      receive(JSON.parse(input.subarray(end + 4, end + 4 + len)))
      input = input.subarray(end + 4 + len)
    }
  })
  server.stderr.on('data', (chunk) => log.append(chunk.toString()))
  const gone = () => {
    alive = false
    pending.forEach((resolve) => resolve(null))
    pending.clear()
  }
  server.stdin.on('error', (e) => log.appendLine(e.message))
  server.on('error', (e) => {
    gone()
    vscode.window.showErrorMessage(`mond-lsp did not start (${e.message}), run \`zig build lsp\``)
  })
  server.on('exit', (code, signal) => {
    gone()
    log.appendLine(`mond-lsp exited with ${signal ?? code}`)
    if (code !== 0) vscode.window.showErrorMessage('mond-lsp stopped, see the mond output')
  })

  // the steps of a macro expansion are shown, not analyzed
  const mond = (doc) => doc.languageId === 'mond' && doc.uri.scheme !== 'mond-pass'
  const uri = (doc) => ({ uri: doc.uri.toString() })
  const open = (doc) => mond(doc) && notify('textDocument/didOpen', { textDocument: { ...uri(doc), languageId: 'mond', version: doc.version, text: doc.getText() } })

  // documents go to the server once it answered `initialize`
  request('initialize', { processId: process.pid, rootUri: null, capabilities: {} }).then((r) => {
    if (!r) return
    notify('initialized', {})
    const { legend } = r.capabilities.semanticTokensProvider
    const tokens = (doc) => request('textDocument/semanticTokens/full', { textDocument: uri(doc) }).then((t) => t && new vscode.SemanticTokens(new Uint32Array(t.data)))
    const at = (doc, p) => ({ textDocument: uri(doc), position: { line: p.line, character: p.character } })
    const mn = { language: 'mond' }
    vscode.workspace.textDocuments.forEach(open)
    context.subscriptions.push(
      vscode.languages.registerDocumentSemanticTokensProvider(mn, { provideDocumentSemanticTokens: tokens }, new vscode.SemanticTokensLegend(legend.tokenTypes, legend.tokenModifiers)),
      vscode.languages.registerDefinitionProvider(mn, { provideDefinition: (doc, p) => request('textDocument/definition', at(doc, p)).then((l) => l && location(l)) }),
      vscode.languages.registerReferenceProvider(mn, { provideReferences: (doc, p, { includeDeclaration }) => request('textDocument/references', { ...at(doc, p), context: { includeDeclaration } }).then((ls) => ls && ls.map(location)) }),
      vscode.languages.registerDocumentSymbolProvider(mn, { provideDocumentSymbols: (doc) => request('textDocument/documentSymbol', { textDocument: uri(doc) }).then((ss) => ss && ss.map(symbol)) }),
      vscode.languages.registerHoverProvider(mn, { provideHover: (doc, p) => request('textDocument/hover', at(doc, p)).then((h) => h && new vscode.Hover(new vscode.MarkdownString(h.contents.value), range(h.range))) }),
      vscode.languages.registerCompletionItemProvider(mn, { provideCompletionItems: (doc, p) => request('textDocument/completion', at(doc, p)).then((cs) => cs && cs.map(completion)) }, ...r.capabilities.completionProvider.triggerCharacters),
      // the values of `stc` variables at the end of their lines, as `#=` checks read them
      vscode.languages.registerInlayHintsProvider(mn, { provideInlayHints: (doc, r) => request('textDocument/inlayHint', { textDocument: uri(doc), range: { start: { line: r.start.line, character: r.start.character }, end: { line: r.end.line, character: r.end.character } } }).then((hs) => hs && hs.map(hint)) }),
      vscode.workspace.onDidOpenTextDocument(open),
      // the server asks for full sync: every change sends the whole text
      vscode.workspace.onDidChangeTextDocument(({ document: doc, contentChanges }) => mond(doc) && contentChanges.length && notify('textDocument/didChange', { textDocument: { ...uri(doc), version: doc.version }, contentChanges: [{ text: doc.getText() }] })),
      vscode.workspace.onDidCloseTextDocument((doc) => mond(doc) && notify('textDocument/didClose', { textDocument: uri(doc) })),
    )
  })
  // the program before and after a macro pass side by side, as `mond-pass:/file.mn?<request>.<pass>`
  const steps = new Map()
  const step = (u) => {
    const [request, pass] = u.query.split('.').map(Number)
    return steps.get(request)?.[pass] ?? ''
  }
  const expansions = async () => {
    const doc = vscode.window.activeTextEditor?.document
    if (!doc || !mond(doc)) return
    const passes = await request('mond/expansions', { textDocument: uri(doc) })
    if (!passes?.length) return vscode.window.showInformationMessage('mond: no macro expands anything here')
    const picks = passes.slice(1).map((_, i) => ({ label: `pass ${i + 1}`, pass: i + 1 }))
    const picked = await vscode.window.showQuickPick(picks.reverse(), { placeHolder: 'the program before and after a macro pass' })
    if (!picked) return
    steps.set(steps.size, passes)
    const name = path.basename(doc.uri.path)
    const at = (pass) => vscode.Uri.from({ scheme: 'mond-pass', path: `/${name}`, query: `${steps.size - 1}.${pass}` })
    const title = `${name}: ${picked.pass === 1 ? 'source' : `pass ${picked.pass - 1}`} ↔ pass ${picked.pass}`
    return vscode.commands.executeCommand('vscode.diff', at(picked.pass - 1), at(picked.pass), title)
  }
  context.subscriptions.push(
    diagnostics,
    log,
    vscode.workspace.registerTextDocumentContentProvider('mond-pass', { provideTextDocumentContent: step }),
    vscode.commands.registerCommand('mond.expansions', expansions),
  )
  stop = () => request('shutdown').then(() => notify('exit'))
}

exports.deactivate = () => stop()
