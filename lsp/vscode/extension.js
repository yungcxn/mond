// a language client without dependencies: runs mond-lsp and speaks the language server protocol with it
const vscode = require('vscode')
const path = require('path')
const { spawn } = require('child_process')

let stop = () => {}

exports.activate = (context) => {
  const server = spawn(path.join(context.extensionPath, 'mond-lsp'))
  const log = vscode.window.createOutputChannel('mond')
  const diagnostics = vscode.languages.createDiagnosticCollection('mond')
  const pending = new Map()
  let id = 0
  let input = Buffer.alloc(0)

  const send = (msg) => {
    const body = Buffer.from(JSON.stringify({ jsonrpc: '2.0', ...msg }))
    server.stdin.write(Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`), body]))
  }
  const request = (method, params) => new Promise((resolve) => {
    pending.set(++id, resolve)
    send({ id, method, params })
  })
  const notify = (method, params) => send({ method, params })

  const range = (r) => new vscode.Range(r.start.line, r.start.character, r.end.line, r.end.character)
  // lsp severities count from error = 1, vscode ones from error = 0
  const diagnostic = (d) => Object.assign(new vscode.Diagnostic(range(d.range), d.message, d.severity - 1), { source: d.source })

  const receive = (msg) => {
    if (pending.has(msg.id)) {
      pending.get(msg.id)(msg.result)
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
  server.stdin.on('error', (e) => log.appendLine(e.message))
  server.on('error', (e) => vscode.window.showErrorMessage(`mond-lsp did not start (${e.message}), run \`zig build lsp\``))
  server.on('exit', (code) => log.appendLine(`mond-lsp exited with ${code}`))

  const mond = (doc) => doc.languageId === 'mond'
  const uri = (doc) => ({ uri: doc.uri.toString() })
  const open = (doc) => mond(doc) && notify('textDocument/didOpen', { textDocument: { ...uri(doc), languageId: 'mond', version: doc.version, text: doc.getText() } })

  request('initialize', { processId: process.pid, rootUri: null, capabilities: {} }).then(({ capabilities }) => {
    notify('initialized', {})
    const { legend } = capabilities.semanticTokensProvider
    const tokens = (doc) => request('textDocument/semanticTokens/full', { textDocument: uri(doc) }).then((r) => new vscode.SemanticTokens(new Uint32Array(r.data)))
    context.subscriptions.push(vscode.languages.registerDocumentSemanticTokensProvider({ language: 'mond' }, { provideDocumentSemanticTokens: tokens }, new vscode.SemanticTokensLegend(legend.tokenTypes, legend.tokenModifiers)))
  })
  vscode.workspace.textDocuments.forEach(open)
  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument(open),
    // the server asks for full sync: every change sends the whole text
    vscode.workspace.onDidChangeTextDocument(({ document: doc, contentChanges }) => mond(doc) && contentChanges.length && notify('textDocument/didChange', { textDocument: { ...uri(doc), version: doc.version }, contentChanges: [{ text: doc.getText() }] })),
    vscode.workspace.onDidCloseTextDocument((doc) => mond(doc) && notify('textDocument/didClose', { textDocument: uri(doc) })),
    diagnostics,
    log,
  )
  stop = () => request('shutdown').then(() => notify('exit'))
}

exports.deactivate = () => stop()
