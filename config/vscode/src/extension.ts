import * as vscode from "vscode";
import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from "vscode-languageclient/node";

let client: LanguageClient | undefined;

export function activate(context: vscode.ExtensionContext): void {
  const config = vscode.workspace.getConfiguration("hsharp");
  const serverPath = config.get<string>("serverPath", "hsharp-lsp");

  const serverOptions: ServerOptions = {
    run: { command: serverPath, transport: TransportKind.stdio },
    debug: { command: serverPath, transport: TransportKind.stdio },
  };

  const clientOptions: LanguageClientOptions = {
    // Only .h# files activate/attach to the server — matches the
    // `onLanguage:hsharp` activation event in package.json and the
    // `hsharp` language ID's `.h#` file association.
    documentSelector: [{ scheme: "file", language: "hsharp" }],
    outputChannelName: "H#",
    traceOutputChannel: vscode.window.createOutputChannel("H# LSP Trace"),
  };

  client = new LanguageClient(
    "hsharp",
    "H# Language Server",
    serverOptions,
    clientOptions
  );

  // `client.start()` handles spawning the process and the initialize
  // handshake; if `serverPath` isn't found on $PATH, this rejects and VS
  // Code surfaces a real error notification to the user (not a silent
  // failure) — see the catch below, which turns that into a more
  // actionable message than the raw ENOENT.
  client.start().catch((err: unknown) => {
    vscode.window.showErrorMessage(
      `H#: couldn't start hsharp-lsp ('${serverPath}'). ` +
        `Make sure it's built and on your $PATH (see source-code/lsp/README.md), ` +
        `or set "hsharp.serverPath" to its full path in settings. (${String(err)})`
    );
  });

  context.subscriptions.push({
    dispose: () => {
      void client?.stop();
    },
  });
}

export function deactivate(): Thenable<void> | undefined {
  return client?.stop();
}
