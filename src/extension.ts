import * as vscode from "vscode";
import * as path from "path";
import { LanguageClient, ServerOptions, LanguageClientOptions } from "vscode-languageclient/node";

let client: LanguageClient;

export function activate(context: vscode.ExtensionContext) {
    const pythonPath = context.asAbsolutePath(path.join(".venv", "Scripts", "python.exe"));

    const serverModule = context.asAbsolutePath(path.join("proofsrc", "lsp_server.py"));

    const serverOptions: ServerOptions = {
        command: pythonPath,
        args: [serverModule],
    };

    const clientOptions: LanguageClientOptions = {
        documentSelector: [{ scheme: "file", language: "proof" }],
    };

    client = new LanguageClient("proofLSP", "Proof Language Server", serverOptions, clientOptions);

    console.log("Proof LSP Client starting...");
    client.start();

    const previewCommand = vscode.commands.registerCommand("dsl-proof.showPreview", () => {
        const panel = vscode.window.createWebviewPanel(
            "proofPreview",
            "Proof Preview",
            vscode.ViewColumn.Two,
            { enableScripts: true }
        );
        panel.webview.html = "webview test message";
    });

    context.subscriptions.push(previewCommand);
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) return undefined;
    return client.stop();
}
