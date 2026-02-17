import * as vscode from "vscode";
import * as path from "path";
import { LanguageClient, ServerOptions, LanguageClientOptions } from "vscode-languageclient/node";

interface PreviewResponse {
    html: string;
}

let client: LanguageClient;

class ProofViewProvider implements vscode.WebviewViewProvider {
    public static readonly viewType = 'proof-view';
    private _view?: vscode.WebviewView;

    constructor(private readonly _extensionUri: vscode.Uri) {}

    public resolveWebviewView(webviewView: vscode.WebviewView) {
        this._view = webviewView;

        webviewView.webview.options = {
            enableScripts: true,
            localResourceRoots: [this._extensionUri]
        };
    }

    public updateHtml(html: string) {
        if (this._view) {
            this._view.webview.html = html;
        }
    }
}

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

    vscode.window.onDidChangeTextEditorSelection((e) => {
        client.sendNotification("proof/moveCursor", {
            uri: e.textEditor.document.uri.toString(),
            position: e.textEditor.selection.active
        });
    });

    const provider = new ProofViewProvider(context.extensionUri);

    context.subscriptions.push(
        vscode.window.registerWebviewViewProvider(ProofViewProvider.viewType, provider)
    );

    client.onNotification("proof/updatePanel", (html: string) => {
        provider.updateHtml(html);
    });
}

export function deactivate(): Thenable<void> | undefined {
    if (!client) { return undefined; }
    return client.stop();
}
