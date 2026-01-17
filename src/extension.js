const vscode = require("vscode");
const path = require("path");
const { LanguageClient } = require("vscode-languageclient/node");

let client;

/** @param {vscode.ExtensionContext} context */
function activate(context) {
    const pythonPath = context.asAbsolutePath(path.join(".venv", "Scripts", "python.exe"));

    const serverModule = context.asAbsolutePath(path.join("proofsrc", "lsp_server.py"));

    const serverOptions = {
        command: pythonPath,
        args: [serverModule],
    };

    const clientOptions = {
        documentSelector: [{ scheme: "file", language: "proof" }],
    };

    client = new LanguageClient("proofLSP", "Proof Language Server", serverOptions, clientOptions);

    console.log("Proof LSP Client starting...");
    client.start();
}

function deactivate() {
    if (!client) return undefined;
    return client.stop();
}

module.exports = { activate, deactivate };
