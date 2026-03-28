from pygls.lsp.server import LanguageServer
from pygls import uris
from lsprotocol import types as lsp
import threading

from analyzer import Analyzer, CursorState, TokenType

class ProofLanguageServer(LanguageServer):
    def __init__(self):
        super().__init__("proof-server", "v0.1") # type: ignore[reportUnknownMemberType]
        self.analyzer = Analyzer()
        self.analysis_timer: threading.Timer | None = None
        self.cancel_analysis = threading.Event()
        self.current_cursor: CursorState | None = None

    def run_analysis(self, uri: str):
        path = uris.to_fs_path(uri)
        if path is None:
            return
        self.cancel_analysis.clear()
        final_diagnostics = self.analyzer.analyze(path, self.get_editor_files(), self.cancel_analysis)
        for uri, diags in final_diagnostics.items():
            self.text_document_publish_diagnostics(
                lsp.PublishDiagnosticsParams(uri=uri, diagnostics=diags)
            )
        self.analysis_timer = None
        self.protocol.send_request("workspace/semanticTokens/refresh")
        self.update_panel()

    def get_editor_files(self) -> dict[str, str]:
        editor_files: dict[str, str] = {}
        for uri, doc in self.workspace.text_documents.items():
            path = uris.to_fs_path(uri)
            if path is None:
                continue
            editor_files[path] = doc.source
        return editor_files

    def did_change(self, params: lsp.DidChangeTextDocumentParams) -> None:
        if self.analysis_timer is not None:
            self.analysis_timer.cancel()
        self.cancel_analysis.set()
        self.analysis_timer = threading.Timer(0.5, self.run_analysis, args=[params.text_document.uri])
        self.analysis_timer.start()

    def get_completion(self, params: lsp.CompletionParams) -> list[lsp.CompletionItem]:
        return self.analyzer.get_completion(params, self.workspace.get_text_document(params.text_document.uri).source)

    def update_panel(self) -> None:
        self.protocol.notify("proof/updatePanel", self.analyzer.get_proofinfo(self.current_cursor))

server = ProofLanguageServer()

@server.feature(lsp.INITIALIZE)
def lsp_initialize(ls: ProofLanguageServer, params: lsp.InitializeParams) -> None:
    ls.window_show_message(
        lsp.ShowMessageParams(
            type=lsp.MessageType.Info,
            message=f"Start server: {ls.name} {ls.version}"
        )
    )

@server.feature(lsp.TEXT_DOCUMENT_DID_OPEN)
def did_open(ls: ProofLanguageServer, params: lsp.DidOpenTextDocumentParams) -> None:
    ls.run_analysis(params.text_document.uri)

@server.feature(lsp.TEXT_DOCUMENT_DID_SAVE)
def did_save(ls: ProofLanguageServer, params: lsp.DidSaveTextDocumentParams) -> None:
    ls.run_analysis(params.text_document.uri)

@server.feature(lsp.TEXT_DOCUMENT_DEFINITION)
def lsp_definition(ls: ProofLanguageServer, params: lsp.DefinitionParams) -> lsp.Location | None:
    return ls.analyzer.get_definition(params)

@server.feature(lsp.TEXT_DOCUMENT_COMPLETION)
def lsp_completion(ls: ProofLanguageServer, params: lsp.CompletionParams):
    items = ls.get_completion(params)
    return lsp.CompletionList(is_incomplete=False, items=items)

@server.feature(lsp.TEXT_DOCUMENT_DID_CHANGE)
def did_change(ls: ProofLanguageServer, params: lsp.DidChangeTextDocumentParams) -> None:
    ls.did_change(params)

@server.feature(lsp.TEXT_DOCUMENT_HOVER)
def hovers(ls: ProofLanguageServer, params: lsp.HoverParams) -> lsp.Hover | None:
    return ls.analyzer.hovers(params)

@server.feature(lsp.TEXT_DOCUMENT_REFERENCES)
def lsp_references(ls: ProofLanguageServer, params: lsp.ReferenceParams) -> list[lsp.Location]:
    return ls.analyzer.get_references(params)

@server.feature("proof/moveCursor")
def move_cursor(ls: ProofLanguageServer, params: CursorState) -> None:
    ls.current_cursor = params
    if ls.analysis_timer is not None:
        return
    ls.update_panel()

SEMANTIC_LEGEND = lsp.SemanticTokensLegend(
    token_types=[t.name.lower() for t in TokenType],
    token_modifiers=[]
)

@server.feature(
    lsp.TEXT_DOCUMENT_SEMANTIC_TOKENS_FULL,
    lsp.SemanticTokensRegistrationOptions(
        legend=SEMANTIC_LEGEND,
        full=True
    )
)
def semantic_tokens_full(ls: ProofLanguageServer, params: lsp.SemanticTokensParams) -> lsp.SemanticTokens:
    return ls.analyzer.semantic_tokens_full(params)

if __name__ == "__main__":
    server.start_io()
