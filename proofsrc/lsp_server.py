from pygls.lsp.server import LanguageServer
from pygls import uris
from lsprotocol import types as lsp
import os

from dependency import DependencyResolver
from ast_types import Context
from parser import Parser
from checker import Checker
from splitter import split

server = LanguageServer("proof-server", "v0.1")

@server.feature(lsp.INITIALIZE)
def lsp_initialize(ls: LanguageServer, params: lsp.InitializeParams) -> None:
    ls.window_show_message(
        lsp.ShowMessageParams(
            type=lsp.MessageType.Info,
            message=f"Start server: {ls.name} {ls.version}"
        )
    )

@server.feature(lsp.TEXT_DOCUMENT_DID_OPEN)
def did_open(ls: LanguageServer, params: lsp.DidOpenTextDocumentParams) -> None:
    ls.window_show_message(
        lsp.ShowMessageParams(
            type=lsp.MessageType.Info,
            message=f"Open file: {os.path.basename(params.text_document.uri)}"
        )
    )

@server.feature(lsp.TEXT_DOCUMENT_DID_SAVE)
def did_save(ls: LanguageServer, params: lsp.DidSaveTextDocumentParams) -> None:
    path = uris.to_fs_path(params.text_document.uri)
    if path is None:
        raise Exception(f"Cannot convert {params.text_document.uri} to path")

    ls.window_show_message(
        lsp.ShowMessageParams(
            type=lsp.MessageType.Info,
            message=f"Checking {os.path.basename(path)}..."
        )
    )

    resolver = DependencyResolver()
    resolver.resolve(path)
    resolved_files, tokens_cache = resolver.get_result()
    workspace = split(resolved_files, tokens_cache, resolver.source_cache)
    context = Context.init()
    for file in workspace.resolved_files:
        for unit in workspace.file_units[file]:
            working_context = context.copy()
            Parser(unit).parse_unit(working_context)
            if Checker(unit).check_unit(working_context):
                context = working_context
            unit.context = context.copy()

    final_diagnostics: dict[str, list[lsp.Diagnostic]] = {}
    for file in workspace.resolved_files:
        uri = uris.from_fs_path(file)
        if uri is None:
            continue
        final_diagnostics[uri] = []
        for unit in workspace.file_units[file]:
            final_diagnostics[uri].extend(unit.diagnostics)
    for uri, diags in resolver.diagnostics.items():
        if uri not in final_diagnostics:
            continue
        final_diagnostics[uri].extend(diags)

    ls.window_show_message(
        lsp.ShowMessageParams(
            type=lsp.MessageType.Info,
            message=f"{sum(len(v) for v in final_diagnostics.values())} errors"
        )
    )

    for uri, diags in final_diagnostics.items():
        ls.text_document_publish_diagnostics(
            lsp.PublishDiagnosticsParams(uri=uri, diagnostics=diags)
        )

if __name__ == "__main__":
    server.start_io()
