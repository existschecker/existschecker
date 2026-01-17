from pygls.lsp.server import LanguageServer
from pygls.uris import to_fs_path
from lsprotocol import types as lsp
import os

from dependency import DependencyResolver
from ast_types import Context
from parser import Parser
from checker import check_ast

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
    result = False

    path = to_fs_path(params.text_document.uri)
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
    parser_context = Context.init()
    checker_context = Context.init()
    for file in resolved_files:
        parser = Parser(tokens_cache[file])
        ast, parser_context = parser.parse_file(parser_context)
        result, _, checker_context = check_ast(ast, checker_context)

    ls.window_show_message(
        lsp.ShowMessageParams(
            type=lsp.MessageType.Info,
            message=f"result: {result}"
        )
    )

    ls.text_document_publish_diagnostics(
        lsp.PublishDiagnosticsParams(uri=params.text_document.uri, diagnostics=checker_context.diagnostics)
    )

if __name__ == "__main__":
    server.start_io()
