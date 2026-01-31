from pygls.lsp.server import LanguageServer
from pygls import uris
from lsprotocol import types as lsp
import os
import re

from dependency import DependencyResolver
from lexer import KEYWORDS, STRINGS, Token
from ast_types import Context, DeclarationUnit, Workspace, Declaration, PrimPred, Axiom, Theorem, DefPred, DefConExist, DefConUniq, DefCon, DefFunExist, DefFunUniq, DefFun, DefFunTerm
from parser import Parser
from checker import Checker
from splitter import split
from to_html import to_html

class ProofLanguageServer(LanguageServer):
    def __init__(self):
        super().__init__("proof-server", "v0.1") # type: ignore[reportUnknownMemberType]
        self.old_workspace: Workspace | None = None
        self.updated_files: set[str] = set()
        self.resolver: DependencyResolver | None = None

    def run_analysis(self, path: str, save_html: bool):
        self.analyze(path)

        if save_html:
            self.to_html()

    def analyze(self, path: str) -> None:
        self.window_show_message(
            lsp.ShowMessageParams(
                type=lsp.MessageType.Info,
                message=f"Checking {os.path.basename(path)}..."
            )
        )

        if self.resolver is None:
            self.resolver = DependencyResolver()
        self.resolver.dependencies.pop(path, None)
        self.resolver.resolve(path, self)
        resolved_files, tokens_cache = self.resolver.get_result()
        workspace = split(resolved_files, tokens_cache, self.resolver.source_cache)

        all_units: list[DeclarationUnit] = []
        for file in workspace.resolved_files:
            all_units.extend(workspace.file_units[file])

        old_all_units: list[DeclarationUnit] = []
        if self.old_workspace is not None:
            for file in self.old_workspace.resolved_files:
                old_all_units.extend(self.old_workspace.file_units[file])

        context = Context.init()
        start_index = 0
        for i in range(min(len(all_units), len(old_all_units))):
            if all_units[i].hash == old_all_units[i].hash:
                all_units[i].ast = old_all_units[i].ast
                all_units[i].context = old_all_units[i].context
                all_units[i].diagnostics = old_all_units[i].diagnostics
                all_units[i].hover = old_all_units[i].hover
                all_units[i].decl_refs = old_all_units[i].decl_refs
                context = all_units[i].context
                start_index = i + 1
            else:
                break

        for i in range(start_index, len(all_units)):
            unit = all_units[i]
            working_context = context.copy()
            Parser(unit).parse_unit(working_context)
            if Checker(unit).check_unit(working_context):
                context = working_context
            unit.context = context.copy()

        workspace.build_token_to_node()

        self.old_workspace = workspace

        final_diagnostics: dict[str, list[lsp.Diagnostic]] = {}
        for file in workspace.resolved_files:
            uri = uris.from_fs_path(file)
            if uri is None:
                continue
            final_diagnostics[uri] = []
            for unit in workspace.file_units[file]:
                final_diagnostics[uri].extend(unit.diagnostics)
        for uri, diags in self.resolver.diagnostics.items():
            if uri not in final_diagnostics:
                continue
            final_diagnostics[uri].extend(diags)

        updated_files: set[str] = set()
        for i in range(start_index, len(all_units)):
            updated_files.add(all_units[i].file)
        for i in range(start_index, len(old_all_units)):
            updated_files.add(old_all_units[i].file)
        self.updated_files.update(updated_files)

        self.window_show_message(
            lsp.ShowMessageParams(
                type=lsp.MessageType.Info,
                message=f"{sum(len(v) for v in final_diagnostics.values())} errors"
            )
        )

        for uri, diags in final_diagnostics.items():
            self.text_document_publish_diagnostics(
                lsp.PublishDiagnosticsParams(uri=uri, diagnostics=diags)
            )

    def to_html(self) -> None:
        if self.old_workspace is None:
            return
        for file in self.old_workspace.resolved_files:
            if file not in self.updated_files:
                continue
            units = self.old_workspace.file_units[file]
            asts = [unit.ast for unit in units if unit.ast is not None]
            last_context = Context.init() if len(units) == 0 else units[-1].context
            title = os.path.splitext(os.path.basename(file))[0]
            checker_html, _ = to_html(asts, last_context, title, "mathjax")
            f = open(os.path.join(os.path.dirname(os.path.dirname(__file__)), "html", f"{title}.html"), 'w', encoding='utf-8')
            f.write(checker_html)
            f.close()

        self.window_show_message(
            lsp.ShowMessageParams(
                type=lsp.MessageType.Info,
                message=f"{len(self.updated_files)} HTML files are updated"
            )
        )

        self.updated_files.clear()

    @staticmethod
    def get_word_at_position(line: str, character: int) -> str | None:
        word_re = re.compile(r"(\\[A-Za-z][A-Za-z0-9_]*)|([A-Za-z_][A-Za-z0-9_]*'*)")
        for match in word_re.finditer(line):
            if match.start() <= character <= match.end():
                return match.group()
        return None

    def get_definition(self, params: lsp.DefinitionParams) -> lsp.Location | None:
        line = self.workspace.get_text_document(params.text_document.uri).lines[params.position.line]
        name = self.get_word_at_position(line, params.position.character)
        if name is None:
            return None
        if server.old_workspace is None:
            return None
        for unit in server.old_workspace.get_all_units():
            if isinstance(unit.ast, PrimPred | Axiom | Theorem | DefPred | DefConExist | DefConUniq | DefCon | DefFunExist | DefFunUniq | DefFun | DefFunTerm) and unit.ast.name == name:
                token = unit.node_to_token[id(unit.ast.ref)][0]
                uri = uris.from_fs_path(token.file)
                if uri is None:
                    return None
                return lsp.Location(
                    uri=uri,
                    range=lsp.Range(
                        start=lsp.Position(line=token.line - 1, character=token.column - 1),
                        end=lsp.Position(line=token.line - 1, character=token.column - 1 + len(token.value))
                    )
                )
        return None

    def get_references(self, params: lsp.ReferenceParams) -> list[lsp.Location]:
        line = self.workspace.get_text_document(params.text_document.uri).lines[params.position.line]
        name = self.get_word_at_position(line, params.position.character)
        if name is None:
            return []
        if self.old_workspace is None:
            return []
        all_decl_refs = self.old_workspace.get_all_decl_refs(name)
        locations: list[lsp.Location] = []
        for token in all_decl_refs:
            uri = uris.from_fs_path(token.file)
            if uri is None:
                return []
            locations.append(lsp.Location(
                uri=uri,
                range=lsp.Range(
                    start=lsp.Position(line=token.line - 1, character=token.column - 1),
                    end=lsp.Position(line=token.line - 1, character=token.column - 1 + len(token.value))
                )
            ))
        return locations

    def get_completion(self) -> list[lsp.CompletionItem]:
        items: list[lsp.CompletionItem] = []
        for keyword in KEYWORDS:
            items.append(
                lsp.CompletionItem(
                    label=keyword,
                    kind=lsp.CompletionItemKind.Keyword
                )
            )
        for operator in STRINGS.keys():
            items.append(
                lsp.CompletionItem(
                    label=operator,
                    kind=lsp.CompletionItemKind.Operator
                )
            )
        if self.old_workspace:
            for unit in self.old_workspace.get_all_units():
                if isinstance(unit.ast, Declaration):
                    items.append(
                        lsp.CompletionItem(
                            label=unit.ast.name,
                            kind=lsp.CompletionItemKind.Function
                        )
                    )
        return items

    @staticmethod
    def find_token_at(unit: DeclarationUnit, pos: lsp.Position) -> Token | None:
        target_line = pos.line + 1
        target_column = pos.character + 1
        for token in unit.tokens:
            if target_line < token.line or target_line > token.end_line:
                continue
            if target_line == token.line and target_column < token.column:
                continue
            if target_line == token.end_line and target_column > token.end_column:
                continue
            return token
        return None

    @staticmethod
    def is_in_range(pos: lsp.Position, unit: DeclarationUnit) -> bool:
        target_line = pos.line + 1
        target_column = pos.character + 1
        start_token = unit.tokens[0]
        end_token = unit.tokens[-1]
        if target_line < start_token.line or target_line > end_token.line:
            return False
        if target_line == start_token.line and target_column < start_token.column:
            return False
        if target_line == end_token.end_line and target_column > end_token.end_column:
            return False
        return True

    def get_unit_at(self, uri: str, position: lsp.Position) -> DeclarationUnit | None:
        path = uris.to_fs_path(uri)
        if path is None:
            return None
        if self.old_workspace is None:
            return None
        units = self.old_workspace.file_units.get(path, [])
        for unit in units:
            if self.is_in_range(position, unit):
                return unit
        return None

    def hovers(self, params: lsp.HoverParams) -> lsp.Hover | None:
        unit = self.get_unit_at(params.text_document.uri, params.position)
        if unit is None:
            return None
        token = self.find_token_at(unit, params.position)
        if token is None:
            return None
        node = unit.token_to_node[token]
        line = self.workspace.get_text_document(params.text_document.uri).lines[params.position.line]
        name = self.get_word_at_position(line, params.position.character)
        if name is None:
            return None
        if self.old_workspace is None:
            return None
        for unit in self.old_workspace.get_all_units():
            if isinstance(unit.ast, Declaration) and unit.ast.name == name and isinstance(unit.hover, str):
                return lsp.Hover(
                    contents=lsp.MarkupContent(
                        kind=lsp.MarkupKind.Markdown,
                        value=f"{node.__class__.__name__}\n{unit.hover}"
                    )
                )
        return lsp.Hover(
            contents=lsp.MarkupContent(
                kind=lsp.MarkupKind.Markdown,
                value=node.__class__.__name__
            )
        )

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
    ls.window_show_message(
        lsp.ShowMessageParams(
            type=lsp.MessageType.Info,
            message=f"Open file: {os.path.basename(params.text_document.uri)}"
        )
    )

@server.feature(lsp.TEXT_DOCUMENT_DID_SAVE)
def did_save(ls: ProofLanguageServer, params: lsp.DidSaveTextDocumentParams) -> None:
    path = uris.to_fs_path(params.text_document.uri)
    if path is None:
        raise Exception(f"Cannot convert {params.text_document.uri} to path")

    ls.run_analysis(path, True)

@server.feature(lsp.TEXT_DOCUMENT_DEFINITION)
def lsp_definition(ls: ProofLanguageServer, params: lsp.DefinitionParams) -> lsp.Location | None:
    return ls.get_definition(params)

@server.feature(lsp.TEXT_DOCUMENT_COMPLETION)
def lsp_completion(ls: ProofLanguageServer, params: lsp.CompletionParams):
    items = ls.get_completion()
    return lsp.CompletionList(is_incomplete=False, items=items)

@server.feature(lsp.TEXT_DOCUMENT_DID_CHANGE)
def did_change(ls: ProofLanguageServer, params: lsp.DidChangeTextDocumentParams) -> None:
    path = uris.to_fs_path(params.text_document.uri)
    if path is None:
        return

    ls.run_analysis(path, False)

@server.feature(lsp.TEXT_DOCUMENT_HOVER)
def hovers(ls: ProofLanguageServer, params: lsp.HoverParams) -> lsp.Hover | None:
    return ls.hovers(params)

@server.feature(lsp.TEXT_DOCUMENT_REFERENCES)
def lsp_references(ls: ProofLanguageServer, params: lsp.ReferenceParams) -> list[lsp.Location]:
    return ls.get_references(params)

if __name__ == "__main__":
    server.start_io()
