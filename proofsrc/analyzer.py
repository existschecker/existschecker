from pygls import uris
from lsprotocol import types as lsp
from dataclasses import dataclass
import threading
import re
from enum import IntEnum
from typing import Sequence

from dependency import DependencyResolver
from lexer import KEYWORDS, STRINGS, Token
from ast_types import Context, DeclarationUnit, Workspace, Declaration, Include, Control, Formula, Term, RefFact, RefDefCon, RefPrimPred, RefDefPred, RefDefFun, RefDefFunTerm, RefEquality, PredLambda, FunLambda, FormatError, RenderError, Bottom
from splitter import split
from to_html import Renderer
from parser import Parser
from checker import Checker

HTML_TEMPLATE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<script id="MathJax-script" async
  src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
<style>
    .syntax-declarations {{ color: #569CD6; }}
    .syntax-controls {{ color: #C586C0; }}
    .semantic-function {{ color: #DCDCAA; }}
    .semantic-constant {{ color: #4FC1FF; }}
    .statement {{ min-height: 1.5em; }}
    .status-icon {{ display: inline-block; min-width: 100px; background: rgba(128, 128, 128, 0.5); border-radius: 12px; text-align: center; }}
    table {{ width: 100%; }}
    td {{ border: 1px solid var(--vscode-panel-border); height: 1.5em; }}
    .current {{ background-color: rgba(255, 255, 0, 0.1); }}
    .block {{ background-color: rgba(0, 122, 204, 0.1); }}
    .context {{ background-color: rgba(128, 128, 128, 0.1); }}
    td:first-child {{ color: var(--vscode-descriptionForeground); width: 200px; }}
</style>
</head>
<body>
{decl_info}
{ctrl_info}
</body>
</html>
"""

class TokenType(IntEnum):
    FUNCTION = 0
    CONSTANT = 1
    VARIABLE = 2

@dataclass
class CursorState:
    uri: str
    position: lsp.Position

def get_hover(node: Include | Declaration | Control | Formula | Term | RefFact) -> str:
    if isinstance(node, (Declaration, Control)):
        return f"{node.__class__.__name__}: {node.proofinfo.status}"
    else:
        return node.__class__.__name__

def render_statement(node: Declaration | Control, context: Context) -> str:
    renderer = Renderer(context)
    method_name = f"render_{node.__class__.__name__.lower()}"
    renderer_method = getattr(renderer, method_name, None)
    if renderer_method is None:
        return f"[{node.__class__.__name__}]"
    else:
        try:
            return " ".join(renderer_method(node)[0][1:])
        except (FormatError, RenderError) as e:
            return f"{e.__class__.__name__}: {e.msg}"

def render_expr_list(renderer: Renderer, formulas: Sequence[RefFact | Bottom | Formula | Term]) -> str:
    try:
        return renderer.render_expr_list(formulas)
    except (FormatError, RenderError) as e:
        return f"{e.__class__.__name__}: {e.msg}"

def render_proofinfo(node: Include | Declaration | Control, context: Context) -> str:
    if isinstance(node, Declaration):
        statement = render_statement(node, context)
        return f"""<div class="statement">
    <span class="status-icon">{node.proofinfo.status}</span>
    {statement}
</div>
"""
    elif isinstance(node, Control):
        statement = render_statement(node, context)
        renderer = Renderer(context)
        context_symbols = render_expr_list(renderer, node.proofinfo.ctrl_ctx.symbols)
        context_formulas = render_expr_list(renderer, node.proofinfo.ctrl_ctx.formulas)
        premises = render_expr_list(renderer, node.proofinfo.premises)
        conclusions = render_expr_list(renderer, node.proofinfo.conclusions)
        local_vars = render_expr_list(renderer, node.proofinfo.local_vars)
        local_premises = render_expr_list(renderer, node.proofinfo.local_premise)
        local_conclusions = render_expr_list(renderer, node.proofinfo.local_conclusion)
        return f"""<div class="statement">
    <span class="status-icon">{node.proofinfo.status}</span>
    {statement}
</div>
<table>
    <tr class="current"><td>Premises of this statement</td><td>{premises}</td></tr>
    <tr class="current"><td>Conclusions of this statement</td><td>{conclusions}</td></tr>
    <tr class="block"><td>New symbols in this block</td><td>{local_vars}</td></tr>
    <tr class="block"><td>New formulas in this block</td><td>{local_premises}</td></tr>
    <tr class="block"><td>Conclusions in this block</td><td>{local_conclusions}</td></tr>
    <tr class="context"><td>Available symbols</td><td>{context_symbols}</td></tr>
    <tr class="context"><td>Available formulas</td><td>{context_formulas}</td></tr>
</table>
"""
    else:
        return node.__class__.__name__

def token_to_location(token: Token) -> lsp.Location | None:
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

def tokens_to_locations(tokens: list[Token]) -> list[lsp.Location]:
    locations: list[lsp.Location] = []
    for token in tokens:
        location = token_to_location(token)
        if location is not None:
            locations.append(location)
    return locations

def prepare_context(file: str, resolver: DependencyResolver, file_final_contexts: dict[str, Context]) -> Context:
    context = Context.init()
    for dep in resolver.dependencies[file]:
        context.merge(file_final_contexts[dep])
    return context

def restore_cache(all_units: list[DeclarationUnit], old_all_units: list[DeclarationUnit], context: Context) -> tuple[Context, int]:
    start_index = 0
    for i in range(min(len(all_units), len(old_all_units))):
        if all_units[i].hash == old_all_units[i].hash:
            all_units[i].restore_from(old_all_units[i])
            context = all_units[i].context
            start_index = i + 1
        else:
            break
    return context, start_index

def analyze_diff(all_units: list[DeclarationUnit], start_index: int, context: Context, cancel_analysis: threading.Event | None = None) -> Context | None:
    for i in range(start_index, len(all_units)):
        if cancel_analysis is not None and cancel_analysis.is_set():
            return None
        unit = all_units[i]
        working_context = context.copy()
        Parser(unit).parse_unit(working_context)
        if Checker(unit).check_unit(working_context):
            context = working_context
        unit.context = context.copy()
        unit.build_token_to_node()
    return context

class Analyzer:
    def __init__(self):
        self.old_workspace: Workspace | None = None
        self.resolver: DependencyResolver | None = None

    def analyze(self, path: str, editor_files: dict[str, str] | None = None, cancel_analysis: threading.Event | None = None) -> dict[str, list[lsp.Diagnostic]]:
        if self.resolver is None:
            self.resolver = DependencyResolver()
        else:
            self.resolver.prepare(path)
        self.resolver.resolve(path, editor_files)
        affected_files = self.resolver.get_affected_files(path)
        order = self.resolver.get_full_order()

        file_units: dict[str, list[DeclarationUnit]] = {}
        file_final_contexts: dict[str, Context] = {}
        newly_analyzed: set[str] = set()
        for file in order:
            is_affected = file in affected_files
            dependency_changed = any(dep in newly_analyzed for dep in self.resolver.dependencies.get(file, []))
            if not is_affected and not dependency_changed:
                if self.old_workspace is not None and file in self.old_workspace.file_units and len(self.old_workspace.file_units[file]) > 0:
                    file_units[file] = self.old_workspace.file_units[file]
                    file_final_contexts[file] = file_units[file][-1].context.copy()
                    continue
            all_units = split(file, self.resolver.tokens_cache[file], self.resolver.source_cache[file])
            file_units[file] = all_units
            context = prepare_context(file, self.resolver, file_final_contexts)
            old_all_units = [] if self.old_workspace is None or dependency_changed else self.old_workspace.file_units.get(file, [])
            context, start_index = restore_cache(all_units, old_all_units, context)
            if start_index < len(all_units):
                newly_analyzed.add(file)
            context = analyze_diff(all_units, start_index, context, cancel_analysis)
            if context is None:
                return {}
            file_final_contexts[file] = context.copy()

        workspace = Workspace(file_units)

        if self.old_workspace is None:
            self.old_workspace = workspace
        else:
            self.old_workspace.merge(workspace)

        final_diagnostics: dict[str, list[lsp.Diagnostic]] = {}
        for file in workspace.file_units:
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

        return final_diagnostics

    def get_definition(self, params: lsp.DefinitionParams) -> lsp.Location | None:
        unit = self.get_unit_at(params.text_document.uri, params.position)
        if unit is None:
            return None
        ref_token = self.find_token_at(unit, params.position)
        if ref_token is None:
            return None
        ctrl_def_token = unit.get_ctrl_def(ref_token)
        if ctrl_def_token is not None:
            return token_to_location(ctrl_def_token)
        ref_name = ref_token.value
        if self.old_workspace is None:
            return None
        if self.resolver is None:
            return None
        order = self.resolver.get_dependent_order(unit.file)
        decl_def_token = self.old_workspace.get_decl_def(ref_name, order)
        if decl_def_token is None:
            return None
        return token_to_location(decl_def_token)

    def get_references(self, params: lsp.ReferenceParams) -> list[lsp.Location]:
        unit = self.get_unit_at(params.text_document.uri, params.position)
        if unit is None:
            return []
        ref_token = self.find_token_at(unit, params.position)
        if ref_token is None:
            return []
        ctrl_ref_tokens = unit.get_ctrl_refs(ref_token)
        if len(ctrl_ref_tokens) > 0:
            return tokens_to_locations(ctrl_ref_tokens)
        ref_name = ref_token.value
        if self.old_workspace is None:
            return []
        if self.resolver is None:
            return []
        affected_files = self.resolver.get_affected_files(unit.file)
        decl_ref_tokens = self.old_workspace.get_all_decl_refs(ref_name, affected_files)
        return tokens_to_locations(decl_ref_tokens)

    def get_completion(self, params: lsp.CompletionParams, source: str) -> list[lsp.CompletionItem]:
        match = re.search(r"\\(\w+)?$", source.splitlines()[params.position.line][:params.position.character])
        typing_backslash = match is not None
        candidates: list[tuple[str, lsp.CompletionItemKind]] = []
        for keyword in KEYWORDS:
            candidates.append((keyword, lsp.CompletionItemKind.Keyword))
        for operator in STRINGS.keys():
            candidates.append((operator, lsp.CompletionItemKind.Operator))
        if self.old_workspace is not None and self.resolver is not None:
            current_unit = self.get_unit_at(params.text_document.uri, params.position)
            if current_unit is not None:
                order = self.resolver.get_dependent_order(current_unit.file)
                for path in order:
                    for unit in self.old_workspace.file_units[path]:
                        if isinstance(unit.ast, Declaration):
                            candidates.append((unit.ast.name, lsp.CompletionItemKind.Function))
        items: list[lsp.CompletionItem] = []
        for name, kind in candidates:
            if typing_backslash and name.startswith("\\"):
                insert_text = name[1:]
            elif (not typing_backslash) and (not name.startswith("\\")):
                insert_text = name
            else:
                continue
            items.append(
                lsp.CompletionItem(
                    label=name,
                    insert_text=insert_text,
                    kind=kind
                )
            )
        return items

    @staticmethod
    def find_token_at(unit: DeclarationUnit, pos: lsp.Position) -> Token | None:
        target_line = pos.line + 1
        target_column = pos.character + 1
        candidate = None
        for token in unit.tokens[:-1]:
            if target_line < token.line or target_line > token.end_line:
                continue
            if target_line == token.line and target_column < token.column:
                continue
            if target_line == token.end_line and target_column > token.end_column:
                continue
            if token.type == "IDENT":
                return token
            candidate = token
        return candidate

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
        target_line = position.line + 1
        last_unit = None
        for unit in units:
            if target_line < unit.tokens[0].line:
                return last_unit
            if self.is_in_range(position, unit):
                return unit
            last_unit = unit
        return last_unit

    def hovers(self, params: lsp.HoverParams) -> lsp.Hover | None:
        unit = self.get_unit_at(params.text_document.uri, params.position)
        if unit is None:
            return None
        token = self.find_token_at(unit, params.position)
        if token is None:
            return None
        if token.index not in unit.token_to_node:
            return None
        node = unit.token_to_node[token.index]
        return lsp.Hover(
            contents=lsp.MarkupContent(
                kind=lsp.MarkupKind.Markdown,
                value=get_hover(node)
            )
        )

    @staticmethod
    def find_node_by_line(unit: DeclarationUnit, position: lsp.Position) -> Control | None:
        target_line = position.line + 1
        last_node = None
        for token in unit.tokens:
            if token.line < target_line and token.index in unit.token_to_control:
                last_node = unit.token_to_control[token.index]
            elif token.line == target_line and token.index in unit.token_to_control:
                return unit.token_to_control[token.index]
        return last_node

    def get_proofinfo(self, current_cursor: CursorState | None) -> str:
        if current_cursor is None:
            return "current_cursor is not found"
        unit = self.get_unit_at(current_cursor.uri, current_cursor.position)
        if unit is None:
            return "unit is not found"
        if unit.ast is None:
            return "ast is not found"
        node = self.find_node_by_line(unit, current_cursor.position)
        path = uris.from_fs_path(current_cursor.uri)
        if path is None:
            return "path is not found"
        decl_info = render_proofinfo(unit.ast, unit.context)
        ctrl_info = "" if node is None else render_proofinfo(node, unit.context)
        return HTML_TEMPLATE.format(decl_info=decl_info, ctrl_info=ctrl_info)

    def semantic_tokens_full(self, params: lsp.SemanticTokensParams) -> lsp.SemanticTokens:
        path = uris.to_fs_path(params.text_document.uri)
        if path is None:
            return lsp.SemanticTokens(data=[])
        if self.old_workspace is None:
            return lsp.SemanticTokens(data=[])
        raw_tokens: list[tuple[int, int, int, int]] = []
        if path not in self.old_workspace.file_units:
            return lsp.SemanticTokens(data=[])
        for unit in self.old_workspace.file_units[path]:
            for index, node in unit.token_to_node.items():
                token = unit.tokens[index]
                if isinstance(node, RefFact):
                    t_type = TokenType.FUNCTION
                elif isinstance(node, (RefEquality, RefPrimPred, RefDefPred, RefDefCon, RefDefFun, RefDefFunTerm)):
                    t_type = TokenType.CONSTANT
                elif isinstance(node, Term) and not isinstance(node, PredLambda) and not isinstance(node, FunLambda):
                    t_type = TokenType.VARIABLE
                else:
                    t_type = None
                if t_type is not None:
                    raw_tokens.append((token.line - 1, token.column - 1, len(token.value), t_type))
        data: list[int] = []
        last_line = 0
        last_column = 0
        for line, column, length, t_type in raw_tokens:
            delta_line = line - last_line
            delta_start = column if delta_line > 0 else column - last_column
            data.extend([delta_line, delta_start, length, t_type, 0])
            last_line = line
            last_column = column
        return lsp.SemanticTokens(data=data)

def print_diags(diagnostics: dict[str, list[lsp.Diagnostic]]) -> None:
    total_errors = 0
    for uri, diags in diagnostics.items():
        count = len(diags)
        if count > 0:
            print(f"[{uri}] ({count} errors)")
            path = uris.to_fs_path(uri)
            for diag in diags:
                print(f"❌ [{path}:{diag.range.start.line + 1}:{diag.range.start.character + 1}] [{diag.source}] {diag.message}")
            total_errors += count
    print(f"({total_errors} total errors)")
