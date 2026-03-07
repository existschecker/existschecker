from pygls.lsp.server import LanguageServer
from pygls import uris
from lsprotocol import types as lsp
from dataclasses import dataclass
import threading
import sys
from enum import IntEnum

from dependency import DependencyResolver
from lexer import KEYWORDS, STRINGS, Token
from ast_types import Context, DeclarationUnit, Workspace, Declaration, Include, Control, Formula, Term, RefFact, RefAxiom, RefTheorem, RefDefConExist, RefDefConUniq, RefDefFunExist, RefDefFunUniq, VarTerm, RefDefCon, PredTerm, RefPrimPred, RefDefPred, FunTerm, RefDefFun, RefDefFunTerm, RefEquality, PredLambda, FunLambda
from parser import Parser
from checker import Checker
from splitter import split
from to_html import Renderer
from logic_utils import ExprFormatter

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

@dataclass
class CursorState:
    uri: str
    position: lsp.Position

def get_hover(node: Include | Declaration | Control | Formula | Term | RefFact, context: Context) -> str:
    if isinstance(node, Declaration):
        return f"{node.__class__.__name__}: {node.proofinfo.status}"
    elif isinstance(node, Control):
        formatter = ExprFormatter(context)
        context_vars = ", ".join(formatter.pretty_expr(context_var) for context_var in node.proofinfo.ctrl_ctx.vars)
        context_pred_tmpls = ", ".join(formatter.pretty_expr(context_pred_tmpl) for context_pred_tmpl in node.proofinfo.ctrl_ctx.pred_tmpls)
        context_fun_tmpls = ", ".join(formatter.pretty_expr(context_fun_tmpl) for context_fun_tmpl in node.proofinfo.ctrl_ctx.fun_tmpls)
        premises = ", ".join(formatter.pretty_expr(premise) for premise in node.proofinfo.premises)
        conclusions = ", ".join(ExprFormatter(context).pretty_expr(conclusion) for conclusion in node.proofinfo.conclusions)
        local_vars = ", ".join(formatter.pretty_expr(var) for var in node.proofinfo.local_vars)
        local_premises = ", ".join(formatter.pretty_expr(local_premise) for local_premise in node.proofinfo.local_premise)
        local_conclusions = ", ".join(formatter.pretty_expr(local_conclusion) for local_conclusion in node.proofinfo.local_conclusion)
        return f"""{node.__class__.__name__}: {node.proofinfo.status}
```proof
context_vars: {context_vars}
context_pred_tmpls: {context_pred_tmpls}
context_fun_tmpls: {context_fun_tmpls}
premises: {premises}
conclusions: {conclusions}
local_vars: {local_vars}
local_premises: {local_premises}
local_conclusions: {local_conclusions}
```"""
    elif isinstance(node, Term):
        if isinstance(node, VarTerm):
            if isinstance(node, RefDefCon):
                defcon = context.decl.defcons[node.name]
                return f"{node.__class__.__name__}\n```proof\ndefinition constant {defcon.name} by {defcon.ref_theorem.name}\n```"
            else:
                return node.__class__.__name__
        elif isinstance(node, PredTerm):
            if isinstance(node, RefPrimPred):
                primpred = context.decl.primpreds[node.name]
                return f"{node.__class__.__name__}\n```proof\nprimitive predicate {primpred.name} arity {primpred.arity}\n```"
            elif isinstance(node, RefDefPred):
                defpred = context.decl.defpreds[node.name]
                return f"{node.__class__.__name__}\n```proof\ndefinition predicate {defpred.name}({", ".join(ExprFormatter(context).pretty_expr(arg) for arg in defpred.args)}) as {ExprFormatter(context).pretty_expr(defpred.formula)}\n```"
            else:
                return node.__class__.__name__
        elif isinstance(node, FunTerm):
            if isinstance(node, RefDefFun):
                deffun = context.decl.deffuns[node.name]
                return f"{node.__class__.__name__}\n```proof\ndefinition function {deffun.name} by {deffun.ref_theorem.name}\n```"
            elif isinstance(node, RefDefFunTerm):
                deffunterm = context.decl.deffunterms[node.name]
                return f"{node.__class__.__name__}\n```proof\ndefinition function {deffunterm.name}({", ".join(ExprFormatter(context).pretty_expr(arg) for arg in deffunterm.args)}) as {ExprFormatter(context).pretty_expr(deffunterm.varterm)}"
            else:
                return node.__class__.__name__
        else:
            return f"{node.__class__.__name__}: Unknown"
    elif isinstance(node, RefFact):
        if isinstance(node, RefAxiom):
            axiom = context.decl.axioms[node.name]
            return f"{node.__class__.__name__}\n```proof\naxiom {axiom.name} {ExprFormatter(context).pretty_expr(axiom.conclusion)}\n```"
        elif isinstance(node, RefTheorem):
            theorem = context.decl.theorems[node.name]
            return f"{node.__class__.__name__}\n```proof\ntheorem {theorem.name} {ExprFormatter(context).pretty_expr(theorem.conclusion)}\n```"
        elif isinstance(node, RefDefConExist):
            defconexist = context.decl.defconexists[node.name]
            return f"{node.__class__.__name__}\n```proof\nexistence {defconexist.name} {ExprFormatter(context).pretty_expr(defconexist.formula)} by {defconexist.ref_con.name}\n```"
        elif isinstance(node, RefDefConUniq):
            defconuniq = context.decl.defconuniqs[node.name]
            return f"{node.__class__.__name__}\n```proof\nuniqueness {defconuniq.name} {ExprFormatter(context).pretty_expr(defconuniq.formula)} by {defconuniq.ref_con.name}\n```"
        elif isinstance(node, RefDefFunExist):
            deffunexist = context.decl.deffunexists[node.name]
            return f"{node.__class__.__name__}\n```proof\nexistence {deffunexist.name} {ExprFormatter(context).pretty_expr(deffunexist.formula)} by {deffunexist.ref_fun.name}"
        elif isinstance(node, RefDefFunUniq):
            deffununiq = context.decl.deffununiqs[node.name]
            return f"{node.__class__.__name__}\n```proof\nuniqueness {deffununiq.name} {ExprFormatter(context).pretty_expr(deffununiq.formula)} by {deffununiq.ref_fun.name}"
        else:
            return f"{node.__class__.__name__}: Unknown"
    else:
        return node.__class__.__name__

def render_statement(node: Declaration | Control, context: Context) -> str:
    renderer = Renderer(context, "mathjax")
    method_name = f"render_{node.__class__.__name__.lower()}"
    renderer_method = getattr(renderer, method_name, None)
    if renderer_method is None:
        return f"[{node.__class__.__name__}]"
    else:
        return " ".join(renderer_method(node)[0][1:])

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
        renderer = Renderer(context, "mathjax")
        context_symbols = renderer.render_expr_list(node.proofinfo.ctrl_ctx.symbols)
        context_formulas = renderer.render_expr_list(node.proofinfo.ctrl_ctx.formulas)
        premises = renderer.render_expr_list(node.proofinfo.premises)
        conclusions = renderer.render_expr_list(node.proofinfo.conclusions)
        local_vars = renderer.render_expr_list(node.proofinfo.local_vars)
        local_premises = renderer.render_expr_list(node.proofinfo.local_premise)
        local_conclusions = renderer.render_expr_list(node.proofinfo.local_conclusion)
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

class ProofLanguageServer(LanguageServer):
    def __init__(self):
        super().__init__("proof-server", "v0.1") # type: ignore[reportUnknownMemberType]
        self.old_workspace: Workspace | None = None
        self.resolver: DependencyResolver | None = None
        self.analysis_timer: threading.Timer | None = None
        self.cancel_analysis = threading.Event()
        self.current_cursor: CursorState | None = None

    def run_analysis(self, uri: str):
        path = uris.to_fs_path(uri)
        if path is None:
            return
        self.analyze(path)
        self.analysis_timer = None
        self.protocol.send_request("workspace/semanticTokens/refresh")
        self.update_panel()

    def restore_cache(self, all_units: list[DeclarationUnit], old_all_units: list[DeclarationUnit], context: Context) -> tuple[Context, int]:
        start_index = 0
        for i in range(min(len(all_units), len(old_all_units))):
            if all_units[i].hash == old_all_units[i].hash:
                all_units[i].restore_from(old_all_units[i])
                context = all_units[i].context
                start_index = i + 1
            else:
                break
        return context, start_index

    def analyze_diff(self, all_units: list[DeclarationUnit], start_index: int, context: Context) -> Context | None:
        for i in range(start_index, len(all_units)):
            if self.cancel_analysis.is_set():
                return None
            unit = all_units[i]
            working_context = context.copy()
            Parser(unit).parse_unit(working_context)
            if Checker(unit).check_unit(working_context):
                context = working_context
            unit.context = context.copy()
        return context

    def prepare_context(self, file: str, resolver: DependencyResolver, file_final_contexts: dict[str, Context]) -> Context:
        context = Context.init()
        processed_files: set[str] = set() # avoid diamond dependency
        for dep in resolver.dependencies[file]:
            if dep not in processed_files:
                context.merge(file_final_contexts[dep])
                processed_files.add(dep)
        return context

    def analyze(self, path: str) -> None:
        self.cancel_analysis.clear()

        if self.resolver is None:
            self.resolver = DependencyResolver()
        else:
            self.resolver.diagnostics = {}
        self.resolver.dependencies.pop(path, None)
        self.resolver.resolve(path, self)
        affected_files = self.resolver.get_affected_files(path)
        order = self.resolver.get_order()
        workspace = split(order, self.resolver.tokens_cache, self.resolver.source_cache)

        file_final_contexts: dict[str, Context] = {}
        newly_analyzed: set[str] = set()
        for file in workspace.resolved_files:
            is_affected = file in affected_files
            dependency_changed = any(dep in newly_analyzed for dep in self.resolver.dependencies.get(file, []))
            if not is_affected and not dependency_changed:
                if self.old_workspace is not None and file in self.old_workspace.file_units:
                    workspace.file_units[file] = self.old_workspace.file_units[file]
                    file_final_contexts[file] = workspace.file_units[file][-1].context.copy()
                    continue
            context = self.prepare_context(file, self.resolver, file_final_contexts)
            all_units = workspace.file_units[file]
            old_all_units = [] if self.old_workspace is None or dependency_changed else self.old_workspace.file_units.get(file, [])
            context, start_index = self.restore_cache(all_units, old_all_units, context)
            if start_index < len(all_units):
                newly_analyzed.add(file)
            context = self.analyze_diff(all_units, start_index, context)
            if context is None:
                return None
            file_final_contexts[file] = context.copy()

        workspace.build_token_to_node()

        if self.old_workspace is None:
            self.old_workspace = workspace
        else:
            self.old_workspace.merge(workspace)

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

        for uri, diags in final_diagnostics.items():
            self.text_document_publish_diagnostics(
                lsp.PublishDiagnosticsParams(uri=uri, diagnostics=diags)
            )

    def did_open(self, params: lsp.DidOpenTextDocumentParams) -> None:
        self.run_analysis(params.text_document.uri)

    def did_save(self, params: lsp.DidSaveTextDocumentParams) -> None:
        self.run_analysis(params.text_document.uri)

    def did_change(self, params: lsp.DidChangeTextDocumentParams) -> None:
        if self.analysis_timer is not None:
            self.analysis_timer.cancel()
        self.cancel_analysis.set()
        self.analysis_timer = threading.Timer(0.5, self.run_analysis, args=[params.text_document.uri])
        self.analysis_timer.start()

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
        order, _ = self.resolver.get_result(unit.file)
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
        decl_ref_tokens = self.old_workspace.get_all_decl_refs(ref_name)
        return tokens_to_locations(decl_ref_tokens)

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
        node = unit.token_to_node[token.index]
        return lsp.Hover(
            contents=lsp.MarkupContent(
                kind=lsp.MarkupKind.Markdown,
                value=get_hover(node, unit.context)
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

    def get_proofinfo(self) -> str:
        if self.current_cursor is None:
            return "current_cursor is not found"
        unit = self.get_unit_at(self.current_cursor.uri, self.current_cursor.position)
        if unit is None:
            return "unit is not found"
        if unit.ast is None:
            return "ast is not found"
        node = self.find_node_by_line(unit, self.current_cursor.position)
        path = uris.from_fs_path(self.current_cursor.uri)
        if path is None:
            return "path is not found"
        decl_info = render_proofinfo(unit.ast, unit.context)
        ctrl_info = "" if node is None else render_proofinfo(node, unit.context)
        return HTML_TEMPLATE.format(decl_info=decl_info, ctrl_info=ctrl_info)

    def update_panel(self) -> None:
        self.protocol.notify("proof/updatePanel", self.get_proofinfo())

    def semantic_tokens_full(self, params: lsp.SemanticTokensParams) -> lsp.SemanticTokens:
        print("[semantic_tokens_full] called", file=sys.stderr)
        path = uris.to_fs_path(params.text_document.uri)
        if path is None:
            print("[semantic_tokens_full] path is None", file=sys.stderr)
            return lsp.SemanticTokens(data=[])
        if self.old_workspace is None:
            print("[semantic_tokens_full] workspace is None", file=sys.stderr)
            return lsp.SemanticTokens(data=[])
        raw_tokens: list[tuple[int, int, int, int]] = []
        if path not in self.old_workspace.file_units:
            print(f"[semantic_tokens_full] {path} is not in workspace", file=sys.stderr)
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
        print(f"[semantic_tokens_full] len(data)={len(data)}", file=sys.stderr)
        for i in range(min(5, len(data) // 5)):
            print(f"[semantic_tokens_full] {data[5*i : 5*(i+1)]}", file=sys.stderr)
        return lsp.SemanticTokens(data=data)

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
    ls.did_open(params)

@server.feature(lsp.TEXT_DOCUMENT_DID_SAVE)
def did_save(ls: ProofLanguageServer, params: lsp.DidSaveTextDocumentParams) -> None:
    ls.did_save(params)

@server.feature(lsp.TEXT_DOCUMENT_DEFINITION)
def lsp_definition(ls: ProofLanguageServer, params: lsp.DefinitionParams) -> lsp.Location | None:
    return ls.get_definition(params)

@server.feature(lsp.TEXT_DOCUMENT_COMPLETION)
def lsp_completion(ls: ProofLanguageServer, params: lsp.CompletionParams):
    items = ls.get_completion()
    return lsp.CompletionList(is_incomplete=False, items=items)

@server.feature(lsp.TEXT_DOCUMENT_DID_CHANGE)
def did_change(ls: ProofLanguageServer, params: lsp.DidChangeTextDocumentParams) -> None:
    ls.did_change(params)

@server.feature(lsp.TEXT_DOCUMENT_HOVER)
def hovers(ls: ProofLanguageServer, params: lsp.HoverParams) -> lsp.Hover | None:
    return ls.hovers(params)

@server.feature(lsp.TEXT_DOCUMENT_REFERENCES)
def lsp_references(ls: ProofLanguageServer, params: lsp.ReferenceParams) -> list[lsp.Location]:
    return ls.get_references(params)

@server.feature("proof/moveCursor")
def move_cursor(ls: ProofLanguageServer, params: CursorState) -> None:
    ls.current_cursor = params
    if ls.analysis_timer is not None:
        return
    ls.update_panel()

class TokenType(IntEnum):
    FUNCTION = 0
    CONSTANT = 1
    VARIABLE = 2

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
    return ls.semantic_tokens_full(params)

if __name__ == "__main__":
    server.start_io()
