from pygls.lsp.server import LanguageServer
from pygls import uris
from lsprotocol import types as lsp
import os
from dataclasses import dataclass
import threading

from dependency import DependencyResolver
from lexer import KEYWORDS, STRINGS, Token
from ast_types import Context, DeclarationUnit, Workspace, Declaration, Include, Control, Formula, Term, RefFact, RefAxiom, RefTheorem, RefDefConExist, RefDefConUniq, RefDefFunExist, RefDefFunUniq, VarTerm, RefDefCon, PredTerm, RefPrimPred, RefDefPred, FunTerm, RefDefFun, RefDefFunTerm
from parser import Parser
from checker import Checker
from splitter import split
from to_html import Renderer, to_html
from logic_utils import ExprFormatter

HTML_TEMPLATE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<script id="MathJax-script" async
  src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
<link rel="stylesheet" href="style_mathjax.css">
</head>
<body>
{body}
</body>
</html>
"""

@dataclass
class GetProofInfoParams:
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
                return f"{node.__class__.__name__}\n```proof\ndefinition constant {defcon.name} by {defcon.theorem}\n```"
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
                return f"{node.__class__.__name__}\n```proof\ndefinition function {deffun.name} by {deffun.theorem}\n```"
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
            return f"{node.__class__.__name__}\n```proof\nexistence {defconexist.name} {ExprFormatter(context).pretty_expr(defconexist.formula)} by {defconexist.con_name}\n```"
        elif isinstance(node, RefDefConUniq):
            defconuniq = context.decl.defconuniqs[node.name]
            return f"{node.__class__.__name__}\n```proof\nuniqueness {defconuniq.name} {ExprFormatter(context).pretty_expr(defconuniq.formula)} by {defconuniq.con_name}\n```"
        elif isinstance(node, RefDefFunExist):
            deffunexist = context.decl.deffunexists[node.name]
            return f"{node.__class__.__name__}\n```proof\nexistence {deffunexist.name} {ExprFormatter(context).pretty_expr(deffunexist.formula)} by {deffunexist.fun_name}"
        elif isinstance(node, RefDefFunUniq):
            deffununiq = context.decl.deffununiqs[node.name]
            return f"{node.__class__.__name__}\n```proof\nuniqueness {deffununiq.name} {ExprFormatter(context).pretty_expr(deffununiq.formula)} by {deffununiq.fun_name}"
        else:
            return f"{node.__class__.__name__}: Unknown"
    else:
        return node.__class__.__name__

def render_proofinfo(node: Include | Declaration | Control, context: Context) -> str:
    if isinstance(node, Declaration):
        return f"{node.__class__.__name__}: {node.proofinfo.status}"
    elif isinstance(node, Control):
        renderer = Renderer(context, "mathjax")
        context_vars = renderer.render_expr_list(node.proofinfo.ctrl_ctx.vars)
        context_formulas = renderer.render_expr_list(node.proofinfo.ctrl_ctx.formulas)
        context_pred_tmpls = renderer.render_expr_list(node.proofinfo.ctrl_ctx.pred_tmpls)
        context_fun_tmpls = renderer.render_expr_list(node.proofinfo.ctrl_ctx.fun_tmpls)
        premises = renderer.render_expr_list(node.proofinfo.premises)
        conclusions = renderer.render_expr_list(node.proofinfo.conclusions)
        local_vars = renderer.render_expr_list(node.proofinfo.local_vars)
        local_premises = renderer.render_expr_list(node.proofinfo.local_premise)
        local_conclusions = renderer.render_expr_list(node.proofinfo.local_conclusion)
        return f"""{node.__class__.__name__}: {node.proofinfo.status}<br>
context_vars: {context_vars}<br>
context_formulas: {context_formulas}<br>
context_pred_tmpls: {context_pred_tmpls}<br>
context_fun_tmpls: {context_fun_tmpls}<br>
premises: {premises}<br>
conclusions: {conclusions}<br>
local_vars: {local_vars}<br>
local_premises: {local_premises}<br>
local_conclusions: {local_conclusions}
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
        self.updated_files: set[str] = set()
        self.resolver: DependencyResolver | None = None
        self.analysis_timer: threading.Timer | None = None
        self.cancel_analysis = threading.Event()

    def run_analysis(self, path: str, save_html: bool):
        self.analyze(path)

        if save_html:
            self.to_html()

    def analyze(self, path: str) -> None:
        self.cancel_analysis.clear()

        if self.resolver is None:
            self.resolver = DependencyResolver()
        else:
            self.resolver.diagnostics = {}
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
                all_units[i].restore_from(old_all_units[i])
                context = all_units[i].context
                start_index = i + 1
            else:
                break

        for i in range(start_index, len(all_units)):
            if self.cancel_analysis.is_set():
                return
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

        self.updated_files.clear()

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
        decl_def_token = self.old_workspace.get_decl_def(ref_name)
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
        node = unit.token_to_node[token.index]
        return lsp.Hover(
            contents=lsp.MarkupContent(
                kind=lsp.MarkupKind.Markdown,
                value=get_hover(node, unit.context)
            )
        )

    @staticmethod
    def find_node_by_line(unit: DeclarationUnit, position: lsp.Position) -> Include | Declaration | Control | None:
        target_line = position.line + 1
        for token in unit.tokens:
            if token.line == target_line and token.index in unit.token_to_control:
                return unit.token_to_control[token.index]
        return None

    def get_proofinfo(self, params: GetProofInfoParams) -> str:
        unit = self.get_unit_at(params.uri, params.position)
        if unit is None:
            return "unit is not found"
        node = self.find_node_by_line(unit, params.position)
        if node is None:
            return "node is not found"
        return HTML_TEMPLATE.format(body=render_proofinfo(node, unit.context))

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

    if ls.analysis_timer is not None:
        ls.analysis_timer.cancel()
    ls.cancel_analysis.set()
    ls.analysis_timer = threading.Timer(0.5, ls.run_analysis, args=[path, False])
    ls.analysis_timer.start()

@server.feature(lsp.TEXT_DOCUMENT_HOVER)
def hovers(ls: ProofLanguageServer, params: lsp.HoverParams) -> lsp.Hover | None:
    return ls.hovers(params)

@server.feature(lsp.TEXT_DOCUMENT_REFERENCES)
def lsp_references(ls: ProofLanguageServer, params: lsp.ReferenceParams) -> list[lsp.Location]:
    return ls.get_references(params)

@server.feature("proof/getProofInfo")
def get_proofinfo(ls: ProofLanguageServer, params: GetProofInfoParams):
    return ls.get_proofinfo(params)

if __name__ == "__main__":
    server.start_io()
