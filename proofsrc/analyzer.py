from pygls import uris
from lsprotocol import types as lsp
from dataclasses import dataclass
import threading
import re
from enum import IntEnum
from typing import Sequence

from dependency import DependencyResolver
from lexer import KEYWORDS, STRINGS, Token
from ast_types import DeclarationUnit, Workspace, Declaration, Include, Control, Formula, Term, RefFact, FormatError, RenderError, Bottom, DeclarationContextNameSpace, RefStruct, RefStructCondition, StructVar, RefStructPred, Equality, PrimPred, DefPred, DefFunTerm, Var, PredTemplate, DefCon, DefFun, Struct, StructPred, LexedUnit
from resolved_ast_types import ResolvedInclude, ResolvedDeclaration, ResolvedControl, ResolvedFormula, ResolvedTerm, ResolvedRefFact, ResolvedRefStruct, ResolvedRefStructField, ResolvedRefStructCondition, ResolvedStructVar, ResolvedRefEquality, ResolvedRefPrimPred, ResolvedRefDefPred, ResolvedRefDefCon, ResolvedRefDefFun, ResolvedRefDefFunTerm, ResolvedPredLambda, ResolvedFunLambda, ResolvedRefStructPred
from splitter import split
from to_html import Renderer
from parser import Parser
from name_resolver import NameResolver
from elaborator import Elaborator
from checker import Checker
from completion_parser import CompletionVar, CompletionTypedVar, CompletionPredTemplate, CompletionFunTemplate, ExpectedTokenError

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
    STRUCT = 3

@dataclass
class CursorState:
    uri: str
    position: lsp.Position

def get_hover(resolved_node: ResolvedInclude | ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedStructVar | ResolvedRefStructPred, node: Include | Declaration | Control | Formula | Term | RefFact | RefStruct | RefStructCondition | StructVar | RefStructPred) -> str:
    if isinstance(node, (Declaration, Control)):
        return f"{resolved_node.__class__.__name__} -> {node.__class__.__name__}: {node.proofinfo.status}"
    else:
        return f"{resolved_node.__class__.__name__} -> {node.__class__.__name__}"

def render_statement(node: Declaration | Control, decl: DeclarationContextNameSpace) -> str:
    renderer = Renderer(decl)
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

def render_proofinfo(node: Include | Declaration | Control, decl: DeclarationContextNameSpace) -> str:
    if isinstance(node, Declaration):
        statement = render_statement(node, decl)
        return f"""<div class="statement">
    <span class="status-icon">{node.proofinfo.status}</span>
    {statement}
</div>
"""
    elif isinstance(node, Control):
        statement = render_statement(node, decl)
        renderer = Renderer(decl)
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

def prepare_context(file: str, resolver: DependencyResolver, file_final_decls: dict[str, DeclarationContextNameSpace]) -> DeclarationContextNameSpace:
    decl = DeclarationContextNameSpace.init()
    for dep in resolver.dependencies[file]:
        decl = decl.merge(file_final_decls[dep])
    return decl

def restore_cache(lexed_units: list[LexedUnit], old_all_units: list[DeclarationUnit], decl: DeclarationContextNameSpace, file_units: dict[str, list[DeclarationUnit]], file: str) -> tuple[DeclarationContextNameSpace, int]:
    start_index = 0
    for i in range(min(len(lexed_units), len(old_all_units))):
        if lexed_units[i].hash == old_all_units[i].lexed_unit.hash:
            file_units[file].append(old_all_units[i])
            decl = old_all_units[i].decl
            start_index = i + 1
        else:
            break
    return decl, start_index

def analyze_diff(lexed_units: list[LexedUnit], start_index: int, decl: DeclarationContextNameSpace, dependency_resolver: DependencyResolver, file_units: dict[str, list[DeclarationUnit]], file: str, cancel_analysis: threading.Event | None = None) -> DeclarationContextNameSpace | None:
    for i in range(start_index, len(lexed_units)):
        if cancel_analysis is not None and cancel_analysis.is_set():
            return None
        lexed_unit = lexed_units[i]
        parsed_unit = Parser(lexed_unit).parse_unit()
        resolved_unit = NameResolver(lexed_unit, parsed_unit, decl, dependency_resolver, file_units).resolve_unit()
        elaborated_unit = Elaborator(lexed_unit, resolved_unit, decl).elaborate_unit()
        checked_unit, decl = Checker(lexed_unit, elaborated_unit, decl).check_unit()
        file_units[file].append(DeclarationUnit(lexed_unit, parsed_unit, resolved_unit, elaborated_unit, checked_unit, decl))
    return decl

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
        file_final_decls: dict[str, DeclarationContextNameSpace] = {}
        newly_analyzed: set[str] = set()
        for file in order:
            is_affected = file in affected_files
            dependency_changed = any(dep in newly_analyzed for dep in self.resolver.dependencies.get(file, []))
            if not is_affected and not dependency_changed:
                if self.old_workspace is not None and file in self.old_workspace.file_units and len(self.old_workspace.file_units[file]) > 0:
                    file_units[file] = self.old_workspace.file_units[file]
                    file_final_decls[file] = file_units[file][-1].decl
                    continue
            lexed_units = split(file, self.resolver.tokens_cache[file], self.resolver.source_cache[file])
            decl = prepare_context(file, self.resolver, file_final_decls)
            old_all_units = [] if self.old_workspace is None or dependency_changed else self.old_workspace.file_units.get(file, [])
            file_units[file] = []
            decl, start_index = restore_cache(lexed_units, old_all_units, decl, file_units, file)
            if start_index < len(lexed_units):
                newly_analyzed.add(file)
            decl = analyze_diff(lexed_units, start_index, decl, self.resolver, file_units, file, cancel_analysis)
            if decl is None:
                return {}
            file_final_decls[file] = decl

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
                final_diagnostics[uri].extend(unit.parsed_unit.diagnostics)
                final_diagnostics[uri].extend(unit.resolved_unit.diagnostics)
                final_diagnostics[uri].extend(unit.elaborated_unit.diagnostics)
                final_diagnostics[uri].extend(unit.checked_unit.diagnostics)
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
        ref_name = ref_token.value
        if self.old_workspace is None:
            return None
        if self.resolver is None:
            return None
        order = self.resolver.get_dependent_order(unit.lexed_unit.file)
        ref_node = unit.resolved_unit.resolved_token_to_node[ref_token.index]
        if id(ref_node) in unit.resolved_unit.resolved_ctrl_defs:
            def_unit_name, def_node_id = unit.resolved_unit.resolved_ctrl_defs[id(ref_node)]
            ctrl_def_token = self.old_workspace.get_ctrl_def(order, def_unit_name, def_node_id)
            if ctrl_def_token is None:
                return None
            return token_to_location(ctrl_def_token)
        else:
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
        ref_name = ref_token.value
        if self.old_workspace is None:
            return []
        ref_node = unit.resolved_unit.resolved_token_to_node[ref_token.index]
        if self.resolver is None:
            return []
        affected_files = self.resolver.get_affected_files(unit.lexed_unit.file)
        if id(ref_node) in unit.resolved_unit.resolved_ctrl_defs:
            def_unit_name, def_node_id = unit.resolved_unit.resolved_ctrl_defs[id(ref_node)]
            ctrl_ref_tokens = self.old_workspace.get_ctrl_refs(affected_files, def_unit_name, def_node_id)
            return tokens_to_locations(ctrl_ref_tokens)
        else:
            decl_ref_tokens = self.old_workspace.get_all_decl_refs(ref_name, affected_files)
            return tokens_to_locations(decl_ref_tokens)

    def resolve_access_type(self, type_name: str, names: tuple[str, ...], order: list[str]) -> str | None:
        if len(names) == 0:
            return type_name
        struct = self.find_struct(type_name, order)
        if struct is None:
            return None
        name = names[0]
        field = next((field for field in struct.fields if field.name == name), None)
        if not isinstance(field, StructVar):
            return None
        return self.resolve_access_type(field.ref_struct.name, names[1:], order)

    def find_struct(self, type_name: str, order: list[str]) -> Struct | None:
        for path in order:
            if self.old_workspace is not None:
                for unit in self.old_workspace.file_units[path]:
                    if isinstance(unit.elaborated_unit.ast, Struct) and unit.elaborated_unit.ast.name == type_name:
                        return unit.elaborated_unit.ast
        return None

    def find_struct_predicate(self, type_name: str, order: list[str]) -> list[StructPred]:
        preds: list[StructPred] = []
        for path in order:
            if self.old_workspace is not None:
                for unit in self.old_workspace.file_units[path]:
                    if isinstance(unit.elaborated_unit.ast, StructPred) and unit.elaborated_unit.ast.name.startswith(f"{type_name}."):
                        preds.append(unit.elaborated_unit.ast)
        return preds

    def get_completion_expected(self, params: lsp.CompletionParams, source: str) -> list[tuple[str, lsp.CompletionItemKind]]:
        path = uris.to_fs_path(params.text_document.uri)
        if path is None:
            return []
        from lexer import lex
        tokens = lex(path, source)
        units = split(path, tokens, source)
        found_unit = None
        for unit in units:
            if self.is_in_range(params.position, unit):
                found_unit = unit
                break
        if found_unit is None:
            return []
        from completion_parser import CompletionParser
        line = params.position.line + 1
        column = params.position.character + 1
        cursor_tokens: list[Token] = []
        for token in found_unit.tokens:
            if token.end_line < line or (token.end_line == line and token.end_column < column) or (token.end_line == line and token.end_column == column and token.type != "IDENT"):
                cursor_tokens.append(token)
        cursor_tokens.append(Token("EOF", "", path, 0, 0, 0, 0, 0))
        e = CompletionParser(cursor_tokens).parse_unit()
        if e is None:
            return []
        candidates: list[tuple[str, lsp.CompletionItemKind]] = []
        for expected_type in e.expected_types:
            if expected_type.lower() in KEYWORDS:
                candidates.append((expected_type.lower(), lsp.CompletionItemKind.Keyword))
            elif expected_type in STRINGS.values():
                found_key = next(k for k, v in STRINGS.items() if v == expected_type)
                candidates.append((found_key, lsp.CompletionItemKind.Operator))
            elif expected_type == "IDENT":
                if e.access is not None:
                    current_unit = self.get_unit_at(params.text_document.uri, params.position)
                    if current_unit is not None:
                        name = e.access.names[0]
                        if e.context is not None:
                            type_name = next((item.type_name for item in e.context.form if isinstance(item, CompletionTypedVar) and item.name == name), None)
                            if type_name is None:
                                type_name = next((item.type_name for item in e.context.ctrl if isinstance(item, CompletionTypedVar) and item.name == name), None)
                                if type_name is None:
                                    return []
                            if self.resolver is not None:
                                order = self.resolver.get_dependent_order(current_unit.lexed_unit.file)
                                type_name = self.resolve_access_type(type_name, e.access.names[1:], order)
                                if type_name is not None:
                                    struct = self.find_struct(type_name, order)
                                    if struct is not None:
                                        candidates.extend((field.name, lsp.CompletionItemKind.Variable) for field in struct.fields)
                                        candidates.extend((condition.name, lsp.CompletionItemKind.Function) for condition in struct.conditions)
                                        preds = self.find_struct_predicate(type_name, order)
                                        candidates.extend((pred.ref.name, lsp.CompletionItemKind.Variable) for pred in preds)
                else:
                    args = self.get_signature_help_args(e, path)
                    if e.call is None:
                        arg_types = (CompletionVar, CompletionPredTemplate, CompletionFunTemplate)
                    elif e.call.argindex < len(args):
                        arg_types = (type(args[e.call.argindex]),)
                    else:
                        arg_types = ()
                    if e.context is not None:
                        for item in e.context.form + e.context.ctrl:
                            if isinstance(item, CompletionVar) and CompletionVar in arg_types:
                                candidates.append((item.name, lsp.CompletionItemKind.Variable))
                            if isinstance(item, CompletionPredTemplate) and CompletionPredTemplate in arg_types:
                                candidates.append((item.name, lsp.CompletionItemKind.Variable))
                            if isinstance(item, CompletionFunTemplate) and (CompletionVar in arg_types or CompletionFunTemplate in arg_types):
                                candidates.append((item.name, lsp.CompletionItemKind.Variable))
                    decl_types: list[type] = []
                    for arg_type in arg_types:
                        if arg_type is CompletionVar:
                            decl_types.extend([DefCon, DefFun, DefFunTerm])
                        elif arg_type is CompletionPredTemplate:
                            decl_types.extend([PrimPred, DefPred, Equality])
                        else:
                            decl_types.extend([DefFun, DefFunTerm])
                    if self.old_workspace is not None and self.resolver is not None:
                        current_unit = self.get_unit_at(params.text_document.uri, params.position)
                        if current_unit is not None:
                            order = self.resolver.get_dependent_order(current_unit.lexed_unit.file)
                            for path in order:
                                for unit in self.old_workspace.file_units[path]:
                                    if isinstance(unit.elaborated_unit.ast, Declaration) and isinstance(unit.elaborated_unit.ast, e.decl_types) and isinstance(unit.elaborated_unit.ast, tuple(decl_types)):
                                        candidates.append((unit.elaborated_unit.ast.name, lsp.CompletionItemKind.Function))
        return candidates

    def get_completion(self, params: lsp.CompletionParams, source: str) -> list[lsp.CompletionItem]:
        candidates = self.get_completion_expected(params, source)
        match = re.search(r"\\(\w+)?$", source.splitlines()[params.position.line][:params.position.character])
        typing_backslash = match is not None
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

    def get_signature_help_args(self, e: ExpectedTokenError, path: str) -> tuple[CompletionVar | CompletionPredTemplate | CompletionFunTemplate, ...]:
        if e.call is None:
            return ()
        if len(e.call.callee.names) > 1:
            if self.resolver is None or e.context is None:
                return ()
            order = self.resolver.get_dependent_order(path)
            root = e.call.callee.names[0]
            type_name = next((item.type_name for item in e.context.form + e.context.ctrl if isinstance(item, CompletionTypedVar) and item.name == root), None)
            if type_name is None:
                return ()
            type_name = self.resolve_access_type(type_name, e.call.callee.names[1:-1], order)
            if type_name is None:
                return ()
            name = e.call.callee.names[-1]
            for pred in self.find_struct_predicate(type_name, order):
                if pred.ref.name == name:
                    return tuple(CompletionVar(arg.name) for arg in pred.args)
            return ()
        elif len(e.call.callee.names) == 1:
            name = e.call.callee.names[0]
            if e.context is not None:
                found_item = None
                for item in e.context.form:
                    if isinstance(item, (CompletionPredTemplate, CompletionFunTemplate)):
                        if item.name == name:
                            found_item = item
                if found_item is not None:
                    return tuple(CompletionVar(f"x{i}") for i in range(1, found_item.arity + 1))
                found_item = None
                for item in e.context.ctrl:
                    if isinstance(item, (CompletionPredTemplate, CompletionFunTemplate)):
                        if item.name == name:
                            found_item = item
                if found_item is not None:
                    return tuple(CompletionVar(f"x{i}") for i in range(1, found_item.arity + 1))
            if self.resolver is None:
                return ()
            order = self.resolver.get_dependent_order(path)
            if self.old_workspace is None:
                return ()
            def_ast = None
            for dep_path in order:
                for unit in self.old_workspace.file_units[dep_path]:
                    if isinstance(unit.elaborated_unit.ast, (Equality, PrimPred, DefPred, DefFunTerm)) and unit.elaborated_unit.ast.name == name:
                        def_ast = unit.elaborated_unit.ast
            if isinstance(def_ast, Equality):
                return (CompletionVar("x"), CompletionVar("y"))
            elif isinstance(def_ast, PrimPred):
                return tuple(CompletionVar(f"x{i}") for i in range(1, def_ast.arity + 1))
            elif isinstance(def_ast, (DefPred, DefFunTerm)):
                args: list[CompletionVar | CompletionPredTemplate | CompletionFunTemplate] = []
                for arg in def_ast.args:
                    if isinstance(arg, Var):
                        args.append(CompletionVar(arg.name))
                    elif isinstance(arg, PredTemplate):
                        args.append(CompletionPredTemplate(arg.name, arg.arity))
                    else:
                        args.append(CompletionFunTemplate(arg.name, arg.arity))
                return tuple(args)
            else:
                return ()
        else:
            return ()

    def get_signature_help(self, params: lsp.SignatureHelpParams, source: str) -> lsp.SignatureHelp | None:
        path = uris.to_fs_path(params.text_document.uri)
        if path is None:
            return None
        from lexer import lex
        tokens = lex(path, source)
        lexer_units = split(path, tokens, source)
        found_index = None
        found_unit = None
        for index, lexer_unit in enumerate(lexer_units):
            if self.is_in_range(params.position, lexer_unit):
                found_index = index
                found_unit = lexer_unit
                break
        if found_index is None or found_unit is None:
            return None
        from completion_parser import CompletionParser
        line = params.position.line + 1
        column = params.position.character + 1
        cursor_tokens: list[Token] = []
        for token in found_unit.tokens:
            if token.end_line < line or (token.end_line == line and token.end_column < column) or (token.end_line == line and token.end_column == column and token.type != "IDENT"):
                cursor_tokens.append(token)
        cursor_tokens.append(Token("EOF", "", path, 0, 0, 0, 0, 0))
        e = CompletionParser(cursor_tokens).parse_unit()
        if e is None or e.call is None:
            return None
        name = ".".join(e.call.callee.names)
        args = self.get_signature_help_args(e, path)
        args_str: list[str] = []
        for arg in args:
            if isinstance(arg, CompletionVar):
                args_str.append(arg.name)
            elif isinstance(arg, CompletionPredTemplate):
                args_str.append(f"predicate {arg.name}[{arg.arity}]")
            else:
                args_str.append(f"function {arg.name}[{arg.arity}]")
        callee = name + "(" + ", ".join(args_str) + ")"
        parameters = [lsp.ParameterInformation(label=arg) for arg in (args_str)]
        return lsp.SignatureHelp(
            signatures=[
                lsp.SignatureInformation(
                    label=callee,
                    parameters=parameters
                )
            ],
            active_signature=0,
            active_parameter=e.call.argindex
        )

    @staticmethod
    def find_token_at(unit: DeclarationUnit, pos: lsp.Position) -> Token | None:
        target_line = pos.line + 1
        target_column = pos.character + 1
        candidate = None
        for token in unit.lexed_unit.tokens[:-1]:
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
    def is_in_range(pos: lsp.Position, lexer_unit: LexedUnit) -> bool:
        target_line = pos.line + 1
        target_column = pos.character + 1
        start_token = lexer_unit.tokens[0]
        end_token = lexer_unit.tokens[-1]
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
            if target_line < unit.lexed_unit.tokens[0].line:
                return last_unit
            if self.is_in_range(position, unit.lexed_unit):
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
        if token.index not in unit.resolved_unit.resolved_token_to_node:
            return None
        resolved_node = unit.resolved_unit.resolved_token_to_node[token.index]
        if token.index not in unit.elaborated_unit.token_to_node:
            return None
        node = unit.elaborated_unit.token_to_node[token.index]
        return lsp.Hover(
            contents=lsp.MarkupContent(
                kind=lsp.MarkupKind.Markdown,
                value=get_hover(resolved_node, node)
            )
        )

    @staticmethod
    def find_node_by_line(unit: DeclarationUnit, position: lsp.Position) -> Control | None:
        target_line = position.line + 1
        last_node = None
        for token in unit.lexed_unit.tokens:
            if token.line < target_line and token.index in unit.elaborated_unit.token_to_control:
                last_node = unit.elaborated_unit.token_to_control[token.index]
            elif token.line == target_line and token.index in unit.elaborated_unit.token_to_control:
                return unit.elaborated_unit.token_to_control[token.index]
        return last_node

    def get_proofinfo(self, current_cursor: CursorState | None) -> str:
        if current_cursor is None:
            return "current_cursor is not found"
        unit = self.get_unit_at(current_cursor.uri, current_cursor.position)
        if unit is None:
            return "unit is not found"
        if unit.elaborated_unit.ast is None:
            return "ast is not found"
        node = self.find_node_by_line(unit, current_cursor.position)
        path = uris.from_fs_path(current_cursor.uri)
        if path is None:
            return "path is not found"
        decl_info = render_proofinfo(unit.elaborated_unit.ast, unit.decl)
        ctrl_info = "" if node is None else render_proofinfo(node, unit.decl)
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
            for index, node in unit.resolved_unit.resolved_token_to_node.items():
                token = unit.lexed_unit.tokens[index]
                if isinstance(node, (ResolvedRefFact, ResolvedRefStructCondition)):
                    t_type = TokenType.FUNCTION
                elif isinstance(node, (ResolvedRefEquality, ResolvedRefPrimPred, ResolvedRefDefPred, ResolvedRefDefCon, ResolvedRefDefFun, ResolvedRefDefFunTerm)):
                    t_type = TokenType.CONSTANT
                elif isinstance(node, ResolvedRefStruct):
                    t_type = TokenType.STRUCT
                elif isinstance(node, (ResolvedTerm, ResolvedStructVar, ResolvedRefStructField, ResolvedRefStructPred)) and not isinstance(node, ResolvedPredLambda) and not isinstance(node, ResolvedFunLambda):
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
