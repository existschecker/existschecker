from lexer import Token, lex
from token_stream import TokenStream
import os
from lsprotocol import types as lsp
from pygls import uris
from ast_types import Context, DeclarationUnit

import sys
import threading

from parser import Parser
from checker import Checker

class DependencyResolver:
    def __init__(self):
        self.dependencies: dict[str, list[str]] = {}
        self.tokens_cache: dict[str, list[Token]] = {}
        self.source_cache: dict[str, str] = {}
        self.visiting_files: set[str] = set()
        self.diagnostics: dict[str, list[lsp.Diagnostic]] = {}

    def add_lsp_error(self, token: Token, message: str):
        uri = uris.from_fs_path(token.file)
        if uri is None:
            return
        diag = lsp.Diagnostic(
            range=lsp.Range(
                start=lsp.Position(line=token.line - 1, character=token.column - 1),
                end=lsp.Position(line=token.end_line - 1, character=token.end_column - 1)
            ),
            message=message,
            source="DependencySolver",
            severity=lsp.DiagnosticSeverity.Error
        )
        if uri not in self.diagnostics:
            self.diagnostics[uri] = []
        self.diagnostics[uri].append(diag)

    def get_content(self, target_path: str, editor_files: dict[str, str] | None = None) -> tuple[str, list[Token]]:
        if editor_files is not None and target_path in editor_files:
            src = editor_files[target_path]
            tokens, _ = lex(target_path, src)
            print(f"editor memory: {os.path.basename(target_path)}", file=sys.stderr)
            return src, tokens
        if target_path in self.source_cache:
            print(f"resolver cache: {os.path.basename(target_path)}", file=sys.stderr)
            return self.source_cache[target_path], self.tokens_cache[target_path]
        f = open(target_path, encoding="utf-8")
        src = f.read()
        f.close()
        tokens, _ = lex(target_path, src)
        print(f"file content: {os.path.basename(target_path)}", file=sys.stderr)
        return src, tokens

    def resolve(self, path: str, editor_files: dict[str, str] | None = None):
        if path in self.dependencies:
            return
        self.visiting_files.add(path)
        src, tokens = self.get_content(path, editor_files)
        self.tokens_cache[path] = tokens
        self.source_cache[path] = src
        dependency: list[str] = []
        stream = TokenStream(tokens)
        while True:
            token = stream.peek()
            if token.type == "INCLUDE":
                stream.consume("INCLUDE")
                token = stream.peek()
                if token.type == "STRING":
                    token = stream.consume("STRING")
                    new_path = os.path.abspath(os.path.join(os.path.dirname(path), token.value))
                    if not os.path.exists(new_path):
                        self.add_lsp_error(token, f"File not found: {new_path}")
                    elif new_path in self.visiting_files:
                        self.add_lsp_error(token, f"Cyclic dependency: {new_path}")
                    else:
                        dependency.append(new_path)
                        self.resolve(new_path, editor_files)
            elif token.type == "EOF":
                break
            else:
                stream.consume(token.type)
        self.visiting_files.remove(path)
        self.dependencies[path] = dependency

    def create_reverse_deps(self) -> dict[str, set[str]]:
        reverse_dependencies: dict[str, set[str]] = {}
        for parent, children in self.dependencies.items():
            for child in children:
                if child not in reverse_dependencies:
                    reverse_dependencies[child] = set()
                reverse_dependencies[child].add(parent)
        return reverse_dependencies

    def get_affected_files(self, start_path: str) -> set[str]:
        reverse_dependencies = self.create_reverse_deps()
        affected = {start_path}
        queue = [start_path]
        while queue:
            current = queue.pop(0)
            parents = reverse_dependencies.get(current, set())
            for p in parents:
                if p not in affected:
                    affected.add(p)
                    queue.append(p)
        return affected

    def get_full_order(self) -> list[str]:
        order: list[str] = []
        visited: set[str] = set()
        all_roots = self.find_all_roots()
        for root in all_roots:
            self.walk(root, visited, order)
        return order

    def get_dependent_order(self, path: str) -> list[str]:
        order: list[str] = []
        visited: set[str] = set()
        self.walk(path, visited, order)
        return order

    def find_all_roots(self) -> list[str]:
        all_files = set(self.dependencies.keys())
        referenced_files: set[str] = set()
        for dependency in self.dependencies.values():
            for file in dependency:
                referenced_files.add(file)
        all_roots = list(all_files - referenced_files)
        return all_roots

    def walk(self, path: str, visited: set[str], order: list[str]):
        if path in visited or path not in self.dependencies:
            return
        visited.add(path)
        for child in self.dependencies[path]:
            self.walk(child, visited, order)
        order.append(path)

def prepare_context(file: str, resolver: DependencyResolver, file_final_contexts: dict[str, Context]) -> Context:
    context = Context.init()
    processed_files: set[str] = set() # avoid diamond dependency
    for dep in resolver.dependencies[file]:
        if dep not in processed_files:
            context.merge(file_final_contexts[dep])
            processed_files.add(dep)
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

if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    resolver = DependencyResolver()
    resolver.resolve(path)
    resolved_files = resolver.get_dependent_order(path)
    for file in resolved_files:
        print(f"file: {file}, length of tokens: {len(resolver.tokens_cache[file])}")
