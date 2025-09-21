from dataclasses import dataclass
from typing import List, Union
from lexer import Token, lex
from expr_parser import parse_expr, Symbol, Forall, Exists, And, Or, Implies, Iff

# === DSL ノード定義 ===
@dataclass
class Theorem:
    name: str
    conclusion: object
    proof: list

@dataclass
class Conclude:
    conclusion: object   # Expr AST

@dataclass
class Assume:
    premise: object      # Expr AST
    conclusion: object   # Expr AST
    body: list

@dataclass
class Any:
    vars: List[str]
    conclusion: object
    body: list

@dataclass
class Definition:
    name: str
    body: str  # TODO: 式パーサーに統合可能


# === パーサー本体 ===
class Parser:
    def __init__(self, tokens: List[Token]):
        self.tokens = tokens
        self.pos = 0

    def peek(self):
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def consume(self, expected_type=None):
        tok = self.peek()
        if tok is None:
            raise SyntaxError("Unexpected EOF")
        if expected_type and tok.type != expected_type:
            raise SyntaxError(f"Expected {expected_type}, got {tok.type}")
        self.pos += 1
        return tok

    def parse_file(self):
        ast = []
        while self.peek():
            tok = self.peek()
            if tok.type == "THEOREM":
                ast.append(self.parse_theorem())
            elif tok.type == "DEFINITION":
                ast.append(self.parse_definition())
            else:
                raise SyntaxError(f"Unexpected token {tok}")
        return ast

    def parse_theorem(self):
        self.consume("THEOREM")
        name = self.consume("IDENT").value
        conclusion, self.pos = parse_expr(self.tokens, self.pos)
        self.consume("LBRACE")
        proof = self.parse_block()
        self.consume("RBRACE")
        return Theorem(name=name, conclusion=conclusion, proof=proof)

    def parse_conclude(self):
        self.consume("CONCLUDE")
        # conclusion 部分の式を読む
        conclusion, self.pos = parse_expr(self.tokens, self.pos)
        return Conclude(conclusion=conclusion)

    def parse_block(self):
        body = []
        while True:
            tok = self.peek()
            if not tok or tok.type == "RBRACE":
                break
            if tok.type == "ANY":
                body.append(self.parse_any())
            elif tok.type == "ASSUME":
                body.append(self.parse_assume())
            elif tok.type == "CONCLUDE":
                body.append(self.parse_conclude())
            else:
                raise SyntaxError(f"Unexpected token in block: {tok}")
        return body

    def parse_any(self):
        self.consume("ANY")
        vars_ = []
        while True:
            tok = self.consume("IDENT")
            vars_.append(tok.value)
            if self.peek().type == "COMMA":
                self.consume("COMMA")
                continue
            break
        self.consume("CONCLUDE")
        conclusion, self.pos = parse_expr(self.tokens, self.pos)
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Any(vars=vars_, conclusion=conclusion, body=body)

    def parse_assume(self):
        self.consume("ASSUME")
        premise, self.pos = parse_expr(self.tokens, self.pos)
        self.consume("CONCLUDE")
        conclusion, self.pos = parse_expr(self.tokens, self.pos)
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Assume(premise=premise, conclusion=conclusion, body=body)

    def parse_definition(self):
        self.consume("DEFINITION")
        name = self.consume("IDENT").value
        self.consume("LBRACE")
        # とりあえず文字列で保持（後で expr_parser に流せるよう拡張）
        body_tok = []
        while self.peek() and self.peek().type != "RBRACE":
            body_tok.append(self.consume())
        self.consume("RBRACE")
        return Definition(name=name, body=" ".join(t.value for t in body_tok))


# === ヘルパー関数 ===
def parse_file_from_source(src: str):
    tokens = lex(src)
    parser = Parser(tokens)
    return parser.parse_file()

def pretty(node, indent=0):
    sp = "  " * indent  # インデント幅2スペース
    if isinstance(node, Theorem):
        print(f"{sp}Theorem {node.name}:")
        pretty(node.proof, indent + 1)

    elif isinstance(node, Conclude):
        print(f"{sp}Conclude {node.conclusion}")
        for stmt in node.body:
            pretty(stmt, indent + 1)

    elif isinstance(node, Any):
        print(f"{sp}Any {', '.join(node.vars)}")
        print(f"{sp}Conclude {node.conclusion}")
        for stmt in node.body:
            pretty(stmt, indent + 1)

    elif isinstance(node, Assume):
        print(f"{sp}Assume {node.premise}")
        print(f"{sp}Conclude {node.conclusion}")
        for stmt in node.body:
            pretty(stmt, indent + 1)

    # elif isinstance(node, By):
    #     print(f"{sp}By {node.target} by {node.definition} using {node.using}")

    elif isinstance(node, Definition):
        print(f"{sp}Definition {node.name}: {node.body}")

    else:
        print(f"{sp}{node}")

if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    f = open(path)
    src = f.read()
    f.close()
    ast = parse_file_from_source(src)
    for node in ast:
        pretty(node)
