from dataclasses import dataclass
from typing import List, Union
import re

# 論理式のAST
class Expr: pass

@dataclass
class Symbol(Expr):
    name: str
    args: list[str]

@dataclass
class Implies(Expr):
    left: Expr
    right: Expr

@dataclass
class And(Expr):
    left: Expr
    right: Expr

@dataclass
class Forall(Expr):
    var: str
    body: Expr
    
@dataclass
class Definition:
    name: str
    body: str

@dataclass
class By:
    target: str
    definition: str
    using: List[str]

@dataclass
class Assume:
    premise: Expr
    conclusion: Expr
    body: list

@dataclass
class Any:
    vars: List[str]
    body: List[Union[Assume, 'Any', By]]

@dataclass
class Conclude:
    conclusion: Expr
    body: list

@dataclass
class Theorem:
    name: str
    proof: Conclude

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
        for stmt in node.body:
            pretty(stmt, indent + 1)

    elif isinstance(node, Assume):
        print(f"{sp}Assume {node.premise}")
        print(f"{sp}Conclude {node.conclusion}")
        for stmt in node.body:
            pretty(stmt, indent + 1)

    elif isinstance(node, By):
        print(f"{sp}By {node.target} by {node.definition} using {node.using}")

    elif isinstance(node, Definition):
        print(f"{sp}Definition {node.name}: {node.body}")

    else:
        print(f"{sp}{node}")

def parse_expr(text: str) -> Expr:
    text = text.strip()

    # 1. 量化子
    if text.startswith("\\forall"):
        m = re.match(r"\\forall\s*([a-zA-Z_][a-zA-Z0-9_]*)(.*)", text)
        if not m:
            raise ValueError(f"Malformed forall: {text}")
        var, rest = m.groups()
        return Forall(var, parse_expr(rest.strip()))

    # 2. 括弧に包まれている場合
    if text.startswith("(") and text.endswith(")"):
        # 括弧の対応が正しいか確認して外す
        depth = 0
        for i, ch in enumerate(text):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i != len(text) - 1:
                    break
        else:
            # 正しく括弧で囲まれていた
            return parse_expr(text[1:-1])

    # 3. 含意 (右結合)
    depth = 0
    i = len(text) - 1
    while i >= 0:
        if text[i] == ")":
            depth += 1
        elif text[i] == "(":
            depth -= 1
        elif text.startswith("\\to", i) and depth == 0:
            left = text[:i].strip()
            right = text[i+3:].strip()  # len("\\to") == 3
            return Implies(parse_expr(left), parse_expr(right))
        i -= 1

    # 4. 連言 (左結合)
    depth = 0
    i = 0
    while i < len(text):
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
        elif text.startswith("\\wedge", i) and depth == 0:
            left = text[:i].strip()
            right = text[i+6:].strip()  # len("\\wedge") == 6
            return And(parse_expr(left), parse_expr(right))
        i += 1

    # 5. 原子式
    # 特別扱い: "x \in y"
    m = re.match(r"^([a-zA-Z_][a-zA-Z0-9_]*)\\in([a-zA-Z_][a-zA-Z0-9_]*)$", text.replace(" ", ""))
    if m:
        left, right = m.groups()
        return Symbol("in", [left, right])

    # 将来的な拡張に備えて、その他は定数や変数として Symbol にする
    return Symbol(text, [])

# --- パース関数（暫定・前に作ったものを流用して拡張）

def parse_by(line: str) -> By:
    lhs, rest = line.split(" by ", 1)
    target = lhs.strip()
    definition, rest = rest.split(" using ", 1)
    definition = definition.strip()
    rest = rest.strip()
    if rest.startswith("(") and rest.endswith(")"):
        rest = rest[1:-1]
    using = [u.strip() for u in rest.split(",")]
    return By(target=target, definition=definition, using=using)

def parse_block(lines, i=0):
    """再帰的にany/assumeブロックを読む"""
    body = []
    while i < len(lines):
        line = lines[i].strip()
        if line.startswith("any "):
            # "any x, y {" のパターンにマッチ
            m = re.match(r"any\s+([^{}]+)\{?", line)
            if not m:
                raise ValueError(f"Invalid any-syntax: {line}")
            vars_text = m.group(1)
            vars_ = [v.strip() for v in vars_text.split(",")]

            # 次の行以降をパース
            sub_body, i = parse_block(lines, i+1)
            body.append(Any(vars=vars_, body=sub_body))
        elif line.startswith("assume "):
            inside = line[7:]
            premise, rest = inside.split("conclude", 1)
            conclusion, _ = rest.split("{", 1)
            premise = premise.strip()
            conclusion = conclusion.strip()
            sub_body, i = parse_block(lines, i+1)
            body.append(
                Assume(
                    premise=parse_expr(premise),
                    conclusion=parse_expr(conclusion),
                    body=sub_body
                )
            )
        elif " by " in line:
            body.append(parse_by(line))
            i += 1
        elif line.startswith("}"):
            return body, i+1
        else:
            i += 1
    return body, i

def parse_file(path: str):
    with open(path, encoding="utf-8") as f:
        content = f.read()

    blocks = content.split("\n\n")
    ast = []

    for block in blocks:
        block = block.strip()
        if block.startswith("definition"):
            header, body = block.split("{", 1)
            name = header.split()[1].strip()
            body = body.rsplit("}", 1)[0].strip()
            ast.append(Definition(name=name, body=body))

        elif block.startswith("theorem"):
            header, body = block.split("{", 1)

            # theorem の名前を取る
            name = header.split()[1].split("(")[0].strip()

            # theorem の本文部分（最後の } を除去）
            body = body.rsplit("}", 1)[0].strip()
            lines = [l.strip() for l in body.splitlines() if l.strip()]

            # 最初の行は "conclude ..." のはず
            if lines[0].startswith("conclude"):
                # conclude の conclusion とブロック本体を取り出す
                rest = lines[0][len("conclude"):].strip()
                if rest.endswith("{"):
                    rest = rest[:-1].strip()
                conclusion = rest

                # conclude の中身（indent の次の行から最後の } まで）
                conclude_lines = lines[1:-1]
                body_nodes, _ = parse_block(conclude_lines)

                proof = Conclude(conclusion=parse_expr(conclusion), body=body_nodes)
                ast.append(Theorem(name=name, proof=proof))
    return ast
