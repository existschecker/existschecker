from dataclasses import dataclass

@dataclass
class Symbol:
    name: str
    args: list[str]

@dataclass
class Forall:
    var: str
    body: object

@dataclass
class Exists:
    var: str
    body: object

@dataclass
class Implies:
    left: object
    right: object

@dataclass
class And:
    left: object
    right: object

@dataclass
class Or:
    left: object
    right: object

@dataclass
class Not:
    body: object

@dataclass
class Iff:
    left: object
    right: object

def parse_primary(tokens, pos):
    tok = tokens[pos]
    if tok.type == "IDENT":
        # 単純なシンボル（引数なし or 2項述語 in）
        # 今は簡単に "x \in y" を処理する
        if pos+2 < len(tokens) and tokens[pos+1].value == "\\in" and tokens[pos+2].type == "IDENT":
            return Symbol("in", [tok.value, tokens[pos+2].value]), pos+3
        return Symbol(tok.value, []), pos+1

    elif tok.type == "LPAREN":
        expr, pos = parse_expr(tokens, pos+1)
        if tokens[pos].type != "RPAREN":
            raise SyntaxError("missing )")
        return expr, pos+1
    
    elif tok.type == "NOT":
        pos += 1
        if pos >= len(tokens) or tokens[pos].type != "LPAREN":
            raise SyntaxError("( is necessary after ¬")
        body, pos = parse_expr(tokens, pos + 1)
        if pos >= len(tokens) or tokens[pos].type != "RPAREN":
            raise SyntaxError("missing )")
        return Not(body), pos+1

    elif tok.type == "FORALL":
        vars = []
        while pos < len(tokens) and tokens[pos].type == "FORALL":
            if pos + 1 > len(tokens) or tokens[pos + 1].type != "IDENT":
                raise SyntaxError("expected variable after ∀")
            vars.append(tokens[pos + 1])
            pos += 2
        if pos >= len(tokens) or tokens[pos].type != "LPAREN":
            raise SyntaxError("( is necessary after ∀-variable")
        body, pos = parse_expr(tokens, pos + 1)
        if pos >= len(tokens) or tokens[pos].type != "RPAREN":
            raise SyntaxError("missing )")
        for var_tok in reversed(vars):
            body = Forall(var_tok.value, body)
        return body, pos + 1

    elif tok.type == "EXISTS":
        vars = []
        while pos < len(tokens) and tokens[pos].type == "EXISTS":
            if pos + 1 >= len(tokens) or tokens[pos + 1].type != "IDENT":
                raise SyntaxError("expected variable after ∃")
            vars.append(tokens[pos + 1])
            pos += 2
        if pos >= len(tokens) or tokens[pos].type != "LPAREN":
            raise SyntaxError("( is necessary after ∃-variable")
        body, pos = parse_expr(tokens, pos + 1)
        if pos >= len(tokens) or tokens[pos].type != "RPAREN":
            raise SyntaxError("missing )")
        for var_tok in reversed(vars):
            body = Exists(var_tok.value, body)
        return body, pos + 1

    else:
        raise SyntaxError(f"Unexpected token: {tok}")

def parse_expr(tokens, pos=0):
    return parse_implies(tokens, pos)

def parse_implies(tokens, pos):
    left, pos = parse_and(tokens, pos)
    while pos < len(tokens) and tokens[pos].type in ("IMPLIES","IFF"):
        op = tokens[pos]
        right, pos = parse_and(tokens, pos+1)
        if op.type == "IMPLIES":
            left = Implies(left, right)
        elif op.type == "IFF":
            left = Iff(left, right)
    return left, pos

def parse_and(tokens, pos):
    left, pos = parse_primary(tokens, pos)
    while pos < len(tokens) and tokens[pos].type in ("AND","OR"):
        op = tokens[pos]
        right, pos = parse_primary(tokens, pos+1)
        if op.type == "AND":
            left = And(left, right)
        elif op.type == "OR":
            left = Or(left, right)
    return left, pos

def pretty_expr(expr):
    if isinstance(expr, Symbol):
        if expr.name == "in":
            return f"{expr.args[0]} \\in {expr.args[1]}"
        return expr.name
    if isinstance(expr, Implies):
        return f"{pretty_expr(expr.left)} \\to {pretty_expr(expr.right)}"
    if isinstance(expr, And):
        return f"{pretty_expr(expr.left)} \\wedge {pretty_expr(expr.right)}"
    if isinstance(expr, Or):
        return f"{pretty_expr(expr.left)} \\vee {pretty_expr(expr.right)}"
    if isinstance(expr, Not):
        return f"\\neg({pretty_expr(expr.body)})"
    if isinstance(expr, Forall):
        return f"\\forall {expr.var}({pretty_expr(expr.body)})"
    if isinstance(expr, Exists):
        return f"\\exists {expr.var}({pretty_expr(expr.body)})"
    raise TypeError(f"Unsupported node type: {type(expr)}")

if __name__ == "__main__":
    from lexer import lex
    src = r"\exists x\exists y(x\in y\vee y\in x)\to\exists x\exists y(\neg(\neg(x\in y)\wedge\neg(y\in x)))"
    tokens = lex(src)
    for t in tokens:
        print(t)
    expr, _ = parse_expr(tokens, 0)
    print(pretty_expr(expr))
