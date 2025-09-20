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

    elif tok.type == "FORALL":
        var_tok = tokens[pos+1]
        if var_tok.type != "IDENT":
            raise SyntaxError("expected variable after ∀")
        body, pos2 = parse_expr(tokens, pos+2)
        return Forall(var_tok.value, body), pos2

    elif tok.type == "EXISTS":
        var_tok = tokens[pos+1]
        if var_tok.type != "IDENT":
            raise SyntaxError("expected variable after ∃")
        body, pos2 = parse_expr(tokens, pos+2)
        return Exists(var_tok.value, body), pos2

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

if __name__ == "__main__":
    from lexer import lex
    src = r"\forall x\forall y(x\in y\to x\in y)"
    tokens = lex(src)
    for t in tokens:
        print(t)
    expr, _ = parse_expr(tokens, 0)
    print(expr)
