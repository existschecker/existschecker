from typing import List, Union
from ast_types import Context, Theorem, Any, Assume, Check, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, Symbol, And, Or, Implies, Forall, Exists, Not, Bottom, Atom, Definition, Iff, pretty, pretty_expr
from lexer import Token, lex
from checker import check_proof

import logging
logger = logging.getLogger(__name__)

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
        self.declared_atoms = {}  # name -> Atom
        self.declared_definitions = {}
        while self.peek():
            tok = self.peek()
            if tok.type == "ATOM":
                self.parse_atom()
            elif tok.type == "THEOREM":
                theorem = self.parse_theorem()
                formulas = []
                for definition in self.declared_definitions.values():
                    formulas.append(definition.formula)
                logger.debug("[Context] " + ", ".join(pretty_expr(formula) for formula in formulas))
                if check_proof(theorem, Context(formulas, False)):
                    print(f"[{theorem.name}] proved")
                else:
                    print(f"❌ [{theorem.name}] not proved")
            elif tok.type == "DEFINITION":
                self.parse_definition()
            else:
                raise SyntaxError(f"Unexpected token {tok}")

    def parse_atom(self):
        self.consume("ATOM")
        tok = self.peek()
        if tok.type == "PREDICATE":
            self.consume(tok.type)
            name = self.consume("IDENT").value
            self.consume("ARITY")
            arity = int(self.consume("NUMBER").value)
            atom = Atom(type=tok.type, name=name, arity=arity)
            self.declared_atoms[name] = atom
        else:
            raise SyntaxError(f"Unexpected token {tok}")

    def parse_theorem(self):
        self.consume("THEOREM")
        name = self.consume("IDENT").value
        conclusion = self.parse_expr()
        self.consume("LBRACE")
        proof = self.parse_block()
        self.consume("RBRACE")
        return Theorem(name=name, conclusion=conclusion, proof=proof)

    def parse_check(self):
        self.consume("CHECK")
        # conclusion 部分の式を読む
        conclusion = self.parse_expr()
        return Check(conclusion=conclusion)

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
            elif tok.type == "DIVIDE":
                body.append(self.parse_divide())
            elif tok.type == "CHECK":
                body.append(self.parse_check())
            elif tok.type == "SOME":
                body.append(self.parse_some())
            elif tok.type == "DENY":
                body.append(self.parse_deny())
            elif tok.type == "CONTRADICT":
                body.append(self.parse_contradict())
            elif tok.type == "EXPLODE":
                body.append(self.parse_explode())
            elif tok.type == "APPLY":
                body.append(self.parse_apply())
            elif tok.type == "LIFT":
                body.append(self.parse_lift())
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
        conclusion = self.parse_expr()
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Any(vars=vars_, conclusion=conclusion, body=body)

    def parse_assume(self):
        self.consume("ASSUME")
        premise = self.parse_expr()
        self.consume("CONCLUDE")
        conclusion = self.parse_expr()
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Assume(premise=premise, conclusion=conclusion, body=body)
    
    def parse_divide(self):
        self.consume("DIVIDE")
        fact = self.parse_expr()
        self.consume("CONCLUDE")
        conclusion = self.parse_expr()
        cases = []
        while self.peek().type == "CASE":
            cases.append(self.parse_case(conclusion))
        if len(cases) < 2:
            raise SyntaxError("At least two cases are necessary")
        return Divide(fact=fact, conclusion=conclusion, cases=cases)
    
    def parse_case(self, conclusion):
        self.consume("CASE")
        premise = self.parse_expr()
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Case(premise=premise, conclusion=conclusion, body=body)
    
    def parse_some(self):
        self.consume("SOME")
        vars_ = []
        while True:
            tok = self.consume("IDENT")
            vars_.append(tok.value)
            if self.peek().type == "COMMA":
                self.consume("COMMA")
                continue
            break
        self.consume("SUCH")
        premise = self.parse_expr()
        self.consume("CONCLUDE")
        conclusion = self.parse_expr()
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Some(vars=vars_, premise=premise, conclusion=conclusion, body=body)
    
    def parse_deny(self):
        self.consume("DENY")
        premise = self.parse_expr()
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Deny(premise=premise, body=body)
    
    def parse_contradict(self):
        self.consume("CONTRADICT")
        contradiction = self.parse_expr()
        return Contradict(contradiction=contradiction)
    
    def parse_explode(self):
        self.consume("EXPLODE")
        conclusion = self.parse_expr()
        return Explode(conclusion=conclusion)
    
    def parse_apply(self):
        self.consume("APPLY")
        fact = self.parse_expr()
        if self.peek().type == "FOR":
            self.consume("FOR")
            env = {}
            while True:
                bound = self.consume("IDENT").value
                self.consume("COLON")
                free = self.consume("IDENT").value
                env[bound] = free
                if self.peek().type == "COMMA":
                    self.consume("COMMA")
                    continue
                break
        else:
            env = None
        if self.peek().type == "WITH":
            self.consume("WITH")
            premise = self.parse_expr()
        else:
            premise = None
        if env is None and premise is None:
            raise SyntaxError("APPLY needs FOR or WITH")
        self.consume("CONCLUDE")
        conclusion = self.parse_expr()
        return Apply(fact=fact, env=env, premise=premise, conclusion=conclusion)
    
    def parse_lift(self):
        self.consume("LIFT")
        fact = self.parse_expr()
        self.consume("FOR")
        env = {}
        while True:
            bound = self.consume("IDENT").value
            self.consume("COLON")
            free = self.consume("IDENT").value
            env[bound] = free
            if self.peek().type == "COMMA":
                self.consume("COMMA")
                continue
            break
        self.consume("CONCLUDE")
        conclusion = self.parse_expr()
        return Lift(fact=fact, env=env, conclusion=conclusion)

    def parse_definition(self):
        self.consume("DEFINITION")
        tok = self.peek()
        if tok.type == "PREDICATE":
            self.consume("PREDICATE")
            name = self.consume("IDENT").value
            self.consume("ARITY")
            arity = int(self.consume("NUMBER").value)
            self.declared_definitions[name] = Definition(type=tok.type, name=name, arity=arity, formula=None)
            formula = self.parse_expr()
            definition = Definition(type=tok.type, name=name, arity=arity, formula=formula)
            self.declared_definitions[name] = definition
        else:
            raise SyntaxError(f"Unexpected token {tok}")

    def parse_primary(self):
        tok = self.peek()
        if tok.type == "IDENT":
            name = self.consume("IDENT").value
            if name in self.declared_atoms:
                arity = self.declared_atoms[name].arity
            elif name in self.declared_definitions:
                arity = self.declared_definitions[name].arity
            else:
                raise SyntaxError("atom is not found")
            self.consume("LPAREN")
            args = [self.consume("IDENT").value]
            while self.peek().type == "COMMA":
                self.consume("COMMA")
                args.append(self.consume("IDENT").value)
            if len(args) != arity:
                raise SyntaxError("arity is different")
            self.consume("RPAREN")
            return Symbol(name, args)

        elif tok.type == "LPAREN":
            self.consume("LPAREN")
            expr = self.parse_expr()
            self.consume("RPAREN")
            return expr
        
        elif tok.type == "NOT":
            self.consume("NOT")
            self.consume("LPAREN")
            body = self.parse_recursion()
            self.consume("RPAREN")
            return Not(body)

        elif tok.type == "FORALL":
            vars = []
            while self.peek().type == "FORALL":
                self.consume("FORALL")
                vars.append(self.consume("IDENT").value)
            self.consume("LPAREN")
            body = self.parse_recursion()
            self.consume("RPAREN")
            for var in reversed(vars):
                body = Forall(var, body)
            return body

        elif tok.type == "EXISTS":
            vars = []
            while self.peek().type == "EXISTS":
                self.consume("EXISTS")
                vars.append(self.consume("IDENT").value)
            self.consume("LPAREN")
            body = self.parse_recursion()
            self.consume("RPAREN")
            for var in reversed(vars):
                body = Exists(var, body)
            return body

        else:
            raise SyntaxError(f"Unexpected token: {tok}")

    def parse_expr(self):
        if self.peek().type == "BOT":
            self.consume("BOT")
            return Bottom()
        else:
            return self.parse_recursion()

    def parse_recursion(self):
        return self.parse_implies()

    def parse_implies(self):
        left = self.parse_and()
        while self.peek().type in ("IMPLIES", "IFF"):
            op = self.peek().type
            self.consume(op)
            right = self.parse_and()
            if op == "IMPLIES":
                left = Implies(left, right)
            elif op == "IFF":
                left = Iff(left, right)
        return left

    def parse_and(self):
        left = self.parse_primary()
        while self.peek().type in ("AND", "OR"):
            op = self.peek().type
            self.consume(op)
            right = self.parse_primary()
            if op == "AND":
                left = And(left, right)
            elif op == "OR":
                left = Or(left, right)
        return left

# === ヘルパー関数 ===
def parse_file_from_source(src: str):
    tokens = lex(src)
    parser = Parser(tokens)
    parser.parse_file()

if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    f = open(path)
    src = f.read()
    f.close()

    import os
    import logging

    logger = logging.getLogger("proof")
    logger.setLevel(logging.DEBUG)

    # 標準出力用ハンドラ
    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.DEBUG)

    # ファイル出力用ハンドラ
    file_handler = logging.FileHandler(os.path.join("logs", os.path.basename(path).replace(".proof", ".log")), mode='w', encoding='utf-8')
    file_handler.setLevel(logging.DEBUG)

    # 共通フォーマット
    formatter = logging.Formatter("%(message)s")
    console_handler.setFormatter(formatter)
    file_handler.setFormatter(formatter)

    # ハンドラ登録
    logger.addHandler(console_handler)
    logger.addHandler(file_handler)

    parse_file_from_source(src)
