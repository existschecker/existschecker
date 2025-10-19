from ast_types import Context, Theorem, Any, Assume, Check, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, Symbol, And, Or, Implies, Forall, Exists, Not, Bottom, PrimPred, DefPred, Iff, Axiom, Invoke, Expand, ExistsUniq, DefCon, Pad, Split, Connect, DefConExist, DefConUniq, DefFun, DefFunExist, DefFunUniq, Compound, Fun, Con, Var, DefFunTerm, Equality, Substitute, Characterize, Show, Pred
from lexer import Token, lex
from logic_utils import collect_quantifier_vars

import logging
logger = logging.getLogger("proof")

# === パーサー本体 ===
class Parser:
    def __init__(self, tokens: list[Token]):
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> Token | None:
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def consume(self, expected_type: str | None = None) -> Token:
        tok = self.peek()
        if tok is None:
            raise SyntaxError("Unexpected EOF")
        if expected_type and tok.type != expected_type:
            raise SyntaxError(f"Expected {expected_type}, got {tok.type} at line {tok.line}")
        self.pos += 1
        return tok

    def parse_file(self) -> list:
        ast = []
        self.context = Context.init()
        while True:
            tok = self.peek()
            if tok.type == "PRIMITIVE":
                ast.append(self.parse_primitive())
            elif tok.type == "AXIOM":
                ast.append(self.parse_axiom())
            elif tok.type == "THEOREM":
                ast.append(self.parse_theorem())
            elif tok.type == "DEFINITION":
                ast.append(self.parse_definition())
            elif tok.type == "EQUALITY":
                ast.append(self.parse_equality())
            elif tok.type == "EOF":
                break
            else:
                raise SyntaxError(f"Unexpected token {tok}")
        return ast, self.context

    def parse_primitive(self) -> PrimPred:
        self.consume("PRIMITIVE")
        tok = self.peek()
        if tok.type == "PREDICATE":
            self.consume(tok.type)
            name = self.consume("IDENT").value
            self.consume("ARITY")
            arity = int(self.consume("NUMBER").value)
            tex = self.parse_tex()
            if len(tex) != arity + 1:
                raise SyntaxError("arity is different")
            primpred = PrimPred(type=tok.type, name=name, arity=arity, tex=tex)
            self.context.primpreds[name] = primpred
            logger.debug(f"[primpred] {name}")
            return primpred
        else:
            raise SyntaxError(f"Unexpected token {tok}")

    def parse_tex(self) -> list[str]:
        self.consume("TEX")
        tex = []
        while True:
            tex.append(self.consume("STRING").value)
            if self.peek().type == "COMMA":
                self.consume("COMMA")
            else:
                break
        return tex

    def parse_axiom(self) -> Axiom:
        self.consume("AXIOM")
        name = self.consume("IDENT").value
        conclusion = self.parse_expr()
        axiom = Axiom(name=name, conclusion=conclusion)
        self.context.axioms[name] = axiom
        logger.debug(f"[axiom] {name}")
        return axiom

    def parse_theorem(self) -> Theorem:
        self.consume("THEOREM")
        name = self.consume("IDENT").value
        conclusion = self.parse_expr()
        self.consume("LBRACE")
        proof = self.parse_block()
        self.consume("RBRACE")
        theorem = Theorem(name=name, conclusion=conclusion, proof=proof)
        self.context.theorems[name] = theorem
        logger.debug(f"[theorem] {name}")
        return theorem

    def parse_check(self) -> Check:
        self.consume("CHECK")
        # conclusion 部分の式を読む
        conclusion = self.parse_expr()
        return Check(conclusion=conclusion)

    def parse_block(self) -> list:
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
            elif tok.type == "CHARACTERIZE":
                body.append(self.parse_characterize())
            elif tok.type == "INVOKE":
                body.append(self.parse_invoke())
            elif tok.type == "EXPAND":
                body.append(self.parse_expand())
            elif tok.type == "PAD":
                body.append(self.parse_pad())
            elif tok.type == "SPLIT":
                body.append(self.parse_split())
            elif tok.type == "CONNECT":
                body.append(self.parse_connect())
            elif tok.type == "SUBSTITUTE":
                body.append(self.parse_substitute())
            elif tok.type == "SHOW":
                body.append(self.parse_show())
            else:
                raise SyntaxError(f"Unexpected token in block: {tok}")
        return body

    def parse_any(self) -> Any:
        self.consume("ANY")
        vars_ = []
        while True:
            tok = self.consume("IDENT")
            vars_.append(Var(tok.value))
            if self.peek().type == "COMMA":
                self.consume("COMMA")
                continue
            break
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_expr()
        else:
            conclusion = None
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Any(vars=vars_, conclusion=conclusion, body=body)

    def parse_assume(self) -> Assume:
        self.consume("ASSUME")
        premise = self.parse_expr()
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_expr()
        else:
            conclusion = None
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Assume(premise=premise, conclusion=conclusion, body=body)
    
    def parse_divide(self) -> Divide:
        self.consume("DIVIDE")
        fact = self.parse_expr()
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_expr()
        else:
            conclusion = None
        cases = []
        while self.peek().type == "CASE":
            cases.append(self.parse_case(conclusion))
        if len(cases) < 2:
            raise SyntaxError("At least two cases are necessary")
        return Divide(fact=fact, conclusion=conclusion, cases=cases)
    
    def parse_case(self, conclusion) -> Case:
        self.consume("CASE")
        premise = self.parse_expr()
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Case(premise=premise, conclusion=conclusion, body=body)
    
    def parse_some(self) -> Some:
        self.consume("SOME")
        env = {}
        while True:
            bound = Var(self.consume("IDENT").value)
            self.consume("COLON")
            free = Var(self.consume("IDENT").value)
            env[bound] = free
            if self.peek().type == "COMMA":
                self.consume("COMMA")
                continue
            break
        self.consume("SUCH")
        fact = self.parse_expr()
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_expr()
        else:
            conclusion = None
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Some(env=env, fact=fact, conclusion=conclusion, body=body)
    
    def parse_deny(self) -> Deny:
        self.consume("DENY")
        premise = self.parse_expr()
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Deny(premise=premise, body=body)
    
    def parse_contradict(self) -> Contradict:
        self.consume("CONTRADICT")
        contradiction = self.parse_expr()
        return Contradict(contradiction=contradiction)
    
    def parse_explode(self) -> Explode:
        self.consume("EXPLODE")
        conclusion = self.parse_expr()
        return Explode(conclusion=conclusion)
    
    def parse_apply(self) -> Apply:
        self.consume("APPLY")
        fact = self.parse_expr()
        self.consume("FOR")
        env = {}
        while True:
            bound = Var(self.consume("IDENT").value)
            self.consume("COLON")
            term = self.parse_term()
            env[bound] = term
            if self.peek().type == "COMMA":
                self.consume("COMMA")
                continue
            break
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_expr()
        else:
            conclusion = None
        return Apply(fact=fact, env=env, conclusion=conclusion)
    
    def parse_lift(self) -> Lift:
        self.consume("LIFT")
        if self.peek().type == "FOR":
            fact = None
        else:
            fact = self.parse_expr()
        self.consume("FOR")
        env = {}
        while True:
            bound = Var(self.consume("IDENT").value)
            self.consume("COLON")
            term = self.parse_term()
            env[bound] = term
            if self.peek().type == "COMMA":
                self.consume("COMMA")
                continue
            break
        self.consume("CONCLUDE")
        conclusion = self.parse_expr()
        return Lift(fact=fact, env=env, conclusion=conclusion)

    def parse_characterize(self) -> Characterize:
        self.consume("CHARACTERIZE")
        if self.peek().type == "FOR":
            fact = None
        else:
            fact = self.parse_expr()
        self.consume("FOR")
        bound = Var(self.consume("IDENT").value)
        self.consume("COLON")
        term = self.parse_term()
        env = {bound: term}
        self.consume("CONCLUDE")
        conclusion = self.parse_expr()
        return Characterize(fact=fact, env=env, conclusion=conclusion)

    def parse_invoke(self) -> Invoke:
        self.consume("INVOKE")
        fact = self.parse_expr()
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_expr()
        else:
            conclusion = None
        return Invoke(fact=fact, conclusion=conclusion)

    def parse_expand(self) -> Expand:
        self.consume("EXPAND")
        fact = self.parse_expr()
        self.consume("CONCLUDE")
        conclusion = self.parse_expr()
        return Expand(fact=fact, conclusion=conclusion)

    def parse_pad(self) -> Pad:
        self.consume("PAD")
        fact = self.parse_expr()
        self.consume("CONCLUDE")
        conclusion = self.parse_expr()
        return Pad(fact=fact, conclusion=conclusion)

    def parse_split(self) -> Split:
        self.consume("SPLIT")
        fact = self.parse_expr()
        return Split(fact=fact)

    def parse_connect(self):
        self.consume("CONNECT")
        conclusion = self.parse_expr()
        return Connect(conclusion=conclusion)

    def parse_substitute(self) -> Substitute:
        self.consume("SUBSTITUTE")
        fact = self.parse_expr()
        self.consume("FOR")
        env = {}
        while True:
            key = self.parse_term()
            self.consume("COLON")
            value = self.parse_term()
            env[key] = value
            if self.peek().type == "COMMA":
                self.consume("COMMA")
            else:
                break
        self.consume("CONCLUDE")
        conclusion = self.parse_expr()
        return Substitute(fact=fact, env=env, conclusion=conclusion)

    def parse_show(self) -> Show:
        self.consume("SHOW")
        conclusion = self.parse_expr()
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Show(conclusion=conclusion, body=body)

    def parse_definition(self) -> DefPred | DefCon | DefFun | DefFunTerm:
        self.consume("DEFINITION")
        tok = self.peek()
        if tok.type == "PREDICATE":
            self.consume("PREDICATE")
            if self.peek().type == "AUTOEXPAND":
                self.consume("AUTOEXPAND")
                autoexpand = True
            else:
                autoexpand =False
            name = self.consume("IDENT").value
            self.consume("LPAREN")
            args = [Var(self.consume("IDENT").value)]
            while self.peek().type == "COMMA":
                self.consume("COMMA")
                args.append(Var(self.consume("IDENT").value))
            self.consume("RPAREN")
            formula = self.parse_expr()
            tex = self.parse_tex()
            if len(tex) != len(args) + 1:
                raise SyntaxError("arity is different")
            defpred = DefPred(name=name, args=args, formula=formula, autoexpand=autoexpand, tex=tex)
            self.context.defpreds[name] = defpred
            logger.debug(f"[defpred] {name}")
            return defpred
        elif tok.type == "CONSTANT":
            self.consume("CONSTANT")
            name = self.consume("IDENT").value
            self.consume("BY")
            theorem = self.consume("IDENT").value
            tex = self.parse_tex()
            if len(tex) != 1:
                raise SyntaxError("arity is different")
            self.context.defcons[name] = DefCon(name=name, theorem=theorem, tex=tex, existence=None, uniqueness=None)
            self.consume("EXISTENCE")
            existence_name = self.consume("IDENT").value
            existence_formula = self.parse_expr()
            existence = DefConExist(name=existence_name, formula=existence_formula)
            self.consume("UNIQUENESS")
            uniqueness_name = self.consume("IDENT").value
            uniqueness_formula = self.parse_expr()
            uniqueness = DefConUniq(name=uniqueness_name, formula=uniqueness_formula)
            defcon = DefCon(name=name, theorem=theorem, tex=tex, existence=existence, uniqueness=uniqueness)
            self.context.defcons[name] = defcon
            logger.debug(f"[defcon] {name}")
            return defcon
        elif tok.type == "FUNCTION":
            self.consume("FUNCTION")
            name = self.consume("IDENT").value
            if self.peek().type == "BY":
                self.consume("BY")
                theorem = self.consume("IDENT").value
                vars_, body = collect_quantifier_vars(self.context.theorems[theorem].conclusion, Forall)
                if not (len(vars_) > 0 and isinstance(body, ExistsUniq)):
                    raise SyntaxError(f"theorem cannot be used for function definition: {theorem}")
                arity = len(vars_)
                tex = self.parse_tex()
                if len(tex) != arity + 1:
                    raise SyntaxError("arity is different")
                self.context.deffuns[name] = DefFun(name=name, arity=arity, theorem=theorem, tex=tex, existence=None, uniqueness=None)
                self.consume("EXISTENCE")
                existence_name = self.consume("IDENT").value
                existence_formula = self.parse_expr()
                existence = DefFunExist(name=existence_name, formula=existence_formula)
                self.consume("UNIQUENESS")
                uniqueness_name = self.consume("IDENT").value
                uniqueness_formula = self.parse_expr()
                uniqueness = DefFunUniq(name=uniqueness_name, formula=uniqueness_formula)
                deffun = DefFun(name=name, arity=arity, theorem=theorem, tex=tex, existence=existence, uniqueness=uniqueness)
                self.context.deffuns[name] = deffun
                logger.debug(f"[deffun] {name}")
                return deffun
            else:
                self.consume("LPAREN")
                args = [Var(self.consume("IDENT").value)]
                while self.peek().type == "COMMA":
                    self.consume("COMMA")
                    args.append(Var(self.consume("IDENT").value))
                self.consume("RPAREN")
                term = self.parse_term()
                tex = self.parse_tex()
                if len(tex) != len(args) + 1:
                    raise SyntaxError("arity is different")
                deffunterm = DefFunTerm(name=name, args=args, term=term, tex=tex)
                self.context.deffunterms[name] = deffunterm
                logger.debug(f"[deffunterm] {name}")
                return deffunterm
        else:
            raise SyntaxError(f"Unexpected token {tok}")

    def parse_equality(self) -> Equality:
        self.consume("EQUALITY")
        name = self.consume("IDENT").value
        if name in self.context.primpreds:
            equal = self.context.primpreds[name]
            if equal.arity != 2:
                raise Exception(f"arity of primpred {name} is not 2")
        elif name in self.context.defpreds:
            equal = self.context.defpreds[name]
            if len(equal.args) != 2:
                raise Exception(f"arity of defpred {name} is not 2")
        else:
            raise Exception(f"{name} is not primpred or defpred")
        self.consume("REFLECTION")
        name = self.consume("IDENT").value
        if name in self.context.axioms:
            reflection = self.context.axioms[name]
        elif name in self.context.theorems:
            reflection = self.context.theorems[name]
        else:
            raise Exception(f"{name} is not axiom or theorem")
        self.consume("REPLACEMENT")
        replacement = {}
        while True:
            predicate = self.consume("IDENT").value
            if not (predicate == equal.name or predicate in self.context.primpreds):
                raise Exception(f"{predicate} is not {equal.name} or primpred")
            self.consume("COLON")
            name = self.consume("IDENT").value
            if name in self.context.axioms:
                formula = self.context.axioms[name]
            elif name in self.context.theorems:
                formula = self.context.theorems[name]
            else:
                raise Exception(f"{name} is not axiom or theorem")
            replacement[predicate] = formula
            if self.peek().type == "COMMA":
                self.consume("COMMA")
            else:
                break
        equality = Equality(equal=equal, reflection=reflection, replacement=replacement)
        self.context.equality = equality
        logger.debug(f"[equality] {type(equal)}: {equal.name}")
        return equality

    def parse_term(self) -> Compound | Con | Var:
        tok = self.peek()
        if tok.type == "IDENT":
            name = self.consume("IDENT").value
            if self.peek().type == "LPAREN":
                if not (name in self.context.deffuns or name in self.context.deffunterms):
                    raise SyntaxError(f"Unexpected token (fun): {tok}")
                self.consume("LPAREN")
                args = [self.parse_term()]
                while self.peek().type == "COMMA":
                    self.consume("COMMA")
                    args.append(self.parse_term())
                self.consume("RPAREN")
                args = tuple(args)
                if name in self.context.deffuns and len(args) != self.context.deffuns[name].arity:
                    raise SyntaxError("arity is different (deffun)")
                if name in self.context.deffunterms and len(args) != len(self.context.deffunterms[name].args):
                    raise SyntaxError("arity is different (deffunterm)")
                return Compound(Fun(name), args)
            elif name in self.context.defcons:
                return Con(name)
            else:
                return Var(name)
        else:
            raise SyntaxError(f"Unexpected token: {tok}")

    def parse_primary(self):
        tok = self.peek()
        if tok.type == "IDENT":
            name = self.consume("IDENT").value
            if name in self.context.primpreds:
                arity = self.context.primpreds[name].arity
            elif name in self.context.defpreds:
                arity = len(self.context.defpreds[name].args)
            else:
                raise SyntaxError(f"not found in primpreds or defpreds: {name}")
            self.consume("LPAREN")
            args = [self.parse_term()]
            while self.peek().type == "COMMA":
                self.consume("COMMA")
                args.append(self.parse_term())
            if len(args) != arity:
                raise SyntaxError("arity is different")
            self.consume("RPAREN")
            return Symbol(Pred(name), args)

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

        elif tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ"):
            quantifiers = []
            vars_ = []
            while tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ"):
                quantifiers.append(self.consume(tok.type).type)
                vars_.append(Var(self.consume("IDENT").value))
                tok = self.peek()
            self.consume("LPAREN")
            body = self.parse_recursion()
            self.consume("RPAREN")
            for quantifier, var in zip(reversed(quantifiers), reversed(vars_)):
                if quantifier == "FORALL":
                    body = Forall(var, body)
                elif quantifier == "EXISTS":
                    body = Exists(var, body)
                elif quantifier == "EXISTS_UNIQ":
                    body = ExistsUniq(var, body)
            return body

        else:
            raise SyntaxError(f"Unexpected token: {tok}")

    def parse_expr(self):
        if self.peek().type == "BOT":
            self.consume("BOT")
            return Bottom()
        elif self.peek().type == "IDENT" and self.peek().value in self.context.axioms:
            return self.context.axioms[self.consume("IDENT").value]
        elif self.peek().type == "IDENT" and self.peek().value in self.context.theorems:
            return self.context.theorems[self.consume("IDENT").value]
        elif self.peek().type == "IDENT" and self.context.has_defcon_existence(self.peek().value):
            return self.context.get_defcon_existence(self.consume("IDENT").value)
        elif self.peek().type == "IDENT" and self.context.has_defcon_uniqueness(self.peek().value):
            return self.context.get_defcon_uniqueness(self.consume("IDENT").value)
        elif self.peek().type == "IDENT" and self.context.has_deffun_existence(self.peek().value):
            return self.context.get_deffun_existence(self.consume("IDENT").value)
        elif self.peek().type == "IDENT" and self.context.has_deffun_uniqueness(self.peek().value):
            return self.context.get_deffun_uniqueness(self.consume("IDENT").value)
        else:
            return self.parse_recursion()

    def parse_recursion(self):
        return self.parse_implies()

    def parse_implies(self):
        left = self.parse_and()
        while self.peek() is not None and self.peek().type in ("IMPLIES", "IFF"):
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
        while self.peek() is not None and self.peek().type in ("AND", "OR"):
            op = self.peek().type
            self.consume(op)
            right = self.parse_primary()
            if op == "AND":
                left = And(left, right)
            elif op == "OR":
                left = Or(left, right)
        return left

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
    file_handler = logging.FileHandler(os.path.join("logs", os.path.basename(path).replace(".proof", "_parser.log")), mode='w', encoding='utf-8')
    file_handler.setLevel(logging.DEBUG)

    # 共通フォーマット
    formatter = logging.Formatter("[%(filename)s] %(message)s")
    console_handler.setFormatter(formatter)
    file_handler.setFormatter(formatter)

    # ハンドラ登録
    logger.addHandler(console_handler)
    logger.addHandler(file_handler)

    tokens = lex(src)
    parser = Parser(tokens)
    parser.parse_file()
