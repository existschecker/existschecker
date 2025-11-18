from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, Symbol, And, Or, Implies, Forall, Exists, Not, Bottom, PrimPred, DefPred, Iff, Axiom, Invoke, Expand, ExistsUniq, DefCon, Pad, Split, Connect, DefConExist, DefConUniq, DefFun, DefFunExist, DefFunUniq, Compound, Fun, Con, Var, DefFunTerm, Equality, Substitute, Characterize, Show, Pred, EqualityReflection, EqualityReplacement, Term, Formula, Control, Declaration, Template, FormulaTerm, FreshVar
from lexer import Token, lex
from logic_utils import collect_quantifier_vars

import logging
logger = logging.getLogger("proof")

# === パーサー本体 ===
class Parser:
    def __init__(self, tokens: list[Token]):
        self.tokens = tokens
        self.pos = 0
        self.bound_items: dict[str, Var | Template] = {}
        self.free_items: dict[str, Var | Template] = {}

    def peek(self) -> Token:
        if self.pos >= len(self.tokens):
            raise Exception("Unexpcted end of input")
        return self.tokens[self.pos]

    def consume(self, expected_type: str | None = None) -> Token:
        tok = self.peek()
        if tok is None:
            raise SyntaxError("Unexpected EOF")
        if expected_type and tok.type != expected_type:
            raise SyntaxError(f"Expected {expected_type}, got {tok.type} at line {tok.line}")
        self.pos += 1
        return tok

    def parse_file(self) -> tuple[list[Declaration], Context]:
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

    def parse_axiom(self) -> Axiom:
        self.consume("AXIOM")
        name = self.consume("IDENT").value
        conclusion = self.parse_formula()
        axiom = Axiom(name=name, conclusion=conclusion)
        self.context.axioms[name] = axiom
        logger.debug(f"[axiom] {name}")
        return axiom

    def parse_theorem(self) -> Theorem:
        self.consume("THEOREM")
        name = self.consume("IDENT").value
        conclusion = self.parse_formula()
        self.consume("LBRACE")
        proof = self.parse_block()
        self.consume("RBRACE")
        theorem = Theorem(name=name, conclusion=conclusion, proof=proof)
        self.context.theorems[name] = theorem
        logger.debug(f"[theorem] {name}")
        return theorem

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
            args: list[Var] = []
            while True:
                args.append(self.parse_var())
                if self.peek().type == "COMMA":
                    self.consume("COMMA")
                else:
                    break
            self.consume("RPAREN")
            self.consume("AS")
            for arg in args:
                self.free_items[arg.name] = arg
            formula = self.parse_formula()
            for arg in args:
                self.free_items.pop(arg.name)
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
            existence_formula = self.parse_formula()
            existence = DefConExist(name=existence_name, formula=existence_formula)
            self.consume("UNIQUENESS")
            uniqueness_name = self.consume("IDENT").value
            uniqueness_formula = self.parse_formula()
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
                existence_formula = self.parse_formula()
                existence = DefFunExist(name=existence_name, formula=existence_formula)
                self.consume("UNIQUENESS")
                uniqueness_name = self.consume("IDENT").value
                uniqueness_formula = self.parse_formula()
                uniqueness = DefFunUniq(name=uniqueness_name, formula=uniqueness_formula)
                deffun = DefFun(name=name, arity=arity, theorem=theorem, tex=tex, existence=existence, uniqueness=uniqueness)
                self.context.deffuns[name] = deffun
                logger.debug(f"[deffun] {name}")
                return deffun
            else:
                self.consume("LPAREN")
                args: list[Var] = []
                while True:
                    args.append(self.parse_var())
                    if self.peek().type == "COMMA":
                        self.consume("COMMA")
                    else:
                        break
                self.consume("RPAREN")
                self.consume("AS")
                for arg in args:
                    self.free_items[arg.name] = arg
                term = self.parse_term()
                for arg in args:
                    self.free_items.pop(arg.name)
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
            reflection_evidence = self.context.axioms[name]
        elif name in self.context.theorems:
            reflection_evidence = self.context.theorems[name]
        else:
            raise Exception(f"{name} is not axiom or theorem")
        reflection = EqualityReflection(evidence=reflection_evidence)
        self.consume("REPLACEMENT")
        replacement_evidence = {}
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
            replacement_evidence[predicate] = formula
            if self.peek().type == "COMMA":
                self.consume("COMMA")
            else:
                break
        replacement = EqualityReplacement(replacement_evidence)
        equality = Equality(equal=equal, reflection=reflection, replacement=replacement)
        self.context.equality = equality
        logger.debug(f"[equality] {type(equal)}: {equal.name}")
        return equality

    def parse_block(self) -> list[Control]:
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
        items: list[Var | Template] = []
        while True:
            if self.peek().type == "TEMPLATE":
                self.consume("TEMPLATE")
                template = self.parse_template()
                items.append(template)
            else:
                var = self.parse_var()
                items.append(var)
            if self.peek().type == "COMMA":
                self.consume("COMMA")
            else:
                break
        for item in items:
            self.free_items[item.name] = item
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_formula()
        else:
            conclusion = None
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        for item in items:
            self.free_items.pop(item.name)
        return Any(items=items, conclusion=conclusion, body=body)

    def parse_assume(self) -> Assume:
        self.consume("ASSUME")
        premise = self.parse_formula()
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_formula()
        else:
            conclusion = None
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Assume(premise=premise, conclusion=conclusion, body=body)
    
    def parse_divide(self) -> Divide:
        self.consume("DIVIDE")
        fact = self.parse_reference_or_formula()
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_bot_or_formula()
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
        premise = self.parse_formula()
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Case(premise=premise, conclusion=conclusion, body=body)
    
    def parse_some(self) -> Some:
        self.consume("SOME")
        env: dict[Var, Var] = {}
        while True:
            bound = self.parse_var()
            self.consume("COLON")
            free = self.parse_var()
            env[bound] = free
            if self.peek().type == "COMMA":
                self.consume("COMMA")
                continue
            break
        self.consume("SUCH")
        fact = self.parse_reference_or_formula()
        for item in env.values():
            self.free_items[item.name] = item
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_bot_or_formula()
        else:
            conclusion = None
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        for item in env.values():
            self.free_items.pop(item.name)
        return Some(env=env, fact=fact, conclusion=conclusion, body=body)
    
    def parse_deny(self) -> Deny:
        self.consume("DENY")
        premise = self.parse_formula()
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Deny(premise=premise, body=body)
    
    def parse_contradict(self) -> Contradict:
        self.consume("CONTRADICT")
        contradiction = self.parse_formula()
        return Contradict(contradiction=contradiction)
    
    def parse_explode(self) -> Explode:
        self.consume("EXPLODE")
        conclusion = self.parse_formula()
        return Explode(conclusion=conclusion)

    def parse_apply(self) -> Apply:
        self.consume("APPLY")
        fact = self.parse_reference_or_formula()
        self.consume("FOR")
        env: dict[str, Term] = {}
        while True:
            bound = self.consume("IDENT").value
            self.consume("COLON")
            term = self.parse_term()
            env[bound] = term
            if self.peek().type == "COMMA":
                self.consume("COMMA")
            else:
                break
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_formula()
        else:
            conclusion = None
        return Apply(fact=fact, env=env, conclusion=conclusion)

    def parse_lift(self) -> Lift:
        self.consume("LIFT")
        if self.peek().type == "FOR":
            fact = None
        else:
            fact = self.parse_formula()
        self.consume("FOR")
        env = {}
        while True:
            bound = self.parse_var()
            self.consume("COLON")
            term = self.parse_term()
            env[bound] = term
            if self.peek().type == "COMMA":
                self.consume("COMMA")
                continue
            break
        self.consume("CONCLUDE")
        conclusion = self.parse_formula()
        if not isinstance(conclusion, Exists):
            raise Exception("Conclusion of Lift has to be Exists object")
        return Lift(fact=fact, env=env, conclusion=conclusion)

    def parse_characterize(self) -> Characterize:
        self.consume("CHARACTERIZE")
        if self.peek().type == "FOR":
            fact = None
        else:
            fact = self.parse_formula()
        self.consume("FOR")
        bound = self.parse_var()
        self.consume("COLON")
        term = self.parse_term()
        env = {bound: term}
        self.consume("CONCLUDE")
        conclusion = self.parse_formula()
        if not isinstance(conclusion, ExistsUniq):
            raise Exception("Conclusion of Characterize has to be ExistsUniq object")
        return Characterize(fact=fact, env=env, conclusion=conclusion)

    def parse_invoke(self) -> Invoke:
        self.consume("INVOKE")
        fact = self.parse_implies()
        if not isinstance(fact, Implies):
            raise Exception("Fact of Invoke has to be Implies object")
        if self.peek().type == "CONCLUDE":
            self.consume("CONCLUDE")
            conclusion = self.parse_formula()
        else:
            conclusion = None
        return Invoke(fact=fact, conclusion=conclusion)

    def parse_expand(self) -> Expand:
        self.consume("EXPAND")
        fact = self.parse_formula()
        self.consume("CONCLUDE")
        conclusion = self.parse_formula()
        return Expand(fact=fact, conclusion=conclusion)

    def parse_pad(self) -> Pad:
        self.consume("PAD")
        fact = self.parse_formula()
        self.consume("CONCLUDE")
        conclusion = self.parse_formula()
        if not isinstance(conclusion, Or):
            raise Exception("Conclusion of Pad has to be Or object")
        return Pad(fact=fact, conclusion=conclusion)

    def parse_split(self) -> Split:
        self.consume("SPLIT")
        if self.peek().type == "NUMBER":
            index = int(self.consume("NUMBER").value)
        else:
            index = None
        fact = self.parse_reference_or_formula()
        if not isinstance(fact, (And, Iff)):
            raise Exception("Fact of Split has to be And or Iff object")
        return Split(index=index, fact=fact)

    def parse_connect(self):
        self.consume("CONNECT")
        conclusion = self.parse_formula()
        if not isinstance(conclusion, (And, Iff)):
            raise Exception("Conclusion of Connect has to be And or Iff object")
        return Connect(conclusion=conclusion)

    def parse_substitute(self) -> Substitute:
        self.consume("SUBSTITUTE")
        fact = self.parse_reference_or_formula()
        self.consume("FOR")
        env: dict[Term, Term] = {}
        evidence: dict[Term, str] = {}
        while True:
            key = self.parse_term()
            self.consume("COLON")
            value = self.parse_term()
            env[key] = value
            if self.peek().type == "BY":
                self.consume("BY")
                evidence_name = self.consume("IDENT").value
                evidence[key] = evidence_name
            if self.peek().type == "COMMA":
                self.consume("COMMA")
            else:
                break
        self.consume("CONCLUDE")
        conclusion = self.parse_formula()
        return Substitute(fact=fact, env=env, evidence=evidence, conclusion=conclusion)

    def parse_show(self) -> Show:
        self.consume("SHOW")
        conclusion = self.parse_bot_or_formula()
        self.consume("LBRACE")
        body = self.parse_block()
        self.consume("RBRACE")
        return Show(conclusion=conclusion, body=body)

    def parse_reference_or_formula(self) -> str | Formula:
        if self.peek().type == "IDENT" and self.context.has_reference(self.peek().value):
            return self.consume("IDENT").value
        else:
            return self.parse_formula()

    def parse_bot_or_formula(self) -> Bottom | Formula:
        if self.peek().type == "BOT":
            self.consume("BOT")
            return Bottom()
        else:
            return self.parse_formula()

    def parse_formula(self) -> Formula:
        return self.parse_implies()

    def parse_implies(self) -> Formula:
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

    def parse_and(self) -> Formula:
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

    def parse_primary(self) -> Formula:
        tok = self.peek()
        if tok.type == "IDENT":
            name = self.consume("IDENT").value
            if name in self.bound_items or name in self.free_items:
                if name in self.bound_items:
                    template = self.bound_items[name]
                else:
                    template = self.free_items[name]
                if not isinstance(template, Template):
                    raise Exception(f"{template} is not Template object")
                return template
            elif name in self.context.primpreds or name in self.context.defpreds:
                if name in self.context.primpreds:
                    arity = self.context.primpreds[name].arity
                else:
                    arity = len(self.context.defpreds[name].args)
                self.consume("LPAREN")
                args = [self.parse_term()]
                while self.peek().type == "COMMA":
                    self.consume("COMMA")
                    args.append(self.parse_term())
                if len(args) != arity:
                    raise SyntaxError("arity is different")
                self.consume("RPAREN")
                return Symbol(Pred(name), args)
            else:
                raise SyntaxError(f"not found in primpreds or defpreds: {name}")

        elif tok.type == "LPAREN":
            self.consume("LPAREN")
            expr = self.parse_formula()
            self.consume("RPAREN")
            return expr
        
        elif tok.type == "NOT":
            self.consume("NOT")
            self.consume("LPAREN")
            body = self.parse_formula()
            self.consume("RPAREN")
            return Not(body)

        elif tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_TEMPLATE"):
            quantifiers = []
            items: list[Var | Template] = []
            while tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_TEMPLATE"):
                if tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ"):
                    quantifiers.append(self.consume(tok.type).type)
                    items.append(self.parse_var())
                    tok = self.peek()
                else:
                    quantifiers.append(self.consume(tok.type).type)
                    template = self.parse_template()
                    items.append(template)
                    tok = self.peek()
            for item in items:
                self.bound_items[item.name] = item
            self.consume("LPAREN")
            body = self.parse_formula()
            self.consume("RPAREN")
            for item in items:
                self.bound_items.pop(item.name)
            for quantifier, item in zip(reversed(quantifiers), reversed(items)):
                if quantifier == "FORALL" or quantifier == "FORALL_TEMPLATE":
                    body = Forall(item, body)
                elif quantifier == "EXISTS":
                    body = Exists(item, body)
                elif quantifier == "EXISTS_UNIQ":
                    body = ExistsUniq(item, body)
            return body

        else:
            raise SyntaxError(f"Unexpected token: {tok}")

    def parse_term(self) -> Term:
        tok = self.peek()
        if tok.type == "IDENT":
            name = self.consume("IDENT").value
            if name in self.bound_items:
                if isinstance(self.bound_items[name], FreshVar):
                    return Var(name)
                else:
                    return self.bound_items[name]
            elif name in self.free_items:
                if isinstance(self.free_items[name], FreshVar):
                    return Var(name)
                else:
                    return self.free_items[name]
            elif name in self.context.defcons:
                return Con(name)
            elif name in self.context.deffuns or name in self.context.deffunterms:
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
            else:
                raise SyntaxError(f"Unexpected token: {tok}")
        elif tok.type == "LBRACKET":
            self.consume("LBRACKET")
            allowed_vars: list[Var] = []
            while True:
                allowed_vars.append(self.parse_var())
                if self.peek().type == "COMMA":
                    self.consume("COMMA")
                else:
                    break
            for var in allowed_vars:
                self.free_items[var.name] = var
            self.consume("SLASH")
            formula = self.parse_formula()
            self.consume("RBRACKET")
            for var in allowed_vars:
                self.free_items.pop(var.name)
            return FormulaTerm(tuple(allowed_vars), formula)
        else:
            raise SyntaxError(f"Unexpected token: {tok}")

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

    def parse_var(self) -> Var:
        name = self.consume("IDENT").value
        if self.peek().type == "LBRACKET":
            self.consume("LBRACKET")
            self.consume("HASH")
            fresh_templates: list[Template] = []
            while True:
                fresh_templates.append(self.parse_template())
                if self.peek().type == "COMMA":
                    self.consume("COMMA")
                else:
                    break
            self.consume("RBRACKET")
            return FreshVar(name, tuple(fresh_templates))
        else:
            return Var(name)

    def parse_template(self) -> Template:
        template_name = self.consume("IDENT").value
        return Template(template_name)

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
