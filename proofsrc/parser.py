from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, Symbol, And, Or, Implies, Forall, Exists, Not, Bottom, PrimPred, DefPred, Iff, Axiom, Invoke, Expand, ExistsUniq, DefCon, Pad, Split, Connect, DefConExist, DefConUniq, DefFun, DefFunExist, DefFunUniq, Compound, Fun, Con, Var, DefFunTerm, Equality, Substitute, Characterize, Show, Pred, EqualityReflection, EqualityReplacement, Term, Formula, Control, Declaration, Template, Lambda, TemplateCall, Include
from lexer import Token
from token_stream import TokenStream
from logic_utils import collect_quantifier_vars

import logging
logger = logging.getLogger("proof")

# === パーサー本体 ===
class Parser:
    def __init__(self, tokens: list[Token]):
        self.stream = TokenStream(tokens)
        self.bound_items: dict[str, Var | Template] = {}
        self.free_items: dict[str, Var | Template] = {}

    def parse_file(self, context: Context) -> tuple[list[Include | Declaration], Context]:
        ast: list[Include | Declaration] = []
        self.context = context
        while True:
            tok = self.stream.peek()
            if tok.type == "INCLUDE":
                ast.append(self.parse_include())
            elif tok.type == "PRIMITIVE":
                ast.append(self.parse_primitive())
            elif tok.type == "AXIOM":
                ast.append(self.parse_axiom())
            elif tok.type == "THEOREM":
                ast.append(self.parse_theorem())
            elif tok.type == "DEFINITION":
                ast.append(self.parse_definition())
            elif tok.type == "EXISTENCE":
                ast.append(self.parse_existence())
            elif tok.type == "UNIQUENESS":
                ast.append(self.parse_uniqueness())
            elif tok.type == "EQUALITY":
                ast.append(self.parse_equality())
            elif tok.type == "EOF":
                break
            else:
                raise SyntaxError(f"Unexpected token {tok}")
        return ast, self.context

    def parse_primitive(self) -> PrimPred:
        self.stream.consume("PRIMITIVE")
        tok = self.stream.peek()
        if tok.type == "PREDICATE":
            self.stream.consume("PREDICATE")
            name = self.stream.consume("IDENT").value
            self.stream.consume("ARITY")
            arity = int(self.stream.consume("NUMBER").value)
            tex = self.parse_tex()
            if len(tex) != arity + 1:
                raise SyntaxError("arity is different")
            primpred = PrimPred(name=name, arity=arity, tex=tex)
            self.context.primpreds[name] = primpred
            logger.debug(f"[primpred] {name}")
            return primpred
        else:
            raise SyntaxError(f"Unexpected token {tok}")

    def parse_axiom(self) -> Axiom:
        self.stream.consume("AXIOM")
        name = self.stream.consume("IDENT").value
        conclusion = self.parse_formula()
        axiom = Axiom(name=name, conclusion=conclusion)
        self.context.axioms[name] = axiom
        logger.debug(f"[axiom] {name}")
        return axiom

    def parse_theorem(self) -> Theorem:
        self.stream.consume("THEOREM")
        name = self.stream.consume("IDENT").value
        conclusion = self.parse_formula()
        self.stream.consume("LBRACE")
        proof = self.parse_block()
        self.stream.consume("RBRACE")
        theorem = Theorem(name=name, conclusion=conclusion, proof=proof)
        self.context.theorems[name] = theorem
        logger.debug(f"[theorem] {name}")
        return theorem

    def parse_definition(self) -> DefPred | DefCon | DefFun | DefFunTerm:
        self.stream.consume("DEFINITION")
        tok = self.stream.peek()
        if tok.type == "PREDICATE":
            self.stream.consume("PREDICATE")
            if self.stream.peek().type == "AUTOEXPAND":
                self.stream.consume("AUTOEXPAND")
                autoexpand = True
            else:
                autoexpand =False
            name = self.stream.consume("IDENT").value
            self.stream.consume("LPAREN")
            args: list[Var] = []
            while True:
                args.append(self.parse_var())
                if self.stream.peek().type == "COMMA":
                    self.stream.consume("COMMA")
                else:
                    break
            self.stream.consume("RPAREN")
            self.stream.consume("AS")
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
            self.stream.consume("CONSTANT")
            name = self.stream.consume("IDENT").value
            self.stream.consume("BY")
            theorem = self.stream.consume("IDENT").value
            tex = self.parse_tex()
            if len(tex) != 1:
                raise SyntaxError("arity is different")
            defcon = DefCon(name=name, theorem=theorem, tex=tex)
            self.context.defcons[name] = defcon
            logger.debug(f"[defcon] {name}")
            return defcon
        elif tok.type == "FUNCTION":
            self.stream.consume("FUNCTION")
            name = self.stream.consume("IDENT").value
            if self.stream.peek().type == "BY":
                self.stream.consume("BY")
                theorem = self.stream.consume("IDENT").value
                vars_, body = collect_quantifier_vars(self.context.theorems[theorem].conclusion, Forall)
                if not (len(vars_) > 0 and isinstance(body, ExistsUniq)):
                    raise SyntaxError(f"theorem cannot be used for function definition: {theorem}")
                arity = len(vars_)
                tex = self.parse_tex()
                if len(tex) != arity + 1:
                    raise SyntaxError("arity is different")
                deffun = DefFun(name=name, arity=arity, theorem=theorem, tex=tex)
                self.context.deffuns[name] = deffun
                logger.debug(f"[deffun] {name}")
                return deffun
            else:
                self.stream.consume("LPAREN")
                args: list[Var] = []
                while True:
                    args.append(self.parse_var())
                    if self.stream.peek().type == "COMMA":
                        self.stream.consume("COMMA")
                    else:
                        break
                self.stream.consume("RPAREN")
                self.stream.consume("AS")
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

    def parse_existence(self) -> DefConExist | DefFunExist:
        self.stream.consume("EXISTENCE")
        existence_name = self.stream.consume("IDENT").value
        existence_formula = self.parse_formula()
        self.stream.consume("BY")
        name = self.stream.consume("IDENT").value
        if name in self.context.defcons:
            defconexist = DefConExist(name=existence_name, formula=existence_formula, con_name=name)
            self.context.defconexists[existence_name] = defconexist
            return defconexist
        elif name in self.context.deffuns:
            deffunexist = DefFunExist(name=existence_name, formula=existence_formula, fun_name=name)
            self.context.deffunexists[existence_name] = deffunexist
            return deffunexist
        else:
            raise Exception(f"Unexpected name: {name}")

    def parse_uniqueness(self) -> DefConUniq | DefFunUniq:
        self.stream.consume("UNIQUENESS")
        uniqueness_name = self.stream.consume("IDENT").value
        uniqueness_formula = self.parse_formula()
        self.stream.consume("BY")
        name = self.stream.consume("IDENT").value
        if name in self.context.defcons:
            defconuniq = DefConUniq(name=uniqueness_name, formula=uniqueness_formula, con_name=name)
            self.context.defconuniqs[uniqueness_name] = defconuniq
            return defconuniq
        elif name in self.context.deffuns:
            deffununiq = DefFunUniq(name=uniqueness_name, formula=uniqueness_formula, fun_name=name)
            self.context.deffununiqs[uniqueness_name] = deffununiq
            return deffununiq
        else:
            raise Exception(f"Unexpected name: {name}")

    def parse_equality(self) -> Equality:
        self.stream.consume("EQUALITY")
        name = self.stream.consume("IDENT").value
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
        reflection = self.parse_equality_reflection(equal)
        replacement = self.parse_equality_replacement(equal)
        equality = Equality(equal=equal, reflection=reflection, replacement=replacement)
        self.context.equality = equality
        logger.debug(f"[equality] {type(equal)}: {equal.name}")
        return equality

    def parse_equality_reflection(self, equal: PrimPred | DefPred) -> EqualityReflection:
        self.stream.consume("REFLECTION")
        name = self.stream.consume("IDENT").value
        if name in self.context.axioms:
            reflection_evidence = self.context.axioms[name]
        elif name in self.context.theorems:
            reflection_evidence = self.context.theorems[name]
        else:
            raise Exception(f"{name} is not axiom or theorem")
        return EqualityReflection(equal=equal, evidence=reflection_evidence)

    def parse_equality_replacement(self, equal: PrimPred | DefPred) -> EqualityReplacement:
        self.stream.consume("REPLACEMENT")
        replacement_evidence: dict[str, Axiom | Theorem] = {}
        while True:
            predicate = self.stream.consume("IDENT").value
            if not (predicate == equal.name or predicate in self.context.primpreds):
                raise Exception(f"{predicate} is not {equal.name} or primpred")
            self.stream.consume("COLON")
            name = self.stream.consume("IDENT").value
            if name in self.context.axioms:
                formula = self.context.axioms[name]
            elif name in self.context.theorems:
                formula = self.context.theorems[name]
            else:
                raise Exception(f"{name} is not axiom or theorem")
            replacement_evidence[predicate] = formula
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return EqualityReplacement(equal=equal, evidence=replacement_evidence)

    def parse_include(self) -> Include:
        self.stream.consume("INCLUDE")
        file = self.stream.consume("STRING").value
        return Include(file)

    def parse_block(self) -> list[Control]:
        body: list[Control] = []
        while True:
            tok = self.stream.peek()
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
        self.stream.consume("ANY")
        items: list[Var | Template] = []
        while True:
            if self.stream.peek().type == "TEMPLATE":
                self.stream.consume("TEMPLATE")
                template = self.parse_template()
                items.append(template)
            else:
                var = self.parse_var()
                items.append(var)
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        for item in items:
            self.free_items[item.name] = item
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        for item in items:
            self.free_items.pop(item.name)
        return Any(items=items, body=body)

    def parse_assume(self) -> Assume:
        self.stream.consume("ASSUME")
        premise = self.parse_formula()
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        return Assume(premise=premise, body=body)
    
    def parse_divide(self) -> Divide:
        self.stream.consume("DIVIDE")
        fact = self.parse_reference_or_formula()
        cases: list[Case] = []
        while self.stream.peek().type == "CASE":
            cases.append(self.parse_case())
        if len(cases) < 2:
            raise SyntaxError("At least two cases are necessary")
        return Divide(fact=fact, cases=cases)
    
    def parse_case(self) -> Case:
        self.stream.consume("CASE")
        premise = self.parse_formula()
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        return Case(premise=premise, body=body)
    
    def parse_some(self) -> Some:
        self.stream.consume("SOME")
        env: dict[Var, Var] = {}
        while True:
            bound = self.parse_var()
            self.stream.consume("COLON")
            free = self.parse_var()
            env[bound] = free
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
                continue
            break
        self.stream.consume("SUCH")
        fact = self.parse_reference_or_formula()
        for item in env.values():
            self.free_items[item.name] = item
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        for item in env.values():
            self.free_items.pop(item.name)
        return Some(env=env, fact=fact, body=body)
    
    def parse_deny(self) -> Deny:
        self.stream.consume("DENY")
        premise = self.parse_formula()
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        return Deny(premise=premise, body=body)
    
    def parse_contradict(self) -> Contradict:
        self.stream.consume("CONTRADICT")
        contradiction = self.parse_formula()
        return Contradict(contradiction=contradiction)
    
    def parse_explode(self) -> Explode:
        self.stream.consume("EXPLODE")
        conclusion = self.parse_formula()
        return Explode(conclusion=conclusion)

    def parse_apply(self) -> Apply:
        self.stream.consume("APPLY")
        fact = self.parse_reference_or_formula()
        self.stream.consume("FOR")
        env: dict[str, Term] = {}
        while True:
            bound = self.stream.consume("IDENT").value
            self.stream.consume("COLON")
            term = self.parse_term()
            env[bound] = term
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return Apply(fact=fact, env=env)

    def parse_lift(self) -> Lift:
        self.stream.consume("LIFT")
        self.stream.consume("FOR")
        env: dict[Var, Term] = {}
        while True:
            bound = self.parse_var()
            self.stream.consume("COLON")
            term = self.parse_term()
            env[bound] = term
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
                continue
            break
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula()
        if not isinstance(conclusion, Exists):
            raise Exception("Conclusion of Lift has to be Exists object")
        return Lift(env=env, conclusion=conclusion)

    def parse_characterize(self) -> Characterize:
        self.stream.consume("CHARACTERIZE")
        self.stream.consume("FOR")
        bound = self.parse_var()
        self.stream.consume("COLON")
        term = self.parse_term()
        env = {bound: term}
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula()
        if not isinstance(conclusion, ExistsUniq):
            raise Exception("Conclusion of Characterize has to be ExistsUniq object")
        return Characterize(env=env, conclusion=conclusion)

    def parse_invoke(self) -> Invoke:
        self.stream.consume("INVOKE")
        if self.stream.peek().type == "RIGHTWARD":
            self.stream.consume("RIGHTWARD")
            direction = "rightward"
        elif self.stream.peek().type == "LEFTWARD":
            self.stream.consume("LEFTWARD")
            direction = "leftward"
        else:
            direction = "none"
        fact = self.parse_implies()
        if direction == "none":
            if not isinstance(fact, Implies):
                raise Exception("direction is none, but fact is not Implies object")
        else:
            if not isinstance(fact, Iff):
                raise Exception("direction is not none, but fact is not Iff object")
        return Invoke(direction=direction, fact=fact)

    def parse_expand(self) -> Expand:
        self.stream.consume("EXPAND")
        fact = self.parse_formula()
        self.stream.consume("FOR")
        defs: list[str] = []
        while True:
            defs.append(self.stream.consume("IDENT").value)
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        if len(defs) == 0:
            raise Exception("len(defs) == 0")
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula()
        return Expand(fact=fact, defs=defs, conclusion=conclusion)

    def parse_pad(self) -> Pad:
        self.stream.consume("PAD")
        fact = self.parse_formula()
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula()
        if not isinstance(conclusion, Or):
            raise Exception("Conclusion of Pad has to be Or object")
        return Pad(fact=fact, conclusion=conclusion)

    def parse_split(self) -> Split:
        self.stream.consume("SPLIT")
        if self.stream.peek().type == "NUMBER":
            index = int(self.stream.consume("NUMBER").value)
        else:
            index = None
        fact = self.parse_reference_or_formula()
        if not isinstance(fact, (And, Iff)):
            raise Exception("Fact of Split has to be And or Iff object")
        return Split(index=index, fact=fact)

    def parse_connect(self):
        self.stream.consume("CONNECT")
        conclusion = self.parse_formula()
        if not isinstance(conclusion, (And, Iff)):
            raise Exception("Conclusion of Connect has to be And or Iff object")
        return Connect(conclusion=conclusion)

    def parse_substitute(self) -> Substitute:
        self.stream.consume("SUBSTITUTE")
        fact = self.parse_reference_or_formula()
        self.stream.consume("FOR")
        env: dict[Term, Term] = {}
        evidence: dict[Term, str] = {}
        while True:
            key = self.parse_term()
            self.stream.consume("COLON")
            value = self.parse_term()
            env[key] = value
            if self.stream.peek().type == "BY":
                self.stream.consume("BY")
                evidence_name = self.stream.consume("IDENT").value
                evidence[key] = evidence_name
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula()
        return Substitute(fact=fact, env=env, evidence=evidence, conclusion=conclusion)

    def parse_show(self) -> Show:
        self.stream.consume("SHOW")
        conclusion = self.parse_bot_or_formula()
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        return Show(conclusion=conclusion, body=body)

    def parse_reference_or_formula(self) -> str | Formula:
        if self.stream.peek().type == "IDENT" and self.context.has_reference(self.stream.peek().value):
            return self.stream.consume("IDENT").value
        else:
            return self.parse_formula()

    def parse_bot_or_formula(self) -> Bottom | Formula:
        if self.stream.peek().type == "BOT":
            self.stream.consume("BOT")
            return Bottom()
        else:
            return self.parse_formula()

    def parse_formula(self) -> Formula:
        return self.parse_implies()

    def parse_implies(self) -> Formula:
        left = self.parse_and()
        while self.stream.peek().type in ("IMPLIES", "IFF"):
            op = self.stream.peek().type
            self.stream.consume(op)
            right = self.parse_and()
            if op == "IMPLIES":
                left = Implies(left, right)
            elif op == "IFF":
                left = Iff(left, right)
        return left

    def parse_and(self) -> Formula:
        left = self.parse_primary()
        while self.stream.peek().type in ("AND", "OR"):
            op = self.stream.peek().type
            self.stream.consume(op)
            right = self.parse_primary()
            if op == "AND":
                left = And(left, right)
            elif op == "OR":
                left = Or(left, right)
        return left

    def parse_primary(self) -> Formula:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            name = self.stream.consume("IDENT").value
            if name in self.bound_items or name in self.free_items:
                if name in self.bound_items:
                    template = self.bound_items[name]
                else:
                    template = self.free_items[name]
                if not isinstance(template, Template):
                    raise Exception(f"{template} is not Template object")
                if template.arity == 0:
                    args: list[Term] = []
                else:
                    self.stream.consume("LPAREN")
                    args: list[Term] = []
                    while True:
                        args.append(self.parse_var())
                        if self.stream.peek().type == "COMMA":
                            self.stream.consume("COMMA")
                        else:
                            break
                    self.stream.consume("RPAREN")
                    if len(args) != template.arity:
                        raise SyntaxError("arity is different")
                return TemplateCall(template, tuple(args))
            elif name in self.context.primpreds or name in self.context.defpreds:
                if name in self.context.primpreds:
                    arity = self.context.primpreds[name].arity
                else:
                    arity = len(self.context.defpreds[name].args)
                self.stream.consume("LPAREN")
                args = [self.parse_term()]
                while self.stream.peek().type == "COMMA":
                    self.stream.consume("COMMA")
                    args.append(self.parse_term())
                if len(args) != arity:
                    raise SyntaxError("arity is different")
                self.stream.consume("RPAREN")
                return Symbol(Pred(name), tuple(args))
            else:
                raise SyntaxError(f"not found in primpreds or defpreds: {name}")

        elif tok.type == "LPAREN":
            self.stream.consume("LPAREN")
            expr = self.parse_formula()
            self.stream.consume("RPAREN")
            return expr
        
        elif tok.type == "NOT":
            self.stream.consume("NOT")
            self.stream.consume("LPAREN")
            body = self.parse_formula()
            self.stream.consume("RPAREN")
            return Not(body)

        elif tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_TEMPLATE"):
            quantifiers: list[str] = []
            items: list[Var | Template] = []
            while tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_TEMPLATE"):
                if tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ"):
                    quantifiers.append(self.stream.consume(tok.type).type)
                    var = self.parse_var()
                    items.append(var)
                    self.bound_items[var.name] = var
                    tok = self.stream.peek()
                else:
                    quantifiers.append(self.stream.consume(tok.type).type)
                    template = self.parse_template()
                    items.append(template)
                    self.bound_items[template.name] = template
                    tok = self.stream.peek()
            self.stream.consume("LPAREN")
            body = self.parse_formula()
            self.stream.consume("RPAREN")
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
        tok = self.stream.peek()
        if tok.type == "IDENT":
            name = self.stream.consume("IDENT").value
            if name in self.bound_items:
                return self.bound_items[name]
            elif name in self.free_items:
                return self.free_items[name]
            elif name in self.context.defcons:
                return Con(name)
            elif name in self.context.deffuns or name in self.context.deffunterms:
                self.stream.consume("LPAREN")
                args = [self.parse_term()]
                while self.stream.peek().type == "COMMA":
                    self.stream.consume("COMMA")
                    args.append(self.parse_term())
                self.stream.consume("RPAREN")
                args = tuple(args)
                if name in self.context.deffuns and len(args) != self.context.deffuns[name].arity:
                    raise SyntaxError("arity is different (deffun)")
                if name in self.context.deffunterms and len(args) != len(self.context.deffunterms[name].args):
                    raise SyntaxError("arity is different (deffunterm)")
                return Compound(Fun(name), args)
            else:
                raise SyntaxError(f"Unexpected token: {tok}")
        elif tok.type == "LAMBDA":
            self.stream.consume("LAMBDA")
            vars: list[Var] = []
            while True:
                vars.append(self.parse_var())
                if self.stream.peek().type == "COMMA":
                    self.stream.consume("COMMA")
                else:
                    break
            for var in vars:
                self.free_items[var.name] = var
            self.stream.consume("DOT")
            formula = self.parse_formula()
            for var in vars:
                self.free_items.pop(var.name)
            return Lambda(tuple(vars), formula)
        else:
            raise SyntaxError(f"Unexpected token: {tok}")

    def parse_tex(self) -> list[str]:
        self.stream.consume("TEX")
        tex: list[str] = []
        while True:
            tex.append(self.stream.consume("STRING").value)
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return tex

    def parse_var(self) -> Var:
        var_name = self.stream.consume("IDENT").value
        return Var(var_name)

    def parse_template(self) -> Template:
        template_name = self.stream.consume("IDENT").value
        self.stream.consume("LBRACKET")
        arity = int(self.stream.consume("NUMBER").value)
        self.stream.consume("RBRACKET")
        return Template(template_name, arity)

if __name__ == "__main__":
    import sys
    path = sys.argv[1]

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

    from dependency import DependencyResolver
    resolver = DependencyResolver()
    resolver.resolve(path)
    resolved_files, tokens_cache = resolver.get_result()
    parser_context = Context.init()
    for file in resolved_files:
        parser = Parser(tokens_cache[file])
        _, parser_context = parser.parse_file(parser_context)
