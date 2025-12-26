from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, Symbol, And, Or, Implies, Forall, Exists, Not, Bottom, PrimPred, DefPred, Iff, Axiom, Invoke, Expand, ExistsUniq, DefCon, Pad, Split, Connect, DefConExist, DefConUniq, DefFun, DefFunExist, DefFunUniq, Compound, Fun, Con, Var, DefFunTerm, Equality, Substitute, Characterize, Show, Pred, EqualityReflection, EqualityReplacement, Term, Formula, Control, Declaration, Template, Lambda, TemplateCall, Include, Assert, Fold
from lexer import Token
from token_stream import TokenStream
from logic_utils import collect_quantifier_vars

import logging
logger = logging.getLogger("proof")

# === パーサー本体 ===
class Parser:
    def __init__(self, tokens: list[Token]):
        self.stream = TokenStream(tokens)

    def parse_file(self, context: Context) -> tuple[list[Include | Declaration], Context]:
        ast: list[Include | Declaration] = []
        while True:
            tok = self.stream.peek()
            if tok.type == "INCLUDE":
                ast.append(self.parse_include())
            elif tok.type == "PRIMITIVE":
                ast.append(self.parse_primitive(context))
            elif tok.type == "AXIOM":
                ast.append(self.parse_axiom(context))
            elif tok.type == "THEOREM":
                ast.append(self.parse_theorem(context))
            elif tok.type == "DEFINITION":
                ast.append(self.parse_definition(context))
            elif tok.type == "EXISTENCE":
                ast.append(self.parse_existence(context))
            elif tok.type == "UNIQUENESS":
                ast.append(self.parse_uniqueness(context))
            elif tok.type == "EQUALITY":
                ast.append(self.parse_equality(context))
            elif tok.type == "EOF":
                break
            else:
                raise SyntaxError(f"{tok.info()}Include, Declaration or EOF is required")
        return ast, context

    def parse_primitive(self, context: Context) -> PrimPred:
        start_token = self.stream.consume("PRIMITIVE")
        tok = self.stream.peek()
        if tok.type == "PREDICATE":
            self.stream.consume("PREDICATE")
            name = self.stream.consume("IDENT").value
            self.stream.consume("ARITY")
            arity = int(self.stream.consume("NUMBER").value)
            tex = self.parse_or_create_tex(name, arity)
            if len(tex) != arity + 1:
                raise SyntaxError(f"{start_token.info()} arity of {name} is {arity}, but length of tex is {len(tex)}")
            primpred = PrimPred(name=name, token=start_token, arity=arity, tex=tex)
            context.add_decl(primpred)
            logger.debug(f"[primpred] {name}")
            return primpred
        else:
            raise SyntaxError(f"{start_token.info()} predicate is required")

    def parse_axiom(self, context: Context) -> Axiom:
        start_token = self.stream.consume("AXIOM")
        name = self.stream.consume("IDENT").value
        conclusion = self.parse_formula(context)
        axiom = Axiom(name=name, token=start_token, conclusion=conclusion)
        context.add_decl(axiom)
        logger.debug(f"[axiom] {name}")
        return axiom

    def parse_theorem(self, context: Context) -> Theorem:
        start_token = self.stream.consume("THEOREM")
        name = self.stream.consume("IDENT").value
        conclusion = self.parse_formula(context)
        self.stream.consume("LBRACE")
        proof = self.parse_block(context.copy_ctrl())
        self.stream.consume("RBRACE")
        theorem = Theorem(name=name, token=start_token, conclusion=conclusion, proof=proof)
        context.add_decl(theorem)
        logger.debug(f"[theorem] {name}")
        return theorem

    def parse_definition(self, context: Context) -> DefPred | DefCon | DefFun | DefFunTerm:
        start_token = self.stream.consume("DEFINITION")
        tok = self.stream.peek()
        if tok.type == "PREDICATE":
            return self.parse_defpred(context, start_token)
        elif tok.type == "CONSTANT":
            return self.parse_defcon(context, start_token)
        elif tok.type == "FUNCTION":
            return self.parse_deffun_or_deffunterm(context, start_token)
        else:
            raise SyntaxError(f"{start_token.info()} predicate, constant or function is required after definition")

    def parse_defpred(self, context: Context, start_token: Token) -> DefPred:
        self.stream.consume("PREDICATE")
        if self.stream.peek().type == "AUTOEXPAND":
            self.stream.consume("AUTOEXPAND")
            autoexpand = True
        else:
            autoexpand =False
        name = self.stream.consume("IDENT").value
        self.stream.consume("LPAREN")
        args, local_vars, local_templates = self.parse_vars_or_templates()
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        formula = self.parse_formula(context.add_form(local_vars, local_templates))
        tex = self.parse_or_create_tex(name, len(args))
        if len(tex) != len(args) + 1:
            raise SyntaxError(f"{start_token.info()} arity of {name} is {len(args)}, but length of tex is {len(tex)}")
        defpred = DefPred(name=name, token=start_token, args=args, formula=formula, autoexpand=autoexpand, tex=tex)
        context.add_decl(defpred)
        logger.debug(f"[defpred] {name}")
        return defpred

    def parse_defcon(self, context: Context, start_token: Token) -> DefCon:
        self.stream.consume("CONSTANT")
        name = self.stream.consume("IDENT").value
        self.stream.consume("BY")
        theorem = self.stream.consume("IDENT").value
        tex = self.parse_or_create_tex(name, 0)
        if len(tex) != 1:
            raise SyntaxError(f"{start_token.info()} {name} is constant, but length of tex is {len(tex)}")
        defcon = DefCon(name=name, token=start_token, theorem=theorem, tex=tex)
        context.add_decl(defcon)
        logger.debug(f"[defcon] {name}")
        return defcon

    def parse_deffun_or_deffunterm(self, context: Context, start_token: Token) -> DefFun | DefFunTerm:
        self.stream.consume("FUNCTION")
        name = self.stream.consume("IDENT").value
        if self.stream.peek().type == "BY":
            return self.parse_deffun(context, start_token, name)
        else:
            return self.parse_deffunterm(context, start_token, name)

    def parse_deffun(self, context: Context, start_token: Token, name: str) -> DefFun:
        self.stream.consume("BY")
        theorem = self.stream.consume("IDENT").value
        vars_, body = collect_quantifier_vars(context.decl.theorems[theorem].conclusion, Forall)
        if not (len(vars_) > 0 and isinstance(body, ExistsUniq)):
            raise SyntaxError(f"{start_token.info()} conclusion of {theorem} cannot be used for function definition")
        arity = len(vars_)
        tex = self.parse_or_create_tex(name, arity)
        if len(tex) != arity + 1:
            raise SyntaxError(f"{start_token.info()} arity or {name} is {arity}, but length of tex is {len(tex)}")
        deffun = DefFun(name=name, token=start_token, arity=arity, theorem=theorem, tex=tex)
        context.add_decl(deffun)
        logger.debug(f"[deffun] {name}")
        return deffun

    def parse_deffunterm(self, context: Context, start_token: Token, name: str):
        self.stream.consume("LPAREN")
        args, local_vars, local_templates = self.parse_vars_or_templates()
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        term = self.parse_term(context.add_form(local_vars, local_templates))
        tex = self.parse_or_create_tex(name, len(args))
        if len(tex) != len(args) + 1:
            raise SyntaxError(f"{start_token.info()} arity of {name} is {len(args)}, but length of tex is {len(tex)}")
        deffunterm = DefFunTerm(name=name, token=start_token, args=args, term=term, tex=tex)
        context.add_decl(deffunterm)
        logger.debug(f"[deffunterm] {name}")
        return deffunterm

    def parse_existence(self, context: Context) -> DefConExist | DefFunExist:
        start_token = self.stream.consume("EXISTENCE")
        existence_name = self.stream.consume("IDENT").value
        existence_formula = self.parse_formula(context)
        self.stream.consume("BY")
        name = self.stream.consume("IDENT").value
        if name in context.decl.defcons:
            defconexist = DefConExist(name=existence_name, token=start_token, formula=existence_formula, con_name=name)
            context.add_decl(defconexist)
            return defconexist
        elif name in context.decl.deffuns:
            deffunexist = DefFunExist(name=existence_name, token=start_token, formula=existence_formula, fun_name=name)
            context.add_decl(deffunexist)
            return deffunexist
        else:
            raise Exception(f"{start_token.info()} defcon or deffun is required, but {name} is unknown")

    def parse_uniqueness(self, context: Context) -> DefConUniq | DefFunUniq:
        start_token = self.stream.consume("UNIQUENESS")
        uniqueness_name = self.stream.consume("IDENT").value
        uniqueness_formula = self.parse_formula(context)
        self.stream.consume("BY")
        name = self.stream.consume("IDENT").value
        if name in context.decl.defcons:
            defconuniq = DefConUniq(name=uniqueness_name, token=start_token, formula=uniqueness_formula, con_name=name)
            context.add_decl(defconuniq)
            return defconuniq
        elif name in context.decl.deffuns:
            deffununiq = DefFunUniq(name=uniqueness_name, token=start_token, formula=uniqueness_formula, fun_name=name)
            context.add_decl(deffununiq)
            return deffununiq
        else:
            raise Exception(f"{start_token.info()} defcon or deffun is required, but {name} is unknown")

    def parse_equality(self, context: Context) -> Equality:
        start_token = self.stream.consume("EQUALITY")
        name = self.stream.consume("IDENT").value
        if name in context.decl.primpreds:
            equal = context.decl.primpreds[name]
            if equal.arity != 2:
                raise Exception(f"{start_token.info()} arity is required to be 2, but arity of {name} is {equal.arity}")
        elif name in context.decl.defpreds:
            equal = context.decl.defpreds[name]
            if len(equal.args) != 2:
                raise Exception(f"{start_token.info()} arity is required to be 2, but arity of {name} is {len(equal.args)}")
        else:
            raise Exception(f"{start_token.info()} primpred or defpred is required, but {name} is unknown")
        reflection = self.parse_equality_reflection(equal, context)
        replacement = self.parse_equality_replacement(equal, context)
        equality = Equality(name=name, token=start_token, equal=equal, reflection=reflection, replacement=replacement)
        context.add_decl(equality)
        logger.debug(f"[equality] {type(equal)}: {equal.name}")
        return equality

    def parse_equality_reflection(self, equal: PrimPred | DefPred, context: Context) -> EqualityReflection:
        start_token = self.stream.consume("REFLECTION")
        name = self.stream.consume("IDENT").value
        if name in context.decl.axioms:
            reflection_evidence = context.decl.axioms[name]
        elif name in context.decl.theorems:
            reflection_evidence = context.decl.theorems[name]
        else:
            raise Exception(f"{start_token.info()} axiom or theorem is required, but {name} is unknown")
        return EqualityReflection(token=start_token, equal=equal, evidence=reflection_evidence)

    def parse_equality_replacement(self, equal: PrimPred | DefPred, context: Context) -> EqualityReplacement:
        start_token = self.stream.consume("REPLACEMENT")
        replacement_evidence: dict[str, Axiom | Theorem] = {}
        while True:
            predicate = self.stream.consume("IDENT").value
            if not (predicate == equal.name or predicate in context.decl.primpreds):
                raise Exception(f"{start_token.info()} {equal.name} or primpred is required, but {predicate} is unknown")
            self.stream.consume("COLON")
            name = self.stream.consume("IDENT").value
            if name in context.decl.axioms:
                formula = context.decl.axioms[name]
            elif name in context.decl.theorems:
                formula = context.decl.theorems[name]
            else:
                raise Exception(f"{start_token.info()} axiom or theorem is required, but {name} is unknown")
            replacement_evidence[predicate] = formula
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return EqualityReplacement(token=start_token, equal=equal, evidence=replacement_evidence)

    def parse_include(self) -> Include:
        self.stream.consume("INCLUDE")
        file = self.stream.consume("STRING").value
        return Include(file)

    def parse_block(self, context: Context) -> list[Control]:
        body: list[Control] = []
        while True:
            tok = self.stream.peek()
            if not tok or tok.type == "RBRACE":
                break
            if tok.type == "ANY":
                body.append(self.parse_any(context))
            elif tok.type == "ASSUME":
                body.append(self.parse_assume(context))
            elif tok.type == "DIVIDE":
                body.append(self.parse_divide(context))
            elif tok.type == "SOME":
                body.append(self.parse_some(context))
            elif tok.type == "DENY":
                body.append(self.parse_deny(context))
            elif tok.type == "CONTRADICT":
                body.append(self.parse_contradict(context))
            elif tok.type == "EXPLODE":
                body.append(self.parse_explode(context))
            elif tok.type == "APPLY":
                body.append(self.parse_apply(context))
            elif tok.type == "LIFT":
                body.append(self.parse_lift(context))
            elif tok.type == "CHARACTERIZE":
                body.append(self.parse_characterize(context))
            elif tok.type == "INVOKE":
                body.append(self.parse_invoke(context))
            elif tok.type == "EXPAND":
                body.append(self.parse_expand(context))
            elif tok.type == "FOLD":
                body.append(self.parse_fold(context))
            elif tok.type == "PAD":
                body.append(self.parse_pad(context))
            elif tok.type == "SPLIT":
                body.append(self.parse_split(context))
            elif tok.type == "CONNECT":
                body.append(self.parse_connect(context))
            elif tok.type == "SUBSTITUTE":
                body.append(self.parse_substitute(context))
            elif tok.type == "SHOW":
                body.append(self.parse_show(context))
            elif tok.type == "ASSERT":
                body.append(self.parse_assert(context))
            else:
                raise SyntaxError(f"{tok.info()} Control is reqiured")
        return body

    def parse_any(self, context: Context) -> Any:
        start_token = self.stream.consume("ANY")
        items, local_vars, local_templates = self.parse_vars_or_templates()
        self.stream.consume("LBRACE")
        body = self.parse_block(context.add_ctrl(local_vars, [], local_templates))
        self.stream.consume("RBRACE")
        return Any(token=start_token, items=items, body=body)

    def parse_assume(self, context: Context) -> Assume:
        start_token = self.stream.consume("ASSUME")
        premise = self.parse_formula(context)
        self.stream.consume("LBRACE")
        body = self.parse_block(context.copy_ctrl())
        self.stream.consume("RBRACE")
        return Assume(token=start_token, premise=premise, body=body)
    
    def parse_divide(self, context: Context) -> Divide:
        start_token = self.stream.consume("DIVIDE")
        fact = self.parse_reference_or_formula(context)
        cases: list[Case] = []
        while self.stream.peek().type == "CASE":
            cases.append(self.parse_case(context.copy_ctrl()))
        if len(cases) < 2:
            raise SyntaxError(f"{start_token.info()} At least two cases are required")
        return Divide(token=start_token, fact=fact, cases=cases)
    
    def parse_case(self, context: Context) -> Case:
        start_token = self.stream.consume("CASE")
        premise = self.parse_formula(context)
        self.stream.consume("LBRACE")
        body = self.parse_block(context.copy_ctrl())
        self.stream.consume("RBRACE")
        return Case(token=start_token, premise=premise, body=body)
    
    def parse_some(self, context: Context) -> Some:
        start_token = self.stream.consume("SOME")
        items: list[Var | Template | None] = []
        while True:
            if self.stream.peek().type == "UNDERSCORE":
                items.append(None)
            else:
                items.append(self.parse_var())
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        self.stream.consume("SUCH")
        fact = self.parse_reference_or_formula(context)
        self.stream.consume("LBRACE")
        local_vars = [item for item in items if isinstance(item, Var)]
        local_templates = [item for item in items if isinstance(item, Template)]
        body = self.parse_block(context.add_ctrl(local_vars, [], local_templates))
        self.stream.consume("RBRACE")
        return Some(token=start_token, items=items, fact=fact, body=body)
    
    def parse_deny(self, context: Context) -> Deny:
        start_token = self.stream.consume("DENY")
        premise = self.parse_formula(context)
        self.stream.consume("LBRACE")
        body = self.parse_block(context.copy_ctrl())
        self.stream.consume("RBRACE")
        return Deny(token=start_token, premise=premise, body=body)
    
    def parse_contradict(self, context: Context) -> Contradict:
        start_token = self.stream.consume("CONTRADICT")
        contradiction = self.parse_formula(context)
        return Contradict(token=start_token, contradiction=contradiction)
    
    def parse_explode(self, context: Context) -> Explode:
        start_token = self.stream.consume("EXPLODE")
        conclusion = self.parse_formula(context)
        return Explode(token=start_token, conclusion=conclusion)

    def parse_apply(self, context: Context) -> Apply:
        start_token = self.stream.consume("APPLY")
        if self.stream.peek().type == "INVOKE":
            self.stream.consume("INVOKE")
            if self.stream.peek().type == "RIGHTWARD":
                self.stream.consume("RIGHTWARD")
                invoke = "invoke-rightward"
            elif self.stream.peek().type == "LEFTWARD":
                self.stream.consume("LEFTWARD")
                invoke = "invoke-leftward"
            else:
                invoke = "invoke"
        else:
            invoke = "none"
        fact = self.parse_reference_or_formula(context)
        self.stream.consume("FOR")
        terms = self.parse_terms_or_none(context)
        return Apply(token=start_token, invoke=invoke, fact=fact, terms=terms)

    def parse_lift(self, context: Context) -> Lift:
        start_token = self.stream.consume("LIFT")
        self.stream.consume("FOR")
        terms = self.parse_terms_or_none(context)
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula(context)
        if not isinstance(conclusion, Exists):
            raise Exception(f"{start_token.info()} Exists object is required")
        return Lift(token=start_token, terms=terms, conclusion=conclusion)

    def parse_characterize(self, context: Context) -> Characterize:
        start_token = self.stream.consume("CHARACTERIZE")
        self.stream.consume("FOR")
        term = self.parse_term(context)
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula(context)
        if not isinstance(conclusion, ExistsUniq):
            raise Exception(f"{start_token.info()} ExistsUniq object is required")
        return Characterize(token=start_token, term=term, conclusion=conclusion)

    def parse_invoke(self, context: Context) -> Invoke:
        start_token = self.stream.consume("INVOKE")
        if self.stream.peek().type == "RIGHTWARD":
            self.stream.consume("RIGHTWARD")
            direction = "rightward"
        elif self.stream.peek().type == "LEFTWARD":
            self.stream.consume("LEFTWARD")
            direction = "leftward"
        else:
            direction = "none"
        fact = self.parse_formula(context)
        if direction == "none":
            if not isinstance(fact, Implies):
                raise Exception(f"{start_token.info()} Implies object is required")
        else:
            if not isinstance(fact, Iff):
                raise Exception(f"{start_token.info()} Iff object is required")
        return Invoke(token=start_token, direction=direction, fact=fact)

    def parse_expand(self, context: Context) -> Expand:
        start_token = self.stream.consume("EXPAND")
        fact = self.parse_formula(context)
        self.stream.consume("FOR")
        defs: list[str] = []
        indexes: dict[str, list[int]] = {}
        while True:
            definition = self.stream.consume("IDENT").value
            defs.append(definition)
            if self.stream.peek().type == "LBRACKET":
                self.stream.consume("LBRACKET")
                indexes_: list[int] = []
                while True:
                    indexes_.append(int(self.stream.consume("NUMBER").value))
                    if self.stream.peek().type == "COMMA":
                        self.stream.consume("COMMA")
                    else:
                        break
                self.stream.consume("RBRACKET")
                indexes[definition] = indexes_
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return Expand(token=start_token, fact=fact, defs=defs, indexes=indexes)

    def parse_fold(self, context: Context) -> Fold:
        start_token = self.stream.consume("FOLD")
        self.stream.consume("FOR")
        defs: list[str] = []
        indexes: dict[str, list[int]] = {}
        while True:
            definition = self.stream.consume("IDENT").value
            defs.append(definition)
            if self.stream.peek().type == "LBRACKET":
                self.stream.consume("LBRACKET")
                indexes_: list[int] = []
                while True:
                    indexes_.append(int(self.stream.consume("NUMBER").value))
                    if self.stream.peek().type == "COMMA":
                        self.stream.consume("COMMA")
                    else:
                        break
                self.stream.consume("RBRACKET")
                indexes[definition] = indexes_
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula(context)
        return Fold(token=start_token, defs=defs, indexes=indexes, conclusion=conclusion)

    def parse_pad(self, context: Context) -> Pad:
        start_token = self.stream.consume("PAD")
        fact = self.parse_formula(context)
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula(context)
        if not isinstance(conclusion, Or):
            raise Exception(f"{start_token.info()} Or object is required")
        return Pad(token=start_token, fact=fact, conclusion=conclusion)

    def parse_split(self, context: Context) -> Split:
        start_token = self.stream.consume("SPLIT")
        if self.stream.peek().type == "NUMBER":
            index = int(self.stream.consume("NUMBER").value)
        else:
            index = None
        fact = self.parse_reference_or_formula(context)
        return Split(token=start_token, index=index, fact=fact)

    def parse_connect(self, context: Context) -> Connect:
        start_token = self.stream.consume("CONNECT")
        conclusion = self.parse_formula(context)
        return Connect(token=start_token, conclusion=conclusion)

    def parse_substitute(self, context: Context) -> Substitute:
        start_token = self.stream.consume("SUBSTITUTE")
        fact = self.parse_reference_or_formula(context)
        self.stream.consume("FOR")
        env: dict[Term, Term] = {}
        indexes: dict[Term, set[int]] = {}
        while True:
            key = self.parse_term(context)
            if self.stream.peek().type == "LBRACKET":
                self.stream.consume("LBRACKET")
                indexes_: list[int] = []
                while True:
                    indexes_.append(int(self.stream.consume("NUMBER").value))
                    if self.stream.peek().type == "COMMA":
                        self.stream.consume("COMMA")
                    else:
                        break
                self.stream.consume("RBRACKET")
                indexes[key] = indexes_
            self.stream.consume("COLON")
            value = self.parse_term(context)
            env[key] = value
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return Substitute(token=start_token, fact=fact, env=env, indexes=indexes)

    def parse_show(self, context: Context) -> Show:
        start_token = self.stream.consume("SHOW")
        conclusion = self.parse_bot_or_formula(context)
        self.stream.consume("LBRACE")
        body = self.parse_block(context.copy_ctrl())
        self.stream.consume("RBRACE")
        return Show(token=start_token, conclusion=conclusion, body=body)

    def parse_assert(self, context: Context) -> Assert:
        start_token = self.stream.consume("ASSERT")
        reference = self.parse_reference_or_formula(context)
        return Assert(token=start_token, reference=reference)

    def parse_reference_or_formula(self, context: Context) -> str | Formula:
        if self.stream.peek().type == "IDENT" and context.decl.has_reference(self.stream.peek().value):
            return self.stream.consume("IDENT").value
        else:
            return self.parse_formula(context)

    def parse_bot_or_formula(self, context: Context) -> Bottom | Formula:
        if self.stream.peek().type == "BOT":
            self.stream.consume("BOT")
            return Bottom()
        else:
            return self.parse_formula(context)

    def parse_formula(self, context: Context) -> Formula:
        return self.parse_implies(context.copy_form())

    def parse_implies(self, context: Context) -> Formula:
        left = self.parse_and(context.copy_form())
        while self.stream.peek().type in ("IMPLIES", "IFF"):
            op = self.stream.peek().type
            self.stream.consume(op)
            right = self.parse_and(context.copy_form())
            if op == "IMPLIES":
                left = Implies(left, right)
            elif op == "IFF":
                left = Iff(left, right)
        return left

    def parse_and(self, context: Context) -> Formula:
        left = self.parse_primary(context.copy_form())
        while self.stream.peek().type in ("AND", "OR"):
            op = self.stream.peek().type
            self.stream.consume(op)
            right = self.parse_primary(context.copy_form())
            if op == "AND":
                left = And(left, right)
            elif op == "OR":
                left = Or(left, right)
        return left

    def parse_primary(self, context: Context) -> Formula:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            name = self.stream.consume("IDENT").value
            if any(template.name == name for template in context.form.templates) or any(template.name == name for template in context.ctrl.templates):
                if any(template.name == name for template in context.form.templates):
                    template = next(template for template in context.form.templates if template.name == name)
                else:
                    template = next(template for template in context.ctrl.templates if template.name == name)
                if template.arity == 0:
                    vars: list[Var] = []
                else:
                    self.stream.consume("LPAREN")
                    vars = self.parse_vars()
                    self.stream.consume("RPAREN")
                    if len(vars) != template.arity:
                        raise SyntaxError(f"{tok.info()} arity of {template.name} is {template.arity}, but length of args is {len(vars)}")
                return TemplateCall(template, tuple(vars))
            elif name in context.decl.primpreds or name in context.decl.defpreds:
                if name in context.decl.primpreds:
                    arity = context.decl.primpreds[name].arity
                else:
                    arity = len(context.decl.defpreds[name].args)
                self.stream.consume("LPAREN")
                args = [self.parse_term(context.copy_form())]
                while self.stream.peek().type == "COMMA":
                    self.stream.consume("COMMA")
                    args.append(self.parse_term(context.copy_form()))
                if len(args) != arity:
                    raise SyntaxError(f"{tok.info()} arity of {name} is {arity}, but length of args is {len(args)}")
                self.stream.consume("RPAREN")
                return Symbol(Pred(name), tuple(args))
            else:
                raise SyntaxError(f"{tok.info()} Formula object is required, but {name} is unknown")

        elif tok.type == "LPAREN":
            self.stream.consume("LPAREN")
            expr = self.parse_formula(context.copy_form())
            self.stream.consume("RPAREN")
            return expr
        
        elif tok.type == "NOT":
            self.stream.consume("NOT")
            self.stream.consume("LPAREN")
            body = self.parse_formula(context.copy_form())
            self.stream.consume("RPAREN")
            return Not(body)

        elif tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_TEMPLATE"):
            quantifiers: list[str] = []
            items: list[Var | Template] = []
            local_bound_vars: list[Var] = []
            local_bound_templates: list[Template] = []
            while tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_TEMPLATE"):
                if tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ"):
                    quantifiers.append(self.stream.consume(tok.type).type)
                    var = self.parse_var()
                    items.append(var)
                    local_bound_vars.append(var)
                    tok = self.stream.peek()
                else:
                    quantifiers.append(self.stream.consume(tok.type).type)
                    template = self.parse_template()
                    items.append(template)
                    local_bound_templates.append(template)
                    tok = self.stream.peek()
            self.stream.consume("LPAREN")
            body = self.parse_formula(context.add_form(local_bound_vars, local_bound_templates))
            self.stream.consume("RPAREN")
            for quantifier, item in zip(reversed(quantifiers), reversed(items)):
                if quantifier == "FORALL" or quantifier == "FORALL_TEMPLATE":
                    body = Forall(item, body)
                elif quantifier == "EXISTS":
                    body = Exists(item, body)
                elif quantifier == "EXISTS_UNIQ":
                    body = ExistsUniq(item, body)
            return body

        else:
            raise SyntaxError(f"{tok.info()} Formula objct is required, but unknown token is found")

    def parse_terms_or_none(self, context: Context) -> list[Term | None]:
        terms: list[Term | None] = []
        while True:
            if self.stream.peek().type == "UNDERSCORE":
                terms.append(None)
            else:
                terms.append(self.parse_term(context))
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return terms

    def parse_term(self, context: Context) -> Term:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            name = self.stream.consume("IDENT").value
            if any(var.name == name for var in context.form.vars):
                return next(var for var in context.form.vars if var.name == name)
            elif any(template.name == name for template in context.form.templates):
                return next(template for template in context.form.templates if template.name == name)
            elif any(var.name == name for var in context.ctrl.vars):
                return next((var for var in context.ctrl.vars if var.name == name))
            elif any(template.name == name for template in context.ctrl.templates):
                return next((template for template in context.ctrl.templates if template.name == name))
            elif name in context.decl.defcons:
                return Con(name)
            elif name in context.decl.deffuns or name in context.decl.deffunterms:
                self.stream.consume("LPAREN")
                args = [self.parse_term(context.copy_form())]
                while self.stream.peek().type == "COMMA":
                    self.stream.consume("COMMA")
                    args.append(self.parse_term(context.copy_form()))
                self.stream.consume("RPAREN")
                args = tuple(args)
                if name in context.decl.deffuns:
                    arity = context.decl.deffuns[name].arity
                    if len(args) != arity:
                        raise SyntaxError(f"{tok.info()} arity of {name} is {arity}, but length of args is {len(args)}")
                else:
                    arity = len(context.decl.deffunterms[name].args)
                    if len(args) != arity:
                        raise SyntaxError(f"{tok.info()} arity of {name} is {arity}, but lenfth of args is {len(args)}")
                return Compound(Fun(name), args)
            elif name in context.decl.primpreds or name in context.decl.defpreds:
                if name in context.decl.primpreds:
                    arity = context.decl.primpreds[name].arity
                else:
                    arity = len(context.decl.defpreds[name].args)
                args = [Var(f"x_{i}") for i in range(arity)]
                return Lambda(tuple(args), Symbol(Pred(name), tuple(args)))
            else:
                raise SyntaxError(f"{tok.info()} Term object is required, but {name} is unknown")
        elif tok.type == "LAMBDA":
            self.stream.consume("LAMBDA")
            if self.stream.peek().type == "DOT":
                vars: list[Var] = []
            else:
                vars = self.parse_vars()
            self.stream.consume("DOT")
            formula = self.parse_formula(context.add_form(vars, []))
            return Lambda(tuple(vars), formula)
        else:
            raise SyntaxError(f"{tok.info()} Term object is required, but unknown token is found at")

    def parse_or_create_tex(self, name: str, arity: int) -> list[str]:
        if self.stream.peek().type == "TEX":
            return self.parse_tex()
        else:
            return self.create_tex(name, arity)

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

    def create_tex(self, name: str, arity: int):
        if arity == 0:
            tex = [f"\\mathrm{{{name}}}"]
        else:
            tex = [f"\\mathrm{{{name}}}("]
            tex.extend(["," for _ in range(arity - 1)])
            tex.append(")")
        return tex

    def parse_vars_or_templates(self) -> tuple[list[Var | Template], list[Var], list[Template]]:
        items: list[Var | Template] = []
        vars: list[Var] = []
        templates: list[Template] = []
        while True:
            if self.stream.peek().type == "TEMPLATE":
                self.stream.consume("TEMPLATE")
                template = self.parse_template()
                items.append(template)
                templates.append(template)
            else:
                var = self.parse_var()
                items.append(var)
                vars.append(var)
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return items, vars, templates

    def parse_vars(self) -> list[Var]:
        vars: list[Var] = []
        while True:
            vars.append(self.parse_var())
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return vars

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
