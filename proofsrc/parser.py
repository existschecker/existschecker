from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, AtomicFormula, And, Or, Implies, Forall, Exists, Not, Bottom, PrimPred, DefPred, Iff, Axiom, Invoke, Expand, ExistsUniq, DefCon, Pad, Split, Connect, DefConExist, DefConUniq, DefFun, DefFunExist, DefFunUniq, Compound, RefDefCon, Var, DefFunTerm, Equality, Substitute, Characterize, Show, EqualityReflection, EqualityReplacement, Term, Formula, Control, Declaration, PredTemplate, PredLambda, Include, Assert, Fold, Membership, MembershipLambda, VarTerm, PredTerm, FunTemplate, FunTerm, FunLambda, RefPrimPred, RefDefPred, RefDefFun, RefDefFunTerm, InvalidInclude, InvalidDeclaration, InvalidControl, ContextError
from lexer import Token
from token_stream import TokenStream, TokenStreamError
from logic_utils import strip_forall_vars

from lsprotocol import types as lsp
from pygls import uris
from typing import Sequence

import logging
logger = logging.getLogger("proof")

class ParseError(Exception):
    pass

# === パーサー本体 ===
class Parser:
    def __init__(self, tokens: list[Token]):
        self.stream = TokenStream(tokens)

    def add_lsp_error(self, tok: Token, message: str, context: Context):
        uri = uris.from_fs_path(tok.file)
        if uri is None:
            return
        line = tok.line - 1
        col = tok.column - 1
        length = len(tok.value)
        diag = lsp.Diagnostic(
            range=lsp.Range(
                start=lsp.Position(line=line, character=col),
                end=lsp.Position(line=line, character=col + length)
            ),
            message=message,
            severity=lsp.DiagnosticSeverity.Error
        )
        if uri not in context.diagnostics:
            context.diagnostics[uri] = []
        context.diagnostics[uri].append(diag)

    def skip_until_next_inclide_or_declaration_or_EOF(self):
        while True:
            tok = self.stream.peek()
            if tok.type in ("INCLUDE", "PRIMITIVE", "AXIOM", "THEOREM", "DEFINITION", "EXISTENCE", "UNIQUENESS", "EQUALITY", "MEMBERSHIP", "EOF"):
                return
            else:
                self.stream.consume(tok.type)

    def skip_until_next_RBRACE_or_control(self):
        nest_level = 0
        while True:
            tok = self.stream.peek()
            if nest_level == 0 and tok.type in ("RBRACE", "ANY", "ASSUME", "DIVIDE", "SOME", "DENY", "CONTRADICT", "EXPLODE", "APPLY", "LIFT", "CHARACTERIZE", "INVOKE", "EXPAND", "FOLD", "PAD", "SPLIT", "CONNECT", "SUBSTITUTE", "SHOW", "ASSERT"):
                return
            else:
                if tok.type == "LBRACE":
                    nest_level += 1
                elif tok.type == "RBRACE":
                    nest_level -= 1
                self.stream.consume(tok.type)

    def parse_file(self, context: Context) -> tuple[list[Include | Declaration], Context]:
        ast: list[Include | Declaration] = []
        while True:
            tok = self.stream.peek()
            if tok.type == "EOF":
                break
            elif tok.type == "INCLUDE":
                include = self.parse_include(context)
                ast.append(include)
                if isinstance(include, InvalidInclude):
                    self.skip_until_next_inclide_or_declaration_or_EOF()
            else:
                declaration = self.parse_declaration(context, tok)
                ast.append(declaration)
                if isinstance(declaration, InvalidDeclaration):
                    self.skip_until_next_inclide_or_declaration_or_EOF()
        return ast, context

    def parse_declaration(self, context: Context, tok: Token) -> Declaration:
        try:
            if tok.type == "PRIMITIVE":
                return self.parse_primitive(context)
            elif tok.type == "AXIOM":
                return self.parse_axiom(context)
            elif tok.type == "THEOREM":
                return self.parse_theorem(context)
            elif tok.type == "DEFINITION":
                return self.parse_definition(context)
            elif tok.type == "EXISTENCE":
                return self.parse_existence(context)
            elif tok.type == "UNIQUENESS":
                return self.parse_uniqueness(context)
            elif tok.type == "EQUALITY":
                return self.parse_equality(context)
            elif tok.type == "MEMBERSHIP":
                return self.parse_membership(context)
            else:
                msg = "Declaration is required"
                self.add_lsp_error(tok, msg, context)
                raise ParseError()
        except ParseError:
            return InvalidDeclaration("<invalid>", tok)
        except (TokenStreamError, ContextError) as e:
            self.add_lsp_error(e.token, e.msg, context)
            return InvalidDeclaration(name="<invalid>", token=tok)

    def parse_primitive(self, context: Context) -> PrimPred:
        start_token = self.stream.consume("PRIMITIVE")
        self.stream.consume("PREDICATE")
        name = self.stream.consume("IDENT").value
        self.stream.consume("ARITY")
        arity = int(self.stream.consume("NUMBER").value)
        tex = self.parse_or_create_tex(name, arity)
        if len(tex) != arity + 1:
            msg = f"arity of {name} is {arity}, but length of tex is {len(tex)}"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
        primpred = PrimPred(name=name, token=start_token, arity=arity, tex=tex)
        context.add_decl(primpred)
        logger.debug(f"[primpred] {name}")
        return primpred

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
            msg = "predicate, constant or function is required after definition"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()

    def parse_defpred(self, context: Context, start_token: Token) -> DefPred:
        self.stream.consume("PREDICATE")
        if self.stream.peek().type == "AUTOEXPAND":
            self.stream.consume("AUTOEXPAND")
            autoexpand = True
        else:
            autoexpand =False
        name = self.stream.consume("IDENT").value
        self.stream.consume("LPAREN")
        args, local_vars, local_pred_tmpls, local_fun_tmpls = self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        formula = self.parse_formula(context.add_form(local_vars, local_pred_tmpls, local_fun_tmpls))
        tex = self.parse_or_create_tex(name, len(args))
        if len(tex) != len(args) + 1:
            msg = f"arity of {name} is {len(args)}, but length of tex is {len(tex)}"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
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
            msg = f"{name} is constant, but length of tex is {len(tex)}"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
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
        vars_, body = strip_forall_vars(context.decl.theorems[theorem].conclusion)
        if isinstance(body, ExistsUniq):
            existsuniq = body
        elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
            existsuniq = body.right
        else:
            msg = f"conclusion of {theorem} cannot be used for function definition"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
        arity = len(vars_)
        tex = self.parse_or_create_tex(name, arity)
        if len(tex) != arity + 1:
            msg = f"arity or {name} is {arity}, but length of tex is {len(tex)}"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
        deffun = DefFun(name=name, token=start_token, args=vars_, returned=existsuniq.var, theorem=theorem, tex=tex)
        context.add_decl(deffun)
        logger.debug(f"[deffun] {name}")
        return deffun

    def parse_deffunterm(self, context: Context, start_token: Token, name: str) -> DefFunTerm:
        self.stream.consume("LPAREN")
        args, local_vars, local_pred_tmpls, local_fun_tmpls = self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        term = self.parse_var_term(context.add_form(local_vars, local_pred_tmpls, local_fun_tmpls))
        tex = self.parse_or_create_tex(name, len(args))
        if len(tex) != len(args) + 1:
            msg = f"arity of {name} is {len(args)}, but length of tex is {len(tex)}"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
        deffunterm = DefFunTerm(name=name, token=start_token, args=args, varterm=term, tex=tex)
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
            msg = f"defcon or deffun is required, but {name} is unknown"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()

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
            msg = f"defcon or deffun is required, but {name} is unknown"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()

    def parse_equality(self, context: Context) -> Equality:
        start_token = self.stream.consume("EQUALITY")
        tok = self.stream.consume("IDENT")
        name = tok.value
        if name in context.decl.primpreds:
            equal = RefPrimPred(tok, name)
            if context.decl.primpreds[name].arity != 2:
                msg = f"arity is required to be 2, but arity of {name} is {context.decl.primpreds[name].arity}"
                self.add_lsp_error(start_token, msg, context)
                raise ParseError()
        elif name in context.decl.defpreds:
            equal = RefDefPred(tok, name)
            if len(context.decl.defpreds[name].args) != 2:
                msg = f"arity is required to be 2, but arity of {name} is {len(context.decl.defpreds[name].args)}"
                self.add_lsp_error(start_token, msg, context)
                raise ParseError()
        else:
            msg = f"primpred or defpred is required, but {name} is unknown"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
        reflection = self.parse_equality_reflection(equal, context)
        replacement = self.parse_equality_replacement(equal, context)
        equality = Equality(name=name, token=start_token, equal=equal, reflection=reflection, replacement=replacement)
        context.add_decl(equality)
        logger.debug(f"[equality] {type(equal)}: {equal.name}")
        return equality

    def parse_equality_reflection(self, equal: RefPrimPred | RefDefPred, context: Context) -> EqualityReflection:
        start_token = self.stream.consume("REFLECTION")
        name = self.stream.consume("IDENT").value
        if name in context.decl.axioms:
            reflection_evidence = context.decl.axioms[name]
        elif name in context.decl.theorems:
            reflection_evidence = context.decl.theorems[name]
        else:
            msg = f"axiom or theorem is required, but {name} is unknown"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
        return EqualityReflection(token=start_token, equal=equal, evidence=reflection_evidence)

    def parse_equality_replacement(self, equal: RefPrimPred | RefDefPred, context: Context) -> EqualityReplacement:
        start_token = self.stream.consume("REPLACEMENT")
        replacement_evidence: dict[str, Axiom | Theorem] = {}
        while True:
            predicate = self.stream.consume("IDENT").value
            if not (predicate == equal.name or predicate in context.decl.primpreds):
                msg = f"{equal.name} or primpred is required, but {predicate} is unknown"
                self.add_lsp_error(start_token, msg, context)
                raise ParseError()
            self.stream.consume("COLON")
            name = self.stream.consume("IDENT").value
            if name in context.decl.axioms:
                formula = context.decl.axioms[name]
            elif name in context.decl.theorems:
                formula = context.decl.theorems[name]
            else:
                msg = f"axiom or theorem is required, but {name} is unknown"
                self.add_lsp_error(start_token, msg, context)
                raise ParseError()
            replacement_evidence[predicate] = formula
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return EqualityReplacement(token=start_token, equal=equal, evidence=replacement_evidence)

    def parse_membership(self, context: Context) -> Membership:
        start_token = self.stream.consume("MEMBERSHIP")
        tok = self.stream.consume("IDENT")
        name = tok.value
        if name in context.decl.primpreds:
            membership = RefPrimPred(tok, name)
            if context.decl.primpreds[name].arity != 2:
                msg = f"arity is required to be 2, but arity of {name} is {context.decl.primpreds[name].arity}"
                self.add_lsp_error(start_token, msg, context)
                raise ParseError()
        elif name in context.decl.defpreds:
            membership = RefDefPred(tok, name)
            if len(context.decl.defpreds[name].args) != 2:
                msg = f"arity is required to be 2, but arity of {name} is {len(context.decl.defpreds[name].args)}"
                self.add_lsp_error(start_token, msg, context)
                raise ParseError()
        else:
            msg = f"primpred or defpred is required, but {name} is unknown"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
        membership = Membership(name=name, token=start_token, membership=membership)
        context.add_decl(membership)
        logger.debug(f"[membership] {type(membership)}: {membership.name}")
        return membership

    def parse_include(self, context: Context) -> Include | InvalidInclude:
        file = "<invalid>"
        start_token = self.stream.consume("INCLUDE")
        try:
            file = self.stream.consume("STRING").value
            return Include(file, start_token)
        except ParseError:
            return InvalidInclude(file, start_token)
        except (TokenStreamError, ContextError) as e:
            self.add_lsp_error(e.token, e.msg, context)
            return InvalidInclude(file="<invalid>", token=e.token)

    def parse_block(self, context: Context) -> list[Control]:
        body: list[Control] = []
        while True:

            tok = self.stream.peek()
            if not tok or tok.type == "RBRACE":
                break
            else:
                control = self.parse_control(context, tok)
                body.append(control)
                if isinstance(control, InvalidControl):
                    self.skip_until_next_RBRACE_or_control()
        return body

    def parse_control(self, context: Context, tok: Token) -> Control:
        try:
            if tok.type == "ANY":
                return self.parse_any(context)
            elif tok.type == "ASSUME":
                return self.parse_assume(context)
            elif tok.type == "DIVIDE":
                return self.parse_divide(context)
            elif tok.type == "SOME":
                return self.parse_some(context)
            elif tok.type == "DENY":
                return self.parse_deny(context)
            elif tok.type == "CONTRADICT":
                return self.parse_contradict(context)
            elif tok.type == "EXPLODE":
                return self.parse_explode(context)
            elif tok.type == "APPLY":
                return self.parse_apply(context)
            elif tok.type == "LIFT":
                return self.parse_lift(context)
            elif tok.type == "CHARACTERIZE":
                return self.parse_characterize(context)
            elif tok.type == "INVOKE":
                return self.parse_invoke(context)
            elif tok.type == "EXPAND":
                return self.parse_expand(context)
            elif tok.type == "FOLD":
                return self.parse_fold(context)
            elif tok.type == "PAD":
                return self.parse_pad(context)
            elif tok.type == "SPLIT":
                return self.parse_split(context)
            elif tok.type == "CONNECT":
                return self.parse_connect(context)
            elif tok.type == "SUBSTITUTE":
                return self.parse_substitute(context)
            elif tok.type == "SHOW":
                return self.parse_show(context)
            elif tok.type == "ASSERT":
                return self.parse_assert(context)
            else:
                msg = "Control is required"
                self.add_lsp_error(tok, msg, context)
                raise ParseError()
        except ParseError:
            return InvalidControl(token=tok)
        except (TokenStreamError, ContextError) as e:
            self.add_lsp_error(e.token, e.msg, context)
            return InvalidControl(token=tok)

    def parse_any(self, context: Context) -> Any:
        start_token = self.stream.consume("ANY")
        items, local_vars, local_pred_tmpls, local_fun_tmpls = self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("LBRACE")
        body = self.parse_block(context.add_ctrl(local_vars, [], local_pred_tmpls, local_fun_tmpls))
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
            msg = "At least two cases are required"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
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
        items: list[Var | None] = []
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
        body = self.parse_block(context.add_ctrl(local_vars, [], [], []))
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
        varterms = self.parse_var_terms_or_none(context)
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula(context)
        if not isinstance(conclusion, Exists):
            msg = "Exists object is required"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
        return Lift(token=start_token, varterms=varterms, conclusion=conclusion)

    def parse_characterize(self, context: Context) -> Characterize:
        start_token = self.stream.consume("CHARACTERIZE")
        self.stream.consume("FOR")
        varterm = self.parse_var_term(context)
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula(context)
        if not isinstance(conclusion, ExistsUniq):
            msg = "ExistsUniq object is required"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
        return Characterize(token=start_token, varterm=varterm, conclusion=conclusion)

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
                msg = "Implies object is required"
                self.add_lsp_error(start_token, msg, context)
                raise ParseError()
        else:
            if not isinstance(fact, Iff):
                msg = "Iff object is required"
                self.add_lsp_error(start_token, msg, context)
                raise ParseError()
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
            msg = "Or object is required"
            self.add_lsp_error(start_token, msg, context)
            raise ParseError()
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
        indexes: dict[Term, list[int]] = {}
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
            tok = self.stream.peek()
            self.stream.consume(tok.type)
            right = self.parse_and(context.copy_form())
            if tok.type == "IMPLIES":
                left = Implies(tok, left, right)
            elif tok.type == "IFF":
                left = Iff(tok, left, right)
        return left

    def parse_and(self, context: Context) -> Formula:
        left = self.parse_primary(context.copy_form())
        while self.stream.peek().type in ("AND", "OR"):
            tok = self.stream.peek()
            self.stream.consume(tok.type)
            right = self.parse_primary(context.copy_form())
            if tok.type == "AND":
                left = And(tok, left, right)
            elif tok.type == "OR":
                left = Or(tok, left, right)
        return left

    def parse_primary(self, context: Context) -> Formula:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            name = self.stream.consume("IDENT").value
            if any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
                pred = next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
                defargs: list[Var | PredTemplate | FunTemplate] = [Var(tok, f"x_{i}") for i in range(pred.arity)]
            elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
                pred = next(pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name)
                defargs: list[Var | PredTemplate | FunTemplate] = [Var(tok, f"x_{i}") for i in range(pred.arity)]
            elif name in context.decl.primpreds:
                pred = RefPrimPred(tok, name)
                defargs: list[Var | PredTemplate | FunTemplate] = [Var(tok, f"x_{i}") for i in range(context.decl.primpreds[name].arity)]
            elif name in context.decl.defpreds:
                pred = RefDefPred(tok, name)
                defargs = context.decl.defpreds[name].args
            else:
                msg = f"Unexpected name: {name}"
                self.add_lsp_error(tok, msg, context)
                raise ParseError()
            if self.stream.peek().type == "LPAREN":
                self.stream.consume("LPAREN")
                subargs = self.parse_terms(context)
                self.stream.consume("RPAREN")
            else:
                subargs: list[Term] = []
            resolved_args = self.match_args(defargs, subargs, context, tok)
            return AtomicFormula(tok, pred, tuple(resolved_args))

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
            return Not(tok, body)

        elif tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"):
            quantified_pairs: list[tuple[Token, Var | PredTemplate | FunTemplate]] = []
            local_bound_vars: list[Var] = []
            local_bound_pred_tmpls: list[PredTemplate] = []
            local_bound_fun_tmpls: list[FunTemplate] = []
            while tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"):
                self.stream.consume(tok.type)
                if tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ"):
                    var = self.parse_var()
                    quantified_pairs.append((tok, var))
                    local_bound_vars.append(var)
                    tok = self.stream.peek()
                elif tok.type == "FORALL_PRED_TMPL":
                    pred_tmpl = self.parse_pred_tmpl()
                    quantified_pairs.append((tok, pred_tmpl))
                    local_bound_pred_tmpls.append(pred_tmpl)
                    tok = self.stream.peek()
                else:
                    fun_tmpl = self.parse_fun_tmpl()
                    quantified_pairs.append((tok, fun_tmpl))
                    local_bound_fun_tmpls.append(fun_tmpl)
                    tok = self.stream.peek()
            self.stream.consume("LPAREN")
            body = self.parse_formula(context.add_form(local_bound_vars, local_bound_pred_tmpls, local_bound_fun_tmpls))
            self.stream.consume("RPAREN")
            for tok, item in reversed(quantified_pairs):
                if tok.type in ("FORALL", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"):
                    body = Forall(tok, item, body)
                elif tok.type == "EXISTS":
                    if isinstance(item, Var):
                        body = Exists(tok, item, body)
                    else:
                        msg = f"Unexpected type: {type(item)}"
                        self.add_lsp_error(tok, msg, context)
                        raise ParseError()
                elif tok.type == "EXISTS_UNIQ":
                    if isinstance(item, Var):
                        body = ExistsUniq(tok, item, body)
                    else:
                        msg = f"Unexpected type: {type(item)}"
                        self.add_lsp_error(tok, msg, context)
                        raise ParseError()
            return body

        else:
            msg = "Formula objct is required, but unknown token is found"
            self.add_lsp_error(tok, msg, context)
            raise ParseError()

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

    def parse_terms(self, context: Context) -> list[Term]:
        terms = [self.parse_term(context.copy_form())]
        while self.stream.peek().type == "COMMA":
            self.stream.consume("COMMA")
            terms.append(self.parse_term(context.copy_form()))
        return terms

    def parse_var_terms_or_none(self, context: Context) -> list[VarTerm | None]:
        varterms: list[VarTerm | None] = []
        while True:
            if self.stream.peek().type == "UNDERSCORE":
                varterms.append(None)
            else:
                varterms.append(self.parse_var_term(context))
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return varterms

    def parse_var_term(self, context: Context) -> VarTerm:
        tok = self.stream.consume("IDENT")
        name = tok.value
        if any(var.name == name for var in context.form.vars):
            return next(var for var in context.form.vars if var.name == name)
        elif any(var.name == name for var in context.ctrl.vars):
            return next((var for var in context.ctrl.vars if var.name == name))
        elif name in context.decl.defcons:
            return RefDefCon(tok, name)
        elif name in context.decl.deffuns or name in context.decl.deffunterms or any(fun_tmpl.name == name for fun_tmpl in context.form.fun_tmpls) or any(fun_tmpl.name == name for fun_tmpl in context.ctrl.fun_tmpls):
            if name in context.decl.deffuns:
                fun = RefDefFun(tok, name)
                defargs = context.decl.deffuns[name].args
            elif name in context.decl.deffunterms:
                fun = RefDefFunTerm(tok, name)
                defargs = context.decl.deffunterms[name].args
            elif any(fun_tmpl.name == name for fun_tmpl in context.form.fun_tmpls):
                fun = next(fun_tmpl for fun_tmpl in context.form.fun_tmpls if fun_tmpl.name == name)
                defargs = [Var(tok, f"x_{i}") for i in range(fun.arity)]
            else:
                fun = next(fun_tmpl for fun_tmpl in context.ctrl.fun_tmpls if fun_tmpl.name == name)
                defargs = [Var(tok, f"x_{i}") for i in range(fun.arity)]
            self.stream.consume("LPAREN")
            subargs = self.parse_terms(context)
            self.stream.consume("RPAREN")
            resolved_args = self.match_args(defargs, subargs, context, tok)
            return Compound(tok, fun, tuple(resolved_args))
        else:
            msg = f"Unexpected name: {name}"
            self.add_lsp_error(tok, msg, context)
            raise ParseError()

    def parse_term(self, context: Context) -> Term:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            name = self.stream.consume("IDENT").value
            if any(var.name == name for var in context.form.vars):
                return next(var for var in context.form.vars if var.name == name)
            elif any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
                return next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
            elif any(var.name == name for var in context.ctrl.vars):
                return next((var for var in context.ctrl.vars if var.name == name))
            elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
                return next((pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name))
            elif name in context.decl.defcons:
                return RefDefCon(tok, name)
            elif name in context.decl.deffuns or name in context.decl.deffunterms or any(fun_tmpl.name == name for fun_tmpl in context.form.fun_tmpls) or any(fun_tmpl.name == name for fun_tmpl in context.ctrl.fun_tmpls):
                if name in context.decl.deffuns:
                    fun = RefDefFun(tok, name)
                    defargs = context.decl.deffuns[name].args
                elif name in context.decl.deffunterms:
                    fun = RefDefFunTerm(tok, name)
                    defargs = context.decl.deffunterms[name].args
                elif any(fun_tmpl.name == name for fun_tmpl in context.form.fun_tmpls):
                    fun = next(fun_tmpl for fun_tmpl in context.form.fun_tmpls if fun_tmpl.name == name)
                    defargs = [Var(tok, f"x_{i}") for i in range(fun.arity)]
                else:
                    fun = next(fun_tmpl for fun_tmpl in context.ctrl.fun_tmpls if fun_tmpl.name == name)
                    defargs = [Var(tok, f"x_{i}") for i in range(fun.arity)]
                if self.stream.peek().type == "LPAREN":
                    self.stream.consume("LPAREN")
                    subargs = self.parse_terms(context)
                    self.stream.consume("RPAREN")
                    resolved_args = self.match_args(defargs, subargs, context, tok)
                    return Compound(tok, fun, tuple(resolved_args))
                else:
                    return fun
            elif name in context.decl.primpreds:
                return RefPrimPred(tok, name)
            elif name in context.decl.defpreds:
                return RefDefPred(tok, name)
            else:
                msg = f"Term object is required, but {name} is unknown"
                self.add_lsp_error(tok, msg, context)
                raise ParseError()
        elif tok.type == "LAMBDA_PRED":
            self.stream.consume("LAMBDA_PRED")
            if self.stream.peek().type == "DOT":
                vars: list[Var] = []
            else:
                vars = self.parse_vars()
            self.stream.consume("DOT")
            formula = self.parse_formula(context.add_form(vars, [], []))
            return PredLambda(tok, tuple(vars), formula)
        elif tok.type == "LAMBDA_FUN":
            self.stream.consume("LAMBDA_FUN")
            if self.stream.peek().type == "DOT":
                vars: list[Var] = []
            else:
                vars = self.parse_vars()
            self.stream.consume("DOT")
            term = self.parse_var_term(context.add_form(vars, [], []))
            return FunLambda(tok, tuple(vars), term)
        else:
            msg = "Term object is required, but unknown token is found"
            self.add_lsp_error(tok, msg, context)
            raise ParseError()

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

    def parse_vars_or_pred_tmpls_or_fun_tmpls(self) -> tuple[list[Var | PredTemplate | FunTemplate], list[Var], list[PredTemplate], list[FunTemplate]]:
        items: list[Var | PredTemplate | FunTemplate] = []
        vars: list[Var] = []
        pred_tmpls: list[PredTemplate] = []
        fun_tmpls: list[FunTemplate] = []
        while True:
            if self.stream.peek().type == "PREDICATE":
                self.stream.consume("PREDICATE")
                pred_tmpl = self.parse_pred_tmpl()
                items.append(pred_tmpl)
                pred_tmpls.append(pred_tmpl)
            elif self.stream.peek().type == "FUNCTION":
                self.stream.consume("FUNCTION")
                fun_tmpl = self.parse_fun_tmpl()
                items.append(fun_tmpl)
                fun_tmpls.append(fun_tmpl)
            else:
                var = self.parse_var()
                items.append(var)
                vars.append(var)
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return items, vars, pred_tmpls, fun_tmpls

    def parse_vars_or_pred_tmpls(self) -> tuple[list[Var | PredTemplate], list[Var], list[PredTemplate]]:
        items: list[Var | PredTemplate] = []
        vars: list[Var] = []
        pred_tmpls: list[PredTemplate] = []
        while True:
            if self.stream.peek().type == "PREDICATE":
                self.stream.consume("PREDICATE")
                pred_tmpl = self.parse_pred_tmpl()
                items.append(pred_tmpl)
                pred_tmpls.append(pred_tmpl)
            else:
                var = self.parse_var()
                items.append(var)
                vars.append(var)
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return items, vars, pred_tmpls

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
        tok = self.stream.consume("IDENT")
        var_name = tok.value
        return Var(tok, var_name)

    def parse_pred_tmpl(self) -> PredTemplate:
        tok = self.stream.consume("IDENT")
        pred_tmpl_name = tok.value
        self.stream.consume("LBRACKET")
        arity = int(self.stream.consume("NUMBER").value)
        self.stream.consume("RBRACKET")
        return PredTemplate(tok, pred_tmpl_name, arity)

    def parse_fun_tmpl(self) -> FunTemplate:
        tok = self.stream.consume("IDENT")
        fun_tmpl_name = tok.value
        self.stream.consume("LBRACKET")
        arity = int(self.stream.consume("NUMBER").value)
        self.stream.consume("RBRACKET")
        return FunTemplate(tok, fun_tmpl_name, arity)

    def match_args(self, defargs: Sequence[Var | PredTemplate | FunTemplate], subargs: Sequence[Term], context: Context, tok: Token) -> list[Term]:
        if len(defargs) != len(subargs):
            msg = f"len(defargs): {len(defargs)}, len(subargs): {len(subargs)}"
            self.add_lsp_error(tok, msg, context)
            raise ParseError()
        resolved_args: list[Term] = []
        for defarg, subarg in zip(defargs, subargs):
            if isinstance(defarg, Var):
                if isinstance(subarg, VarTerm):
                    resolved_args.append(subarg)
                else:
                    msg = f"VarTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted"
                    self.add_lsp_error(tok, msg, context)
                    raise ParseError()
            elif isinstance(defarg, PredTemplate):
                if isinstance(subarg, PredTerm):
                    resolved_args.append(subarg)
                elif isinstance(subarg, VarTerm):
                    if defarg.arity == 1:
                        if context.decl.membership is None:
                            msg = "VarTerm is substituted into PredTerm with arity 1, but membership has not been declared"
                            self.add_lsp_error(tok, msg, context)
                            raise ParseError()
                        else:
                            resolved_args.append(MembershipLambda(tok, subarg))
                    else:
                        msg = f"VarTerm cannot be substituted into PredTerm with arity {defarg.arity}"
                        self.add_lsp_error(tok, msg, context)
                        raise ParseError()
                else:
                    msg = f"Unexpected type: {type(subarg)}"
                    self.add_lsp_error(tok, msg, context)
                    raise ParseError()
            else:
                if isinstance(subarg, FunTerm):
                    resolved_args.append(subarg)
                else:
                    msg = f"FunTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted"
                    self.add_lsp_error(tok, msg, context)
                    raise ParseError()
        return resolved_args

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
