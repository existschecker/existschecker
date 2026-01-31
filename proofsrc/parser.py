from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, AtomicFormula, And, Or, Implies, Forall, Exists, Not, Bottom, PrimPred, DefPred, Iff, Axiom, Invoke, Expand, ExistsUniq, DefCon, Pad, Split, Connect, DefConExist, DefConUniq, DefFun, DefFunExist, DefFunUniq, Compound, RefDefCon, Var, DefFunTerm, Equality, Substitute, Characterize, Show, EqualityReflection, EqualityReplacement, Term, Formula, Control, Declaration, PredTemplate, PredLambda, Include, Assert, Fold, Membership, MembershipLambda, VarTerm, PredTerm, FunTemplate, FunTerm, FunLambda, RefPrimPred, RefDefPred, RefDefFun, RefDefFunTerm, InvalidInclude, InvalidDeclaration, InvalidControl, ContextError, DeclarationUnit, RefFact, RefAxiom, RefTheorem, RefDefConExist, RefDefConUniq, RefDefFunExist, RefDefFunUniq, DeclarationSupport
from lexer import Token
from token_stream import TokenStream, TokenStreamError
from logic_utils import strip_forall_vars

from lsprotocol import types as lsp
from pygls import uris
from typing import Sequence

import logging
logger = logging.getLogger("proof")

class ParseError(Exception):
    def __init__(self, token: Token, msg: str):
        self.token = token
        self.msg = msg

# === パーサー本体 ===
class Parser:
    def __init__(self, unit: DeclarationUnit):
        self.unit = unit
        self.stream = TokenStream(unit.tokens)

    def add_lsp_error(self, tok: Token, message: str, context: Context):
        uri = uris.from_fs_path(tok.file)
        if uri is None:
            return
        diag = lsp.Diagnostic(
            range=lsp.Range(
                start=lsp.Position(line=tok.line - 1, character=tok.column - 1),
                end=lsp.Position(line=tok.end_line - 1, character=tok.end_column - 1)
            ),
            message=message,
            source="Parser",
            severity=lsp.DiagnosticSeverity.Error
        )
        self.unit.diagnostics.append(diag)

    def add_node_to_token(self, node: Declaration | DeclarationSupport | Control | Formula | Term | RefFact, start_token: Token, end_token: Token):
        self.unit.node_to_token[id(node)] = (start_token.index, end_token.index)
        self.unit.nodes.append(node)

    def add_decl_ref(self, name: str, token: Token) -> None:
        if name not in self.unit.decl_refs:
            self.unit.decl_refs[name] = []
        self.unit.decl_refs[name].append(token)

    def add_ctrl_defs_refs(self, def_node: Term, ref_node: Term) -> None:
        self.unit.ctrl_defs[id(ref_node)] = id(def_node)
        if id(def_node) not in self.unit.ctrl_refs:
            self.unit.ctrl_refs[id(def_node)] = []
        self.unit.ctrl_refs[id(def_node)].append(id(ref_node))

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

    def parse_unit(self, context: Context) -> None:
        self.stream = TokenStream(self.unit.tokens)
        tok = self.stream.peek()
        try:
            if tok.type == "INCLUDE":
                self.unit.ast = self.parse_include(context)
            else:
                self.unit.ast = self.parse_declaration(context, tok)
            tok = self.stream.peek()
            if tok.type != "EOF":
                msg = f"Unexpected token {tok.type} after Include or Declaration"
                raise ParseError(tok, msg)
        except (ParseError, TokenStreamError, ContextError) as e:
            self.add_lsp_error(e.token, e.msg, context)
            node = InvalidDeclaration("<invalid>")
            self.add_node_to_token(node, tok, self.stream.last_token)
            self.unit.ast = node

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
                raise ParseError(tok, msg)
        except (ParseError, TokenStreamError, ContextError) as e:
            self.add_lsp_error(e.token, e.msg, context)
            node = InvalidDeclaration("<invalid>")
            self.add_node_to_token(node, tok, self.stream.last_token)
            return node

    def parse_primitive(self, context: Context) -> PrimPred:
        start_token = self.stream.consume("PRIMITIVE")
        self.stream.consume("PREDICATE")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = RefPrimPred(name)
        self.add_node_to_token(ref, name_token, name_token)
        self.stream.consume("ARITY")
        arity = int(self.stream.consume("NUMBER").value)
        tex = self.parse_or_create_tex(name, arity)
        if len(tex) != arity + 1:
            msg = f"arity of {name} is {arity}, but length of tex is {len(tex)}"
            raise ParseError(start_token, msg)
        primpred = PrimPred(name=name, ref=ref, arity=arity, tex=tex)
        self.add_node_to_token(primpred, start_token, self.stream.last_token)
        # context.add_decl(primpred)
        logger.debug(f"[primpred] {name}")
        return primpred

    def parse_axiom(self, context: Context) -> Axiom:
        start_token = self.stream.consume("AXIOM")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = RefAxiom(name)
        self.add_node_to_token(ref, name_token, name_token)
        conclusion = self.parse_formula(context)
        axiom = Axiom(name=name, ref=ref, conclusion=conclusion)
        self.add_node_to_token(axiom, start_token, self.stream.last_token)
        # context.add_decl(axiom)
        logger.debug(f"[axiom] {name}")
        return axiom

    def parse_theorem(self, context: Context) -> Theorem:
        start_token = self.stream.consume("THEOREM")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = RefTheorem(name)
        self.add_node_to_token(ref, name_token, name_token)
        conclusion = self.parse_formula(context)
        self.stream.consume("LBRACE")
        proof = self.parse_block(context.copy_ctrl())
        self.stream.consume("RBRACE")
        theorem = Theorem(name=name, ref=ref, conclusion=conclusion, proof=proof)
        self.add_node_to_token(theorem, start_token, self.stream.last_token)
        # context.add_decl(theorem)
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
            raise ParseError(start_token, msg)

    def parse_defpred(self, context: Context, start_token: Token) -> DefPred:
        self.stream.consume("PREDICATE")
        if self.stream.peek().type == "AUTOEXPAND":
            self.stream.consume("AUTOEXPAND")
            autoexpand = True
        else:
            autoexpand =False
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = RefDefPred(name)
        self.add_node_to_token(ref, name_token, name_token)
        self.stream.consume("LPAREN")
        args, local_vars, local_pred_tmpls, local_fun_tmpls = self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        formula = self.parse_formula(context.add_form(local_vars, local_pred_tmpls, local_fun_tmpls))
        tex = self.parse_or_create_tex(name, len(args))
        if len(tex) != len(args) + 1:
            msg = f"arity of {name} is {len(args)}, but length of tex is {len(tex)}"
            raise ParseError(start_token, msg)
        defpred = DefPred(name=name, ref=ref, args=args, formula=formula, autoexpand=autoexpand, tex=tex)
        self.add_node_to_token(defpred, start_token, self.stream.last_token)
        # context.add_decl(defpred)
        logger.debug(f"[defpred] {name}")
        return defpred

    def parse_defcon(self, context: Context, start_token: Token) -> DefCon:
        self.stream.consume("CONSTANT")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = RefDefCon(name)
        self.add_node_to_token(ref, name_token, name_token)
        self.stream.consume("BY")
        theorem = self.stream.consume("IDENT").value
        tex = self.parse_or_create_tex(name, 0)
        if len(tex) != 1:
            msg = f"{name} is constant, but length of tex is {len(tex)}"
            raise ParseError(start_token, msg)
        defcon = DefCon(name=name, ref=ref, theorem=theorem, tex=tex)
        self.add_node_to_token(defcon, start_token, self.stream.last_token)
        # context.add_decl(defcon)
        logger.debug(f"[defcon] {name}")
        return defcon

    def parse_deffun_or_deffunterm(self, context: Context, start_token: Token) -> DefFun | DefFunTerm:
        self.stream.consume("FUNCTION")
        name_token = self.stream.consume("IDENT")
        if self.stream.peek().type == "BY":
            return self.parse_deffun(context, start_token, name_token)
        else:
            return self.parse_deffunterm(context, start_token, name_token)

    def parse_deffun(self, context: Context, start_token: Token, name_token: Token) -> DefFun:
        name = name_token.value
        ref = RefDefFun(name)
        self.add_node_to_token(ref, name_token, name_token)
        self.stream.consume("BY")
        theorem = self.stream.consume("IDENT").value
        if theorem not in context.decl.theorems:
            msg = f"{theorem} is not in context.decl.theorems"
            raise ParseError(start_token, msg)
        vars_, body = strip_forall_vars(context.decl.theorems[theorem].conclusion)
        if isinstance(body, ExistsUniq):
            existsuniq = body
        elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
            existsuniq = body.right
        else:
            msg = f"conclusion of {theorem} cannot be used for function definition"
            raise ParseError(start_token, msg)
        arity = len(vars_)
        tex = self.parse_or_create_tex(name, arity)
        if len(tex) != arity + 1:
            msg = f"arity or {name} is {arity}, but length of tex is {len(tex)}"
            raise ParseError(start_token, msg)
        deffun = DefFun(name=name, ref=ref, args=vars_, returned=existsuniq.var, theorem=theorem, tex=tex)
        self.add_node_to_token(deffun, start_token, self.stream.last_token)
        # context.add_decl(deffun)
        logger.debug(f"[deffun] {name}")
        return deffun

    def parse_deffunterm(self, context: Context, start_token: Token, name_token: Token) -> DefFunTerm:
        name = name_token.value
        ref = RefDefFunTerm(name)
        self.add_node_to_token(ref, name_token, name_token)
        self.stream.consume("LPAREN")
        args, local_vars, local_pred_tmpls, local_fun_tmpls = self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        term = self.parse_var_term(context.add_form(local_vars, local_pred_tmpls, local_fun_tmpls))
        tex = self.parse_or_create_tex(name, len(args))
        if len(tex) != len(args) + 1:
            msg = f"arity of {name} is {len(args)}, but length of tex is {len(tex)}"
            raise ParseError(start_token, msg)
        deffunterm = DefFunTerm(name=name, ref=ref, args=args, varterm=term, tex=tex)
        self.add_node_to_token(deffunterm, start_token, self.stream.last_token)
        # context.add_decl(deffunterm)
        logger.debug(f"[deffunterm] {name}")
        return deffunterm

    def parse_existence(self, context: Context) -> DefConExist | DefFunExist:
        start_token = self.stream.consume("EXISTENCE")
        existence_name_token = self.stream.consume("IDENT")
        existence_name = existence_name_token.value
        existence_formula = self.parse_formula(context)
        self.stream.consume("BY")
        name = self.stream.consume("IDENT").value
        if name in context.decl.defcons:
            ref = RefDefConExist(existence_name)
            self.add_node_to_token(ref, existence_name_token, existence_name_token)
            defconexist = DefConExist(name=existence_name, ref=ref, formula=existence_formula, con_name=name)
            self.add_node_to_token(defconexist, start_token, self.stream.last_token)
            # context.add_decl(defconexist)
            return defconexist
        elif name in context.decl.deffuns:
            ref = RefDefFunExist(existence_name)
            self.add_node_to_token(ref, existence_name_token, existence_name_token)
            deffunexist = DefFunExist(name=existence_name, ref=ref, formula=existence_formula, fun_name=name)
            self.add_node_to_token(deffunexist, start_token, self.stream.last_token)
            # context.add_decl(deffunexist)
            return deffunexist
        else:
            msg = f"defcon or deffun is required, but {name} is unknown"
            raise ParseError(start_token, msg)

    def parse_uniqueness(self, context: Context) -> DefConUniq | DefFunUniq:
        start_token = self.stream.consume("UNIQUENESS")
        uniqueness_name_token = self.stream.consume("IDENT")
        uniqueness_name = uniqueness_name_token.value
        uniqueness_formula = self.parse_formula(context)
        self.stream.consume("BY")
        name = self.stream.consume("IDENT").value
        if name in context.decl.defcons:
            ref = RefDefConUniq(uniqueness_name)
            self.add_node_to_token(ref, uniqueness_name_token, uniqueness_name_token)
            defconuniq = DefConUniq(name=uniqueness_name, ref=ref, formula=uniqueness_formula, con_name=name)
            self.add_node_to_token(defconuniq, start_token, self.stream.last_token)
            # context.add_decl(defconuniq)
            return defconuniq
        elif name in context.decl.deffuns:
            ref = RefDefFunUniq(uniqueness_name)
            self.add_node_to_token(ref, uniqueness_name_token, uniqueness_name_token)
            deffununiq = DefFunUniq(name=uniqueness_name, ref=ref, formula=uniqueness_formula, fun_name=name)
            self.add_node_to_token(deffununiq, start_token, self.stream.last_token)
            # context.add_decl(deffununiq)
            return deffununiq
        else:
            msg = f"defcon or deffun is required, but {name} is unknown"
            raise ParseError(start_token, msg)

    def parse_equality(self, context: Context) -> Equality:
        start_token = self.stream.consume("EQUALITY")
        tok = self.stream.consume("IDENT")
        name = tok.value
        if name in context.decl.primpreds:
            self.add_decl_ref(name, tok)
            equal = RefPrimPred(name)
            self.add_node_to_token(equal, tok, tok)
            if context.decl.primpreds[name].arity != 2:
                msg = f"arity is required to be 2, but arity of {name} is {context.decl.primpreds[name].arity}"
                raise ParseError(start_token, msg)
        elif name in context.decl.defpreds:
            self.add_decl_ref(name, tok)
            equal = RefDefPred(name)
            self.add_node_to_token(equal, tok, tok)
            if len(context.decl.defpreds[name].args) != 2:
                msg = f"arity is required to be 2, but arity of {name} is {len(context.decl.defpreds[name].args)}"
                raise ParseError(start_token, msg)
        else:
            msg = f"primpred or defpred is required, but {name} is unknown"
            raise ParseError(start_token, msg)
        reflection = self.parse_equality_reflection(equal, context)
        replacement = self.parse_equality_replacement(equal, context)
        equality = Equality(name=name, equal=equal, reflection=reflection, replacement=replacement)
        self.add_node_to_token(equality, start_token, self.stream.last_token)
        # context.add_decl(equality)
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
            raise ParseError(start_token, msg)
        equality_reflection = EqualityReflection(equal=equal, evidence=reflection_evidence)
        self.add_node_to_token(equality_reflection, start_token, self.stream.last_token)
        return equality_reflection

    def parse_equality_replacement(self, equal: RefPrimPred | RefDefPred, context: Context) -> EqualityReplacement:
        start_token = self.stream.consume("REPLACEMENT")
        replacement_evidence: dict[str, Axiom | Theorem] = {}
        while True:
            predicate = self.stream.consume("IDENT").value
            if not (predicate == equal.name or predicate in context.decl.primpreds):
                msg = f"{equal.name} or primpred is required, but {predicate} is unknown"
                raise ParseError(start_token, msg)
            self.stream.consume("COLON")
            name = self.stream.consume("IDENT").value
            if name in context.decl.axioms:
                formula = context.decl.axioms[name]
            elif name in context.decl.theorems:
                formula = context.decl.theorems[name]
            else:
                msg = f"axiom or theorem is required, but {name} is unknown"
                raise ParseError(start_token, msg)
            replacement_evidence[predicate] = formula
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        equality_replacement = EqualityReplacement(equal=equal, evidence=replacement_evidence)
        self.add_node_to_token(equality_replacement, start_token, self.stream.last_token)
        return equality_replacement

    def parse_membership(self, context: Context) -> Membership:
        start_token = self.stream.consume("MEMBERSHIP")
        tok = self.stream.consume("IDENT")
        name = tok.value
        if name in context.decl.primpreds:
            self.add_decl_ref(name, tok)
            membership = RefPrimPred(name)
            self.add_node_to_token(membership, tok, tok)
            if context.decl.primpreds[name].arity != 2:
                msg = f"arity is required to be 2, but arity of {name} is {context.decl.primpreds[name].arity}"
                raise ParseError(start_token, msg)
        elif name in context.decl.defpreds:
            self.add_decl_ref(name, tok)
            membership = RefDefPred(name)
            self.add_node_to_token(membership, tok, tok)
            if len(context.decl.defpreds[name].args) != 2:
                msg = f"arity is required to be 2, but arity of {name} is {len(context.decl.defpreds[name].args)}"
                raise ParseError(start_token, msg)
        else:
            msg = f"primpred or defpred is required, but {name} is unknown"
            raise ParseError(start_token, msg)
        membership = Membership(name=name, membership=membership)
        self.add_node_to_token(membership, start_token, self.stream.last_token)
        # context.add_decl(membership)
        logger.debug(f"[membership] {type(membership)}: {membership.membership.name}")
        return membership

    def parse_include(self, context: Context) -> Include | InvalidInclude:
        start_token = self.stream.consume("INCLUDE")
        try:
            file = self.stream.consume("STRING").value
            return Include(file, start_token)
        except (ParseError, TokenStreamError, ContextError) as e:
            self.add_lsp_error(e.token, e.msg, context)
            return InvalidInclude(file="<invalid>", token=start_token)

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
                raise ParseError(tok, msg)
        except (ParseError, TokenStreamError, ContextError) as e:
            self.add_lsp_error(e.token, e.msg, context)
            node = InvalidControl()
            self.add_node_to_token(node, tok, self.stream.last_token)
            return node

    def parse_any(self, context: Context) -> Any:
        start_token = self.stream.consume("ANY")
        items, local_vars, local_pred_tmpls, local_fun_tmpls = self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("LBRACE")
        body = self.parse_block(context.add_ctrl(local_vars, [], local_pred_tmpls, local_fun_tmpls))
        self.stream.consume("RBRACE")
        node = Any(items=items, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_assume(self, context: Context) -> Assume:
        start_token = self.stream.consume("ASSUME")
        premise = self.parse_formula(context)
        self.stream.consume("LBRACE")
        body = self.parse_block(context.copy_ctrl())
        self.stream.consume("RBRACE")
        node = Assume(premise=premise, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
    def parse_divide(self, context: Context) -> Divide:
        start_token = self.stream.consume("DIVIDE")
        fact = self.parse_reference_or_formula(context)
        cases: list[Case] = []
        while self.stream.peek().type == "CASE":
            cases.append(self.parse_case(context.copy_ctrl()))
        if len(cases) < 2:
            msg = "At least two cases are required"
            raise ParseError(start_token, msg)
        node = Divide(fact=fact, cases=cases)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
    def parse_case(self, context: Context) -> Case:
        start_token = self.stream.consume("CASE")
        premise = self.parse_formula(context)
        self.stream.consume("LBRACE")
        body = self.parse_block(context.copy_ctrl())
        self.stream.consume("RBRACE")
        node = Case(premise=premise, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
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
        node = Some(items=items, fact=fact, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
    def parse_deny(self, context: Context) -> Deny:
        start_token = self.stream.consume("DENY")
        premise = self.parse_formula(context)
        self.stream.consume("LBRACE")
        body = self.parse_block(context.copy_ctrl())
        self.stream.consume("RBRACE")
        node = Deny(premise=premise, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
    def parse_contradict(self, context: Context) -> Contradict:
        start_token = self.stream.consume("CONTRADICT")
        contradiction = self.parse_formula(context)
        node = Contradict(contradiction=contradiction)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
    def parse_explode(self, context: Context) -> Explode:
        start_token = self.stream.consume("EXPLODE")
        conclusion = self.parse_formula(context)
        node = Explode(conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

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
        node = Apply(invoke=invoke, fact=fact, terms=terms)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_lift(self, context: Context) -> Lift:
        start_token = self.stream.consume("LIFT")
        self.stream.consume("FOR")
        varterms = self.parse_var_terms_or_none(context)
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula(context)
        if not isinstance(conclusion, Exists):
            msg = "Exists object is required"
            raise ParseError(start_token, msg)
        node = Lift(varterms=varterms, conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_characterize(self, context: Context) -> Characterize:
        start_token = self.stream.consume("CHARACTERIZE")
        self.stream.consume("FOR")
        varterm = self.parse_var_term(context)
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula(context)
        if not isinstance(conclusion, ExistsUniq):
            msg = "ExistsUniq object is required"
            raise ParseError(start_token, msg)
        node = Characterize(varterm=varterm, conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

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
                raise ParseError(start_token, msg)
        else:
            if not isinstance(fact, Iff):
                msg = "Iff object is required"
                raise ParseError(start_token, msg)
        node = Invoke(direction=direction, fact=fact)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

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
        node = Expand(fact=fact, defs=defs, indexes=indexes)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

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
        node = Fold(defs=defs, indexes=indexes, conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_pad(self, context: Context) -> Pad:
        start_token = self.stream.consume("PAD")
        fact = self.parse_formula(context)
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula(context)
        if not isinstance(conclusion, Or):
            msg = "Or object is required"
            raise ParseError(start_token, msg)
        node = Pad(fact=fact, conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_split(self, context: Context) -> Split:
        start_token = self.stream.consume("SPLIT")
        if self.stream.peek().type == "NUMBER":
            index = int(self.stream.consume("NUMBER").value)
        else:
            index = None
        fact = self.parse_reference_or_formula(context)
        node = Split(index=index, fact=fact)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_connect(self, context: Context) -> Connect:
        start_token = self.stream.consume("CONNECT")
        conclusion = self.parse_formula(context)
        node = Connect(conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

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
        node = Substitute(fact=fact, env=env, indexes=indexes)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_show(self, context: Context) -> Show:
        start_token = self.stream.consume("SHOW")
        conclusion = self.parse_bot_or_formula(context)
        self.stream.consume("LBRACE")
        body = self.parse_block(context.copy_ctrl())
        self.stream.consume("RBRACE")
        node = Show(conclusion=conclusion, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_assert(self, context: Context) -> Assert:
        start_token = self.stream.consume("ASSERT")
        reference = self.parse_reference_or_formula(context)
        node = Assert(reference=reference)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_reference_or_formula(self, context: Context) -> RefFact | Formula:
        token = self.stream.peek()
        if token.type == "IDENT":
            name = token.value
            ref = None
            if name in context.decl.axioms:
                ref = RefAxiom
            elif name in context.decl.theorems:
                ref = RefTheorem
            elif name in context.decl.defconexists:
                ref = RefDefConExist
            elif name in context.decl.defconuniqs:
                ref = RefDefConUniq
            elif name in context.decl.deffunexists:
                ref = RefDefFunExist
            elif name in context.decl.deffununiqs:
                ref = RefDefFunUniq
            if ref is not None:
                self.add_decl_ref(name, token)
                self.stream.consume(token.type)
                node = ref(name)
                self.add_node_to_token(node, token, token)
                return node
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
        start_token = self.unit.tokens[self.unit.node_to_token[id(left)][0]]
        while self.stream.peek().type in ("IMPLIES", "IFF"):
            tok = self.stream.peek()
            self.stream.consume(tok.type)
            right = self.parse_and(context.copy_form())
            if tok.type == "IMPLIES":
                left = Implies(left, right)
                self.add_node_to_token(left, start_token, self.stream.last_token)
            elif tok.type == "IFF":
                left = Iff(left, right)
                self.add_node_to_token(left, start_token, self.stream.last_token)
        return left

    def parse_and(self, context: Context) -> Formula:
        left = self.parse_primary(context.copy_form())
        start_token = self.unit.tokens[self.unit.node_to_token[id(left)][0]]
        while self.stream.peek().type in ("AND", "OR"):
            tok = self.stream.peek()
            self.stream.consume(tok.type)
            right = self.parse_primary(context.copy_form())
            if tok.type == "AND":
                left = And(left, right)
                self.add_node_to_token(left, start_token, self.stream.last_token)
            elif tok.type == "OR":
                left = Or(left, right)
                self.add_node_to_token(left, start_token, self.stream.last_token)
        return left

    def parse_primary(self, context: Context) -> Formula:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            name = self.stream.consume("IDENT").value
            if any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
                pred = next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
                defargs: list[Var | PredTemplate | FunTemplate] = [Var(f"x_{i}") for i in range(pred.arity)]
            elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
                pred = next(pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name)
                defargs: list[Var | PredTemplate | FunTemplate] = [Var(f"x_{i}") for i in range(pred.arity)]
            elif name in context.decl.primpreds:
                self.add_decl_ref(name, tok)
                pred = RefPrimPred(name)
                self.add_node_to_token(pred, tok, tok)
                defargs: list[Var | PredTemplate | FunTemplate] = [Var(f"x_{i}") for i in range(context.decl.primpreds[name].arity)]
            elif name in context.decl.defpreds:
                self.add_decl_ref(name, tok)
                pred = RefDefPred(name)
                self.add_node_to_token(pred, tok, tok)
                defargs = context.decl.defpreds[name].args
            else:
                msg = f"Unexpected name: {name}"
                raise ParseError(tok, msg)
            if self.stream.peek().type == "LPAREN":
                self.stream.consume("LPAREN")
                subargs = self.parse_terms(context)
                self.stream.consume("RPAREN")
            else:
                subargs: list[Term] = []
            resolved_args = self.match_args(defargs, subargs, context, tok)
            formula = AtomicFormula(pred, tuple(resolved_args))
            self.add_node_to_token(formula, tok, self.stream.last_token)
            return formula

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
            formula = Not(body)
            self.add_node_to_token(formula, tok, self.stream.last_token)
            return formula

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
                    body = Forall(item, body)
                    self.add_node_to_token(body, tok, self.stream.last_token)
                elif tok.type == "EXISTS":
                    if isinstance(item, Var):
                        body = Exists(item, body)
                        self.add_node_to_token(body, tok, self.stream.last_token)
                    else:
                        msg = f"Unexpected type: {type(item)}"
                        raise ParseError(tok, msg)
                elif tok.type == "EXISTS_UNIQ":
                    if isinstance(item, Var):
                        body = ExistsUniq(item, body)
                        self.add_node_to_token(body, tok, self.stream.last_token)
                    else:
                        msg = f"Unexpected type: {type(item)}"
                        raise ParseError(tok, msg)
            return body

        else:
            msg = "Formula objct is required, but unknown token is found"
            raise ParseError(tok, msg)

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
        term = self.parse_term(context)
        if isinstance(term, VarTerm):
            return term
        else:
            msg = f"Expected VarTerm, got {type(term)}"
            raise ParseError(self.unit.tokens[self.unit.node_to_token[id(term)][0]], msg)

    def parse_term(self, context: Context) -> Term:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            name = self.stream.consume("IDENT").value
            if any(var.name == name for var in context.form.vars):
                def_var = next(var for var in context.form.vars if var.name == name)
                ref_var = Var(name)
                self.add_node_to_token(ref_var, tok, tok)
                self.add_ctrl_defs_refs(def_var, ref_var)
                return ref_var
            elif any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
                return next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
            elif any(var.name == name for var in context.ctrl.vars):
                def_var = next((var for var in context.ctrl.vars if var.name == name))
                ref_var = Var(name)
                self.add_node_to_token(ref_var, tok, tok)
                self.add_ctrl_defs_refs(def_var, ref_var)
                return ref_var
            elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
                return next((pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name))
            elif name in context.decl.defcons:
                self.add_decl_ref(name, tok)
                ref = RefDefCon(name)
                self.add_node_to_token(ref, tok, tok)
                return ref
            elif name in context.decl.deffuns or name in context.decl.deffunterms or any(fun_tmpl.name == name for fun_tmpl in context.form.fun_tmpls) or any(fun_tmpl.name == name for fun_tmpl in context.ctrl.fun_tmpls):
                if name in context.decl.deffuns:
                    self.add_decl_ref(name, tok)
                    fun = RefDefFun(name)
                    self.add_node_to_token(fun, tok, tok)
                    defargs = context.decl.deffuns[name].args
                elif name in context.decl.deffunterms:
                    self.add_decl_ref(name, tok)
                    fun = RefDefFunTerm(name)
                    self.add_node_to_token(fun, tok, tok)
                    defargs = context.decl.deffunterms[name].args
                elif any(fun_tmpl.name == name for fun_tmpl in context.form.fun_tmpls):
                    fun = next(fun_tmpl for fun_tmpl in context.form.fun_tmpls if fun_tmpl.name == name)
                    defargs = [Var(f"x_{i}") for i in range(fun.arity)]
                else:
                    fun = next(fun_tmpl for fun_tmpl in context.ctrl.fun_tmpls if fun_tmpl.name == name)
                    defargs = [Var(f"x_{i}") for i in range(fun.arity)]
                if self.stream.peek().type == "LPAREN":
                    self.stream.consume("LPAREN")
                    subargs = self.parse_terms(context)
                    self.stream.consume("RPAREN")
                    resolved_args = self.match_args(defargs, subargs, context, tok)
                    term = Compound(fun, tuple(resolved_args))
                    self.add_node_to_token(term, tok, self.stream.last_token)
                    return term
                else:
                    return fun
            elif name in context.decl.primpreds:
                self.add_decl_ref(name, tok)
                ref = RefPrimPred(name)
                self.add_node_to_token(ref, tok, tok)
                return ref
            elif name in context.decl.defpreds:
                self.add_decl_ref(name, tok)
                ref = RefDefPred(name)
                self.add_node_to_token(ref, tok, tok)
                return ref
            else:
                msg = f"Term object is required, but {name} is unknown"
                raise ParseError(tok, msg)
        elif tok.type == "LAMBDA_PRED":
            self.stream.consume("LAMBDA_PRED")
            if self.stream.peek().type == "DOT":
                vars: list[Var] = []
            else:
                vars = self.parse_vars()
            self.stream.consume("DOT")
            formula = self.parse_formula(context.add_form(vars, [], []))
            term = PredLambda(tuple(vars), formula)
            self.add_node_to_token(term, tok, self.stream.last_token)
            return term
        elif tok.type == "LAMBDA_FUN":
            self.stream.consume("LAMBDA_FUN")
            if self.stream.peek().type == "DOT":
                vars: list[Var] = []
            else:
                vars = self.parse_vars()
            self.stream.consume("DOT")
            term = self.parse_var_term(context.add_form(vars, [], []))
            term = FunLambda(tuple(vars), term)
            self.add_node_to_token(term, tok, self.stream.last_token)
            return term
        else:
            msg = "Term object is required, but unknown token is found"
            raise ParseError(tok, msg)

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
        var = Var(var_name)
        self.add_node_to_token(var, tok, tok)
        self.add_ctrl_defs_refs(var, var)
        return var

    def parse_pred_tmpl(self) -> PredTemplate:
        tok = self.stream.consume("IDENT")
        pred_tmpl_name = tok.value
        self.stream.consume("LBRACKET")
        arity = int(self.stream.consume("NUMBER").value)
        self.stream.consume("RBRACKET")
        pred = PredTemplate(pred_tmpl_name, arity)
        self.add_node_to_token(pred, tok, self.stream.last_token)
        return pred

    def parse_fun_tmpl(self) -> FunTemplate:
        tok = self.stream.consume("IDENT")
        fun_tmpl_name = tok.value
        self.stream.consume("LBRACKET")
        arity = int(self.stream.consume("NUMBER").value)
        self.stream.consume("RBRACKET")
        fun = FunTemplate(fun_tmpl_name, arity)
        self.add_node_to_token(fun, tok, self.stream.last_token)
        return fun

    def match_args(self, defargs: Sequence[Var | PredTemplate | FunTemplate], subargs: Sequence[Term], context: Context, tok: Token) -> list[Term]:
        if len(defargs) != len(subargs):
            msg = f"len(defargs): {len(defargs)}, len(subargs): {len(subargs)}"
            raise ParseError(tok, msg)
        resolved_args: list[Term] = []
        for defarg, subarg in zip(defargs, subargs):
            if isinstance(defarg, Var):
                if isinstance(subarg, VarTerm):
                    resolved_args.append(subarg)
                else:
                    msg = f"VarTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted"
                    raise ParseError(tok, msg)
            elif isinstance(defarg, PredTemplate):
                if isinstance(subarg, PredTerm):
                    resolved_args.append(subarg)
                elif isinstance(subarg, VarTerm):
                    if defarg.arity == 1:
                        if context.decl.membership is None:
                            msg = "VarTerm is substituted into PredTerm with arity 1, but membership has not been declared"
                            raise ParseError(tok, msg)
                        else:
                            term = MembershipLambda(subarg)
                            start_token = self.unit.tokens[self.unit.node_to_token[id(subarg)][0]]
                            end_token = self.unit.tokens[self.unit.node_to_token[id(subarg)][1]]
                            self.add_node_to_token(term, start_token, end_token)
                            resolved_args.append(term)
                    else:
                        msg = f"VarTerm cannot be substituted into PredTerm with arity {defarg.arity}"
                        raise ParseError(tok, msg)
                else:
                    msg = f"Unexpected type: {type(subarg)}"
                    raise ParseError(tok, msg)
            else:
                if isinstance(subarg, FunTerm):
                    resolved_args.append(subarg)
                else:
                    msg = f"FunTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted"
                    raise ParseError(tok, msg)
        return resolved_args
