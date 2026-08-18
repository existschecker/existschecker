from ast_types import DeclarationUnit, ContextError, TokenStreamError, ParseError
from parsed_ast_types import ParsedExpr, ParsedIdent, ParsedIdentArgs, ParsedFunTemplate, ParsedFunLambda, ParsedPredTemplate, ParsedPredLambda, ParsedNot, ParsedAnd, ParsedOr, ParsedImplies, ParsedIff, ParsedForall, ParsedExists, ParsedExistsUniq, ParsedBottom, ParsedControl, ParsedInvalidControl, ParsedAny, ParsedAssume, ParsedDivide, ParsedSome, ParsedDeny, ParsedContradict, ParsedCase, ParsedExplode, ParsedApply, ParsedLift, ParsedCharacterize, ParsedInvoke, ParsedExpand, ParsedFold, ParsedPad, ParsedSplit, ParsedConnect, ParsedSubstitute, ParsedShow, ParsedAssert, ParsedDeclaration, ParsedInvalidDeclaration, ParsedPrimPred, ParsedAxiom, ParsedTheorem, ParsedDefPred, ParsedDefCon, ParsedDefFun, ParsedDefFunTerm, ParsedDefExist, ParsedDefUniq, ParsedEquality, ParsedInclude, ParsedInvalidInclude, ParsedUnit, ParsedStruct, ParsedTypedIdent, ParsedAccess
from lexer import Token
from token_stream import TokenStream

from lsprotocol import types as lsp
from pygls import uris

import logging
logger = logging.getLogger("proof")

class Parser:
    def __init__(self, unit: DeclarationUnit):
        self.unit = unit
        self.stream = TokenStream(unit.tokens)
        self.parsed_unit = ParsedUnit()

    def add_lsp_error(self, tok: Token, message: str):
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

    def add_node_to_token(self, node: ParsedInclude | ParsedDeclaration | ParsedControl | ParsedExpr, start_token: Token, end_token: Token):
        self.parsed_unit.node_to_token[id(node)] = (start_token.index, end_token.index)

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

    def parse_unit(self) -> ParsedUnit:
        self.stream = TokenStream(self.unit.tokens)
        tok = self.stream.peek()
        try:
            if tok.type == "INCLUDE":
                self.parsed_unit.ast = self.parse_include()
            else:
                self.parsed_unit.ast = self.parse_declaration(tok)
            tok = self.stream.peek()
            if tok.type != "EOF":
                msg = f"Unexpected token {tok.type} after Include or Declaration"
                raise ParseError(tok, msg)
        except (ParseError, TokenStreamError) as e:
            self.add_lsp_error(e.token, e.msg)
            node = ParsedInvalidDeclaration("<invalid>")
            self.add_node_to_token(node, tok, self.stream.last_token)
            self.parsed_unit.ast = node
        except ContextError as e:
            msg = f"{e.__class__.__name__}: {e.msg}"
            self.add_lsp_error(tok, msg)
            node = ParsedInvalidDeclaration("<invalid>")
            self.add_node_to_token(node, tok, self.stream.last_token)
            self.parsed_unit.ast = node
        return self.parsed_unit

    def parse_declaration(self, tok: Token) -> ParsedDeclaration:
        try:
            if tok.type == "PRIMITIVE":
                return self.parse_primitive()
            elif tok.type == "AXIOM":
                return self.parse_axiom()
            elif tok.type == "THEOREM":
                return self.parse_theorem()
            elif tok.type == "DEFINITION":
                return self.parse_definition()
            elif tok.type == "EXISTENCE":
                return self.parse_existence()
            elif tok.type == "UNIQUENESS":
                return self.parse_uniqueness()
            elif tok.type == "EQUALITY":
                return self.parse_equality()
            elif tok.type == "STRUCT":
                return self.parse_struct()
            else:
                msg = "Declaration is required"
                raise ParseError(tok, msg)
        except (ParseError, TokenStreamError) as e:
            self.add_lsp_error(e.token, e.msg)
            node = ParsedInvalidDeclaration("<invalid>")
            self.add_node_to_token(node, tok, self.stream.last_token)
            return node
        except ContextError as e:
            msg = f"{e.__class__.__name__}: {e.msg}"
            self.add_lsp_error(tok, msg)
            node = ParsedInvalidDeclaration("<invalid>")
            self.add_node_to_token(node, tok, self.stream.last_token)
            return node

    def parse_primitive(self) -> ParsedPrimPred:
        start_token = self.stream.consume("PRIMITIVE")
        self.stream.consume("PREDICATE")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = ParsedIdent(name)
        self.add_node_to_token(ref, name_token, name_token)
        self.stream.consume("ARITY")
        arity = int(self.stream.consume("NUMBER").value)
        tex = self.parse_tex()
        primpred = ParsedPrimPred(name=name, ref=ref, arity=arity, tex=tex)
        self.add_node_to_token(primpred, start_token, self.stream.last_token)
        logger.debug(f"[primpred] {name}")
        return primpred

    def parse_axiom(self) -> ParsedAxiom:
        start_token = self.stream.consume("AXIOM")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = ParsedIdent(name)
        self.add_node_to_token(ref, name_token, name_token)
        conclusion = self.parse_formula()
        axiom = ParsedAxiom(name=name, ref=ref, conclusion=conclusion)
        self.add_node_to_token(axiom, start_token, self.stream.last_token)
        logger.debug(f"[axiom] {name}")
        return axiom

    def parse_theorem(self) -> ParsedTheorem:
        start_token = self.stream.consume("THEOREM")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = ParsedIdent(name)
        self.add_node_to_token(ref, name_token, name_token)
        conclusion = self.parse_formula()
        self.stream.consume("LBRACE")
        proof = self.parse_block()
        self.stream.consume("RBRACE")
        theorem = ParsedTheorem(name=name, ref=ref, conclusion=conclusion, proof=proof)
        self.add_node_to_token(theorem, start_token, self.stream.last_token)
        logger.debug(f"[theorem] {name}")
        return theorem

    def parse_definition(self) -> ParsedDefPred | ParsedDefCon | ParsedDefFun | ParsedDefFunTerm:
        start_token = self.stream.consume("DEFINITION")
        tok = self.stream.peek()
        if tok.type == "PREDICATE":
            return self.parse_defpred(start_token)
        elif tok.type == "CONSTANT":
            return self.parse_defcon(start_token)
        elif tok.type == "FUNCTION":
            return self.parse_deffun_or_deffunterm(start_token)
        else:
            msg = "predicate, constant or function is required after definition"
            raise ParseError(start_token, msg)

    def parse_defpred(self, start_token: Token) -> ParsedDefPred:
        self.stream.consume("PREDICATE")
        if self.stream.peek().type == "AUTOEXPAND":
            self.stream.consume("AUTOEXPAND")
            autoexpand = True
        else:
            autoexpand =False
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = ParsedIdent(name)
        self.add_node_to_token(ref, name_token, name_token)
        self.stream.consume("LPAREN")
        args, _, _, _ = self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        formula = self.parse_formula()
        tex = self.parse_tex()
        defpred = ParsedDefPred(name=name, ref=ref, args=args, formula=formula, autoexpand=autoexpand, tex=tex)
        self.add_node_to_token(defpred, start_token, self.stream.last_token)
        logger.debug(f"[defpred] {name}")
        return defpred

    def parse_defcon(self, start_token: Token) -> ParsedDefCon:
        self.stream.consume("CONSTANT")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = ParsedIdent(name)
        self.add_node_to_token(ref, name_token, name_token)
        self.stream.consume("BY")
        theorem_token = self.stream.consume("IDENT")
        theorem_name = theorem_token.value
        ref_theorem = ParsedIdent(theorem_name)
        self.add_node_to_token(ref_theorem, theorem_token, theorem_token)
        tex = self.parse_tex()
        defcon = ParsedDefCon(name=name, ref=ref, ref_theorem=ref_theorem, tex=tex)
        self.add_node_to_token(defcon, start_token, self.stream.last_token)
        logger.debug(f"[defcon] {name}")
        return defcon

    def parse_deffun_or_deffunterm(self, start_token: Token) -> ParsedDefFun | ParsedDefFunTerm:
        self.stream.consume("FUNCTION")
        name_token = self.stream.consume("IDENT")
        if self.stream.peek().type == "BY":
            return self.parse_deffun(start_token, name_token)
        else:
            return self.parse_deffunterm(start_token, name_token)

    def parse_deffun(self, start_token: Token, name_token: Token) -> ParsedDefFun:
        name = name_token.value
        ref = ParsedIdent(name)
        self.add_node_to_token(ref, name_token, name_token)
        self.stream.consume("BY")
        theorem_token = self.stream.consume("IDENT")
        theorem_name = theorem_token.value
        ref_theorem = ParsedIdent(theorem_name)
        self.add_node_to_token(ref_theorem, theorem_token, theorem_token)
        tex = self.parse_tex()
        deffun = ParsedDefFun(name=name, ref=ref, args=[], ref_theorem=ref_theorem, tex=tex)
        self.add_node_to_token(deffun, start_token, self.stream.last_token)
        logger.debug(f"[deffun] {name}")
        return deffun

    def parse_deffunterm(self, start_token: Token, name_token: Token) -> ParsedDefFunTerm:
        name = name_token.value
        ref = ParsedIdent(name)
        self.add_node_to_token(ref, name_token, name_token)
        self.stream.consume("LPAREN")
        args, _, _, _ = self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        term = self.parse_term()
        tex = self.parse_tex()
        deffunterm = ParsedDefFunTerm(name=name, ref=ref, args=args, varterm=term, tex=tex)
        self.add_node_to_token(deffunterm, start_token, self.stream.last_token)
        logger.debug(f"[deffunterm] {name}")
        return deffunterm

    def parse_existence(self) -> ParsedDefExist:
        start_token = self.stream.consume("EXISTENCE")
        existence_name_token = self.stream.consume("IDENT")
        existence_name = existence_name_token.value
        existence_formula = self.parse_formula()
        self.stream.consume("BY")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = ParsedIdent(existence_name)
        ref_term = ParsedIdent(name)
        defexist = ParsedDefExist(name=existence_name, ref=ref, formula=existence_formula, ref_term=ref_term)
        self.add_node_to_token(ref, existence_name_token, existence_name_token)
        self.add_node_to_token(ref_term, name_token, name_token)
        self.add_node_to_token(defexist, start_token, self.stream.last_token)
        return defexist

    def parse_uniqueness(self) -> ParsedDefUniq:
        start_token = self.stream.consume("UNIQUENESS")
        uniqueness_name_token = self.stream.consume("IDENT")
        uniqueness_name = uniqueness_name_token.value
        uniqueness_formula = self.parse_formula()
        self.stream.consume("BY")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = ParsedIdent(uniqueness_name)
        ref_term = ParsedIdent(name)
        defuniq = ParsedDefUniq(name=uniqueness_name, ref=ref, formula=uniqueness_formula, ref_term=ref_term)
        self.add_node_to_token(ref, uniqueness_name_token, uniqueness_name_token)
        self.add_node_to_token(ref_term, name_token, name_token)
        self.add_node_to_token(defuniq, start_token, self.stream.last_token)
        return defuniq

    def parse_equality(self) -> ParsedEquality:
        start_token = self.stream.consume("EQUALITY")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = ParsedIdent(name)
        self.add_node_to_token(ref, name_token, name_token)
        tex = self.parse_tex()
        equality = ParsedEquality(name=name, ref=ref, tex=tex)
        self.add_node_to_token(equality, start_token, self.stream.last_token)
        logger.debug(f"[equality] {name}")
        return equality

    def parse_struct(self) -> ParsedStruct:
        start_token = self.stream.consume("STRUCT")
        name_token = self.stream.consume("IDENT")
        name = name_token.value
        ref = ParsedIdent(name)
        self.add_node_to_token(ref, name_token, name_token)
        self.stream.consume("LBRACE")
        self.stream.consume("FIELD")
        self.stream.consume("LBRACE")
        vars = self.parse_vars_or_struct_vars()
        self.stream.consume("RBRACE")
        self.stream.consume("CONDITION")
        self.stream.consume("LBRACE")
        formulas: dict[ParsedIdent, ParsedExpr] = {}
        while True:
            formula_name_token = self.stream.consume("IDENT")
            formula_name = formula_name_token.value
            ref_formula = ParsedIdent(formula_name)
            self.add_node_to_token(ref_formula, formula_name_token, formula_name_token)
            self.stream.consume("COLON")
            formula = self.parse_formula()
            formulas[ref_formula] = formula
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        self.stream.consume("RBRACE")
        self.stream.consume("RBRACE")
        struct = ParsedStruct(name=name, ref=ref, vars=vars, formulas=formulas)
        self.add_node_to_token(struct, start_token, self.stream.last_token)
        logger.debug(f"[struct] {name}")
        return struct

    def parse_include(self) -> ParsedInclude:
        start_token = self.stream.consume("INCLUDE")
        try:
            file = self.stream.consume("STRING").value
            node = ParsedInclude(file, start_token)
            self.add_node_to_token(node, start_token, self.stream.last_token)
            return node
        except (ParseError, TokenStreamError) as e:
            self.add_lsp_error(e.token, e.msg)
            node = ParsedInvalidInclude(file="<invalid>", token=start_token)
            self.add_node_to_token(node, start_token, self.stream.last_token)
            return node
        except ContextError as e:
            msg = f"{e.__class__.__name__}: {e.msg}"
            self.add_lsp_error(start_token, msg)
            node = ParsedInvalidInclude(file="<invalid>", token=start_token)
            self.add_node_to_token(node, start_token, self.stream.last_token)
            return node

    def parse_block(self) -> list[ParsedControl]:
        body: list[ParsedControl] = []
        while True:

            tok = self.stream.peek()
            if not tok or tok.type == "RBRACE":
                break
            else:
                control = self.parse_control(tok)
                body.append(control)
                if isinstance(control, ParsedInvalidControl):
                    self.skip_until_next_RBRACE_or_control()
        return body

    def parse_control(self, tok: Token) -> ParsedControl:
        try:
            if tok.type == "ANY":
                return self.parse_any()
            elif tok.type == "ASSUME":
                return self.parse_assume()
            elif tok.type == "DIVIDE":
                return self.parse_divide()
            elif tok.type == "SOME":
                return self.parse_some()
            elif tok.type == "DENY":
                return self.parse_deny()
            elif tok.type == "CONTRADICT":
                return self.parse_contradict()
            elif tok.type == "EXPLODE":
                return self.parse_explode()
            elif tok.type == "APPLY":
                return self.parse_apply()
            elif tok.type == "LIFT":
                return self.parse_lift()
            elif tok.type == "CHARACTERIZE":
                return self.parse_characterize()
            elif tok.type == "INVOKE":
                return self.parse_invoke()
            elif tok.type == "EXPAND":
                return self.parse_expand()
            elif tok.type == "FOLD":
                return self.parse_fold()
            elif tok.type == "PAD":
                return self.parse_pad()
            elif tok.type == "SPLIT":
                return self.parse_split()
            elif tok.type == "CONNECT":
                return self.parse_connect()
            elif tok.type == "SUBSTITUTE":
                return self.parse_substitute()
            elif tok.type == "SHOW":
                return self.parse_show()
            elif tok.type == "ASSERT":
                return self.parse_assert()
            else:
                msg = "Control is required"
                raise ParseError(tok, msg)
        except (ParseError, TokenStreamError) as e:
            self.add_lsp_error(e.token, e.msg)
            node = ParsedInvalidControl()
            self.add_node_to_token(node, tok, self.stream.last_token)
            return node
        except ContextError as e:
            msg = f"{e.__class__.__name__}: {e.msg}"
            self.add_lsp_error(tok, msg)
            node = ParsedInvalidControl()
            self.add_node_to_token(node, tok, self.stream.last_token)
            return node

    def parse_any(self) -> ParsedAny:
        start_token = self.stream.consume("ANY")
        items, _, _, _ = self.parse_vars_or_struct_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        node = ParsedAny(items=items, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_assume(self) -> ParsedAssume:
        start_token = self.stream.consume("ASSUME")
        premise = self.parse_formula()
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        node = ParsedAssume(premise=premise, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
    def parse_divide(self) -> ParsedDivide:
        start_token = self.stream.consume("DIVIDE")
        fact = self.parse_formula()
        cases: list[ParsedCase] = []
        while self.stream.peek().type == "CASE":
            cases.append(self.parse_case())
        node = ParsedDivide(fact=fact, cases=cases)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
    def parse_case(self) -> ParsedCase:
        start_token = self.stream.consume("CASE")
        premise = self.parse_formula()
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        node = ParsedCase(premise=premise, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
    def parse_some(self) -> ParsedSome:
        start_token = self.stream.consume("SOME")
        items: list[ParsedIdent | None] = []
        while True:
            if self.stream.peek().type == "UNDERSCORE":
                self.stream.consume("UNDERSCORE")
                items.append(None)
            else:
                items.append(self.parse_var())
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        self.stream.consume("SUCH")
        fact = self.parse_formula()
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        node = ParsedSome(items=items, fact=fact, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
    def parse_deny(self) -> ParsedDeny:
        start_token = self.stream.consume("DENY")
        premise = self.parse_formula()
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        node = ParsedDeny(premise=premise, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
    def parse_contradict(self) -> ParsedContradict:
        start_token = self.stream.consume("CONTRADICT")
        contradiction = self.parse_formula()
        node = ParsedContradict(contradiction=contradiction)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node
    
    def parse_explode(self) -> ParsedExplode:
        start_token = self.stream.consume("EXPLODE")
        conclusion = self.parse_formula()
        node = ParsedExplode(conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_apply(self) -> ParsedApply:
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
        fact = self.parse_formula()
        self.stream.consume("FOR")
        terms = self.parse_terms_or_none()
        node = ParsedApply(invoke=invoke, fact=fact, terms=terms)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_lift(self) -> ParsedLift:
        start_token = self.stream.consume("LIFT")
        self.stream.consume("FOR")
        varterms = self.parse_terms_or_none()
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula()
        node = ParsedLift(varterms=varterms, conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_characterize(self) -> ParsedCharacterize:
        start_token = self.stream.consume("CHARACTERIZE")
        self.stream.consume("FOR")
        varterm = self.parse_term()
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula()
        node = ParsedCharacterize(varterm=varterm, conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_invoke(self) -> ParsedInvoke:
        start_token = self.stream.consume("INVOKE")
        if self.stream.peek().type == "RIGHTWARD":
            self.stream.consume("RIGHTWARD")
            direction = "rightward"
        elif self.stream.peek().type == "LEFTWARD":
            self.stream.consume("LEFTWARD")
            direction = "leftward"
        else:
            direction = "none"
        fact = self.parse_formula()
        node = ParsedInvoke(direction=direction, fact=fact)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_expand(self) -> ParsedExpand:
        start_token = self.stream.consume("EXPAND")
        fact = self.parse_formula()
        self.stream.consume("FOR")
        refs, indexes = self.parse_refs_indexes()
        node = ParsedExpand(fact=fact, refs=refs, indexes=indexes)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_fold(self) -> ParsedFold:
        start_token = self.stream.consume("FOLD")
        self.stream.consume("FOR")
        refs, indexes = self.parse_refs_indexes()
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula()
        node = ParsedFold(refs=refs, indexes=indexes, conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_pad(self) -> ParsedPad:
        start_token = self.stream.consume("PAD")
        fact = self.parse_formula()
        self.stream.consume("CONCLUDE")
        conclusion = self.parse_formula()
        node = ParsedPad(fact=fact, conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_split(self) -> ParsedSplit:
        start_token = self.stream.consume("SPLIT")
        if self.stream.peek().type == "NUMBER":
            index = int(self.stream.consume("NUMBER").value)
        else:
            index = None
        fact = self.parse_formula()
        node = ParsedSplit(index=index, fact=fact)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_connect(self) -> ParsedConnect:
        start_token = self.stream.consume("CONNECT")
        conclusion = self.parse_formula()
        node = ParsedConnect(conclusion=conclusion)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_substitute(self) -> ParsedSubstitute:
        start_token = self.stream.consume("SUBSTITUTE")
        fact = self.parse_formula()
        self.stream.consume("FOR")
        env: dict[ParsedExpr, ParsedExpr] = {}
        indexes: dict[ParsedExpr, list[int]] = {}
        while True:
            key = self.parse_term()
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
            value = self.parse_term()
            env[key] = value
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        node = ParsedSubstitute(fact=fact, env=env, indexes=indexes)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_show(self) -> ParsedShow:
        start_token = self.stream.consume("SHOW")
        conclusion = self.parse_bot_or_formula()
        self.stream.consume("LBRACE")
        body = self.parse_block()
        self.stream.consume("RBRACE")
        node = ParsedShow(conclusion=conclusion, body=body)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_assert(self) -> ParsedAssert:
        start_token = self.stream.consume("ASSERT")
        reference = self.parse_formula()
        node = ParsedAssert(reference=reference)
        self.add_node_to_token(node, start_token, self.stream.last_token)
        return node

    def parse_bot_or_formula(self) -> ParsedBottom | ParsedExpr:
        if self.stream.peek().type == "BOT":
            self.stream.consume("BOT")
            return ParsedBottom()
        else:
            return self.parse_formula()

    def parse_formula(self) -> ParsedExpr:
        return self.parse_implies()

    def parse_implies(self) -> ParsedExpr:
        left = self.parse_and()
        start_token = self.unit.tokens[self.parsed_unit.node_to_token[id(left)][0]]
        while self.stream.peek().type in ("IMPLIES", "IFF"):
            tok = self.stream.peek()
            self.stream.consume(tok.type)
            right = self.parse_and()
            if tok.type == "IMPLIES":
                left = ParsedImplies(left, right)
                self.add_node_to_token(left, start_token, self.stream.last_token)
            elif tok.type == "IFF":
                left = ParsedIff(left, right)
                self.add_node_to_token(left, start_token, self.stream.last_token)
        return left

    def parse_and(self) -> ParsedExpr:
        left = self.parse_primary()
        start_token = self.unit.tokens[self.parsed_unit.node_to_token[id(left)][0]]
        while self.stream.peek().type in ("AND", "OR"):
            tok = self.stream.peek()
            self.stream.consume(tok.type)
            right = self.parse_primary()
            if tok.type == "AND":
                left = ParsedAnd(left, right)
                self.add_node_to_token(left, start_token, self.stream.last_token)
            elif tok.type == "OR":
                left = ParsedOr(left, right)
                self.add_node_to_token(left, start_token, self.stream.last_token)
        return left

    def parse_primary(self) -> ParsedExpr:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            pred_tok = self.stream.consume("IDENT")
            ident = ParsedIdent(pred_tok.value)
            self.add_node_to_token(ident, pred_tok, pred_tok)
            if self.stream.peek().type == "LPAREN":
                self.stream.consume("LPAREN")
                args = self.parse_terms()
                self.stream.consume("RPAREN")
                formula = ParsedIdentArgs(ident, tuple(args))
                self.add_node_to_token(formula, tok, self.stream.last_token)
                return formula
            elif self.stream.peek().type == "DOT":
                return self.parse_access(ident, pred_tok)
            else:
                return ident

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
            formula = ParsedNot(body)
            self.add_node_to_token(formula, tok, self.stream.last_token)
            return formula

        elif tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"):
            quantified_pairs: list[tuple[Token, ParsedIdent | ParsedTypedIdent | ParsedPredTemplate | ParsedFunTemplate]] = []
            while tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"):
                self.stream.consume(tok.type)
                if tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ"):
                    var = self.parse_var_or_struct_var()
                    quantified_pairs.append((tok, var))
                    tok = self.stream.peek()
                elif tok.type == "FORALL_PRED_TMPL":
                    pred_tmpl = self.parse_pred_tmpl()
                    quantified_pairs.append((tok, pred_tmpl))
                    tok = self.stream.peek()
                else:
                    fun_tmpl = self.parse_fun_tmpl()
                    quantified_pairs.append((tok, fun_tmpl))
                    tok = self.stream.peek()
            self.stream.consume("LPAREN")
            body = self.parse_formula()
            self.stream.consume("RPAREN")
            for tok, item in reversed(quantified_pairs):
                if tok.type in ("FORALL", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"):
                    body = ParsedForall(item, body)
                    self.add_node_to_token(body, tok, self.stream.last_token)
                elif tok.type == "EXISTS":
                    if isinstance(item, ParsedIdent):
                        body = ParsedExists(item, body)
                        self.add_node_to_token(body, tok, self.stream.last_token)
                    else:
                        msg = f"Unexpected type: {type(item)}"
                        raise ParseError(tok, msg)
                elif tok.type == "EXISTS_UNIQ":
                    if isinstance(item, ParsedIdent):
                        body = ParsedExistsUniq(item, body)
                        self.add_node_to_token(body, tok, self.stream.last_token)
                    else:
                        msg = f"Unexpected type: {type(item)}"
                        raise ParseError(tok, msg)
            return body

        else:
            msg = "Formula objct is required, but unknown token is found"
            raise ParseError(tok, msg)

    def parse_terms_or_none(self) -> list[ParsedExpr | None]:
        terms: list[ParsedExpr | None] = []
        while True:
            if self.stream.peek().type == "UNDERSCORE":
                self.stream.consume("UNDERSCORE")
                terms.append(None)
            else:
                terms.append(self.parse_term())
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return terms

    def parse_terms(self) -> list[ParsedExpr]:
        terms = [self.parse_term()]
        while self.stream.peek().type == "COMMA":
            self.stream.consume("COMMA")
            terms.append(self.parse_term())
        return terms

    def parse_access(self, parent: ParsedIdent | ParsedAccess, start_token: Token) -> ParsedExpr:
        current_expr = parent
        while True:
            self.stream.consume("DOT")
            child_tok = self.stream.consume("IDENT")
            child = ParsedIdent(child_tok.value)
            self.add_node_to_token(child, child_tok, child_tok)
            current_expr = ParsedAccess(current_expr, child)
            self.add_node_to_token(current_expr, start_token, child_tok)
            if self.stream.peek().type != "DOT":
                break
        return current_expr

    def parse_term(self) -> ParsedExpr:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            fun_token = self.stream.consume("IDENT")
            ident = ParsedIdent(fun_token.value)
            self.add_node_to_token(ident, fun_token, fun_token)
            if self.stream.peek().type == "LPAREN":
                self.stream.consume("LPAREN")
                args = self.parse_terms()
                self.stream.consume("RPAREN")
                term = ParsedIdentArgs(ident, tuple(args))
                self.add_node_to_token(term, tok, self.stream.last_token)
                return term
            elif self.stream.peek().type == "DOT":
                return self.parse_access(ident, tok)
            else:
                return ident
        elif tok.type == "LAMBDA_PRED":
            self.stream.consume("LAMBDA_PRED")
            if self.stream.peek().type == "DOT":
                vars: list[ParsedIdent] = []
            else:
                vars = self.parse_vars()
            self.stream.consume("DOT")
            formula = self.parse_formula()
            term = ParsedPredLambda(tuple(vars), formula)
            self.add_node_to_token(term, tok, self.stream.last_token)
            return term
        elif tok.type == "LAMBDA_FUN":
            self.stream.consume("LAMBDA_FUN")
            if self.stream.peek().type == "DOT":
                vars: list[ParsedIdent] = []
            else:
                vars = self.parse_vars()
            self.stream.consume("DOT")
            term = self.parse_term()
            term = ParsedFunLambda(tuple(vars), term)
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
        if self.stream.peek().type == "TEX":
            self.stream.consume("TEX")
            if self.stream.peek().type == "INFIX":
                self.stream.consume("INFIX")
                return ["", self.stream.consume("STRING").value, ""]
            else:
                tex: list[str] = []
                while True:
                    tex.append(self.stream.consume("STRING").value)
                    if self.stream.peek().type == "COMMA":
                        self.stream.consume("COMMA")
                    else:
                        break
                return tex
        else:
            return []

    def create_tex(self, name: str, arity: int):
        if arity == 0:
            tex = [f"\\mathrm{{{name}}}"]
        else:
            tex = [f"\\mathrm{{{name}}}("]
            tex.extend(["," for _ in range(arity - 1)])
            tex.append(")")
        return tex

    def parse_vars_or_struct_vars(self) -> list[ParsedIdent | ParsedTypedIdent]:
        vars: list[ParsedIdent | ParsedTypedIdent] = []
        while True:
            vars.append(self.parse_var_or_struct_var())
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return vars

    def parse_vars_or_struct_vars_or_pred_tmpls_or_fun_tmpls(self) -> tuple[list[ParsedIdent | ParsedTypedIdent | ParsedPredTemplate | ParsedFunTemplate], list[ParsedIdent | ParsedTypedIdent], list[ParsedPredTemplate], list[ParsedFunTemplate]]:
        items: list[ParsedIdent | ParsedTypedIdent | ParsedPredTemplate | ParsedFunTemplate] = []
        vars: list[ParsedIdent | ParsedTypedIdent] = []
        pred_tmpls: list[ParsedPredTemplate] = []
        fun_tmpls: list[ParsedFunTemplate] = []
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
                var = self.parse_var_or_struct_var()
                items.append(var)
                vars.append(var)
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return items, vars, pred_tmpls, fun_tmpls

    def parse_vars_or_pred_tmpls_or_fun_tmpls(self) -> tuple[list[ParsedIdent | ParsedPredTemplate | ParsedFunTemplate], list[ParsedIdent], list[ParsedPredTemplate], list[ParsedFunTemplate]]:
        items: list[ParsedIdent | ParsedPredTemplate | ParsedFunTemplate] = []
        vars: list[ParsedIdent] = []
        pred_tmpls: list[ParsedPredTemplate] = []
        fun_tmpls: list[ParsedFunTemplate] = []
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

    def parse_vars(self) -> list[ParsedIdent]:
        vars: list[ParsedIdent] = []
        while True:
            vars.append(self.parse_var())
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return vars

    def parse_var_or_struct_var(self) -> ParsedIdent | ParsedTypedIdent:
        tok = self.stream.consume("IDENT")
        var_name = tok.value
        var = ParsedIdent(var_name)
        self.add_node_to_token(var, tok, tok)
        if self.stream.peek().type == "COLON":
            self.stream.consume("COLON")
            struct_tok = self.stream.consume("IDENT")
            struct_type = ParsedIdent(struct_tok.value)
            self.add_node_to_token(struct_type, struct_tok, struct_tok)
            struct_var = ParsedTypedIdent(var, struct_type)
            self.add_node_to_token(struct_var, tok, struct_tok)
            return struct_var
        else:
            return var

    def parse_var(self) -> ParsedIdent:
        tok = self.stream.consume("IDENT")
        var_name = tok.value
        var = ParsedIdent(var_name)
        self.add_node_to_token(var, tok, tok)
        return var

    def parse_pred_tmpl(self) -> ParsedPredTemplate:
        tok = self.stream.consume("IDENT")
        pred_tmpl_name = tok.value
        self.stream.consume("LBRACKET")
        arity = int(self.stream.consume("NUMBER").value)
        self.stream.consume("RBRACKET")
        pred = ParsedPredTemplate(pred_tmpl_name, arity)
        self.add_node_to_token(pred, tok, tok)
        return pred

    def parse_fun_tmpl(self) -> ParsedFunTemplate:
        tok = self.stream.consume("IDENT")
        fun_tmpl_name = tok.value
        self.stream.consume("LBRACKET")
        arity = int(self.stream.consume("NUMBER").value)
        self.stream.consume("RBRACKET")
        fun = ParsedFunTemplate(fun_tmpl_name, arity)
        self.add_node_to_token(fun, tok, tok)
        return fun

    def parse_refs_indexes(self) -> tuple[list[ParsedIdent], dict[ParsedIdent, list[int]]]:
        refs: list[ParsedIdent] = []
        indexes: dict[ParsedIdent, list[int]] = {}
        while True:
            ref_token = self.stream.consume("IDENT")
            ref_name = ref_token.value
            parsed_name = ParsedIdent(ref_name)
            self.add_node_to_token(parsed_name, ref_token, ref_token)
            refs.append(parsed_name)
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
                indexes[parsed_name] = indexes_
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return refs, indexes
