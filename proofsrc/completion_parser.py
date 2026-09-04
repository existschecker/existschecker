from lexer import Token
from ast_types import PrimPred, DefPred, Equality, DefCon, DefFun, DefFunTerm, Axiom, Theorem, DefConExist, DefConUniq, DefFunExist, DefFunUniq

class ExpectedTokenError(Exception):
    def __init__(self, expected_types: tuple[str, ...], decl_types: tuple[type, ...] | None = None) -> None:
        self.expected_types = expected_types
        if decl_types is None:
            decl_types = ()
        self.decl_types = decl_types

class CompletionTokenStream:
    def __init__(self, tokens: list[Token]):
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> Token:
        if self.pos >= len(self.tokens):
            raise Exception("Unexpected end of input")
        return self.tokens[self.pos]

    def consume(self, expected_type: str, decl_types: tuple[type, ...] | None = None) -> Token:
        if decl_types is None:
            decl_types = ()
        tok = self.peek()
        if tok.type != expected_type:
            raise ExpectedTokenError((expected_type,), decl_types)
        self.pos += 1
        return tok

class CompletionParser:
    def __init__(self, tokens: list[Token]):
        self.stream = CompletionTokenStream(tokens)

    def parse_unit(self) -> ExpectedTokenError | None:
        tok = self.stream.peek()
        try:
            if tok.type == "INCLUDE":
                self.parse_include()
            else:
                self.parse_declaration(tok)
            raise ExpectedTokenError(("INCLUDE", "PRIMITIVE", "AXIOM", "THEOREM", "DEFINITION", "EXISTENCE", "UNIQUENESS", "EQUALITY", "STRUCT"))
        except ExpectedTokenError as e:
            if self.stream.peek().type == "EOF":
                return e
            else:
                return None

    def parse_declaration(self, tok: Token) -> None:
        if tok.type == "PRIMITIVE":
            self.parse_primitive()
        elif tok.type == "AXIOM":
            self.parse_axiom()
        elif tok.type == "THEOREM":
            self.parse_theorem()
        elif tok.type == "DEFINITION":
            self.parse_definition()
        elif tok.type == "EXISTENCE":
            self.parse_existence()
        elif tok.type == "UNIQUENESS":
            self.parse_uniqueness()
        elif tok.type == "EQUALITY":
            self.parse_equality()
        elif tok.type == "STRUCT":
            self.parse_struct()
        else:
            raise ExpectedTokenError(("PRIMITIVE", "AXIOM", "THEOREM", "DEFINITION", "EXISTENCE", "UNIQUENESS", "EQUALITY", "STRUCT"))

    def parse_primitive(self) -> None:
        self.stream.consume("PRIMITIVE")
        self.stream.consume("PREDICATE")
        self.stream.consume("IDENT")
        self.stream.consume("ARITY")
        self.stream.consume("NUMBER")
        self.parse_tex()

    def parse_axiom(self) -> None:
        self.stream.consume("AXIOM")
        self.stream.consume("IDENT")
        self.parse_formula()

    def parse_theorem(self) -> None:
        self.stream.consume("THEOREM")
        self.stream.consume("IDENT")
        self.parse_formula()
        self.stream.consume("LBRACE")
        self.parse_block()
        self.stream.consume("RBRACE")

    def parse_definition(self) -> None:
        self.stream.consume("DEFINITION")
        tok = self.stream.peek()
        if tok.type == "PREDICATE":
            return self.parse_defpred()
        elif tok.type == "CONSTANT":
            return self.parse_defcon()
        elif tok.type == "FUNCTION":
            return self.parse_deffun_or_deffunterm()
        else:
            raise ExpectedTokenError(("DEFINITION", "CONSTANT", "FUNCTION"))

    def parse_defpred(self) -> None:
        self.stream.consume("PREDICATE")
        if self.stream.peek().type == "AUTOEXPAND":
            self.stream.consume("AUTOEXPAND")
        self.stream.consume("IDENT")
        self.stream.consume("LPAREN")
        self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        self.parse_formula()
        self.parse_tex()

    def parse_defcon(self) -> None:
        self.stream.consume("CONSTANT")
        self.stream.consume("IDENT")
        self.stream.consume("BY")
        self.stream.consume("IDENT", (Theorem,))
        self.parse_tex()

    def parse_deffun_or_deffunterm(self) -> None:
        self.stream.consume("FUNCTION")
        self.stream.consume("IDENT")
        if self.stream.peek().type == "BY":
            return self.parse_deffun()
        else:
            return self.parse_deffunterm()

    def parse_deffun(self) -> None:
        self.stream.consume("BY")
        self.stream.consume("IDENT", (Theorem,))
        self.parse_tex()

    def parse_deffunterm(self) -> None:
        self.stream.consume("LPAREN")
        self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        self.parse_term()
        self.parse_tex()

    def parse_existence(self) -> None:
        self.stream.consume("EXISTENCE")
        self.stream.consume("IDENT")
        self.parse_formula()
        self.stream.consume("BY")
        self.stream.consume("IDENT", (DefCon, DefFun))

    def parse_uniqueness(self) -> None:
        self.stream.consume("UNIQUENESS")
        self.stream.consume("IDENT")
        self.parse_formula()
        self.stream.consume("BY")
        self.stream.consume("IDENT", (DefCon, DefFun))

    def parse_equality(self) -> None:
        self.stream.consume("EQUALITY")
        self.stream.consume("IDENT")
        self.parse_tex()

    def parse_struct(self) -> None:
        self.stream.consume("STRUCT")
        self.stream.consume("IDENT")
        tok = self.stream.peek()
        if tok.type == "LBRACE":
            return self.parse_struct_main()
        elif tok.type == "PREDICATE":
            return self.parse_struct_predicate()
        else:
            raise ExpectedTokenError(("LBRACE", "PREDICATE"))

    def parse_struct_main(self) -> None:
        self.stream.consume("LBRACE")
        self.stream.consume("FIELD")
        self.stream.consume("LBRACE")
        self.parse_vars_or_struct_vars()
        self.stream.consume("RBRACE")
        self.stream.consume("CONDITION")
        self.stream.consume("LBRACE")
        while True:
            self.stream.consume("IDENT")
            self.stream.consume("COLON")
            self.parse_formula()
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        self.stream.consume("RBRACE")
        self.stream.consume("RBRACE")

    def parse_struct_predicate(self) -> None:
        self.stream.consume("PREDICATE")
        self.stream.consume("IDENT")
        self.stream.consume("LPAREN")
        self.parse_vars()
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        self.parse_formula()

    def parse_include(self) -> None:
        self.stream.consume("INCLUDE")
        self.stream.consume("STRING")

    def parse_block(self) -> None:
        while True:
            tok = self.stream.peek()
            if not tok or tok.type == "RBRACE":
                break
            else:
                try:
                    self.parse_control(tok)
                except ExpectedTokenError:
                    if self.stream.peek().type == "EOF":
                        raise
                    else:
                        self.skip_until_next_RBRACE_or_control()

    def skip_until_next_RBRACE_or_control(self):
        nest_level = 0
        while True:
            tok = self.stream.peek()
            if tok.type == "EOF":
                return
            if nest_level == 0 and tok.type in ("RBRACE", "ANY", "ASSUME", "DIVIDE", "SOME", "DENY", "CONTRADICT", "EXPLODE", "APPLY", "LIFT", "CHARACTERIZE", "INVOKE", "EXPAND", "FOLD", "PAD", "SPLIT", "CONNECT", "SUBSTITUTE", "SHOW", "ASSERT"):
                return
            if tok.type == "LBRACE":
                nest_level += 1
            elif tok.type == "RBRACE":
                nest_level -= 1
            self.stream.consume(tok.type)

    def parse_control(self, tok: Token) -> None:
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
            raise ExpectedTokenError(("ANY", "ASSUME", "DIVIDE", "SOME", "DENY", "CONTRADICT", "EXPLODE", "APPLY", "LIFT", "CHARACTERIZE", "INVOKE", "EXPAND", "FOLD", "PAD", "SPLIT", "CONNECT", "SUBSTITUTE", "SHOW", "ASSERT"))

    def parse_any(self) -> None:
        self.stream.consume("ANY")
        self.parse_vars_or_struct_vars_or_pred_tmpls_or_fun_tmpls()
        self.stream.consume("LBRACE")
        self.parse_block()
        self.stream.consume("RBRACE")

    def parse_assume(self) -> None:
        self.stream.consume("ASSUME")
        self.parse_formula()
        self.stream.consume("LBRACE")
        self.parse_block()
        self.stream.consume("RBRACE")

    def parse_divide(self) -> None:
        self.stream.consume("DIVIDE")
        self.parse_formula()
        while self.stream.peek().type == "CASE":
            self.parse_case()

    def parse_case(self) -> None:
        self.stream.consume("CASE")
        self.parse_formula()
        self.stream.consume("LBRACE")
        self.parse_block()
        self.stream.consume("RBRACE")

    def parse_some(self) -> None:
        self.stream.consume("SOME")
        while True:
            if self.stream.peek().type == "UNDERSCORE":
                self.stream.consume("UNDERSCORE")
            else:
                self.parse_var()
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        self.stream.consume("SUCH")
        self.parse_formula()
        self.stream.consume("LBRACE")
        self.parse_block()
        self.stream.consume("RBRACE")

    def parse_deny(self) -> None:
        self.stream.consume("DENY")
        self.parse_formula()
        self.stream.consume("LBRACE")
        self.parse_block()
        self.stream.consume("RBRACE")

    def parse_contradict(self) -> None:
        self.stream.consume("CONTRADICT")
        self.parse_formula()

    def parse_explode(self) -> None:
        self.stream.consume("EXPLODE")
        self.parse_formula()

    def parse_apply(self) -> None:
        self.stream.consume("APPLY")
        if self.stream.peek().type == "INVOKE":
            self.stream.consume("INVOKE")
            if self.stream.peek().type == "RIGHTWARD":
                self.stream.consume("RIGHTWARD")
            elif self.stream.peek().type == "LEFTWARD":
                self.stream.consume("LEFTWARD")
        self.parse_formula()
        self.stream.consume("FOR")
        self.parse_terms_or_none()

    def parse_lift(self) -> None:
        self.stream.consume("LIFT")
        self.stream.consume("FOR")
        self.parse_terms_or_none()
        self.stream.consume("CONCLUDE")
        self.parse_formula()

    def parse_characterize(self) -> None:
        self.stream.consume("CHARACTERIZE")
        self.stream.consume("FOR")
        self.parse_term()
        self.stream.consume("CONCLUDE")
        self.parse_formula()

    def parse_invoke(self) -> None:
        self.stream.consume("INVOKE")
        if self.stream.peek().type == "RIGHTWARD":
            self.stream.consume("RIGHTWARD")
        elif self.stream.peek().type == "LEFTWARD":
            self.stream.consume("LEFTWARD")
        self.parse_formula()

    def parse_expand(self) -> None:
        self.stream.consume("EXPAND")
        self.parse_formula()
        self.stream.consume("FOR")
        self.parse_refs_indexes()

    def parse_fold(self) -> None:
        self.stream.consume("FOLD")
        self.stream.consume("FOR")
        self.parse_refs_indexes()
        self.stream.consume("CONCLUDE")
        self.parse_formula()

    def parse_pad(self) -> None:
        self.stream.consume("PAD")
        self.parse_formula()
        self.stream.consume("CONCLUDE")
        self.parse_formula()

    def parse_split(self) -> None:
        self.stream.consume("SPLIT")
        if self.stream.peek().type == "NUMBER":
            self.stream.consume("NUMBER")
        self.parse_formula()

    def parse_connect(self) -> None:
        self.stream.consume("CONNECT")
        self.parse_formula()

    def parse_substitute(self) -> None:
        self.stream.consume("SUBSTITUTE")
        self.parse_formula()
        self.stream.consume("FOR")
        while True:
            self.parse_term()
            if self.stream.peek().type == "LBRACKET":
                self.stream.consume("LBRACKET")
                while True:
                    self.stream.consume("NUMBER")
                    if self.stream.peek().type == "COMMA":
                        self.stream.consume("COMMA")
                    else:
                        break
                self.stream.consume("RBRACKET")
            self.stream.consume("COLON")
            self.parse_term()
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break

    def parse_show(self) -> None:
        self.stream.consume("SHOW")
        self.parse_bot_or_formula()
        self.stream.consume("LBRACE")
        self.parse_block()
        self.stream.consume("RBRACE")

    def parse_assert(self) -> None:
        self.stream.consume("ASSERT")
        self.parse_formula()

    def parse_bot_or_formula(self) -> None:
        if self.stream.peek().type == "BOT":
            self.stream.consume("BOT")
        else:
            self.parse_formula()

    def parse_formula(self) -> None:
        return self.parse_implies()

    def parse_implies(self) -> None:
        self.parse_and()
        while self.stream.peek().type in ("IMPLIES", "IFF"):
            tok = self.stream.peek()
            self.stream.consume(tok.type)
            self.parse_and()

    def parse_and(self) -> None:
        self.parse_primary()
        while self.stream.peek().type in ("AND", "OR"):
            tok = self.stream.peek()
            self.stream.consume(tok.type)
            self.parse_primary()

    def parse_primary(self) -> None:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            self.stream.consume("IDENT", (PrimPred, DefPred, Equality, Axiom, Theorem, DefConExist, DefConUniq, DefFunExist, DefFunUniq))
            if self.stream.peek().type == "DOT":
                self.parse_access()
            if self.stream.peek().type == "LPAREN":
                self.stream.consume("LPAREN")
                self.parse_terms()
                self.stream.consume("RPAREN")

        elif tok.type == "LPAREN":
            self.stream.consume("LPAREN")
            self.parse_formula()
            self.stream.consume("RPAREN")

        elif tok.type == "NOT":
            self.stream.consume("NOT")
            self.stream.consume("LPAREN")
            self.parse_formula()
            self.stream.consume("RPAREN")

        elif tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"):
            while tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"):
                self.stream.consume(tok.type)
                if tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ"):
                    self.parse_var_or_struct_var()
                    tok = self.stream.peek()
                elif tok.type == "FORALL_PRED_TMPL":
                    self.parse_pred_tmpl()
                    tok = self.stream.peek()
                else:
                    self.parse_fun_tmpl()
                    tok = self.stream.peek()
            self.stream.consume("LPAREN")
            self.parse_formula()
            self.stream.consume("RPAREN")

        else:
            raise ExpectedTokenError(("IDENT", "LPAREN", "NOT", "FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"), (PrimPred, DefPred, Equality, Axiom, Theorem, DefConExist, DefConUniq, DefFunExist, DefFunUniq))

    def parse_terms_or_none(self) -> None:
        while True:
            if self.stream.peek().type == "UNDERSCORE":
                self.stream.consume("UNDERSCORE")
            else:
                self.parse_term()
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break

    def parse_terms(self) -> None:
        self.parse_term()
        while self.stream.peek().type == "COMMA":
            self.stream.consume("COMMA")
            self.parse_term()

    def parse_access(self) -> None:
        while True:
            self.stream.consume("DOT")
            self.stream.consume("IDENT")
            if self.stream.peek().type != "DOT":
                break

    def parse_term(self) -> None:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            self.stream.consume("IDENT", (PrimPred, DefPred, Equality, DefCon, DefFun, DefFunTerm))
            if self.stream.peek().type == "LPAREN":
                self.stream.consume("LPAREN")
                self.parse_terms()
                self.stream.consume("RPAREN")
            elif self.stream.peek().type == "DOT":
                return self.parse_access()
        elif tok.type == "LAMBDA_PRED":
            self.stream.consume("LAMBDA_PRED")
            if self.stream.peek().type != "DOT":
                self.parse_vars()
            self.stream.consume("DOT")
            self.parse_formula()
        elif tok.type == "LAMBDA_FUN":
            self.stream.consume("LAMBDA_FUN")
            if self.stream.peek().type != "DOT":
                self.parse_vars()
            self.stream.consume("DOT")
            self.parse_term()
        else:
            raise ExpectedTokenError(("IDENT", "LAMBDA_PRED", "LAMBDA_FUN"), (PrimPred, DefPred, Equality, DefCon, DefFun, DefFunTerm))

    def parse_tex(self) -> None:
        if self.stream.peek().type == "TEX":
            self.stream.consume("TEX")
            if self.stream.peek().type == "INFIX":
                self.stream.consume("INFIX")
                self.stream.consume("STRING")
            else:
                while True:
                    self.stream.consume("STRING")
                    if self.stream.peek().type == "COMMA":
                        self.stream.consume("COMMA")
                    else:
                        break

    def parse_vars_or_struct_vars(self) -> None:
        while True:
            self.parse_var_or_struct_var()
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break

    def parse_vars_or_struct_vars_or_pred_tmpls_or_fun_tmpls(self) -> None:
        while True:
            if self.stream.peek().type == "PREDICATE":
                self.stream.consume("PREDICATE")
                self.parse_pred_tmpl()
            elif self.stream.peek().type == "FUNCTION":
                self.stream.consume("FUNCTION")
                self.parse_fun_tmpl()
            else:
                self.parse_var_or_struct_var()
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break

    def parse_vars_or_pred_tmpls_or_fun_tmpls(self) -> None:
        while True:
            if self.stream.peek().type == "PREDICATE":
                self.stream.consume("PREDICATE")
                self.parse_pred_tmpl()
            elif self.stream.peek().type == "FUNCTION":
                self.stream.consume("FUNCTION")
                self.parse_fun_tmpl()
            else:
                self.parse_var()
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break

    def parse_vars(self) -> None:
        while True:
            self.parse_var()
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break

    def parse_var_or_struct_var(self) -> None:
        self.stream.consume("IDENT")
        if self.stream.peek().type == "COLON":
            self.stream.consume("COLON")
            self.stream.consume("IDENT")

    def parse_var(self) -> None:
        self.stream.consume("IDENT")

    def parse_pred_tmpl(self) -> None:
        self.stream.consume("IDENT")
        self.stream.consume("LBRACKET")
        int(self.stream.consume("NUMBER").value)
        self.stream.consume("RBRACKET")

    def parse_fun_tmpl(self) -> None:
        self.stream.consume("IDENT")
        self.stream.consume("LBRACKET")
        int(self.stream.consume("NUMBER").value)
        self.stream.consume("RBRACKET")

    def parse_refs_indexes(self) -> None:
        while True:
            self.stream.consume("IDENT", (DefPred, DefFunTerm))
            if self.stream.peek().type == "LBRACKET":
                self.stream.consume("LBRACKET")
                while True:
                    self.stream.consume("NUMBER")
                    if self.stream.peek().type == "COMMA":
                        self.stream.consume("COMMA")
                    else:
                        break
                self.stream.consume("RBRACKET")
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
