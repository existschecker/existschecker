from lexer import Token
from ast_types import PrimPred, DefPred, Equality, DefCon, DefFun, DefFunTerm, Axiom, Theorem, DefConExist, DefConUniq, DefFunExist, DefFunUniq
from dataclasses import dataclass

@dataclass(frozen=True)
class AccessState:
    names: tuple[str, ...]

@dataclass(frozen=True)
class CallState:
    callee: AccessState
    argindex: int

@dataclass(frozen=True)
class CompletionVar:
    name: str

@dataclass(frozen=True)
class CompletionTypedVar:
    name: str
    type_name: str

@dataclass(frozen=True)
class CompletionPredTemplate:
    name: str
    arity: int

@dataclass(frozen=True)
class CompletionFunTemplate:
    name: str
    arity: int

@dataclass(frozen=True)
class CompletionContext:
    ctrl: tuple[CompletionVar | CompletionTypedVar | CompletionPredTemplate | CompletionFunTemplate, ...]
    form: tuple[CompletionVar | CompletionTypedVar | CompletionPredTemplate | CompletionFunTemplate, ...]

    @staticmethod
    def init() -> "CompletionContext":
        return CompletionContext((), ())

    def add_ctrl(self, items: tuple[CompletionVar | CompletionTypedVar | CompletionPredTemplate | CompletionFunTemplate, ...]) -> "CompletionContext":
        return CompletionContext(self.ctrl + items, self.form)

    def add_form(self, items: tuple[CompletionVar | CompletionTypedVar | CompletionPredTemplate | CompletionFunTemplate, ...]) -> "CompletionContext":
        return CompletionContext(self.ctrl, self.form + items)

class ExpectedTokenError(Exception):
    def __init__(self, expected_types: tuple[str, ...], decl_types: tuple[type, ...] | None = None, call: CallState | None = None, context: CompletionContext | None = None, access: AccessState | None = None) -> None:
        self.expected_types = expected_types
        if decl_types is None:
            decl_types = ()
        self.decl_types = decl_types
        self.call = call
        self.context = context
        self.access = access

class CompletionTokenStream:
    def __init__(self, tokens: list[Token]):
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> Token:
        if self.pos >= len(self.tokens):
            raise Exception("Unexpected end of input")
        return self.tokens[self.pos]

    def consume(self, expected_type: str) -> Token:
        tok = self.peek()
        if tok.type != expected_type:
            raise ExpectedTokenError((expected_type,))
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
        self.parse_formula(CompletionContext.init())

    def parse_theorem(self) -> None:
        self.stream.consume("THEOREM")
        self.stream.consume("IDENT")
        self.parse_formula(CompletionContext.init())
        self.stream.consume("LBRACE")
        self.parse_block(CompletionContext.init())
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
            raise ExpectedTokenError(("PREDICATE", "CONSTANT", "FUNCTION"))

    def parse_defpred(self) -> None:
        self.stream.consume("PREDICATE")
        if self.stream.peek().type == "AUTOEXPAND":
            self.stream.consume("AUTOEXPAND")
        self.stream.consume("IDENT")
        self.stream.consume("LPAREN")
        context = CompletionContext.init()
        items = self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        local_ctx = context.add_ctrl(items)
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        self.parse_formula(local_ctx)
        self.parse_tex()

    def parse_defcon(self) -> None:
        self.stream.consume("CONSTANT")
        self.stream.consume("IDENT")
        self.stream.consume("BY")
        if self.stream.peek().type == "IDENT":
            self.stream.consume("IDENT")
        else:
            raise ExpectedTokenError(("IDENT",), (Theorem,))
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
        if self.stream.peek().type == "IDENT":
            self.stream.consume("IDENT")
        else:
            raise ExpectedTokenError(("IDENT",), (Theorem,))
        self.parse_tex()

    def parse_deffunterm(self) -> None:
        self.stream.consume("LPAREN")
        context = CompletionContext.init()
        items = self.parse_vars_or_pred_tmpls_or_fun_tmpls()
        local_ctx = context.add_ctrl(items)
        self.stream.consume("RPAREN")
        self.stream.consume("AS")
        self.parse_term(local_ctx)
        self.parse_tex()

    def parse_existence(self) -> None:
        self.stream.consume("EXISTENCE")
        self.stream.consume("IDENT")
        self.parse_formula(CompletionContext.init())
        self.stream.consume("BY")
        if self.stream.peek().type == "IDENT":
            self.stream.consume("IDENT")
        else:
            raise ExpectedTokenError(("IDENT",), (DefCon, DefFun))

    def parse_uniqueness(self) -> None:
        self.stream.consume("UNIQUENESS")
        self.stream.consume("IDENT")
        self.parse_formula(CompletionContext.init())
        self.stream.consume("BY")
        if self.stream.peek().type == "IDENT":
            self.stream.consume("IDENT")
        else:
            raise ExpectedTokenError(("IDENT",), (DefCon, DefFun))

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
            self.parse_formula(CompletionContext.init())
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
        self.parse_formula(CompletionContext.init())

    def parse_include(self) -> None:
        self.stream.consume("INCLUDE")
        self.stream.consume("STRING")

    def parse_block(self, context: CompletionContext) -> None:
        while True:
            tok = self.stream.peek()
            if not tok or tok.type == "RBRACE":
                break
            else:
                try:
                    self.parse_control(tok, context)
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

    def parse_control(self, tok: Token, context: CompletionContext) -> None:
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
            raise ExpectedTokenError(("ANY", "ASSUME", "DIVIDE", "SOME", "DENY", "CONTRADICT", "EXPLODE", "APPLY", "LIFT", "CHARACTERIZE", "INVOKE", "EXPAND", "FOLD", "PAD", "SPLIT", "CONNECT", "SUBSTITUTE", "SHOW", "ASSERT"))

    def parse_any(self, context: CompletionContext) -> None:
        self.stream.consume("ANY")
        items = self.parse_vars_or_struct_vars_or_pred_tmpls_or_fun_tmpls()
        local_ctx = context.add_ctrl(items)
        self.stream.consume("LBRACE")
        self.parse_block(local_ctx)
        self.stream.consume("RBRACE")

    def parse_assume(self, context: CompletionContext) -> None:
        self.stream.consume("ASSUME")
        self.parse_formula(context)
        self.stream.consume("LBRACE")
        self.parse_block(context)
        self.stream.consume("RBRACE")

    def parse_divide(self, context: CompletionContext) -> None:
        self.stream.consume("DIVIDE")
        self.parse_formula(context)
        while self.stream.peek().type == "CASE":
            self.parse_case(context)

    def parse_case(self, context: CompletionContext) -> None:
        self.stream.consume("CASE")
        self.parse_formula(context)
        self.stream.consume("LBRACE")
        self.parse_block(context)
        self.stream.consume("RBRACE")

    def parse_some(self, context: CompletionContext) -> None:
        self.stream.consume("SOME")
        items: list[CompletionVar] = []
        while True:
            if self.stream.peek().type == "UNDERSCORE":
                self.stream.consume("UNDERSCORE")
            else:
                items.append(self.parse_var())
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        local_ctx = context.add_ctrl(tuple(items))
        self.stream.consume("SUCH")
        self.parse_formula(local_ctx)
        self.stream.consume("LBRACE")
        self.parse_block(local_ctx)
        self.stream.consume("RBRACE")

    def parse_deny(self, context: CompletionContext) -> None:
        self.stream.consume("DENY")
        self.parse_formula(context)
        self.stream.consume("LBRACE")
        self.parse_block(context)
        self.stream.consume("RBRACE")

    def parse_contradict(self, context: CompletionContext) -> None:
        self.stream.consume("CONTRADICT")
        self.parse_formula(context)

    def parse_explode(self, context: CompletionContext) -> None:
        self.stream.consume("EXPLODE")
        self.parse_formula(context)

    def parse_apply(self, context: CompletionContext) -> None:
        self.stream.consume("APPLY")
        if self.stream.peek().type == "INVOKE":
            self.stream.consume("INVOKE")
            if self.stream.peek().type == "RIGHTWARD":
                self.stream.consume("RIGHTWARD")
            elif self.stream.peek().type == "LEFTWARD":
                self.stream.consume("LEFTWARD")
        self.parse_formula(context)
        self.stream.consume("FOR")
        self.parse_terms_or_none(context)

    def parse_lift(self, context: CompletionContext) -> None:
        self.stream.consume("LIFT")
        self.stream.consume("FOR")
        self.parse_terms_or_none(context)
        self.stream.consume("CONCLUDE")
        self.parse_formula(context)

    def parse_characterize(self, context: CompletionContext) -> None:
        self.stream.consume("CHARACTERIZE")
        self.stream.consume("FOR")
        self.parse_term(context)
        self.stream.consume("CONCLUDE")
        self.parse_formula(context)

    def parse_invoke(self, context: CompletionContext) -> None:
        self.stream.consume("INVOKE")
        if self.stream.peek().type == "RIGHTWARD":
            self.stream.consume("RIGHTWARD")
        elif self.stream.peek().type == "LEFTWARD":
            self.stream.consume("LEFTWARD")
        self.parse_formula(context)

    def parse_expand(self, context: CompletionContext) -> None:
        self.stream.consume("EXPAND")
        self.parse_formula(context)
        self.stream.consume("FOR")
        self.parse_refs_indexes()

    def parse_fold(self, context: CompletionContext) -> None:
        self.stream.consume("FOLD")
        self.stream.consume("FOR")
        self.parse_refs_indexes()
        self.stream.consume("CONCLUDE")
        self.parse_formula(context)

    def parse_pad(self, context: CompletionContext) -> None:
        self.stream.consume("PAD")
        self.parse_formula(context)
        self.stream.consume("CONCLUDE")
        self.parse_formula(context)

    def parse_split(self, context: CompletionContext) -> None:
        self.stream.consume("SPLIT")
        if self.stream.peek().type == "NUMBER":
            self.stream.consume("NUMBER")
        self.parse_formula(context)

    def parse_connect(self, context: CompletionContext) -> None:
        self.stream.consume("CONNECT")
        self.parse_formula(context)

    def parse_substitute(self, context: CompletionContext) -> None:
        self.stream.consume("SUBSTITUTE")
        self.parse_formula(context)
        self.stream.consume("FOR")
        while True:
            self.parse_term(context)
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
            self.parse_term(context)
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break

    def parse_show(self, context: CompletionContext) -> None:
        self.stream.consume("SHOW")
        self.parse_bot_or_formula(context)
        self.stream.consume("LBRACE")
        self.parse_block(context)
        self.stream.consume("RBRACE")

    def parse_assert(self, context: CompletionContext) -> None:
        self.stream.consume("ASSERT")
        self.parse_formula(context)

    def parse_bot_or_formula(self, context: CompletionContext) -> None:
        if self.stream.peek().type == "BOT":
            self.stream.consume("BOT")
        else:
            self.parse_formula(context)

    def parse_formula(self, context: CompletionContext, call: CallState | None = None) -> None:
        return self.parse_implies(context, call)

    def parse_implies(self, context: CompletionContext, call: CallState | None) -> None:
        self.parse_and(context, call)
        while self.stream.peek().type in ("IMPLIES", "IFF"):
            tok = self.stream.peek()
            self.stream.consume(tok.type)
            self.parse_and(context, call)

    def parse_and(self, context: CompletionContext, call: CallState | None) -> None:
        self.parse_primary(context, call)
        while self.stream.peek().type in ("AND", "OR"):
            tok = self.stream.peek()
            self.stream.consume(tok.type)
            self.parse_primary(context, call)

    def parse_primary(self, context: CompletionContext, call: CallState | None) -> None:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            parent = self.stream.consume("IDENT").value
            access = AccessState((parent,))
            if self.stream.peek().type == "DOT":
                access = self.parse_access(access, context, call)
            if self.stream.peek().type == "LPAREN":
                self.stream.consume("LPAREN")
                local_call = CallState(access, 0)
                self.parse_terms(context, local_call)
                self.stream.consume("RPAREN")

        elif tok.type == "LPAREN":
            self.stream.consume("LPAREN")
            self.parse_formula(context, call)
            self.stream.consume("RPAREN")

        elif tok.type == "NOT":
            self.stream.consume("NOT")
            self.stream.consume("LPAREN")
            self.parse_formula(context, call)
            self.stream.consume("RPAREN")

        elif tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"):
            items: list[CompletionVar | CompletionTypedVar | CompletionPredTemplate | CompletionFunTemplate] = []
            while tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"):
                self.stream.consume(tok.type)
                if tok.type in ("FORALL", "EXISTS", "EXISTS_UNIQ"):
                    items.append(self.parse_var_or_struct_var())
                    tok = self.stream.peek()
                elif tok.type == "FORALL_PRED_TMPL":
                    items.append(self.parse_pred_tmpl())
                    tok = self.stream.peek()
                else:
                    items.append(self.parse_fun_tmpl())
                    tok = self.stream.peek()
            local_ctx = context.add_form(tuple(items))
            self.stream.consume("LPAREN")
            self.parse_formula(local_ctx, call)
            self.stream.consume("RPAREN")

        else:
            raise ExpectedTokenError(("IDENT", "LPAREN", "NOT", "FORALL", "EXISTS", "EXISTS_UNIQ", "FORALL_PRED_TMPL", "FORALL_FUN_TMPL"), (PrimPred, DefPred, Equality, Axiom, Theorem, DefConExist, DefConUniq, DefFunExist, DefFunUniq), None, context)

    def parse_terms_or_none(self, context: CompletionContext) -> None:
        while True:
            if self.stream.peek().type == "UNDERSCORE":
                self.stream.consume("UNDERSCORE")
            else:
                self.parse_term(context)
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break

    def parse_terms(self, context: CompletionContext, call: CallState) -> None:
        self.parse_term(context, call)
        while self.stream.peek().type == "COMMA":
            self.stream.consume("COMMA")
            call = CallState(call.callee, call.argindex + 1)
            self.parse_term(context, call)

    def parse_access(self, access: AccessState, context: CompletionContext, call: CallState | None) -> AccessState:
        while True:
            self.stream.consume("DOT")
            if self.stream.peek().type == "IDENT":
                child = self.stream.consume("IDENT").value
            else:
                raise ExpectedTokenError(("IDENT",), None, call, context, access)
            access = AccessState(access.names + (child,))
            if self.stream.peek().type != "DOT":
                break
        return access

    def parse_term(self, context: CompletionContext, call: CallState | None = None) -> None:
        tok = self.stream.peek()
        if tok.type == "IDENT":
            parent = self.stream.consume("IDENT").value
            access = AccessState((parent,))
            if self.stream.peek().type == "LPAREN":
                self.stream.consume("LPAREN")
                local_call = CallState(access, 0)
                self.parse_terms(context, local_call)
                self.stream.consume("RPAREN")
            elif self.stream.peek().type == "DOT":
                self.parse_access(access, context, call)
        elif tok.type == "LAMBDA_PRED":
            self.stream.consume("LAMBDA_PRED")
            if self.stream.peek().type != "DOT":
                vars = self.parse_vars()
            else:
                vars = ()
            local_ctx = context.add_form(vars)
            self.stream.consume("DOT")
            self.parse_formula(local_ctx, call)
        elif tok.type == "LAMBDA_FUN":
            self.stream.consume("LAMBDA_FUN")
            if self.stream.peek().type != "DOT":
                vars = self.parse_vars()
            else:
                vars = ()
            local_ctx = context.add_form(vars)
            self.stream.consume("DOT")
            self.parse_term(local_ctx, call)
        else:
            raise ExpectedTokenError(("IDENT", "LAMBDA_PRED", "LAMBDA_FUN"), (PrimPred, DefPred, Equality, DefCon, DefFun, DefFunTerm), call, context)

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

    def parse_vars_or_struct_vars_or_pred_tmpls_or_fun_tmpls(self) -> tuple[CompletionVar | CompletionTypedVar | CompletionPredTemplate | CompletionFunTemplate, ...]:
        items: list[CompletionVar | CompletionTypedVar | CompletionPredTemplate | CompletionFunTemplate] = []
        while True:
            if self.stream.peek().type == "PREDICATE":
                self.stream.consume("PREDICATE")
                items.append(self.parse_pred_tmpl())
            elif self.stream.peek().type == "FUNCTION":
                self.stream.consume("FUNCTION")
                items.append(self.parse_fun_tmpl())
            else:
                items.append(self.parse_var_or_struct_var())
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return tuple(items)

    def parse_vars_or_pred_tmpls_or_fun_tmpls(self) -> tuple[CompletionVar | CompletionPredTemplate | CompletionFunTemplate, ...]:
        items: list[CompletionVar | CompletionPredTemplate | CompletionFunTemplate] = []
        while True:
            if self.stream.peek().type == "PREDICATE":
                self.stream.consume("PREDICATE")
                items.append(self.parse_pred_tmpl())
            elif self.stream.peek().type == "FUNCTION":
                self.stream.consume("FUNCTION")
                items.append(self.parse_fun_tmpl())
            else:
                items.append(self.parse_var())
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return tuple(items)

    def parse_vars(self) -> tuple[CompletionVar, ...]:
        vars: list[CompletionVar] = []
        while True:
            vars.append(self.parse_var())
            if self.stream.peek().type == "COMMA":
                self.stream.consume("COMMA")
            else:
                break
        return tuple(vars)

    def parse_var_or_struct_var(self) -> CompletionVar | CompletionTypedVar:
        var_name = self.stream.consume("IDENT").value
        if self.stream.peek().type == "COLON":
            self.stream.consume("COLON")
            type_name = self.stream.consume("IDENT").value
            return CompletionTypedVar(var_name, type_name)
        else:
            return CompletionVar(var_name)

    def parse_var(self) -> CompletionVar:
        name = self.stream.consume("IDENT").value
        return CompletionVar(name)

    def parse_pred_tmpl(self) -> CompletionPredTemplate:
        name = self.stream.consume("IDENT").value
        self.stream.consume("LBRACKET")
        arity = int(self.stream.consume("NUMBER").value)
        self.stream.consume("RBRACKET")
        return CompletionPredTemplate(name, arity)

    def parse_fun_tmpl(self) -> CompletionFunTemplate:
        name = self.stream.consume("IDENT").value
        self.stream.consume("LBRACKET")
        arity = int(self.stream.consume("NUMBER").value)
        self.stream.consume("RBRACKET")
        return CompletionFunTemplate(name, arity)

    def parse_refs_indexes(self) -> None:
        while True:
            if self.stream.peek().type == "IDENT":
                self.stream.consume("IDENT")
            else:
                raise ExpectedTokenError(("IDENT",), (DefPred, DefFunTerm))
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
