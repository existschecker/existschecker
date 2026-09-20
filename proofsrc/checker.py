from lexer import Token
from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, AtomicFormula, And, Or, Implies, Forall, Exists, Not, Bottom, Iff, Axiom, Invoke, Expand, PrimPred, DefPred, DefCon, Pad, Split, Connect, ExistsUniq, DefFun, DefFunTerm, Equality, Var, Substitute, Characterize, Show, Control, Formula, Declaration, Term, Assert, Fold, VarTerm, RefDefPred, InvalidDeclaration, InvalidControl, LexedUnit, RefFact, RefEquality, CheckError, ContextError, LogicError, FormatError, DeclarationContextNameSpace, Struct, StructPred, ElaboratedUnit, CheckedUnit, StructCon, ProofInfo, ProofStatus
from logic_utils import Substitutor, DefExpander, strip_forall_vars, strip_exists_vars, make_forall_vars, make_exists_vars, collect_vars, flatten_op, fresh_var, alpha_equiv_with_defs, alpha_safe_formula, beta_reduction_formula, mapping_adapter
from formatter import ExprFormatter
from lsprotocol import types as lsp
from pygls import uris
from decl_logic import make_formula_from_fact, DeclLogicError

def expr_in_context(expr: Bottom | Formula, context: Context, decl: DeclarationContextNameSpace) -> bool:
    return any(alpha_equiv_with_defs(expr, f, decl) for f in context.ctrl.formulas)

def goal_in_context(goal: Bottom | Formula, context: Context, decl: DeclarationContextNameSpace) -> bool:
    if isinstance(goal, AtomicFormula) and decl.get_equality() is not None and isinstance(goal.pred, RefEquality) and goal.args[0] == goal.args[1]:
        return True
    else:
        return expr_in_context(goal, context, decl)

def get_fact(fact: RefFact | Formula, node: Declaration | Control, decl: DeclarationContextNameSpace, expand_symbol: bool = False) -> Formula:
    if isinstance(fact, RefFact):
        fact = make_formula_from_fact(fact, decl)
    elif not isinstance(fact, Formula):
        msg = f"Expected Formula, got {type(fact)}"
        raise CheckError(node, msg)
    if expand_symbol and isinstance(fact, AtomicFormula) and isinstance(fact.pred, RefDefPred):
        fact = DefExpander([fact.pred], decl, {fact.pred: [1]}).expand_defs_formula(fact)
    return fact

def expand_if_atomic(formula: Formula, node: Declaration | Control, decl: DeclarationContextNameSpace) -> Formula:
    if isinstance(formula, AtomicFormula):
        if not isinstance(formula.pred, RefDefPred):
            msg = f"Expected RefDefPred, got {type(formula.pred)}"
            raise CheckError(node, msg)
        return DefExpander([formula.pred], decl).expand_defs_formula(formula)
    else:
        return formula

class Checker:
    def __init__(self, lexed_unit: LexedUnit, elaborated_unit: ElaboratedUnit, decl: DeclarationContextNameSpace) -> None:
        self.lexed_unit = lexed_unit
        self.elaborated_unit = elaborated_unit
        self.decl = decl

    def get_node_token(self, node: Declaration | Control) -> Token:
        return self.elaborated_unit.node_to_token[id(node)][0]

    def add_lsp_error(self, node: Declaration | Control, message: str):
        token = self.get_node_token(node)
        uri = uris.from_fs_path(token.file)
        if uri is None:
            return
        diag = lsp.Diagnostic(
            range=lsp.Range(
                start=lsp.Position(line=token.line - 1, character=token.column - 1),
                end=lsp.Position(line=token.end_line - 1, character=token.end_column - 1)
            ),
            message=message,
            source="Checker",
            severity=lsp.DiagnosticSeverity.Error
        )
        self.diagnostics.append(diag)

    def add_proofinfo(self, node: Declaration | Control, proofinfo: ProofInfo) -> None:
        self.proofinfo[id(node)] = proofinfo

    def check_unit(self) -> CheckedUnit:
        self.diagnostics: list[lsp.Diagnostic] = []
        self.proofinfo: dict[int, ProofInfo] = {}
        if isinstance(self.elaborated_unit.ast, Declaration):
            self.check_declaration(self.elaborated_unit.ast)
        return CheckedUnit(self.diagnostics, self.proofinfo)

    def check_declaration(self, node: Declaration) -> None:
        try:
            if isinstance(node, PrimPred):
                self.check_primpred(node)
            elif isinstance(node, Axiom):
                self.check_axiom(node)
            elif isinstance(node, Theorem):
                self.check_theorem(node)
            elif isinstance(node, DefPred):
                self.check_defpred(node)
            elif isinstance(node, DefCon):
                self.check_defcon(node)
            elif isinstance(node, DefFun):
                self.check_deffun(node)
            elif isinstance(node, DefFunTerm):
                self.check_deffunterm(node)
            elif isinstance(node, Equality):
                self.check_equality(node)
            elif isinstance(node, Struct):
                self.check_struct(node)
            elif isinstance(node, StructPred):
                self.check_struct_predicate(node)
            elif isinstance(node, StructCon):
                self.check_struct_constant(node)
            elif isinstance(node, InvalidDeclaration):
                self.add_lsp_error(node, "InvalidDeclaration")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED))
            else:
                self.add_lsp_error(node, f"Unsupported node {node}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED))
        except CheckError as e:
            self.add_lsp_error(e.node, e.msg)
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED))
        except (DeclLogicError, ContextError, LogicError, FormatError) as e:
            msg = f"{e.__class__.__name__}: {e.msg}"
            self.add_lsp_error(node, msg)
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED))

    def check_primpred(self, node: PrimPred) -> None:
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED))

    def check_axiom(self, node: Axiom) -> None:
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED))

    def check_theorem(self, node: Theorem) -> None:
        local_ctx = Context.init()
        for stmt in node.proof:
            local_ctx = self.check_control(stmt, local_ctx)
        if not goal_in_context(node.conclusion, local_ctx, self.decl):
            self.add_lsp_error(node, f"{node.name} not proved: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED))
            return
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED))

    def check_defpred(self, node: DefPred) -> None:
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED))

    def check_defcon(self, node: DefCon) -> None:
        existsuniq = self.decl.get_ast(Theorem, node.ref_theorem.name).conclusion
        if not isinstance(existsuniq, ExistsUniq):
            self.add_lsp_error(node, f"Not ExistsUniq object: {ExprFormatter(self.decl).pretty_expr(existsuniq)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED))
            return
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED))

    def check_deffun(self, node: DefFun) -> None:
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED))

    def check_deffunterm(self, node: DefFunTerm) -> None:
        fv, _, fpt, _, fft, _ = collect_vars(node.varterm)
        if set(node.args) != set(fv) | set(fpt) | set(fft):
            self.add_lsp_error(node, f"args are not matched with free vars: {set(fv) | set(fpt) | set(fft)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED))
            return
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED))

    def check_equality(self, node: Equality) -> None:
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED))

    def check_struct(self, node: Struct) -> None:
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED))

    def check_struct_predicate(self, node: StructPred) -> None:
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED))

    def check_struct_constant(self, node: StructCon) -> None:
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED))

    def check_control(self, node: Control, context: Context) -> Context:
        try:
            if isinstance(node, Any):
                context = self.check_any(node, context)
            elif isinstance(node, Assume):
                context = self.check_assume(node, context)
            elif isinstance(node, Divide):
                context = self.check_divide(node, context)
            elif isinstance(node, Some):
                context = self.check_some(node, context)
            elif isinstance(node, Deny):
                context = self.check_deny(node, context)
            elif isinstance(node, Case):
                context = self.check_case(node, context)
            elif isinstance(node, Contradict):
                context = self.check_contradict(node, context)
            elif isinstance(node, Explode):
                context = self.check_explode(node, context)
            elif isinstance(node, Apply):
                context = self.check_apply(node, context)
            elif isinstance(node, Lift):
                context = self.check_lift(node, context)
            elif isinstance(node, Characterize):
                context = self.check_characterize(node, context)
            elif isinstance(node, Invoke):
                context = self.check_invoke(node, context)
            elif isinstance(node, Expand):
                context = self.check_expand(node, context)
            elif isinstance(node, Fold):
                context = self.check_fold(node, context)
            elif isinstance(node, Pad):
                context = self.check_pad(node, context)
            elif isinstance(node, Split):
                context = self.check_split(node, context)
            elif isinstance(node, Connect):
                context = self.check_connect(node, context)
            elif isinstance(node, Substitute):
                context = self.check_substitute(node, context)
            elif isinstance(node, Show):
                context = self.check_show(node, context)
            elif isinstance(node, Assert):
                context = self.check_assert(node, context)
            elif isinstance(node, InvalidControl):
                self.add_lsp_error(node, "InvalidControl")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            else:
                self.add_lsp_error(node, f"Unsupported node {node}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        except CheckError as e:
            self.add_lsp_error(e.node, e.msg)
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        except (DeclLogicError, ContextError, LogicError, FormatError) as e:
            self.add_lsp_error(node, f"{e.__class__.__name__}: {e.msg}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context

    def check_any(self, node: Any, context: Context) -> Context:
        local_ctx = context.add_ctrl((), tuple(node.items))
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            self.add_lsp_error(node, "Local context must extend the parent context")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        local_goal = local_ctx.ctrl.formulas[-1]
        if isinstance(local_goal, Bottom):
            self.add_lsp_error(node, "Bottom cannot be generalized")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        goal = local_goal
        for item in reversed(node.items):
            goal = Forall(item, goal)
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (), (goal,), tuple(node.items), (), (local_goal,)))
        return context.add_ctrl((goal,), ())

    def check_assume(self, node: Assume, context: Context) -> Context:
        local_ctx = context.add_ctrl((node.premise,), ())
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            self.add_lsp_error(node, "Local context must extend the parent context")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        goal = local_ctx.ctrl.formulas[-1]
        if isinstance(goal, Bottom):
            self.add_lsp_error(node, "Bottom is not allowed as goal")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        implication = Implies(node.premise, goal)
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (), (implication,), (), (node.premise,), (goal,)))
        return context.add_ctrl((implication,), ())

    def check_divide(self, node: Divide, context: Context) -> Context:
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                self.add_lsp_error(node, f"Not fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
        fact = get_fact(node.fact, node, self.decl, True)
        connected_premise = Or(node.cases[0].premise, node.cases[1].premise)
        i = 2
        while i < len(node.cases):
            connected_premise = Or(connected_premise, node.cases[i].premise)
            i += 1
        if not alpha_equiv_with_defs(connected_premise, fact, self.decl):
            self.add_lsp_error(node, f"not matched: fact={ExprFormatter(self.decl).pretty_expr(fact)}, conected_premise={ExprFormatter(self.decl).pretty_expr(connected_premise)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        goals: list[Bottom | Formula] = []
        for stmt in node.cases:
            local_ctx = self.check_control(stmt, context)
            if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
                self.add_lsp_error(node, "Local context must extend the parent context")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            goal = local_ctx.ctrl.formulas[-1]
            goals.append(goal)
        for i in range(len(goals) - 1):
            if not alpha_equiv_with_defs(goals[i], goals[i + 1], self.decl):
                self.add_lsp_error(node, f"Not matched: goals[{i}]: {ExprFormatter(self.decl).pretty_expr(goals[i])}, goals[{i + 1}]: {ExprFormatter(self.decl).pretty_expr(goals[i + 1])}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact,), (goals[0],), (), (), (goals[0],)))
        return context.add_ctrl((goals[0],), ())

    def check_case(self, node: Case, context: Context) -> Context:
        local_ctx = context.add_ctrl((node.premise,), ())
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            self.add_lsp_error(node, "Local context must extend the parent context")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        goal = local_ctx.ctrl.formulas[-1]
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (), (goal,), (), (node.premise,), (goal,)))
        return context.add_ctrl((goal,), ())

    def check_some(self, node: Some, context: Context) -> Context:
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                self.add_lsp_error(node, f"not derivable: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
        fact = get_fact(node.fact, node, self.decl, True)
        if isinstance(fact, Exists):
            vars, body = strip_exists_vars(fact, Exists)
            body = make_exists_vars(body, Exists, [bound for bound, free in zip(vars, node.items) if free is None])
        elif isinstance(fact, ExistsUniq):
            vars, body= strip_exists_vars(fact, ExistsUniq)
            if len(vars) != 1:
                self.add_lsp_error(node, f"Unexpected len(vars): {len(vars)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
        else:
            self.add_lsp_error(node, f"Unexpected type: {type(fact)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        if len(vars) != len(node.items):
            self.add_lsp_error(node, f"len(vars): {len(vars)}, len(node.items): {len(node.items)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        mapping: dict[Term, Term] = {bound: free for bound, free in zip(vars, node.items) if free is not None}
        renamed_body = alpha_safe_formula(body, mapping)
        existence = beta_reduction_formula(Substitutor(mapping_adapter(mapping)).substitute_formula(renamed_body))
        if isinstance(fact, Exists):
            premises: tuple[Bottom | Formula, ...] = (existence,)
        else:
            fv, bv, fpt, bpt, fft, bft = collect_vars(existence)
            var = fresh_var(vars[0], fv | bv | fpt | bpt | fft | bft)
            body = beta_reduction_formula(Substitutor(({vars[0]: var}, {}, {})).substitute_formula(existence))
            equality = self.decl.get_equality()
            if equality is None:
                self.add_lsp_error(node, "equality has not been declared yet")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            uniqueness = Forall(var, Implies(body, AtomicFormula(RefEquality(equality.ref.name), (var, vars[0]))))
            premises: tuple[Bottom | Formula, ...] = (existence, uniqueness)
        local_vars = tuple(item for item in node.items if isinstance(item, Var))
        local_ctx = context.add_ctrl(premises, local_vars)
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            self.add_lsp_error(node, "Local context must extend the parent context")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        goal = local_ctx.ctrl.formulas[-1]
        if isinstance(goal, Formula):
            goal_fv, _, _, _, _, _ = collect_vars(goal)
            for fv in goal_fv:
                if fv in local_vars:
                    self.add_lsp_error(node, f"Conclusion depends on local variable {ExprFormatter(self.decl).pretty_expr(fv)}")
                    self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                    return context
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact,), (goal,), local_vars, premises, (goal,)))
        return context.add_ctrl((goal,), ())

    def check_deny(self, node: Deny, context: Context) -> Context:
        local_ctx = context.add_ctrl((node.premise,), ())
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            self.add_lsp_error(node, "Local context must extend the parent context")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        goal = local_ctx.ctrl.formulas[-1]
        if isinstance(goal, Bottom):
            if isinstance(node.premise, Not):
                conclusion = node.premise.body
            else:
                conclusion = Not(node.premise)
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (), (conclusion,), (), (node.premise,), (goal,)))
            return context.add_ctrl((conclusion,), ())
        else:
            self.add_lsp_error(node, "conradiction has not been deried")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context

    def check_contradict(self, node: Contradict, context: Context) -> Context:
        if not goal_in_context(node.contradiction, context, self.decl):
            self.add_lsp_error(node, f"Cannot derive {ExprFormatter(self.decl).pretty_expr(node.contradiction)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        if not goal_in_context(Not(node.contradiction), context, self.decl):
            self.add_lsp_error(node, f"Cannot derive {ExprFormatter(self.decl).pretty_expr(Not(node.contradiction))}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        conclusion = Bottom()
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.contradiction, Not(node.contradiction)), (conclusion,)))
        return context.add_ctrl((conclusion,), ())

    def check_explode(self, node: Explode, context: Context) -> Context:
        if goal_in_context(Bottom(), context, self.decl):
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (Bottom(),), (node.conclusion,)))
            return context.add_ctrl((node.conclusion,), ())
        else:
            self.add_lsp_error(node, "contradiction has not been derived")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context

    def check_apply(self, node: Apply, context: Context) -> Context:
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                self.add_lsp_error(node, f"Cannot derive fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
        fact = get_fact(node.fact, node, self.decl, True)
        items, body = strip_forall_vars(fact)
        if len(items) != len(node.terms):
            self.add_lsp_error(node, f"Formula has {len(items)} forall vars, but {len(node.terms)} terms are given")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        body = make_forall_vars(body, [item for item, term in zip(items, node.terms) if term is None])
        mapping: dict[Term, Term] = {}
        for item, term in zip(items, node.terms):
            if term is None:
                continue
            mapping[item] = term
        renamed_body = alpha_safe_formula(body, mapping)
        instantiation = beta_reduction_formula(Substitutor(mapping_adapter(mapping)).substitute_formula(renamed_body))
        if node.invoke == "none":
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact,), (instantiation,)))
            return context.add_ctrl((instantiation,), ())
        elif node.invoke == "invoke":
            if not isinstance(instantiation, Implies):
                self.add_lsp_error(node, "instantiation is not Implies object")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            if not goal_in_context(instantiation.left, context, self.decl):
                self.add_lsp_error(node, f"Left of instantiation is not derivable: {ExprFormatter(self.decl).pretty_expr(instantiation.left)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact, instantiation.left), (instantiation.right,)))
            return context.add_ctrl((instantiation.right,), ())
        elif node.invoke == "invoke-rightward":
            if not isinstance(instantiation, Iff):
                self.add_lsp_error(node, "instantiation is not Iff object")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            if not goal_in_context(instantiation.left, context, self.decl):
                self.add_lsp_error(node, f"Left of instantiation is not derivable: {ExprFormatter(self.decl).pretty_expr(instantiation.left)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact, instantiation.left), (instantiation.right,)))
            return context.add_ctrl((instantiation.right,), ())
        elif node.invoke == "invoke-leftward":
            if not isinstance(instantiation, Iff):
                self.add_lsp_error(node, "instantiation is not Iff object")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            if not goal_in_context(instantiation.right, context, self.decl):
                self.add_lsp_error(node, f"Right of instantiation is not derivable: {ExprFormatter(self.decl).pretty_expr(instantiation.right)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact, instantiation.right), (instantiation.left,)))
            return context.add_ctrl((instantiation.left,), ())
        else:
            self.add_lsp_error(node, f"Unexpected invoke option {node.invoke}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context

    def check_lift(self, node: Lift, context: Context) -> Context:
        conclusion = expand_if_atomic(node.conclusion, node, self.decl)
        if not isinstance(conclusion, Exists):
            self.add_lsp_error(node, f"Expected Exists, got {type(conclusion)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        items, body = strip_exists_vars(conclusion, Exists)
        if len(items) != len(node.varterms):
            self.add_lsp_error(node, f"Formula has {len(items)} exists vars, but {len(node.varterms)} terms are given")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        body = make_exists_vars(body, Exists, [item for item, term in zip(items, node.varterms) if term is None])
        mapping: dict[Term, Term] = {item: term for item, term in zip(items, node.varterms) if term is not None}
        renamed_body = alpha_safe_formula(body, mapping)
        fact = beta_reduction_formula(Substitutor(mapping_adapter(mapping)).substitute_formula(renamed_body))
        if not goal_in_context(fact, context, self.decl):
            self.add_lsp_error(node, f"Not fact: {ExprFormatter(self.decl).pretty_expr(fact)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (fact,), (node.conclusion,)))
        return context.add_ctrl((node.conclusion,), ())

    def check_characterize(self, node: Characterize, context: Context) -> Context:
        used_free_vars, used_bound_vars, used_free_pred_tmpls, used_bound_pred_tmpls, used_free_fun_tmpls, used_bound_fun_tmpls = collect_vars(node.conclusion.body)
        fv, bv, fpt, bpt, fft, bft = collect_vars(node.varterm)
        vardash = fresh_var(Var(node.conclusion.var.name + "'"), used_free_vars | used_bound_vars | used_free_pred_tmpls | used_bound_pred_tmpls | used_free_fun_tmpls | used_bound_fun_tmpls | fv | bv | fpt | bpt | fft | bft)
        renamed_conclusion = alpha_safe_formula(node.conclusion, {node.conclusion.var: node.varterm})
        if not isinstance(renamed_conclusion, ExistsUniq):
            self.add_lsp_error(node, f"renamed_conclusion is not ExistsUniq object: {ExprFormatter(self.decl).pretty_expr(renamed_conclusion)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        existence = beta_reduction_formula(Substitutor(({renamed_conclusion.var: node.varterm}, {}, {})).substitute_formula(renamed_conclusion.body))
        existence_dash = beta_reduction_formula(Substitutor(({renamed_conclusion.var: vardash}, {}, {})).substitute_formula(renamed_conclusion.body))
        equality = self.decl.get_equality()
        if equality is None:
            self.add_lsp_error(node, "equality has not been declared yet")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        fact = And(existence, Forall(vardash, Implies(existence_dash, AtomicFormula(RefEquality(equality.ref.name), (vardash, node.varterm)))))
        if not goal_in_context(fact, context, self.decl):
            self.add_lsp_error(node, f"Not fact: {ExprFormatter(self.decl).pretty_expr(fact)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (fact,), (node.conclusion,)))
        return context.add_ctrl((node.conclusion,), ())

    def check_invoke(self, node: Invoke, context: Context) -> Context:
        if not goal_in_context(node.fact, context, self.decl):
            self.add_lsp_error(node, f"Not fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        if node.direction == "none":
            if not isinstance(node.fact, Implies):
                self.add_lsp_error(node, f"Not Implies object: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            if not goal_in_context(node.fact.left, context, self.decl):
                self.add_lsp_error(node, f"Left of Implies object not derived: {ExprFormatter(self.decl).pretty_expr(node.fact.left)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact, node.fact.left), (node.fact.right,)))
            return context.add_ctrl((node.fact.right,), ())
        elif node.direction == "rightward":
            if not isinstance(node.fact, Iff):
                self.add_lsp_error(node, f"Not Iff object: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            if not goal_in_context(node.fact.left, context, self.decl):
                self.add_lsp_error(node, f"Left of Iff object not derived: {ExprFormatter(self.decl).pretty_expr(node.fact.left)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact, node.fact.left), (node.fact.right,)))
            return context.add_ctrl((node.fact.right,), ())
        elif node.direction == "leftward":
            if not isinstance(node.fact, Iff):
                self.add_lsp_error(node, f"Not Iff object: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            if not goal_in_context(node.fact.right, context, self.decl):
                self.add_lsp_error(node, f"Right of Iff object not derived: {ExprFormatter(self.decl).pretty_expr(node.fact.right)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact, node.fact.right), (node.fact.left,)))
            return context.add_ctrl((node.fact.left,), ())
        else:
            self.add_lsp_error(node, f"Unexpected direction: {node.direction}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context

    def check_expand(self, node: Expand, context: Context) -> Context:
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                self.add_lsp_error(node, f"Not fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
        fact = get_fact(node.fact, node, self.decl)
        conclusion = DefExpander(node.refs, self.decl, node.indexes).expand_defs_formula(fact)
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact,), (conclusion,)))
        return context.add_ctrl((conclusion,), ())

    def check_fold(self, node: Fold, context: Context) -> Context:
        fact = DefExpander(node.refs, self.decl, node.indexes).expand_defs_formula(node.conclusion)
        if not goal_in_context(fact, context, self.decl):
            self.add_lsp_error(node, f"Not fact: {ExprFormatter(self.decl).pretty_expr(fact)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (fact,), (node.conclusion,)))
        return context.add_ctrl((node.conclusion,), ())

    def check_pad(self, node: Pad, context: Context) -> Context:
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                self.add_lsp_error(node, f"Not derivable: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
        fact = get_fact(node.fact, node, self.decl)
        fact_parts = flatten_op(fact, Or)
        conclusion = expand_if_atomic(node.conclusion, node, self.decl)
        if not isinstance(conclusion, Or):
            self.add_lsp_error(node, f"Expected Or, got {type(conclusion)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        conclusion_parts = flatten_op(conclusion, Or)
        if not all(any(alpha_equiv_with_defs(c, f, self.decl) for c in conclusion_parts) for f in fact_parts):
            self.add_lsp_error(node, f"neither left or right not derivable: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact,), (node.conclusion,)))
        return context.add_ctrl((node.conclusion,), ())

    def check_split(self, node: Split, context: Context) -> Context:
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                self.add_lsp_error(node, f"Not derivable: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
        fact = get_fact(node.fact, node, self.decl, True)
        if isinstance(fact, And):
            fact_parts = flatten_op(fact, And)
            if node.index is None:
                self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact,), tuple(fact_parts)))
                return context.add_ctrl(tuple(fact_parts), ())
            else:
                if node.index <= 0 or node.index > len(fact_parts):
                    self.add_lsp_error(node, f"index out of range, index: {node.index}, len(fact_parts): {len(fact_parts)}")
                    self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                    return context
                f = fact_parts[node.index - 1]
                self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact,), (f,)))
                return context.add_ctrl((f,), ())
        elif isinstance(fact, Iff):
            implication_rightward = Implies(fact.left, fact.right)
            implication_leftward = Implies(fact.right, fact.left)
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact,), (implication_rightward, implication_leftward)))
            return context.add_ctrl((implication_rightward, implication_leftward), ())
        else:
            self.add_lsp_error(node, f"Not And or Iff object: {ExprFormatter(self.decl).pretty_expr(fact)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context

    def check_connect(self, node: Connect, context: Context) -> Context:
        conclusion = expand_if_atomic(node.conclusion, node, self.decl)
        if isinstance(conclusion, And):
            conclusion_parts = flatten_op(conclusion, And)
            for c in conclusion_parts:
                if not goal_in_context(c, context, self.decl):
                    self.add_lsp_error(node, f"Not derivable: {ExprFormatter(self.decl).pretty_expr(c)}")
                    self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                    return context
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, tuple(conclusion_parts), (node.conclusion,)))
            return context.add_ctrl((node.conclusion,), ())
        elif isinstance(conclusion, Iff):
            implication_rightward = Implies(conclusion.left, conclusion.right)
            if not goal_in_context(implication_rightward, context, self.decl):
                self.add_lsp_error(node, f"Not derivable: {ExprFormatter(self.decl).pretty_expr(implication_rightward)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            implication_leftward = Implies(conclusion.right, conclusion.left)
            if not goal_in_context(implication_leftward, context, self.decl):
                self.add_lsp_error(node, f"Not derivable: {ExprFormatter(self.decl).pretty_expr(implication_leftward)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (implication_rightward, implication_leftward), (node.conclusion,)))
            return context.add_ctrl((node.conclusion,), ())
        else:
            self.add_lsp_error(node, f"Not And or Iff object: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context

    def check_substitute(self, node: Substitute, context: Context) -> Context:
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                self.add_lsp_error(node, f"Not fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
        fact = get_fact(node.fact, node, self.decl)
        equality = self.decl.get_equality()
        if equality is None:
            self.add_lsp_error(node, "equality has not been declared yet")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        premises_equal: list[AtomicFormula] = []
        for k, v in node.env.items():
            if not isinstance(k, VarTerm):
                self.add_lsp_error(node, f"Expected VarTerm, got {type(k)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            if not isinstance(v, VarTerm):
                self.add_lsp_error(node, f"Expected VarTerm, got {type(v)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            equation = AtomicFormula(RefEquality(equality.ref.name), (k, v))
            if not goal_in_context(equation, context, self.decl):
                self.add_lsp_error(node, f"Not fact: {ExprFormatter(self.decl).pretty_expr(equation)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
            premises_equal.append(equation)
        renamed_fact = alpha_safe_formula(fact, node.env)
        conclusion = beta_reduction_formula(Substitutor(mapping_adapter(node.env), node.indexes).substitute_formula(renamed_fact))
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (node.fact,) + tuple(premises_equal), (conclusion,)))
        return context.add_ctrl((conclusion,), ())

    def check_show(self, node: Show, context: Context) -> Context:
        local_ctx = context
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            self.add_lsp_error(node, "Local context must extend the parent context")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        goal = local_ctx.ctrl.formulas[-1]
        if not alpha_equiv_with_defs(node.conclusion, goal, self.decl):
            self.add_lsp_error(node, f"Not matched with target conclusion: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
            self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
            return context
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (), (goal,), (), (), (goal,)))
        return context.add_ctrl((goal,), ())

    def check_assert(self, node: Assert, context: Context) -> Context:
        if isinstance(node.reference, (Bottom, Formula)):
            if not goal_in_context(node.reference, context, self.decl):
                self.add_lsp_error(node, f"Not fact: {ExprFormatter(self.decl).pretty_expr(node.reference)}")
                self.add_proofinfo(node, ProofInfo(ProofStatus.FAILED, context.ctrl))
                return context
        formula = get_fact(node.reference, node, self.decl)
        self.add_proofinfo(node, ProofInfo(ProofStatus.PASSED, context.ctrl, (), (formula,)))
        return context.add_ctrl((formula,), ())
