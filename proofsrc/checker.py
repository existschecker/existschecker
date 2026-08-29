from lexer import Token
from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, AtomicFormula, And, Or, Implies, Forall, Exists, Not, Bottom, Iff, Axiom, Invoke, Expand, PrimPred, DefPred, DefCon, Pad, Split, Connect, ExistsUniq, Compound, RefDefCon, DefFun, DefFunTerm, Equality, Var, Substitute, Characterize, Show, Control, Formula, Declaration, PredTemplate, Term, DefConExist, DefConUniq, DefFunExist, DefFunUniq, Include, Assert, Fold, VarTerm, FunTemplate, RefDefPred, RefDefFun, InvalidDeclaration, InvalidControl, InvalidInclude, DeclarationUnit, RefFact, RefEquality, CheckError, ContextError, LogicError, FormatError, DeclarationContextNameSpace, Struct, StructPred
from logic_utils import Substitutor, DefExpander, expr_in_context, strip_forall_vars, strip_exists_vars, make_forall_vars, make_exists_vars, collect_vars, flatten_op, fresh_var, alpha_equiv_with_defs, alpha_safe_formula
from formatter import ExprFormatter
from copy import deepcopy
from lsprotocol import types as lsp
from pygls import uris

import logging
logger = logging.getLogger("proof")

def goal_in_context(goal: Bottom | Formula, context: Context, decl: DeclarationContextNameSpace) -> bool:
    if isinstance(goal, AtomicFormula) and decl.get_equality() is not None and isinstance(goal.pred, RefEquality) and goal.args[0] == goal.args[1]:
        return True
    else:
        return expr_in_context(goal, context, decl)

def get_fact(fact: RefFact | Formula, context: Context, node: Declaration | Control, decl: DeclarationContextNameSpace, expand_symbol: bool = False) -> Formula:
    if isinstance(fact, RefFact):
        fact = decl.get_fact(fact)
    elif not isinstance(fact, Formula):
        msg = f"Expected Formula, got {type(fact)}"
        raise CheckError(node, msg)
    if expand_symbol and isinstance(fact, AtomicFormula) and isinstance(fact.pred, RefDefPred):
        fact = DefExpander([fact.pred], decl, {fact.pred: [1]}).expand_defs_formula(fact, context)
    return fact

def expand_if_atomic(formula: Formula, context: Context, node: Declaration | Control, decl: DeclarationContextNameSpace) -> Formula:
    if isinstance(formula, AtomicFormula):
        if not isinstance(formula.pred, RefDefPred):
            msg = f"Expected RefDefPred, got {type(formula.pred)}"
            raise CheckError(node, msg)
        return DefExpander([formula.pred], decl).expand_defs_formula(formula, context)
    else:
        return formula

def make_debug_prefix(node: Declaration | Control, indent: int) -> str:
    return "  " * indent + f"[{node.__class__.__name__}] "

class Checker:
    def __init__(self, unit: DeclarationUnit, decl: DeclarationContextNameSpace) -> None:
        self.unit = unit
        self.decl = decl

    def make_error_prefix(self, node: Declaration | Control, indent: int) -> str:
        return "  " * indent + f"❌ [{node.__class__.__name__}] {self.unit.get_node_token(node).info()} "

    def add_lsp_error(self, token: Token, message: str):
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
        self.unit.diagnostics.append(diag)

    def check_unit(self) -> bool:
        ast = self.unit.ast
        if isinstance(ast, Include):
            return not isinstance(ast, InvalidInclude)
        elif isinstance(ast, Declaration):
            return self.check_declaration(ast)
        else:
            return False

    def check_declaration(self, node: Declaration, indent: int = 0) -> bool:
        try:
            if isinstance(node, PrimPred):
                self.check_primpred(node, indent)
            elif isinstance(node, Axiom):
                self.check_axiom(node, indent)
            elif isinstance(node, Theorem):
                self.check_theorem(node, indent)
            elif isinstance(node, DefPred):
                self.check_defpred(node, indent)
            elif isinstance(node, DefCon):
                self.check_defcon(node, indent)
            elif isinstance(node, DefConExist):
                self.check_defconexist(node, indent)
            elif isinstance(node, DefConUniq):
                self.check_defconuniq(node, indent)
            elif isinstance(node, DefFun):
                self.check_deffun(node, indent)
            elif isinstance(node, DefFunExist):
                self.check_deffunexist(node, indent)
            elif isinstance(node, DefFunUniq):
                self.check_deffununiq(node, indent)
            elif isinstance(node, DefFunTerm):
                self.check_deffunterm(node, indent)
            elif isinstance(node, Equality):
                self.check_equality(node, indent)
            elif isinstance(node, Struct):
                self.check_struct(node, indent)
            elif isinstance(node, StructPred):
                self.check_struct_predicate(node, indent)
            elif isinstance(node, InvalidDeclaration):
                msg = "InvalidDeclaration"
                raise CheckError(node, msg)
            else:
                msg = f"Unsupported node {node}"
                raise CheckError(node, msg)
            node.proofinfo.status = "✅Passed"
            return True
        except CheckError as e:
            self.add_lsp_error(self.unit.get_node_token(e.node), e.msg)
            logger.debug(f"{self.make_error_prefix(node, indent)}{e.msg}")
            node.proofinfo.status = "❌Failed"
            return False
        except (ContextError, LogicError, FormatError) as e:
            msg = f"{e.__class__.__name__}: {e.msg}"
            self.add_lsp_error(self.unit.get_node_token(node), msg)
            logger.debug(f"{self.make_error_prefix(node, indent)}{msg}")
            node.proofinfo.status = "❌Failed"
            return False

    def check_primpred(self, node: PrimPred, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, arity: {node.arity}")
        self.decl.add(self.unit.file, node)

    def check_axiom(self, node: Axiom, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, conclusion: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
        self.decl.add(self.unit.file, node)

    def check_theorem(self, node: Theorem, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}{node.name}: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
        local_ctx = Context.init()
        for stmt in node.proof:
            local_ctx = self.check_control(stmt, local_ctx, indent+1)
        if goal_in_context(node.conclusion, local_ctx, self.decl):
            logger.debug(f"{debug_prefix}{node.name} proved: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
            self.decl.add(self.unit.file, node)
        else:
            msg = f"{node.name} not proved: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}"
            raise CheckError(node, msg)

    def check_defpred(self, node: DefPred, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, args: {node.args}, formula: {ExprFormatter(self.decl).pretty_expr(node.formula)}")
        self.decl.add(self.unit.file, node)

    def check_defcon(self, node: DefCon, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, theorem: {node.ref_theorem.name}")
        existsuniq = self.decl.get_theorem(node.ref_theorem).conclusion
        if not isinstance(existsuniq, ExistsUniq):
            msg = f"Not ExistsUniq object: {ExprFormatter(self.decl).pretty_expr(existsuniq)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}ExistsUniq object: {ExprFormatter(self.decl).pretty_expr(existsuniq)}")
        self.decl.add(self.unit.file, node)

    def check_defconexist(self, node: DefConExist, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, con_name: {node.ref_con.name}")
        existsuniq = self.decl.get_theorem(self.decl.get_defcon(node.ref_con).ref_theorem).conclusion
        if not isinstance(existsuniq, ExistsUniq):
            msg = f"Not ExistsUniq object: {ExprFormatter(self.decl).pretty_expr(existsuniq)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}ExistsUniq object: {ExprFormatter(self.decl).pretty_expr(existsuniq)}")
        context = Context.init()
        existence_formula = Substitutor(({existsuniq.var: RefDefCon(node.ref_con.name)}, {}, {}), self.decl).substitute_formula(existsuniq.body)
        if not alpha_equiv_with_defs(node.formula, existence_formula, context, self.decl):
            msg = f"existence_formula is not matched with theorem: {ExprFormatter(self.decl).pretty_expr(node.formula)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}existence_formula is matched with theorem: {ExprFormatter(self.decl).pretty_expr(node.formula)}")
        self.decl.add(self.unit.file, node)

    def check_defconuniq(self, node: DefConUniq, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, con_name: {node.ref_con.name}")
        existsuniq = self.decl.get_theorem(self.decl.get_defcon(node.ref_con).ref_theorem).conclusion
        if not isinstance(existsuniq, ExistsUniq):
            msg = f"Not ExistsUniq object: {ExprFormatter(self.decl).pretty_expr(existsuniq)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}ExistsUniq object: {ExprFormatter(self.decl).pretty_expr(existsuniq)}")
        fv, bv, fpt, bpt, fft, bft = collect_vars(existsuniq.body)
        context = Context.init()
        var = fresh_var(existsuniq.var, fv | bv | fpt | bpt | fft | bft, context, self.decl)
        body = Substitutor(({existsuniq.var: var}, {}, {}), self.decl).substitute_formula(existsuniq.body)
        equality = self.decl.get_equality()
        if equality is None:
            msg = "equality has not been declared yet"
            raise CheckError(node, msg)
        uniqueness_formula = Forall(var, Implies(body, AtomicFormula(RefEquality(equality.ref.name), (var, RefDefCon(node.ref_con.name)))))
        if not alpha_equiv_with_defs(node.formula, uniqueness_formula, context, self.decl):
            msg = f"uniqueness_formula is not matched with theorem: {ExprFormatter(self.decl).pretty_expr(node.formula)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}uniqueness_formula is matched with theorem: {ExprFormatter(self.decl).pretty_expr(node.formula)}")
        self.decl.add(self.unit.file, node)

    def check_deffun(self, node: DefFun, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, theorem: {node.ref_theorem.name}")
        self.decl.add(self.unit.file, node)

    def check_deffunexist(self, node: DefFunExist, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, fun_name: {node.ref_fun.name}")
        args, body = strip_forall_vars(self.decl.get_theorem(self.decl.get_deffun(node.ref_fun).ref_theorem).conclusion)
        context = Context.init()
        if isinstance(body, ExistsUniq):
            existence_formula = Substitutor(({body.var: Compound(RefDefFun(node.ref_fun.name), tuple(args))}, {}, {}), self.decl).substitute_formula(body.body)
        elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
            existence_formula = Implies(body.left, Substitutor(({body.right.var: Compound(RefDefFun(node.ref_fun.name), tuple(args))}, {}, {}), self.decl).substitute_formula(body.right.body))
        else:
            msg = f"Unexpected formula: {ExprFormatter(self.decl).pretty_expr(body)}"
            raise CheckError(node, msg)
        existence_formula = make_forall_vars(existence_formula, args)
        if not alpha_equiv_with_defs(node.formula, existence_formula, context, self.decl):
            msg = f"existence_formula is not matched with theorem: {ExprFormatter(self.decl).pretty_expr(node.formula)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}existence_formula is matched with theorem: {ExprFormatter(self.decl).pretty_expr(node.formula)}")
        self.decl.add(self.unit.file, node)

    def check_deffununiq(self, node: DefFunUniq, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, fun_name: {node.ref_fun.name}")
        equality = self.decl.get_equality()
        if equality is None:
            msg = "equality has not been declared yet"
            raise CheckError(node, msg)
        args, body = strip_forall_vars(self.decl.get_theorem(self.decl.get_deffun(node.ref_fun).ref_theorem).conclusion)
        if isinstance(body, ExistsUniq):
            uniqueness_formula = Forall(body.var, Implies(body.body, AtomicFormula(RefEquality(equality.ref.name), (Var(body.var.name), Compound(RefDefFun(node.ref_fun.name), tuple(args))))))
        elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
            uniqueness_formula = Implies(body.left, Forall(body.right.var, Implies(body.right.body, AtomicFormula(RefEquality(equality.ref.name), (Var(body.right.var.name), Compound(RefDefFun(node.ref_fun.name), tuple(args)))))))
        else:
            msg = f"Unexpected formula: {ExprFormatter(self.decl).pretty_expr(body)}"
            raise CheckError(node, msg)
        uniqueness_formula = make_forall_vars(uniqueness_formula, args)
        if not alpha_equiv_with_defs(node.formula, uniqueness_formula, Context.init(), self.decl):
            msg = f"uniqueness_formula is not matched with theorem: {ExprFormatter(self.decl).pretty_expr(node.formula)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}uniqueness_formula is matched with theorem: {ExprFormatter(self.decl).pretty_expr(node.formula)}")
        self.decl.add(self.unit.file, node)

    def check_deffunterm(self, node: DefFunTerm, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, args: {node.args}, term: {ExprFormatter(self.decl).pretty_expr(node.varterm)}")
        fv, _, fpt, _, fft, _ = collect_vars(node.varterm)
        if set(node.args) != set(fv) | set(fpt) | set(fft):
            msg = f"args are not matched with free vars: {set(fv) | set(fpt) | set(fft)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}args are mathced with free vars of term: {set(fv) | set(fpt) | set(fft)}")
        self.decl.add(self.unit.file, node)

    def check_equality(self, node: Equality, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.ref.name}")
        self.decl.add(self.unit.file, node)
        logger.debug(f"{debug_prefix}{node.ref.name} is registered as equality")

    def check_struct(self, node: Struct, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}")
        self.decl.add(self.unit.file, node)

    def check_struct_predicate(self, node: StructPred, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}")
        self.decl.add(self.unit.file, node)

    def check_control(self, node: Control, context: Context, indent: int) -> Context:

        node.proofinfo.ctrl_ctx = deepcopy(context.ctrl)

        try:
            if isinstance(node, Any):
                context = self.check_any(node, context, indent)
            elif isinstance(node, Assume):
                context = self.check_assume(node, context, indent)
            elif isinstance(node, Divide):
                context = self.check_divide(node, context, indent)
            elif isinstance(node, Some):
                context = self.check_some(node, context, indent)
            elif isinstance(node, Deny):
                context = self.check_deny(node, context, indent)
            elif isinstance(node, Case):
                context = self.check_case(node, context, indent)
            elif isinstance(node, Contradict):
                context = self.check_contradict(node, context, indent)
            elif isinstance(node, Explode):
                context = self.check_explode(node, context, indent)
            elif isinstance(node, Apply):
                context = self.check_apply(node, context, indent)
            elif isinstance(node, Lift):
                context = self.check_lift(node, context, indent)
            elif isinstance(node, Characterize):
                context = self.check_characterize(node, context, indent)
            elif isinstance(node, Invoke):
                context = self.check_invoke(node, context, indent)
            elif isinstance(node, Expand):
                context = self.check_expand(node, context, indent)
            elif isinstance(node, Fold):
                context = self.check_fold(node, context, indent)
            elif isinstance(node, Pad):
                context = self.check_pad(node, context, indent)
            elif isinstance(node, Split):
                context = self.check_split(node, context, indent)
            elif isinstance(node, Connect):
                context = self.check_connect(node, context, indent)
            elif isinstance(node, Substitute):
                context = self.check_substitute(node, context, indent)
            elif isinstance(node, Show):
                context = self.check_show(node, context, indent)
            elif isinstance(node, Assert):
                context = self.check_assert(node, context, indent)
            elif isinstance(node, InvalidControl):
                msg = "InvalidControl"
                raise CheckError(node, msg)
            else:
                msg = f"Unsupported node {node}"
                raise CheckError(node, msg)
            node.proofinfo.status = "✅Passed"
            return context
        except CheckError as e:
            logger.error(f"{self.make_error_prefix(node, indent)}{e.msg}")
            node.proofinfo.status = "❌Failed"
            raise
        except (ContextError, LogicError, FormatError) as e:
            msg = f"{e.__class__.__name__}: {e.msg}"
            logger.error(f"{self.make_error_prefix(node, indent)}{msg}")
            node.proofinfo.status = "❌Failed"
            raise CheckError(node, msg)

    def check_any(self, node: Any, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        for item in node.items:
            if item.name in context.ctrl.used_names or item.name in self.decl.get_used_names():
                msg = f"{ExprFormatter(self.decl).pretty_expr(item)} is already used"
                raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}Taking {node.items}")
        local_vars = [item for item in node.items if isinstance(item, Var)]
        local_pred_tmpls = [item for item in node.items if isinstance(item, PredTemplate)]
        local_fun_tmpls = [item for item in node.items if isinstance(item, FunTemplate)]
        local_ctx = context.add_ctrl(local_vars, [], local_pred_tmpls, local_fun_tmpls, node.items)
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(node, msg)
        local_goal = local_ctx.ctrl.formulas[-1]
        if isinstance(local_goal, Bottom):
            msg = "Bottom cannot be generalized"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}derived local_goal: {ExprFormatter(self.decl).pretty_expr(local_goal)}")
        goal = local_goal
        for item in reversed(node.items):
            goal = Forall(item, goal)
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = node.items
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [local_goal]
        logger.debug(f"{debug_prefix}Generalized to {ExprFormatter(self.decl).pretty_expr(goal)}")
        return context.add_ctrl([], [goal], [], [], [])

    def check_assume(self, node: Assume, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}premise={ExprFormatter(self.decl).pretty_expr(node.premise)}")
        local_ctx = context.add_ctrl([], [node.premise], [], [], [])
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(node, msg)
        goal = local_ctx.ctrl.formulas[-1]
        if isinstance(goal, Bottom):
            msg = "Bottom is not allowed as goal"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(self.decl).pretty_expr(goal)}")
        implication = Implies(node.premise, goal)
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [implication]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = [node.premise]
        node.proofinfo.local_conclusion = [goal]
        logger.debug(f"{debug_prefix}Added implication {ExprFormatter(self.decl).pretty_expr(implication)}")
        return context.add_ctrl([], [implication], [], [], [])

    def check_divide(self, node: Divide, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                msg = f"Not fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}"
                raise CheckError(node, msg)
        fact = get_fact(node.fact, context, node, self.decl, True)
        connected_premise = Or(node.cases[0].premise, node.cases[1].premise)
        i = 2
        while i < len(node.cases):
            connected_premise = Or(connected_premise, node.cases[i].premise)
            i += 1
        if alpha_equiv_with_defs(connected_premise, fact, context, self.decl):
            logger.debug(f"{debug_prefix}mathched: fact={ExprFormatter(self.decl).pretty_expr(fact)}, connected_premise={ExprFormatter(self.decl).pretty_expr(connected_premise)}")
        else:
            msg = f"not matched: fact={ExprFormatter(self.decl).pretty_expr(fact)}, conected_premise={ExprFormatter(self.decl).pretty_expr(connected_premise)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}fact={ExprFormatter(self.decl).pretty_expr(fact)}")
        goals: list[Bottom | Formula] = []
        for stmt in node.cases:
            local_ctx = self.check_control(stmt, context, indent+1)
            if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
                msg = "Local context must extend the parent context"
                raise CheckError(node, msg)
            goal = local_ctx.ctrl.formulas[-1]
            logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(self.decl).pretty_expr(goal)}")
            goals.append(goal)
        for i in range(len(goals) - 1):
            if not alpha_equiv_with_defs(goals[i], goals[i + 1], context, self.decl):
                msg = f"Not matched: goals[{i}]: {ExprFormatter(self.decl).pretty_expr(goals[i])}, goals[{i + 1}]: {ExprFormatter(self.decl).pretty_expr(goals[i + 1])}"
                raise CheckError(node, msg)
        node.proofinfo.premises = [node.fact]
        node.proofinfo.conclusions = [goals[0]]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [goals[0]]
        logger.debug(f"{debug_prefix}derived in all cases: {ExprFormatter(self.decl).pretty_expr(goals[0])}")
        return context.add_ctrl([], [goals[0]], [], [], [])

    def check_case(self, node: Case, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}premise={ExprFormatter(self.decl).pretty_expr(node.premise)}")
        local_ctx = context.add_ctrl([], [node.premise], [], [], [])
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(node, msg)
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(self.decl).pretty_expr(goal)}")
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = [node.premise]
        node.proofinfo.local_conclusion = [goal]
        logger.debug(f"{debug_prefix}Added goal {ExprFormatter(self.decl).pretty_expr(goal)}")
        return context.add_ctrl([], [goal], [], [], [])

    def check_some(self, node: Some, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                msg = f"not derivable: {ExprFormatter(self.decl).pretty_expr(node.fact)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}derivable: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
        fact = get_fact(node.fact, context, node, self.decl, True)
        if isinstance(fact, Exists):
            vars, body = strip_exists_vars(fact, Exists)
            body = make_exists_vars(body, Exists, [bound for bound, free in zip(vars, node.items) if free is None])
        elif isinstance(fact, ExistsUniq):
            vars, body= strip_exists_vars(fact, ExistsUniq)
            if len(vars) != 1:
                msg = f"Unexpected len(vars): {len(vars)}"
                raise CheckError(node, msg)
        else:
            msg = f"Unexpected type: {type(fact)}"
            raise CheckError(node, msg)
        if len(vars) != len(node.items):
            msg = f"len(vars): {len(vars)}, len(node.items): {len(node.items)}"
            raise CheckError(node, msg)
        for item in node.items:
            if item is None:
                continue
            if item.name in context.ctrl.used_names or item.name in self.decl.get_used_names():
                msg = f"{ExprFormatter(self.decl).pretty_expr(item)} is already used"
                raise CheckError(node, msg)
        mapping: dict[Term, Term] = {bound: free for bound, free in zip(vars, node.items) if free is not None}
        renamed_body, renamed_mapping = alpha_safe_formula(body, mapping, context, self.decl)
        existence = Substitutor(renamed_mapping, self.decl).substitute_formula(renamed_body)
        if isinstance(fact, Exists):
            premises: list[Bottom | Formula] = [existence]
        else:
            fv, bv, fpt, bpt, fft, bft = collect_vars(existence)
            var = fresh_var(vars[0], fv | bv | fpt | bpt | fft | bft, context, self.decl)
            body = Substitutor(({vars[0]: var}, {}, {}), self.decl).substitute_formula(existence)
            equality = self.decl.get_equality()
            if equality is None:
                msg = "equality has not been declared yet"
                raise CheckError(node, msg)
            uniqueness = Forall(var, Implies(body, AtomicFormula(RefEquality(equality.ref.name), (var, vars[0]))))
            premises: list[Bottom | Formula] = [existence, uniqueness]
        logger.debug(f"{debug_prefix}Taking {node.items}, premise={ExprFormatter(self.decl).pretty_expr(existence)}")
        local_vars = [item for item in node.items if isinstance(item, Var)]
        local_symbols: list[Var | PredTemplate | FunTemplate] = list(local_vars)
        local_ctx = context.add_ctrl(local_vars, premises, [], [], local_symbols)
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(node, msg)
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(self.decl).pretty_expr(goal)}")
        if isinstance(goal, Formula):
            goal_fv, _, _, _, _, _ = collect_vars(goal)
            for fv in goal_fv:
                if fv in local_vars:
                    msg = f"Conclusion depends on local variable {ExprFormatter(self.decl).pretty_expr(fv)}"
                    raise CheckError(node, msg)
        node.proofinfo.premises = [node.fact]
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = list(local_vars)
        node.proofinfo.local_premise = premises
        node.proofinfo.local_conclusion = [goal]
        logger.debug(f"{debug_prefix}Added goal {ExprFormatter(self.decl).pretty_expr(goal)}")
        return context.add_ctrl([], [goal], [], [], [])

    def check_deny(self, node: Deny, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}premise={ExprFormatter(self.decl).pretty_expr(node.premise)}")
        local_ctx = context.add_ctrl([], [node.premise], [], [], [])
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(node, msg)
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(self.decl).pretty_expr(goal)}")
        if isinstance(goal, Bottom):
            if isinstance(node.premise, Not):
                conclusion = node.premise.body
            else:
                conclusion = Not(node.premise)
            node.proofinfo.premises = []
            node.proofinfo.conclusions = [conclusion]
            node.proofinfo.local_vars = []
            node.proofinfo.local_premise = [node.premise]
            node.proofinfo.local_conclusion = [goal]
            logger.debug(f"{debug_prefix}contradiction is derived; added {ExprFormatter(self.decl).pretty_expr(conclusion)}")
            return context.add_ctrl([], [conclusion], [], [], [])
        else:
            msg = "conradiction has not been deried"
            raise CheckError(node, msg)

    def check_contradict(self, node: Contradict, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        if not goal_in_context(node.contradiction, context, self.decl):
            msg = f"Cannot derive {ExprFormatter(self.decl).pretty_expr(node.contradiction)}"
            raise CheckError(node, msg)
        if not goal_in_context(Not(node.contradiction), context, self.decl):
            msg = f"Cannot derive {ExprFormatter(self.decl).pretty_expr(Not(node.contradiction))}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}Derived contradiction: {ExprFormatter(self.decl).pretty_expr(node.contradiction)}, {ExprFormatter(self.decl).pretty_expr(Not(node.contradiction))}")
        conclusion = Bottom()
        node.proofinfo.premises = [node.contradiction, Not(node.contradiction)]
        node.proofinfo.conclusions = [conclusion]
        return context.add_ctrl([], [conclusion], [], [], [])

    def check_explode(self, node: Explode, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        if goal_in_context(Bottom(), context, self.decl):
            node.proofinfo.premises = [Bottom()]
            node.proofinfo.conclusions = [node.conclusion]
            logger.debug(f"{debug_prefix}added {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
            return context.add_ctrl([], [node.conclusion], [], [], [])
        else:
            msg = "contradiction has not been derived"
            raise CheckError(node, msg)

    def check_apply(self, node: Apply, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                msg = f"Cannot derive fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Drivable fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
        fact = get_fact(node.fact, context, node, self.decl, True)
        items, body = strip_forall_vars(fact)
        if len(items) != len(node.terms):
            msg = f"Formula has {len(items)} forall vars, but {len(node.terms)} terms are given"
            raise CheckError(node, msg)
        body = make_forall_vars(body, [item for item, term in zip(items, node.terms) if term is None])
        mapping: dict[Term, Term] = {}
        for item, term in zip(items, node.terms):
            if term is None:
                continue
            mapping[item] = term
        renamed_body, renamed_map = alpha_safe_formula(body, mapping, context, self.decl)
        logger.debug(f"{debug_prefix}Instantiable: mapping={mapping}")
        instantiation = Substitutor(renamed_map, self.decl).substitute_formula(renamed_body)
        logger.debug(f"{debug_prefix}\\forall-elimination is done: instantiation={ExprFormatter(self.decl).pretty_expr(instantiation)}")
        if node.invoke == "none":
            node.proofinfo.premises = [node.fact]
            node.proofinfo.conclusions = [instantiation]
            logger.debug(f"{debug_prefix}Added {ExprFormatter(self.decl).pretty_expr(instantiation)}")
            return context.add_ctrl([], [instantiation], [], [], [])
        elif node.invoke == "invoke":
            if not isinstance(instantiation, Implies):
                msg = "instantiation is not Implies object"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}instantiation is Implies object")
            if not goal_in_context(instantiation.left, context, self.decl):
                msg = f"Left of instantiation is not derivable: {ExprFormatter(self.decl).pretty_expr(instantiation.left)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Left of instantiation is derivable: {ExprFormatter(self.decl).pretty_expr(instantiation.left)}")
            node.proofinfo.premises = [node.fact, instantiation.left]
            node.proofinfo.conclusions = [instantiation.right]
            logger.debug(f"{debug_prefix}Added {ExprFormatter(self.decl).pretty_expr(instantiation.right)}")
            return context.add_ctrl([], [instantiation.right], [], [], [])
        elif node.invoke == "invoke-rightward":
            if not isinstance(instantiation, Iff):
                msg = "instantiation is not Iff object"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}instantiation is Iff object")
            if not goal_in_context(instantiation.left, context, self.decl):
                msg = f"Left of instantiation is not derivable: {ExprFormatter(self.decl).pretty_expr(instantiation.left)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Left of instantiation is derivable: {ExprFormatter(self.decl).pretty_expr(instantiation.left)}")
            node.proofinfo.premises = [node.fact, instantiation.left]
            node.proofinfo.conclusions = [instantiation.right]
            logger.debug(f"{debug_prefix}Added {ExprFormatter(self.decl).pretty_expr(instantiation.right)}")
            return context.add_ctrl([], [instantiation.right], [], [], [])
        elif node.invoke == "invoke-leftward":
            if not isinstance(instantiation, Iff):
                msg = "instantiation is not Iff object"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}instantiation is Iff object")
            if not goal_in_context(instantiation.right, context, self.decl):
                msg = f"Right of instantiation is not derivable: {ExprFormatter(self.decl).pretty_expr(instantiation.right)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Right of instantiation is derivable: {ExprFormatter(self.decl).pretty_expr(instantiation.right)}")
            node.proofinfo.premises = [node.fact, instantiation.right]
            node.proofinfo.conclusions = [instantiation.left]
            logger.debug(f"{debug_prefix}Added {ExprFormatter(self.decl).pretty_expr(instantiation.left)}")
            return context.add_ctrl([], [instantiation.left], [], [], [])
        else:
            msg = f"Unexpected invoke option {node.invoke}"
            raise CheckError(node, msg)

    def check_lift(self, node: Lift, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}Target conclusion: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
        conclusion = expand_if_atomic(node.conclusion, context, node, self.decl)
        if not isinstance(conclusion, Exists):
            msg = f"Expected Exists, got {type(conclusion)}"
            raise CheckError(node, msg)
        items, body = strip_exists_vars(conclusion, Exists)
        if len(items) != len(node.varterms):
            msg = f"Formula has {len(items)} exists vars, but {len(node.varterms)} terms are given"
            raise CheckError(node, msg)
        body = make_exists_vars(body, Exists, [item for item, term in zip(items, node.varterms) if term is None])
        mapping: dict[Term, Term] = {item: term for item, term in zip(items, node.varterms) if term is not None}
        renamed_body, renamed_mapping = alpha_safe_formula(body, mapping, context, self.decl)
        fact = Substitutor(renamed_mapping, self.decl).substitute_formula(renamed_body)
        if not goal_in_context(fact, context, self.decl):
            msg = f"Not fact: {ExprFormatter(self.decl).pretty_expr(fact)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}Fact: {ExprFormatter(self.decl).pretty_expr(fact)}")
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        return context.add_ctrl([], [node.conclusion], [], [], [])

    def check_characterize(self, node: Characterize, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        _, used_bound_vars, _, used_bound_pred_tmpls, _, used_bound_fun_tmpls = collect_vars(node.conclusion.body)
        fv, bv, fpt, bpt, fft, bft = collect_vars(node.varterm)
        vardash = fresh_var(Var(node.conclusion.var.name + "'"), used_bound_vars | used_bound_pred_tmpls | used_bound_fun_tmpls | fv | bv | fpt | bpt | fft | bft, context, self.decl)
        renamed_conclusion, _ = alpha_safe_formula(node.conclusion, {node.conclusion.var: node.varterm}, context, self.decl)
        if not isinstance(renamed_conclusion, ExistsUniq):
            msg = f"renamed_conclusion is not ExistsUniq object: {ExprFormatter(self.decl).pretty_expr(renamed_conclusion)}"
            raise CheckError(node, msg)
        existence = Substitutor(({renamed_conclusion.var: node.varterm}, {}, {}), self.decl).substitute_formula(renamed_conclusion.body)
        existence_dash = Substitutor(({renamed_conclusion.var: vardash}, {}, {}), self.decl).substitute_formula(renamed_conclusion.body)
        equality = self.decl.get_equality()
        if equality is None:
            msg = "equality has not been declared yet"
            raise CheckError(node, msg)
        fact = And(existence, Forall(vardash, Implies(existence_dash, AtomicFormula(RefEquality(equality.ref.name), (vardash, node.varterm)))))
        if not goal_in_context(fact, context, self.decl):
            msg = f"Not fact: {ExprFormatter(self.decl).pretty_expr(fact)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}Fact: {ExprFormatter(self.decl).pretty_expr(fact)}")
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        return context.add_ctrl([], [node.conclusion], [], [], [])

    def check_invoke(self, node: Invoke, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        if not goal_in_context(node.fact, context, self.decl):
            msg = f"Not fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
        if node.direction == "none":
            if not isinstance(node.fact, Implies):
                msg = f"Not Implies object: {ExprFormatter(self.decl).pretty_expr(node.fact)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Implies object: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
            if not goal_in_context(node.fact.left, context, self.decl):
                msg = f"Left of Implies object not derived: {ExprFormatter(self.decl).pretty_expr(node.fact.left)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Left of Implies object derived: {ExprFormatter(self.decl).pretty_expr(node.fact.left)}")
            node.proofinfo.premises = [node.fact, node.fact.left]
            node.proofinfo.conclusions = [node.fact.right]
            logger.debug(f"{debug_prefix}Right of Implies object added: {ExprFormatter(self.decl).pretty_expr(node.fact.right)}")
            return context.add_ctrl([], [node.fact.right], [], [], [])
        elif node.direction == "rightward":
            if not isinstance(node.fact, Iff):
                msg = f"Not Iff object: {ExprFormatter(self.decl).pretty_expr(node.fact)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Iff object: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
            if not goal_in_context(node.fact.left, context, self.decl):
                msg = f"Left of Iff object not derived: {ExprFormatter(self.decl).pretty_expr(node.fact.left)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Left of Iff object derived: {ExprFormatter(self.decl).pretty_expr(node.fact.left)}")
            node.proofinfo.premises = [node.fact, node.fact.left]
            node.proofinfo.conclusions = [node.fact.right]
            logger.debug(f"{debug_prefix}Right of Iff object added: {ExprFormatter(self.decl).pretty_expr(node.fact.right)}")
            return context.add_ctrl([], [node.fact.right], [], [], [])
        elif node.direction == "leftward":
            if not isinstance(node.fact, Iff):
                msg = f"Not Iff object: {ExprFormatter(self.decl).pretty_expr(node.fact)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Iff object: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
            if not goal_in_context(node.fact.right, context, self.decl):
                msg = f"Right of Iff object not derived: {ExprFormatter(self.decl).pretty_expr(node.fact.right)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Right of Iff object derived: {ExprFormatter(self.decl).pretty_expr(node.fact.right)}")
            node.proofinfo.premises = [node.fact, node.fact.right]
            node.proofinfo.conclusions = [node.fact.left]
            logger.debug(f"{debug_prefix}Left of Iff object added: {ExprFormatter(self.decl).pretty_expr(node.fact.left)}")
            return context.add_ctrl([], [node.fact.left], [], [], [])
        else:
            msg = f"Unexpected direction: {node.direction}"
            raise CheckError(node, msg)

    def check_expand(self, node: Expand, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                msg = f"Not fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
        fact = get_fact(node.fact, context, node, self.decl)
        conclusion = DefExpander(node.refs, self.decl, node.indexes).expand_defs_formula(fact, context)
        node.proofinfo.premises = [node.fact]
        node.proofinfo.conclusions = [conclusion]
        logger.debug(f"{debug_prefix}Added: {ExprFormatter(self.decl).pretty_expr(conclusion)}")
        return context.add_ctrl([], [conclusion], [], [], [])

    def check_fold(self, node: Fold, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        fact = DefExpander(node.refs, self.decl, node.indexes).expand_defs_formula(node.conclusion, context)
        if not goal_in_context(fact, context, self.decl):
            msg = f"Not fact: {ExprFormatter(self.decl).pretty_expr(fact)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}fact: {ExprFormatter(self.decl).pretty_expr(fact)}")
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        logger.debug(f"{debug_prefix}Added: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
        return context.add_ctrl([], [node.conclusion], [], [], [])

    def check_pad(self, node: Pad, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                msg = f"Not derivable: {ExprFormatter(self.decl).pretty_expr(node.fact)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Derivable: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
        fact = get_fact(node.fact, context, node, self.decl)
        fact_parts = flatten_op(fact, Or)
        conclusion = expand_if_atomic(node.conclusion, context, node, self.decl)
        if not isinstance(conclusion, Or):
            msg = f"Expected Or, got {type(conclusion)}"
            raise CheckError(node, msg)
        conclusion_parts = flatten_op(conclusion, Or)
        if not all(any(alpha_equiv_with_defs(c, f, context, self.decl) for c in conclusion_parts) for f in fact_parts):
            msg = f"neither left or right not derivable: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}"
            raise CheckError(node, msg)
        node.proofinfo.premises = [node.fact]
        node.proofinfo.conclusions = [node.conclusion]
        logger.debug(f"{debug_prefix}Derivable, added {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
        return context.add_ctrl([], [node.conclusion], [], [], [])

    def check_split(self, node: Split, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                msg = f"Not derivable: {ExprFormatter(self.decl).pretty_expr(node.fact)}"
                raise CheckError(node, msg)
        fact = get_fact(node.fact, context, node, self.decl, True)
        logger.debug(f"{debug_prefix}Derivable: {ExprFormatter(self.decl).pretty_expr(fact)}")
        if isinstance(fact, And):
            logger.debug(f"{debug_prefix}And object: {ExprFormatter(self.decl).pretty_expr(fact)}")
            fact_parts = flatten_op(fact, And)
            node.proofinfo.premises = [node.fact]
            if node.index is None:
                node.proofinfo.conclusions = fact_parts
                for f in fact_parts:
                    logger.debug(f"{debug_prefix}added {ExprFormatter(self.decl).pretty_expr(f)}")
                return context.add_ctrl([], list(fact_parts), [], [], [])
            else:
                if node.index <= 0 or node.index > len(fact_parts):
                    msg = f"index out of range, index: {node.index}, len(fact_parts): {len(fact_parts)}"
                    raise CheckError(node, msg)
                f = fact_parts[node.index - 1]
                node.proofinfo.conclusions = [f]
                logger.debug(f"{debug_prefix}added {ExprFormatter(self.decl).pretty_expr(f)}")
                return context.add_ctrl([], [f], [], [], [])
        elif isinstance(fact, Iff):
            logger.debug(f"{debug_prefix}Iff object: {ExprFormatter(self.decl).pretty_expr(fact)}")
            implication_rightward = Implies(fact.left, fact.right)
            implication_leftward = Implies(fact.right, fact.left)
            node.proofinfo.premises = [node.fact]
            node.proofinfo.conclusions = [implication_rightward, implication_leftward]
            logger.debug(f"{debug_prefix}added {ExprFormatter(self.decl).pretty_expr(implication_rightward)}")
            logger.debug(f"{debug_prefix}added {ExprFormatter(self.decl).pretty_expr(implication_leftward)}")
            return context.add_ctrl([], [implication_rightward, implication_leftward], [], [], [])
        else:
            msg = f"Not And or Iff object: {ExprFormatter(self.decl).pretty_expr(fact)}"
            raise CheckError(node, msg)

    def check_connect(self, node: Connect, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        conclusion = expand_if_atomic(node.conclusion, context, node, self.decl)
        if isinstance(conclusion, And):
            logger.debug(f"{debug_prefix}And object: {ExprFormatter(self.decl).pretty_expr(conclusion)}")
            conclusion_parts = flatten_op(conclusion, And)
            for c in conclusion_parts:
                if not goal_in_context(c, context, self.decl):
                    msg = f"Not derivable: {ExprFormatter(self.decl).pretty_expr(c)}"
                    raise CheckError(node, msg)
            node.proofinfo.premises = conclusion_parts
            node.proofinfo.conclusions = [node.conclusion]
            logger.debug(f"{debug_prefix}Derivable, added {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
            return context.add_ctrl([], [node.conclusion], [], [], [])
        elif isinstance(conclusion, Iff):
            logger.debug(f"{debug_prefix}Iff object: {ExprFormatter(self.decl).pretty_expr(conclusion)}")
            implication_rightward = Implies(conclusion.left, conclusion.right)
            if not goal_in_context(implication_rightward, context, self.decl):
                msg = f"Not derivable: {ExprFormatter(self.decl).pretty_expr(implication_rightward)}"
                raise CheckError(node, msg)
            implication_leftward = Implies(conclusion.right, conclusion.left)
            if not goal_in_context(implication_leftward, context, self.decl):
                msg = f"Not derivable: {ExprFormatter(self.decl).pretty_expr(implication_leftward)}"
                raise CheckError(node, msg)
            node.proofinfo.premises = [implication_rightward, implication_leftward]
            node.proofinfo.conclusions = [node.conclusion]
            logger.debug(f"{debug_prefix}derivable, added {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
            return context.add_ctrl([], [node.conclusion], [], [], [])
        else:
            msg = f"Not And or Iff object: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}"
            raise CheckError(node, msg)

    def check_substitute(self, node: Substitute, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context, self.decl):
                msg = f"Not fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Fact: {ExprFormatter(self.decl).pretty_expr(node.fact)}")
        fact = get_fact(node.fact, context, node, self.decl)
        equality = self.decl.get_equality()
        if equality is None:
            msg = "equality has not been declared yet"
            raise CheckError(node, msg)
        premises_equal: list[AtomicFormula] = []
        for k, v in node.env.items():
            if not isinstance(k, VarTerm):
                msg = f"Expected VarTerm, got {type(k)}"
                raise CheckError(node, msg)
            if not isinstance(v, VarTerm):
                msg = f"Expected VarTerm, got {type(v)}"
                raise CheckError(node, msg)
            equation = AtomicFormula(RefEquality(equality.ref.name), (k, v))
            if not goal_in_context(equation, context, self.decl):
                msg = f"Not fact: {ExprFormatter(self.decl).pretty_expr(equation)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Fact: {ExprFormatter(self.decl).pretty_expr(equation)}")
            premises_equal.append(equation)
        renamed_fact, mapping = alpha_safe_formula(fact, node.env, context, self.decl, True)
        conclusion = Substitutor(mapping, self.decl, node.indexes).substitute_formula(renamed_fact)
        logger.debug(f"{debug_prefix}conclusion: {ExprFormatter(self.decl).pretty_expr(conclusion)}")
        logger.debug(f"{debug_prefix}Matched")
        node.proofinfo.premises = [node.fact] + premises_equal
        node.proofinfo.conclusions = [conclusion]
        logger.debug(f"{debug_prefix}Added {ExprFormatter(self.decl).pretty_expr(conclusion)}")
        return context.add_ctrl([], [conclusion], [], [], [])

    def check_show(self, node: Show, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}Target conclusion: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
        local_ctx = context
        for stmt in node.body:
            local_ctx = self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(node, msg)
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(self.decl).pretty_expr(goal)}")
        if not alpha_equiv_with_defs(node.conclusion, goal, context, self.decl):
            msg = f"Not matched with target conclusion: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}"
            raise CheckError(node, msg)
        logger.debug(f"{debug_prefix}Matched with target conclusion: {ExprFormatter(self.decl).pretty_expr(node.conclusion)}")
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [goal]
        logger.debug(f"{debug_prefix}Added {ExprFormatter(self.decl).pretty_expr(goal)}")
        return context.add_ctrl([], [goal], [], [], [])

    def check_assert(self, node: Assert, context: Context, indent: int) -> Context:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.reference, (Bottom, Formula)):
            if not goal_in_context(node.reference, context, self.decl):
                msg = f"Not fact: {ExprFormatter(self.decl).pretty_expr(node.reference)}"
                raise CheckError(node, msg)
            logger.debug(f"{debug_prefix}Fact: {ExprFormatter(self.decl).pretty_expr(node.reference)}")
        formula = get_fact(node.reference, context, node, self.decl)
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [formula]
        logger.debug(f"{debug_prefix}Added {ExprFormatter(self.decl).pretty_expr(formula)}")
        return context.add_ctrl([], [formula], [], [], [])

if __name__ == "__main__":
    import sys
    path = sys.argv[1]

    import os
    import logging

    logger = logging.getLogger("proof")
    logger.setLevel(logging.DEBUG)

    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.DEBUG)

    file_handler = logging.FileHandler(os.path.join("logs", os.path.basename(path).replace(".proof", "_checker.log")), mode='w', encoding='utf-8')
    file_handler.setLevel(logging.DEBUG)

    formatter = logging.Formatter("[%(filename)s] %(message)s")
    console_handler.setFormatter(formatter)
    file_handler.setFormatter(formatter)

    logger.addHandler(console_handler)
    logger.addHandler(file_handler)

    from analyzer import Analyzer, print_diags
    analyzer = Analyzer()
    diagnostics = analyzer.analyze(path)
    print_diags(diagnostics)
