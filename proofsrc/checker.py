from lexer import Token
from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, AtomicFormula, And, Or, Implies, Forall, Exists, Not, Bottom, Iff, Axiom, Invoke, Expand, PrimPred, DefPred, DefCon, Pad, Split, Connect, ExistsUniq, Compound, RefDefCon, DefFun, DefFunTerm, Equality, Var, Substitute, Characterize, Show, Control, Formula, Declaration, PredTemplate, Term, DefConExist, DefConUniq, DefFunExist, DefFunUniq, EqualityReflection, EqualityReplacement, Include, DeclarationSupport, Assert, Fold, Membership, MembershipLambda, VarTerm, PredTerm, FunTemplate, RefPrimPred, RefDefPred, RefDefFun, InvalidDeclaration, InvalidControl, InvalidInclude, DeclarationUnit
from logic_utils import Substitutor, DefExpander, expr_in_context, strip_forall_vars, strip_exists_vars, make_forall_vars, make_exists_vars, collect_vars, flatten_op, fresh_var, alpha_equiv_with_defs, pretty_expr, alpha_safe_formula
from copy import deepcopy
from lsprotocol import types as lsp
from pygls import uris

import logging
logger = logging.getLogger("proof")

def goal_in_context(goal: str | Bottom | Formula, context: Context) -> bool:
    if isinstance(goal, str):
        return context.decl.has_reference(goal)
    elif isinstance(goal, AtomicFormula) and context.decl.equality is not None and isinstance(goal.pred, (RefPrimPred, RefDefPred)) and goal.pred == context.decl.equality.equal and goal.args[0] == goal.args[1]:
        return True
    else:
        return expr_in_context(goal, context)

def get_fact(fact: str | Formula, context: Context, token: Token, expand_symbol: bool = False) -> Formula:
    if isinstance(fact, str):
        fact = context.decl.get_reference(fact, token)
    elif not isinstance(fact, Formula):
        raise Exception(f"Unexpected type {type(fact)}")
    if expand_symbol and isinstance(fact, AtomicFormula) and isinstance(fact.pred, RefDefPred):
        fact = DefExpander([fact.pred.name], {fact.pred.name: [1]}).expand_defs_formula(fact, context)
    return fact

def add_conclusion(context: Context, conclusion: Bottom | Formula) -> None:
    context.ctrl.formulas.append(conclusion)

def make_debug_prefix(node: Declaration | DeclarationSupport | Control, indent: int) -> str:
    return "  " * indent + f"[{node.__class__.__name__}] "

def make_error_prefix(node: Declaration | DeclarationSupport | Control, indent: int) -> str:
    return "  " * indent + f"❌ [{node.__class__.__name__}] {node.token.info()} "

class Checker:
    def __init__(self, unit: DeclarationUnit) -> None:
        self.unit = unit

    def add_lsp_error(self, node: Declaration | DeclarationSupport | Control, message: str, context: Context):
        uri = uris.from_fs_path(node.token.file)
        if uri is None:
            return
        line = node.token.line - 1
        col = node.token.column - 1
        length = len(node.token.value)
        diag = lsp.Diagnostic(
            range=lsp.Range(
                start=lsp.Position(line=line, character=col),
                end=lsp.Position(line=line, character=col + length)
            ),
            message=message,
            source="Checker",
            severity=lsp.DiagnosticSeverity.Error
        )
        self.unit.diagnostics.append(diag)

    def check_unit(self, context: Context) -> bool:
        ast = self.unit.ast
        if isinstance(ast, Include):
            return not isinstance(ast, InvalidInclude)
        elif isinstance(ast, Declaration):
            return self.check_declaration(ast, context)
        else:
            return False

    def check_ast(self, ast: list[Include | Declaration], context: Context) -> tuple[bool, list[Include | Declaration], Context]:
        return all(self.check_declaration(node, context) for node in ast if isinstance(node, Declaration)), ast, context

    # === 証明チェッカー ===
    def check_declaration(self, node: Declaration, context: Context, indent: int = 0) -> bool:
        error_prefix = make_error_prefix(node, indent)

        node.proofinfo.ctrl_ctx = deepcopy(context.ctrl)

        if isinstance(node, PrimPred):
            return self.check_primpred(node, context, indent)
        elif isinstance(node, Axiom):
            return self.check_axiom(node, context, indent)
        elif isinstance(node, Theorem):
            return self.check_theorem(node, context, indent)
        elif isinstance(node, DefPred):
            return self.check_defpred(node, context, indent)
        elif isinstance(node, DefCon):
            return self.check_defcon(node, context, indent)
        elif isinstance(node, DefConExist):
            return self.check_defconexist(node, context, indent)
        elif isinstance(node, DefConUniq):
            return self.check_defconuniq(node, context, indent)
        elif isinstance(node, DefFun):
            return self.check_deffun(node, context, indent)
        elif isinstance(node, DefFunExist):
            return self.check_deffunexist(node, context, indent)
        elif isinstance(node, DefFunUniq):
            return self.check_deffununiq(node, context, indent)
        elif isinstance(node, DefFunTerm):
            return self.check_deffunterm(node, context, indent)
        elif isinstance(node, Equality):
            return self.check_equality(node, context, indent)
        elif isinstance(node, Membership):
            return self.check_membership(node, context, indent)
        elif isinstance(node, InvalidDeclaration):
            msg = "InvalidDeclaration"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            return False
        else:
            msg = f"Unsupported node {node}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            return False

    def check_primpred(self, node: PrimPred, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, arity: {node.arity}")
        context.add_decl(node)
        node.proofinfo.status = "OK"
        return True

    def check_axiom(self, node: Axiom, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, conclusion: {pretty_expr(node.conclusion, context)}")
        context.add_decl(node)
        node.proofinfo.status = "OK"
        return True

    def check_theorem(self, node: Theorem, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}{node.name}: {pretty_expr(node.conclusion, context)}")
        local_ctx = context.copy_ctrl()
        for stmt in node.proof:
            if not self.check_control(stmt, local_ctx, indent+1):
                msg = f"{node.name} not proved: {pretty_expr(node.conclusion, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
        if goal_in_context(node.conclusion, local_ctx):
            logger.debug(f"{debug_prefix}{node.name} proved: {pretty_expr(node.conclusion, context)}")
            context.add_decl(node)
            node.proofinfo.status = "OK"
            return True
        else:
            msg = f"{node.name} not proved: {pretty_expr(node.conclusion, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False    

    def check_defpred(self, node: DefPred, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, args: {node.args}, formula: {pretty_expr(node.formula, context)}")
        context.add_decl(node)
        node.proofinfo.status = "OK"
        return True

    def check_defcon(self, node: DefCon, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, theorem: {node.theorem}")
        existsuniq = context.decl.theorems[node.theorem].conclusion
        if not isinstance(existsuniq, ExistsUniq):
            msg = f"Not ExistsUniq object: {pretty_expr(existsuniq, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}ExistsUniq object: {pretty_expr(existsuniq, context)}")
        context.add_decl(node)
        node.proofinfo.status = "OK"
        return True

    def check_defconexist(self, node: DefConExist, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, con_name: {node.con_name}")
        existsuniq = context.decl.theorems[context.decl.defcons[node.con_name].theorem].conclusion
        if not isinstance(existsuniq, ExistsUniq):
            msg = f"Not ExistsUniq object: {pretty_expr(existsuniq, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}ExistsUniq object: {pretty_expr(existsuniq, context)}")
        existence_formula = Substitutor(({existsuniq.var: RefDefCon(node.token, node.con_name)}, {}, {}), context).substitute_formula(existsuniq.body)
        if not alpha_equiv_with_defs(node.formula, existence_formula, context):
            msg = f"existence_formula is not matched with theorem: {pretty_expr(node.formula, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}existence_formula is matched with theorem: {pretty_expr(node.formula, context)}")
        context.add_decl(node)
        node.proofinfo.status = "OK"
        return True

    def check_defconuniq(self, node: DefConUniq, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, con_name: {node.con_name}")
        existsuniq = context.decl.theorems[context.decl.defcons[node.con_name].theorem].conclusion
        if not isinstance(existsuniq, ExistsUniq):
            msg = f"Not ExistsUniq object: {pretty_expr(existsuniq, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}ExistsUniq object: {pretty_expr(existsuniq, context)}")
        fv, bv, fpt, bpt, fft, bft = collect_vars(existsuniq.body)
        var = fresh_var(existsuniq.var, fv | bv | fpt | bpt | fft | bft, context)
        body = Substitutor(({existsuniq.var: var}, {}, {}), context).substitute_formula(existsuniq.body)
        if context.decl.equality is None:
            msg = "equality has not been declared yet"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        uniqueness_formula = Forall(node.token, var, Implies(node.token, body, AtomicFormula(node.token, context.decl.equality.equal, (MembershipLambda(node.token, var), MembershipLambda(node.token, RefDefCon(node.token, node.con_name))))))
        if not alpha_equiv_with_defs(node.formula, uniqueness_formula, context):
            msg = f"uniqueness_formula is not matched with theorem: {pretty_expr(node.formula, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}uniqueness_formula is matched with theorem: {pretty_expr(node.formula, context)}")
        context.add_decl(node)
        node.proofinfo.status = "OK"
        return True

    def check_deffun(self, node: DefFun, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, theorem: {node.theorem}")
        context.add_decl(node)
        node.proofinfo.status = "OK"
        return True

    def check_deffunexist(self, node: DefFunExist, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, fun_name: {node.fun_name}")
        args, body = strip_forall_vars(context.decl.theorems[context.decl.deffuns[node.fun_name].theorem].conclusion)
        if isinstance(body, ExistsUniq):
            existence_formula = Substitutor(({body.var: Compound(node.token, RefDefFun(node.token, node.fun_name), tuple(args))}, {}, {}), context).substitute_formula(body.body)
        elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
            existence_formula = Implies(node.token, body.left, Substitutor(({body.right.var: Compound(node.token, RefDefFun(node.token, node.fun_name), tuple(args))}, {}, {}), context).substitute_formula(body.right.body))
        else:
            msg = f"Unexpected formula: {pretty_expr(body, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        existence_formula = make_forall_vars(existence_formula, args)
        if not alpha_equiv_with_defs(node.formula, existence_formula, context):
            msg = f"existence_formula is not matched with theorem: {pretty_expr(node.formula, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}existence_formula is matched with theorem: {pretty_expr(node.formula, context)}")
        context.add_decl(node)
        node.proofinfo.status = "OK"
        return True

    def check_deffununiq(self, node: DefFunUniq, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, fun_name: {node.fun_name}")
        if context.decl.equality is None:
            msg = "equality has not been declared yet"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        args, body = strip_forall_vars(context.decl.theorems[context.decl.deffuns[node.fun_name].theorem].conclusion)
        if isinstance(body, ExistsUniq):
            uniqueness_formula = Forall(node.token, body.var, Implies(node.token, body.body, AtomicFormula(node.token, context.decl.equality.equal, (MembershipLambda(node.token, Var(node.token, body.var.name)), MembershipLambda(node.token, Compound(node.token, RefDefFun(node.token, node.fun_name), tuple(args)))))))
        elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
            uniqueness_formula = Implies(node.token, body.left, Forall(node.token, body.right.var, Implies(node.token, body.right.body, AtomicFormula(node.token, context.decl.equality.equal, (MembershipLambda(node.token, Var(node.token, body.right.var.name)), MembershipLambda(node.token, Compound(node.token, RefDefFun(node.token, node.fun_name), tuple(args))))))))
        else:
            msg = f"Unexpected formula: {pretty_expr(body, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        uniqueness_formula = make_forall_vars(uniqueness_formula, args)
        if not alpha_equiv_with_defs(node.formula, uniqueness_formula, context):
            msg = f"uniqueness_formula is not matched with theorem: {pretty_expr(node.formula, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}uniqueness_formula is matched with theorem: {pretty_expr(node.formula, context)}")
        context.add_decl(node)
        node.proofinfo.status = "OK"
        return True

    def check_deffunterm(self, node: DefFunTerm, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, args: {node.args}, term: {pretty_expr(node.varterm, context)}")
        fv, _, fpt, _, fft, _ = collect_vars(node.varterm)
        if set(node.args) != set(fv) | set(fpt) | set(fft):
            msg = f"args are not matched with free vars: {set(fv) | set(fpt) | set(fft)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}args are mathced with free vars of term: {set(fv) | set(fpt) | set(fft)}")
        context.add_decl(node)
        node.proofinfo.status = "OK"
        return True

    def check_equality(self, node: Equality, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.equal.name}")
        if not self.check_equality_reflection(node.reflection, context, indent+1):
            node.proofinfo.status = "ERROR"
            return False
        if not self.check_equality_replacement(node.replacement, context, indent+1):
            node.proofinfo.status = "ERROR"
            return False
        context.add_decl(node)
        logger.debug(f"{debug_prefix}{node.equal.name} is registered as equality")
        node.proofinfo.status = "OK"
        return True

    def check_equality_reflection(self, node: EqualityReflection, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}Checking {node.equal.name} reflection theorem: {pretty_expr(node.evidence.conclusion, context)}")
        reflection = Forall(node.token, Var(node.token, "x"), AtomicFormula(node.token, node.equal, (MembershipLambda(node.token, Var(node.token, "x")), MembershipLambda(node.token, Var(node.token, "x")))))
        if not alpha_equiv_with_defs(node.evidence.conclusion, reflection, context):
            msg = f"Not matched with expected formula: {pretty_expr(reflection, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Matched with expected formula: {pretty_expr(reflection, context)}")
        node.proofinfo.status = "OK"
        return True

    def check_equality_replacement(self, node: EqualityReplacement, context: Context, indent: int):
        # debug_prefix = make_debug_prefix(node, indent)
        # error_prefix = make_error_prefix(node, indent)
        # for predicate in node.evidence:
        #     logger.debug(f"{debug_prefix}Checking {predicate} replacement theorem: {pretty_expr(node.evidence[predicate].conclusion, context)}")
        #     if predicate == node.equal.name:
        #         if isinstance(node.equal, PrimPred):
        #             arity = node.equal.arity
        #         elif isinstance(node.equal, DefPred):
        #             arity = len(node.equal.args)
        #         else:
        #             raise Exception("node.equal is not PrimPred or DefPred")
        #     else:
        #         arity = context.decl.primpreds[predicate].arity
        #     args_x: list[Var] = []
        #     args_y: list[Var] = []
        #     for i in range(arity):
        #         args_x.append(Var(f"x_{i}"))
        #         args_y.append(Var(f"y_{i}"))
        #     premise = Symbol(Pred(node.equal.name), (MembershipLambda(args_x[0]), MembershipLambda(args_y[0])))
        #     for i in range(1, arity):
        #         premise = And(premise, Symbol(Pred(node.equal.name), (MembershipLambda(args_x[i]), MembershipLambda(args_y[i]))))
        #     conclusion = Implies(Symbol(Pred(predicate), tuple(args_x)), Symbol(Pred(predicate), tuple(args_y)))
        #     replacement = Implies(premise, conclusion)
        #     for arg in reversed(args_y):
        #         replacement = Forall(arg, replacement)
        #     for arg in reversed(args_x):
        #         replacement = Forall(arg, replacement)
        #     if not alpha_equiv_with_defs(node.evidence[predicate].conclusion, replacement, context):
        #         logger.error(f"{error_prefix}Not matched with expected formula: {pretty_expr(replacement, context)}")
        #         node.proofinfo.status = "ERROR"
        #         return False
        #     logger.debug(f"{debug_prefix}Matched with expected formula: {pretty_expr(replacement, context)}")
        node.proofinfo.status = "OK"
        return True

    def check_membership(self, node: Membership, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.membership.name}")
        context.add_decl(node)
        logger.debug(f"{debug_prefix}{node.membership.name} is registered as membership")
        node.proofinfo.status = "OK"
        return True

    def check_control(self, node: Control, context: Context, indent: int):
        error_prefix = make_error_prefix(node, indent)

        node.proofinfo.ctrl_ctx = deepcopy(context.ctrl)

        if isinstance(node, Any):
            return self.check_any(node, context, indent)
        elif isinstance(node, Assume):
            return self.check_assume(node, context, indent)
        elif isinstance(node, Divide):
            return self.check_divide(node, context, indent)
        elif isinstance(node, Some):
            return self.check_some(node, context, indent)
        elif isinstance(node, Deny):
            return self.check_deny(node, context, indent)
        elif isinstance(node, Contradict):
            return self.check_contradict(node, context, indent)
        elif isinstance(node, Explode):
            return self.check_explode(node, context, indent)
        elif isinstance(node, Apply):
            return self.check_apply(node, context, indent)
        elif isinstance(node, Lift):
            return self.check_lift(node, context, indent)
        elif isinstance(node, Characterize):
            return self.check_characterize(node, context, indent)
        elif isinstance(node, Invoke):
            return self.check_invoke(node, context, indent)
        elif isinstance(node, Expand):
            return self.check_expand(node, context, indent)
        elif isinstance(node, Fold):
            return self.check_fold(node, context, indent)
        elif isinstance(node, Pad):
            return self.check_pad(node, context, indent)
        elif isinstance(node, Split):
            return self.check_split(node, context, indent)
        elif isinstance(node, Connect):
            return self.check_connect(node, context, indent)
        elif isinstance(node, Substitute):
            return self.check_substitute(node, context, indent)
        elif isinstance(node, Show):
            return self.check_show(node, context, indent)
        elif isinstance(node, Assert):
            return self.check_assert(node, context, indent)
        elif isinstance(node, InvalidControl):
            msg = "InvalidControl"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            return False
        else:
            msg = f"Unsupported node {node}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            return False

    def check_any(self, node: Any, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        for item in node.items:
            if item.name in context.ctrl.used_names or item.name in context.decl.used_names:
                msg = f"{pretty_expr(item, context)} is already used"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
        logger.debug(f"{debug_prefix}Taking {node.items}")
        local_vars = [item for item in node.items if isinstance(item, Var)]
        local_pred_tmpls = [item for item in node.items if isinstance(item, PredTemplate)]
        local_fun_tmpls = [item for item in node.items if isinstance(item, FunTemplate)]
        local_ctx = context.add_ctrl(local_vars, [], local_pred_tmpls, local_fun_tmpls)
        for stmt in node.body:
            if not self.check_control(stmt, local_ctx, indent+1):
                node.proofinfo.status = "ERROR"
                return False
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        local_goal = local_ctx.ctrl.formulas[-1]
        if isinstance(local_goal, Bottom):
            msg = "Bottom cannot be generalized"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}derived local_goal: {pretty_expr(local_goal, context)}")
        goal = local_goal
        for item in reversed(node.items):
            goal = Forall(node.token, item, goal)
        node.proofinfo.status = "OK"
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = local_vars
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [local_goal]
        add_conclusion(context, goal)
        logger.debug(f"{debug_prefix}Generalized to {pretty_expr(goal, context)}")
        return True

    def check_assume(self, node: Assume, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}premise={pretty_expr(node.premise, context)}")
        local_ctx = context.add_ctrl([], [node.premise], [], [])
        for stmt in node.body:
            if not self.check_control(stmt, local_ctx, indent+1):
                node.proofinfo.status = "ERROR"
                return False
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        goal = local_ctx.ctrl.formulas[-1]
        if isinstance(goal, Bottom):
            msg = "Bottom is not allowed as goal"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}derived goal: {pretty_expr(goal, context)}")
        implication = Implies(node.token, node.premise, goal)
        node.proofinfo.status = "OK"
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [implication]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = [node.premise]
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, implication)
        logger.debug(f"{debug_prefix}Added implication {pretty_expr(implication, context)}")
        return True

    def check_divide(self, node: Divide, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if not goal_in_context(node.fact, context):
            msg = f"Not fact: {pretty_expr(node.fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        fact = get_fact(node.fact, context, node.token, True)
        connected_premise = Or(node.token, node.cases[0].premise, node.cases[1].premise)
        i = 2
        while i < len(node.cases):
            connected_premise = Or(node.token, connected_premise, node.cases[i].premise)
            i += 1
        if alpha_equiv_with_defs(connected_premise, fact, context):
            logger.debug(f"{debug_prefix}mathched: fact={pretty_expr(fact, context)}, connected_premise={pretty_expr(connected_premise, context)}")
        else:
            msg = f"not matched: fact={pretty_expr(fact, context)}, conected_premise={pretty_expr(connected_premise, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}fact={pretty_expr(fact, context)}")
        local_ctx = context.copy_ctrl()
        goals: list[Bottom | Formula] = []
        for stmt in node.cases:
            if not self.check_case(stmt, local_ctx, indent+1):
                node.proofinfo.status = "ERROR"
                return False
            if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
                msg = "Local context must extend the parent context"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            goal = local_ctx.ctrl.formulas[-1]
            logger.debug(f"{debug_prefix}derived goal: {pretty_expr(goal, context)}")
            goals.append(goal)
        for i in range(len(goals) - 1):
            if not alpha_equiv_with_defs(goals[i], goals[i + 1], context):
                msg = f"Not matched: goals[{i}]: {pretty_expr(goals[i], context)}, goals[{i + 1}]: {pretty_expr(goals[i + 1], context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [goals[0]]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [goals[0]]
        add_conclusion(context, goals[0])
        logger.debug(f"{debug_prefix}derived in all cases: {pretty_expr(goals[0], context)}")
        return True

    def check_case(self, node: Case, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}premise={pretty_expr(node.premise, context)}")
        local_ctx = context.add_ctrl([], [node.premise], [], [])
        for stmt in node.body:
            if not self.check_control(stmt, local_ctx, indent+1):
                node.proofinfo.status = "ERROR"
                return False
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {pretty_expr(goal, context)}")
        node.proofinfo.status = "OK"
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = [node.premise]
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, goal)
        logger.debug(f"{debug_prefix}Added goal {pretty_expr(goal, context)}")
        return True

    def check_some(self, node: Some, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if not goal_in_context(node.fact, context):
            msg = f"not derivable: {pretty_expr(node.fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}derivable: {pretty_expr(node.fact, context)}")
        fact = get_fact(node.fact, context, node.token, True)
        if isinstance(fact, Exists):
            vars, body = strip_exists_vars(fact, Exists)
            body = make_exists_vars(body, Exists, [bound for bound, free in zip(vars, node.items) if free is None])
        elif isinstance(fact, ExistsUniq):
            vars, body= strip_exists_vars(fact, ExistsUniq)
            if len(vars) != 1:
                msg = f"Unexpected len(vars): {len(vars)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
        else:
            msg = f"Unexpected type: {type(fact)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        if len(vars) != len(node.items):
            msg = f"len(vars): {len(vars)}, len(node.items): {len(node.items)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        for item in node.items:
            if item is None:
                continue
            if item.name in context.ctrl.used_names or item.name in context.decl.used_names:
                msg = f"{pretty_expr(item, context)} is already used"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
        mapping: dict[Term, Term] = {bound: free for bound, free in zip(vars, node.items) if free is not None}
        renamed_body, renamed_mapping = alpha_safe_formula(body, mapping, context)
        existence = Substitutor(renamed_mapping, context).substitute_formula(renamed_body)
        if isinstance(fact, Exists):
            premises: list[Bottom | Formula] = [existence]
        else:
            fv, bv, fpt, bpt, fft, bft = collect_vars(existence)
            var = fresh_var(vars[0], fv | bv | fpt | bpt | fft | bft, context)
            body = Substitutor(({vars[0]: var}, {}, {}), context).substitute_formula(existence)
            if context.decl.equality is None:
                msg = "equality has not been declared yet"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            uniqueness = Forall(node.token, var, Implies(node.token, body, AtomicFormula(node.token, context.decl.equality.equal, (MembershipLambda(node.token, var), MembershipLambda(node.token, vars[0])))))
            premises: list[Bottom | Formula] = [existence, uniqueness]
        logger.debug(f"{debug_prefix}Taking {node.items}, premise={pretty_expr(existence, context)}")
        local_vars = [item for item in node.items if isinstance(item, Var)]
        local_ctx = context.add_ctrl(local_vars, premises, [], [])
        for stmt in node.body:
            if not self.check_control(stmt, local_ctx, indent+1):
                node.proofinfo.status = "ERROR"
                return False
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {pretty_expr(goal, context)}")
        if isinstance(goal, Formula):
            goal_fv, _, _, _, _, _ = collect_vars(goal)
            for fv in goal_fv:
                if fv in local_vars:
                    msg = f"Conclusion depends on local variable {pretty_expr(fv, context)}"
                    self.add_lsp_error(node, msg, context)
                    logger.error(f"{error_prefix}{msg}")
                    node.proofinfo.status = "ERROR"
                    return False
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [node.fact]
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = list(local_vars)
        node.proofinfo.local_premise = premises
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, goal)
        logger.debug(f"{debug_prefix}Added goal {pretty_expr(goal, context)}")
        return True

    def check_deny(self, node: Deny, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}premise={pretty_expr(node.premise, context)}")
        local_ctx = context.add_ctrl([], [node.premise], [], [])
        for stmt in node.body:
            if not self.check_control(stmt, local_ctx, indent+1):
                node.proofinfo.status = "ERROR"
                return False
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {pretty_expr(goal, context)}")
        if isinstance(goal, Bottom):
            if isinstance(node.premise, Not):
                conclusion = node.premise.body
            else:
                conclusion = Not(node.token, node.premise)
            node.proofinfo.status = "OK"
            node.proofinfo.premises = []
            node.proofinfo.conclusions = [conclusion]
            node.proofinfo.local_vars = []
            node.proofinfo.local_premise = [node.premise]
            node.proofinfo.local_conclusion = [goal]
            add_conclusion(context, conclusion)
            logger.debug(f"{debug_prefix}contradiction is derived; added {pretty_expr(conclusion, context)}")
            return True
        else:
            msg = "conradiction has not been deried"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False

    def check_contradict(self, node: Contradict, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if not goal_in_context(node.contradiction, context):
            msg = f"Cannot derive {pretty_expr(node.contradiction, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        if not goal_in_context(Not(node.token, node.contradiction), context):
            msg = f"Cannot derive {pretty_expr(Not(node.token, node.contradiction), context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Derived contradiction: {pretty_expr(node.contradiction, context)}, {pretty_expr(Not(node.token, node.contradiction), context)}")
        conclusion = Bottom()
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [node.contradiction, Not(node.token, node.contradiction)]
        node.proofinfo.conclusions = [conclusion]
        add_conclusion(context, conclusion)
        return True

    def check_explode(self, node: Explode, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if goal_in_context(Bottom(), context):
            node.proofinfo.status = "OK"
            node.proofinfo.premises = [Bottom()]
            node.proofinfo.conclusions = [node.conclusion]
            add_conclusion(context, node.conclusion)
            logger.debug(f"{debug_prefix}added {pretty_expr(node.conclusion, context)}")
            return True
        else:
            msg = "contradiction has not been derived"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False

    def check_apply(self, node: Apply, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if not goal_in_context(node.fact, context):
            msg = f"Cannot derive fact: {pretty_expr(node.fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Drivable fact: {pretty_expr(node.fact, context)}")
        fact = get_fact(node.fact, context, node.token, True)
        items, body = strip_forall_vars(fact)
        body = make_forall_vars(body, [item for item, term in zip(items, node.terms) if term is None])
        mapping: dict[Term, Term] = {}
        for item, term in zip(items, node.terms):
            if term is None:
                continue
            if isinstance(item, PredTerm) and item.arity == 1 and isinstance(term, VarTerm):
                mapping[item] = MembershipLambda(node.token, term)
            else:
                mapping[item] = term
        renamed_body, renamed_map = alpha_safe_formula(body, mapping, context)
        logger.debug(f"{debug_prefix}Instantiable: mapping={mapping}")
        instantiation = Substitutor(renamed_map, context).substitute_formula(renamed_body)
        logger.debug(f"{debug_prefix}\\forall-elimination is done: instantiation={pretty_expr(instantiation, context)}")
        if node.invoke == "none":
            node.proofinfo.premises = [node.fact]
            node.proofinfo.conclusions = [instantiation]
            add_conclusion(context, instantiation)
            logger.debug(f"{debug_prefix}Added {pretty_expr(instantiation, context)}")
        elif node.invoke == "invoke":
            if not isinstance(instantiation, Implies):
                msg = "instantiation is not Implies object"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}instantiation is Implies object")
            if not goal_in_context(instantiation.left, context):
                msg = f"Left of instantiation is not derivable: {pretty_expr(instantiation.left, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}Left of instantiation is derivable: {pretty_expr(instantiation.left, context)}")
            node.proofinfo.premises = [node.fact, instantiation.left]
            node.proofinfo.conclusions = [instantiation.right]
            add_conclusion(context, instantiation.right)
            logger.debug(f"{debug_prefix}Added {pretty_expr(instantiation.right, context)}")
        elif node.invoke == "invoke-rightward":
            if not isinstance(instantiation, Iff):
                msg = "instantiation is not Iff object"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}instantiation is Iff object")
            if not goal_in_context(instantiation.left, context):
                msg = f"Left of instantiation is not derivable: {pretty_expr(instantiation.left, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}Left of instantiation is derivable: {pretty_expr(instantiation.left, context)}")
            node.proofinfo.premises = [node.fact, instantiation.left]
            node.proofinfo.conclusions = [instantiation.right]
            add_conclusion(context, instantiation.right)
            logger.debug(f"{debug_prefix}Added {pretty_expr(instantiation.right, context)}")
        elif node.invoke == "invoke-leftward":
            if not isinstance(instantiation, Iff):
                msg = "instantiation is not Iff object"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}instantiation is Iff object")
            if not goal_in_context(instantiation.right, context):
                msg = f"Right of instantiation is not derivable: {pretty_expr(instantiation.right, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}Right of instantiation is derivable: {pretty_expr(instantiation.right, context)}")
            node.proofinfo.premises = [node.fact, instantiation.right]
            node.proofinfo.conclusions = [instantiation.left]
            add_conclusion(context, instantiation.left)
            logger.debug(f"{debug_prefix}Added {pretty_expr(instantiation.left, context)}")
        else:
            msg = f"Unexpected invoke option {node.invoke}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        node.proofinfo.status = "OK"
        return True

    def check_lift(self, node: Lift, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}Target conclusion: {pretty_expr(node.conclusion, context)}")
        items, body = strip_exists_vars(node.conclusion, Exists)
        body = make_exists_vars(body, Exists, [item for item, term in zip(items, node.varterms) if term is None])
        mapping: dict[Term, Term] = {item: term for item, term in zip(items, node.varterms) if term is not None}
        renamed_body, renamed_mapping = alpha_safe_formula(body, mapping, context)
        fact = Substitutor(renamed_mapping, context).substitute_formula(renamed_body)
        if not goal_in_context(fact, context):
            msg = f"Not fact: {pretty_expr(fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Fact: {pretty_expr(fact, context)}")
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        logger.debug(f"{debug_prefix}Added {pretty_expr(node.conclusion, context)}")
        return True

    def check_characterize(self, node: Characterize, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        _, used_bound_vars, _, used_bound_pred_tmpls, _, used_bound_fun_tmpls = collect_vars(node.conclusion.body)
        fv, bv, fpt, bpt, fft, bft = collect_vars(node.varterm)
        vardash = fresh_var(Var(node.token, node.conclusion.var.name + "'"), used_bound_vars | used_bound_pred_tmpls | used_bound_fun_tmpls | fv | bv | fpt | bpt | fft | bft, context)
        renamed_conclusion, _ = alpha_safe_formula(node.conclusion, {node.conclusion.var: node.varterm}, context)
        if not isinstance(renamed_conclusion, ExistsUniq):
            msg = f"renamed_conclusion is not ExistsUniq object: {pretty_expr(renamed_conclusion, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        existence = Substitutor(({renamed_conclusion.var: node.varterm}, {}, {}), context).substitute_formula(renamed_conclusion.body)
        existence_dash = Substitutor(({renamed_conclusion.var: vardash}, {}, {}), context).substitute_formula(renamed_conclusion.body)
        if context.decl.equality is None:
            msg = "equality has not been declared yet"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        fact = And(node.token, existence, Forall(node.token, vardash, Implies(node.token, existence_dash, AtomicFormula(node.token, context.decl.equality.equal, (MembershipLambda(node.token, vardash), MembershipLambda(node.token, node.varterm))))))
        if not goal_in_context(fact, context):
            msg = f"Not fact: {pretty_expr(fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Fact: {pretty_expr(fact, context)}")
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        return True

    def check_invoke(self, node: Invoke, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if not goal_in_context(node.fact, context):
            msg = f"Not fact: {pretty_expr(node.fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}fact: {pretty_expr(node.fact, context)}")
        if node.direction == "none":
            if not isinstance(node.fact, Implies):
                msg = f"Not Implies object: {pretty_expr(node.fact, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}Implies object: {pretty_expr(node.fact, context)}")
            if not goal_in_context(node.fact.left, context):
                msg = f"Left of Implies object not derived: {pretty_expr(node.fact.left, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}Left of Implies object derived: {pretty_expr(node.fact.left, context)}")
            node.proofinfo.premises = [node.fact, node.fact.left]
            node.proofinfo.conclusions = [node.fact.right]
            add_conclusion(context, node.fact.right)
            logger.debug(f"{debug_prefix}Right of Implies object added: {pretty_expr(node.fact.right, context)}")
        elif node.direction == "rightward":
            if not isinstance(node.fact, Iff):
                msg = f"Not Iff object: {pretty_expr(node.fact, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}Iff object: {pretty_expr(node.fact, context)}")
            if not goal_in_context(node.fact.left, context):
                msg = f"Left of Iff object not derived: {pretty_expr(node.fact.left, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}Left of Iff object derived: {pretty_expr(node.fact.left, context)}")
            node.proofinfo.premises = [node.fact, node.fact.left]
            node.proofinfo.conclusions = [node.fact.right]
            add_conclusion(context, node.fact.right)
            logger.debug(f"{debug_prefix}Right of Iff object added: {pretty_expr(node.fact.right, context)}")
        elif node.direction == "leftward":
            if not isinstance(node.fact, Iff):
                msg = f"Not Iff object: {pretty_expr(node.fact, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}Iff object: {pretty_expr(node.fact, context)}")
            if not goal_in_context(node.fact.right, context):
                msg = f"Right of Iff object not derived: {pretty_expr(node.fact.right, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}Right of Iff object derived: {pretty_expr(node.fact.right, context)}")
            node.proofinfo.premises = [node.fact, node.fact.right]
            node.proofinfo.conclusions = [node.fact.left]
            add_conclusion(context, node.fact.left)
            logger.debug(f"{debug_prefix}Left of Iff object added: {pretty_expr(node.fact.left, context)}")
        else:
            msg = f"Unexpected direction: {node.direction}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        node.proofinfo.status = "OK"
        return True

    def check_expand(self, node: Expand, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if not goal_in_context(node.fact, context):
            msg = f"Not fact: {pretty_expr(node.fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}fact: {pretty_expr(node.fact, context)}")
        fact = get_fact(node.fact, context, node.token)
        conclusion = DefExpander(node.defs, node.indexes).expand_defs_formula(fact, context)
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [conclusion]
        add_conclusion(context, conclusion)
        logger.debug(f"{debug_prefix}Added: {pretty_expr(conclusion, context)}")
        return True

    def check_fold(self, node: Fold, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        fact = DefExpander(node.defs, node.indexes).expand_defs_formula(node.conclusion, context)
        if not goal_in_context(fact, context):
            msg = f"Not fact: {pretty_expr(fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}fact: {pretty_expr(fact, context)}")
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        logger.debug(f"{debug_prefix}Added: {pretty_expr(node.conclusion, context)}")
        return True

    def check_pad(self, node: Pad, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if not goal_in_context(node.fact, context):
            msg = f"Not derivable: {pretty_expr(node.fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Derivable: {pretty_expr(node.fact, context)}")
        fact = get_fact(node.fact, context, node.token)
        fact_parts = flatten_op(fact, Or)
        conclusion_parts = flatten_op(node.conclusion, Or)
        if not all(any(alpha_equiv_with_defs(c, f, context) for c in conclusion_parts) for f in fact_parts):
            msg = f"neither left or right not derivable: {pretty_expr(node.conclusion, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        logger.debug(f"{debug_prefix}Derivable, added {pretty_expr(node.conclusion, context)}")
        return True

    def check_split(self, node: Split, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if not goal_in_context(node.fact, context):
            msg = f"Not derivable: {pretty_expr(node.fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        fact = get_fact(node.fact, context, node.token, True)
        logger.debug(f"{debug_prefix}Derivable: {pretty_expr(fact, context)}")
        if isinstance(fact, And):
            logger.debug(f"{debug_prefix}And object: {pretty_expr(fact, context)}")
            fact_parts = flatten_op(fact, And)
            node.proofinfo.premises = [fact]
            if node.index is None:
                node.proofinfo.conclusions = fact_parts
                for f in fact_parts:
                    add_conclusion(context, f)
                    logger.debug(f"{debug_prefix}added {pretty_expr(f, context)}")
            else:
                if node.index <= 0 or node.index > len(fact_parts):
                    msg = f"index out of range, index: {node.index}, len(fact_parts): {len(fact_parts)}"
                    self.add_lsp_error(node, msg, context)
                    logger.error(f"{error_prefix}{msg}")
                    node.proofinfo.status = "ERROR"
                    return False
                f = fact_parts[node.index - 1]
                node.proofinfo.conclusions = [f]
                add_conclusion(context, f)
                logger.debug(f"{debug_prefix}added {pretty_expr(f, context)}")
            node.proofinfo.status = "OK"
            return True
        elif isinstance(fact, Iff):
            logger.debug(f"{debug_prefix}Iff object: {pretty_expr(fact, context)}")
            implication_rightward = Implies(node.token, fact.left, fact.right)
            implication_leftward = Implies(node.token, fact.right, fact.left)
            node.proofinfo.status = "OK"
            node.proofinfo.premises = [fact]
            node.proofinfo.conclusions = [implication_rightward, implication_leftward]
            add_conclusion(context, implication_rightward)
            add_conclusion(context, implication_leftward)
            logger.debug(f"{debug_prefix}added {pretty_expr(implication_rightward, context)}")
            logger.debug(f"{debug_prefix}added {pretty_expr(implication_leftward, context)}")
            return True
        else:
            msg = f"Not And or Iff object: {pretty_expr(fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False

    def check_connect(self, node: Connect, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if isinstance(node.conclusion, AtomicFormula):
            if not isinstance(node.conclusion.pred, RefDefPred):
                raise Exception(f"Unexpected type: {type(node.conclusion.pred)}")
            conclusion = DefExpander([node.conclusion.pred.name]).expand_defs_formula(node.conclusion, context)
        else:
            conclusion = node.conclusion
        if isinstance(conclusion, And):
            logger.debug(f"{debug_prefix}And object: {pretty_expr(conclusion, context)}")
            conclusion_parts = flatten_op(conclusion, And)
            for c in conclusion_parts:
                if not goal_in_context(c, context):
                    msg = f"Not derivable: {pretty_expr(c, context)}"
                    self.add_lsp_error(node, msg, context)
                    logger.error(f"{error_prefix}{msg}")
                    node.proofinfo.status = "ERROR"
                    return False
            node.proofinfo.status = "OK"
            node.proofinfo.premises = conclusion_parts
            node.proofinfo.conclusions = [node.conclusion]
            add_conclusion(context, node.conclusion)
            logger.debug(f"{debug_prefix}Derivable, added {pretty_expr(node.conclusion, context)}")
            return True
        elif isinstance(conclusion, Iff):
            logger.debug(f"{debug_prefix}Iff object: {pretty_expr(conclusion, context)}")
            implication_rightward = Implies(node.token, conclusion.left, conclusion.right)
            if not goal_in_context(implication_rightward, context):
                msg = f"Not derivable: {pretty_expr(implication_rightward, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            implication_leftward = Implies(node.token, conclusion.right, conclusion.left)
            if not goal_in_context(implication_leftward, context):
                msg = f"Not derivable: {pretty_expr(implication_leftward, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            node.proofinfo.status = "OK"
            node.proofinfo.premises = [implication_rightward, implication_leftward]
            node.proofinfo.conclusions = [node.conclusion]
            add_conclusion(context, node.conclusion)
            logger.debug(f"{debug_prefix}derivable, added {pretty_expr(node.conclusion, context)}")
            return True
        else:
            msg = f"Not And or Iff object: {pretty_expr(node.conclusion, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False

    def check_substitute(self, node: Substitute, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if not goal_in_context(node.fact, context):
            msg = f"Not fact: {pretty_expr(node.fact, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Fact: {pretty_expr(node.fact, context)}")
        fact = get_fact(node.fact, context, node.token)
        if context.decl.equality is None:
            msg = "equality has not been declared yet"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        premises_equal: list[str | AtomicFormula] = []
        for k, v in node.env.items():
            if not isinstance(k, VarTerm):
                raise Exception(f"Unexpected type: {type(k)}")
            if not isinstance(v, VarTerm):
                raise Exception(f"Unexpected type: {type(v)}")
            equation = AtomicFormula(node.token, context.decl.equality.equal, (MembershipLambda(node.token, k), MembershipLambda(node.token, v)))
            if not goal_in_context(equation, context):
                msg = f"Not fact: {pretty_expr(equation, context)}"
                self.add_lsp_error(node, msg, context)
                logger.error(f"{error_prefix}{msg}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}Fact: {pretty_expr(equation, context)}")
            premises_equal.append(equation)
        renamed_fact, mapping = alpha_safe_formula(fact, node.env, context, True)
        conclusion = Substitutor(mapping, context, node.indexes).substitute_formula(renamed_fact)
        logger.debug(f"{debug_prefix}conclusion: {pretty_expr(conclusion, context)}")
        logger.debug(f"{debug_prefix}Matched")
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [fact] + premises_equal
        node.proofinfo.conclusions = [conclusion]
        add_conclusion(context, conclusion)
        logger.debug(f"{debug_prefix}Added {pretty_expr(conclusion, context)}")
        return True

    def check_show(self, node: Show, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        logger.debug(f"{debug_prefix}Target conclusion: {pretty_expr(node.conclusion, context)}")
        local_ctx = context.copy_ctrl()
        for stmt in node.body:
            if not self.check_control(stmt, local_ctx, indent+1):
                node.proofinfo.status = "ERROR"
                return False
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {pretty_expr(goal, context)}")
        if not alpha_equiv_with_defs(node.conclusion, goal, context):
            msg = f"Not matched with target conclusion: {pretty_expr(node.conclusion, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Matched with target conclusion: {pretty_expr(node.conclusion, context)}")
        node.proofinfo.status = "OK"
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, goal)
        logger.debug(f"{debug_prefix}Added {pretty_expr(goal, context)}")
        return True

    def check_assert(self, node: Assert, context: Context, indent: int):
        debug_prefix = make_debug_prefix(node, indent)
        error_prefix = make_error_prefix(node, indent)
        if not goal_in_context(node.reference, context):
            msg = f"Not fact: {pretty_expr(node.reference, context)}"
            self.add_lsp_error(node, msg, context)
            logger.error(f"{error_prefix}{msg}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Fact: {pretty_expr(node.reference, context)}")
        formula = get_fact(node.reference, context, node.token)
        node.proofinfo.status = "OK"
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [formula]
        add_conclusion(context, formula)
        logger.debug(f"{debug_prefix}Added {pretty_expr(formula, context)}")
        return True

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
    file_handler = logging.FileHandler(os.path.join("logs", os.path.basename(path).replace(".proof", "_checker.log")), mode='w', encoding='utf-8')
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
    from splitter import split
    workspace = split(resolved_files, tokens_cache, resolver.source_cache)
    context = Context.init()
    from parser import Parser
    for file in workspace.resolved_files:
        for unit in workspace.file_units[file]:
            working_context = context.copy()
            Parser(unit).parse_unit(working_context)
            if Checker(unit).check_unit(working_context):
                context = working_context
            unit.context = context.copy()
    total_errors = sum(len(unit.diagnostics) for file in workspace.file_units.values() for unit in file)
    print(f"tota_errors: {total_errors}")
