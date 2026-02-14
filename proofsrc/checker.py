from lexer import Token
from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, AtomicFormula, And, Or, Implies, Forall, Exists, Not, Bottom, Iff, Axiom, Invoke, Expand, PrimPred, DefPred, DefCon, Pad, Split, Connect, ExistsUniq, Compound, RefDefCon, DefFun, DefFunTerm, Equality, Var, Substitute, Characterize, Show, Control, Formula, Declaration, PredTemplate, Term, DefConExist, DefConUniq, DefFunExist, DefFunUniq, Include, Assert, Fold, VarTerm, FunTemplate, RefDefPred, RefDefFun, InvalidDeclaration, InvalidControl, InvalidInclude, DeclarationUnit, RefFact, RefEquality
from logic_utils import Substitutor, DefExpander, ExprFormatter, expr_in_context, strip_forall_vars, strip_exists_vars, make_forall_vars, make_exists_vars, collect_vars, flatten_op, fresh_var, alpha_equiv_with_defs, alpha_safe_formula
from copy import deepcopy
from lsprotocol import types as lsp
from pygls import uris

import logging
logger = logging.getLogger("proof")

class CheckError(Exception):
    def __init__(self, token: Token, msg: str) -> None:
        self.token = token
        self.msg = msg

def goal_in_context(goal: Bottom | Formula, context: Context) -> bool:
    if isinstance(goal, AtomicFormula) and context.decl.equality is not None and isinstance(goal.pred, RefEquality) and goal.args[0] == goal.args[1]:
        return True
    else:
        return expr_in_context(goal, context)

def get_fact(fact: RefFact | Formula, context: Context, token: Token, expand_symbol: bool = False) -> Formula:
    if isinstance(fact, RefFact):
        fact = context.decl.get_reference(fact, token)
    elif not isinstance(fact, Formula):
        raise Exception(f"Unexpected type {type(fact)}")
    if expand_symbol and isinstance(fact, AtomicFormula) and isinstance(fact.pred, RefDefPred):
        fact = DefExpander([fact.pred.name], {fact.pred.name: [1]}).expand_defs_formula(fact, context)
    return fact

def add_conclusion(context: Context, conclusion: Bottom | Formula) -> None:
    context.ctrl.formulas.append(conclusion)

def make_debug_prefix(node: Declaration | Control, indent: int) -> str:
    return "  " * indent + f"[{node.__class__.__name__}] "

class Checker:
    def __init__(self, unit: DeclarationUnit) -> None:
        self.unit = unit

    def make_error_prefix(self, node: Declaration | Control, indent: int) -> str:
        return "  " * indent + f"❌ [{node.__class__.__name__}] {self.unit.tokens[self.unit.node_to_token[id(node)][0]].info()} "

    def add_lsp_error(self, token: Token, message: str, context: Context):
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

        node.proofinfo.ctrl_ctx = deepcopy(context.ctrl)

        try:
            if isinstance(node, PrimPred):
                self.check_primpred(node, context, indent)
            elif isinstance(node, Axiom):
                self.check_axiom(node, context, indent)
            elif isinstance(node, Theorem):
                self.check_theorem(node, context, indent)
            elif isinstance(node, DefPred):
                self.check_defpred(node, context, indent)
            elif isinstance(node, DefCon):
                self.check_defcon(node, context, indent)
            elif isinstance(node, DefConExist):
                self.check_defconexist(node, context, indent)
            elif isinstance(node, DefConUniq):
                self.check_defconuniq(node, context, indent)
            elif isinstance(node, DefFun):
                self.check_deffun(node, context, indent)
            elif isinstance(node, DefFunExist):
                self.check_deffunexist(node, context, indent)
            elif isinstance(node, DefFunUniq):
                self.check_deffununiq(node, context, indent)
            elif isinstance(node, DefFunTerm):
                self.check_deffunterm(node, context, indent)
            elif isinstance(node, Equality):
                self.check_equality(node, context, indent)
            elif isinstance(node, InvalidDeclaration):
                msg = "InvalidDeclaration"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            else:
                msg = f"Unsupported node {node}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            node.proofinfo.status = "OK"
            return True
        except CheckError as e:
            self.add_lsp_error(e.token, e.msg, context)
            logger.error(f"{self.make_error_prefix(node, indent)}{e.msg}")
            node.proofinfo.status = "ERROR"
            return False

    def check_primpred(self, node: PrimPred, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, arity: {node.arity}")
        context.add_decl(node)

    def check_axiom(self, node: Axiom, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, conclusion: {ExprFormatter(context).pretty_expr(node.conclusion)}")
        context.add_decl(node)

    def check_theorem(self, node: Theorem, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}{node.name}: {ExprFormatter(context).pretty_expr(node.conclusion)}")
        local_ctx = context.copy_ctrl()
        for stmt in node.proof:
            self.check_control(stmt, local_ctx, indent+1)
        if goal_in_context(node.conclusion, local_ctx):
            logger.debug(f"{debug_prefix}{node.name} proved: {ExprFormatter(context).pretty_expr(node.conclusion)}")
            context.add_decl(node)
        else:
            msg = f"{node.name} not proved: {ExprFormatter(context).pretty_expr(node.conclusion)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)

    def check_defpred(self, node: DefPred, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, args: {node.args}, formula: {ExprFormatter(context).pretty_expr(node.formula)}")
        context.add_decl(node)

    def check_defcon(self, node: DefCon, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, theorem: {node.theorem}")
        existsuniq = context.decl.theorems[node.theorem].conclusion
        if not isinstance(existsuniq, ExistsUniq):
            msg = f"Not ExistsUniq object: {ExprFormatter(context).pretty_expr(existsuniq)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}ExistsUniq object: {ExprFormatter(context).pretty_expr(existsuniq)}")
        context.add_decl(node)

    def check_defconexist(self, node: DefConExist, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, con_name: {node.con_name}")
        existsuniq = context.decl.theorems[context.decl.defcons[node.con_name].theorem].conclusion
        if not isinstance(existsuniq, ExistsUniq):
            msg = f"Not ExistsUniq object: {ExprFormatter(context).pretty_expr(existsuniq)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}ExistsUniq object: {ExprFormatter(context).pretty_expr(existsuniq)}")
        existence_formula = Substitutor(({existsuniq.var: RefDefCon(node.con_name)}, {}, {}), context).substitute_formula(existsuniq.body)
        if not alpha_equiv_with_defs(node.formula, existence_formula, context):
            msg = f"existence_formula is not matched with theorem: {ExprFormatter(context).pretty_expr(node.formula)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}existence_formula is matched with theorem: {ExprFormatter(context).pretty_expr(node.formula)}")
        context.add_decl(node)

    def check_defconuniq(self, node: DefConUniq, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, con_name: {node.con_name}")
        existsuniq = context.decl.theorems[context.decl.defcons[node.con_name].theorem].conclusion
        if not isinstance(existsuniq, ExistsUniq):
            msg = f"Not ExistsUniq object: {ExprFormatter(context).pretty_expr(existsuniq)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}ExistsUniq object: {ExprFormatter(context).pretty_expr(existsuniq)}")
        fv, bv, fpt, bpt, fft, bft = collect_vars(existsuniq.body)
        var = fresh_var(existsuniq.var, fv | bv | fpt | bpt | fft | bft, context)
        body = Substitutor(({existsuniq.var: var}, {}, {}), context).substitute_formula(existsuniq.body)
        if context.decl.equality is None:
            msg = "equality has not been declared yet"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        uniqueness_formula = Forall(var, Implies(body, AtomicFormula(RefEquality(context.decl.equality.ref.name), (var, RefDefCon(node.con_name)))))
        if not alpha_equiv_with_defs(node.formula, uniqueness_formula, context):
            msg = f"uniqueness_formula is not matched with theorem: {ExprFormatter(context).pretty_expr(node.formula)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}uniqueness_formula is matched with theorem: {ExprFormatter(context).pretty_expr(node.formula)}")
        context.add_decl(node)

    def check_deffun(self, node: DefFun, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, theorem: {node.theorem}")
        context.add_decl(node)

    def check_deffunexist(self, node: DefFunExist, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, fun_name: {node.fun_name}")
        args, body = strip_forall_vars(context.decl.theorems[context.decl.deffuns[node.fun_name].theorem].conclusion)
        if isinstance(body, ExistsUniq):
            existence_formula = Substitutor(({body.var: Compound(RefDefFun(node.fun_name), tuple(args))}, {}, {}), context).substitute_formula(body.body)
        elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
            existence_formula = Implies(body.left, Substitutor(({body.right.var: Compound(RefDefFun(node.fun_name), tuple(args))}, {}, {}), context).substitute_formula(body.right.body))
        else:
            msg = f"Unexpected formula: {ExprFormatter(context).pretty_expr(body)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        existence_formula = make_forall_vars(existence_formula, args)
        if not alpha_equiv_with_defs(node.formula, existence_formula, context):
            msg = f"existence_formula is not matched with theorem: {ExprFormatter(context).pretty_expr(node.formula)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}existence_formula is matched with theorem: {ExprFormatter(context).pretty_expr(node.formula)}")
        context.add_decl(node)

    def check_deffununiq(self, node: DefFunUniq, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, fun_name: {node.fun_name}")
        if context.decl.equality is None:
            msg = "equality has not been declared yet"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        args, body = strip_forall_vars(context.decl.theorems[context.decl.deffuns[node.fun_name].theorem].conclusion)
        if isinstance(body, ExistsUniq):
            uniqueness_formula = Forall(body.var, Implies(body.body, AtomicFormula(RefEquality(context.decl.equality.ref.name), (Var(body.var.name), Compound(RefDefFun(node.fun_name), tuple(args))))))
        elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
            uniqueness_formula = Implies(body.left, Forall(body.right.var, Implies(body.right.body, AtomicFormula(RefEquality(context.decl.equality.ref.name), (Var(body.right.var.name), Compound(RefDefFun(node.fun_name), tuple(args)))))))
        else:
            msg = f"Unexpected formula: {ExprFormatter(context).pretty_expr(body)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        uniqueness_formula = make_forall_vars(uniqueness_formula, args)
        if not alpha_equiv_with_defs(node.formula, uniqueness_formula, context):
            msg = f"uniqueness_formula is not matched with theorem: {ExprFormatter(context).pretty_expr(node.formula)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}uniqueness_formula is matched with theorem: {ExprFormatter(context).pretty_expr(node.formula)}")
        context.add_decl(node)

    def check_deffunterm(self, node: DefFunTerm, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.name}, args: {node.args}, term: {ExprFormatter(context).pretty_expr(node.varterm)}")
        fv, _, fpt, _, fft, _ = collect_vars(node.varterm)
        if set(node.args) != set(fv) | set(fpt) | set(fft):
            msg = f"args are not matched with free vars: {set(fv) | set(fpt) | set(fft)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}args are mathced with free vars of term: {set(fv) | set(fpt) | set(fft)}")
        context.add_decl(node)

    def check_equality(self, node: Equality, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}name: {node.ref.name}")
        context.add_decl(node)
        logger.debug(f"{debug_prefix}{node.ref.name} is registered as equality")

    def check_control(self, node: Control, context: Context, indent: int) -> None:

        node.proofinfo.ctrl_ctx = deepcopy(context.ctrl)

        try:
            if isinstance(node, Any):
                self.check_any(node, context, indent)
            elif isinstance(node, Assume):
                self.check_assume(node, context, indent)
            elif isinstance(node, Divide):
                self.check_divide(node, context, indent)
            elif isinstance(node, Some):
                self.check_some(node, context, indent)
            elif isinstance(node, Deny):
                self.check_deny(node, context, indent)
            elif isinstance(node, Case):
                self.check_case(node, context, indent)
            elif isinstance(node, Contradict):
                self.check_contradict(node, context, indent)
            elif isinstance(node, Explode):
                self.check_explode(node, context, indent)
            elif isinstance(node, Apply):
                self.check_apply(node, context, indent)
            elif isinstance(node, Lift):
                self.check_lift(node, context, indent)
            elif isinstance(node, Characterize):
                self.check_characterize(node, context, indent)
            elif isinstance(node, Invoke):
                self.check_invoke(node, context, indent)
            elif isinstance(node, Expand):
                self.check_expand(node, context, indent)
            elif isinstance(node, Fold):
                self.check_fold(node, context, indent)
            elif isinstance(node, Pad):
                self.check_pad(node, context, indent)
            elif isinstance(node, Split):
                self.check_split(node, context, indent)
            elif isinstance(node, Connect):
                self.check_connect(node, context, indent)
            elif isinstance(node, Substitute):
                self.check_substitute(node, context, indent)
            elif isinstance(node, Show):
                self.check_show(node, context, indent)
            elif isinstance(node, Assert):
                self.check_assert(node, context, indent)
            elif isinstance(node, InvalidControl):
                msg = "InvalidControl"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            else:
                msg = f"Unsupported node {node}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            node.proofinfo.status = "OK"
        except CheckError as e:
            logger.error(f"{self.make_error_prefix(node, indent)}{e.msg}")
            node.proofinfo.status = "ERROR"
            raise

    def check_any(self, node: Any, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        for item in node.items:
            if item.name in context.ctrl.used_names or item.name in context.decl.used_names:
                msg = f"{ExprFormatter(context).pretty_expr(item)} is already used"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(item)][0]], msg)
        logger.debug(f"{debug_prefix}Taking {node.items}")
        local_vars = [item for item in node.items if isinstance(item, Var)]
        local_pred_tmpls = [item for item in node.items if isinstance(item, PredTemplate)]
        local_fun_tmpls = [item for item in node.items if isinstance(item, FunTemplate)]
        local_ctx = context.add_ctrl(local_vars, [], local_pred_tmpls, local_fun_tmpls)
        for stmt in node.body:
            self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        local_goal = local_ctx.ctrl.formulas[-1]
        if isinstance(local_goal, Bottom):
            msg = "Bottom cannot be generalized"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}derived local_goal: {ExprFormatter(context).pretty_expr(local_goal)}")
        goal = local_goal
        for item in reversed(node.items):
            goal = Forall(item, goal)
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = local_vars
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [local_goal]
        add_conclusion(context, goal)
        logger.debug(f"{debug_prefix}Generalized to {ExprFormatter(context).pretty_expr(goal)}")

    def check_assume(self, node: Assume, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}premise={ExprFormatter(context).pretty_expr(node.premise)}")
        local_ctx = context.add_ctrl([], [node.premise], [], [])
        for stmt in node.body:
            self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        goal = local_ctx.ctrl.formulas[-1]
        if isinstance(goal, Bottom):
            msg = "Bottom is not allowed as goal"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(context).pretty_expr(goal)}")
        implication = Implies(node.premise, goal)
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [implication]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = [node.premise]
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, implication)
        logger.debug(f"{debug_prefix}Added implication {ExprFormatter(context).pretty_expr(implication)}")

    def check_divide(self, node: Divide, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context):
                msg = f"Not fact: {ExprFormatter(context).pretty_expr(node.fact)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        fact = get_fact(node.fact, context, self.unit.tokens[self.unit.node_to_token[id(node)][0]], True)
        connected_premise = Or(node.cases[0].premise, node.cases[1].premise)
        i = 2
        while i < len(node.cases):
            connected_premise = Or(connected_premise, node.cases[i].premise)
            i += 1
        if alpha_equiv_with_defs(connected_premise, fact, context):
            logger.debug(f"{debug_prefix}mathched: fact={ExprFormatter(context).pretty_expr(fact)}, connected_premise={ExprFormatter(context).pretty_expr(connected_premise)}")
        else:
            msg = f"not matched: fact={ExprFormatter(context).pretty_expr(fact)}, conected_premise={ExprFormatter(context).pretty_expr(connected_premise)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}fact={ExprFormatter(context).pretty_expr(fact)}")
        local_ctx = context.copy_ctrl()
        goals: list[Bottom | Formula] = []
        for stmt in node.cases:
            self.check_control(stmt, local_ctx, indent+1)
            if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
                msg = "Local context must extend the parent context"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            goal = local_ctx.ctrl.formulas[-1]
            logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(context).pretty_expr(goal)}")
            goals.append(goal)
        for i in range(len(goals) - 1):
            if not alpha_equiv_with_defs(goals[i], goals[i + 1], context):
                msg = f"Not matched: goals[{i}]: {ExprFormatter(context).pretty_expr(goals[i])}, goals[{i + 1}]: {ExprFormatter(context).pretty_expr(goals[i + 1])}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [goals[0]]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [goals[0]]
        add_conclusion(context, goals[0])
        logger.debug(f"{debug_prefix}derived in all cases: {ExprFormatter(context).pretty_expr(goals[0])}")

    def check_case(self, node: Case, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}premise={ExprFormatter(context).pretty_expr(node.premise)}")
        local_ctx = context.add_ctrl([], [node.premise], [], [])
        for stmt in node.body:
            self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(context).pretty_expr(goal)}")
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = [node.premise]
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, goal)
        logger.debug(f"{debug_prefix}Added goal {ExprFormatter(context).pretty_expr(goal)}")

    def check_some(self, node: Some, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context):
                msg = f"not derivable: {ExprFormatter(context).pretty_expr(node.fact)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}derivable: {ExprFormatter(context).pretty_expr(node.fact)}")
        fact = get_fact(node.fact, context, self.unit.tokens[self.unit.node_to_token[id(node)][0]], True)
        if isinstance(fact, Exists):
            vars, body = strip_exists_vars(fact, Exists)
            body = make_exists_vars(body, Exists, [bound for bound, free in zip(vars, node.items) if free is None])
        elif isinstance(fact, ExistsUniq):
            vars, body= strip_exists_vars(fact, ExistsUniq)
            if len(vars) != 1:
                msg = f"Unexpected len(vars): {len(vars)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        else:
            msg = f"Unexpected type: {type(fact)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        if len(vars) != len(node.items):
            msg = f"len(vars): {len(vars)}, len(node.items): {len(node.items)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        for item in node.items:
            if item is None:
                continue
            if item.name in context.ctrl.used_names or item.name in context.decl.used_names:
                msg = f"{ExprFormatter(context).pretty_expr(item)} is already used"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
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
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            uniqueness = Forall(var, Implies(body, AtomicFormula(RefEquality(context.decl.equality.ref.name), (var, vars[0]))))
            premises: list[Bottom | Formula] = [existence, uniqueness]
        logger.debug(f"{debug_prefix}Taking {node.items}, premise={ExprFormatter(context).pretty_expr(existence)}")
        local_vars = [item for item in node.items if isinstance(item, Var)]
        local_ctx = context.add_ctrl(local_vars, premises, [], [])
        for stmt in node.body:
            self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(context).pretty_expr(goal)}")
        if isinstance(goal, Formula):
            goal_fv, _, _, _, _, _ = collect_vars(goal)
            for fv in goal_fv:
                if fv in local_vars:
                    msg = f"Conclusion depends on local variable {ExprFormatter(context).pretty_expr(fv)}"
                    raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        node.proofinfo.premises = [node.fact]
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = list(local_vars)
        node.proofinfo.local_premise = premises
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, goal)
        logger.debug(f"{debug_prefix}Added goal {ExprFormatter(context).pretty_expr(goal)}")

    def check_deny(self, node: Deny, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}premise={ExprFormatter(context).pretty_expr(node.premise)}")
        local_ctx = context.add_ctrl([], [node.premise], [], [])
        for stmt in node.body:
            self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(context).pretty_expr(goal)}")
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
            add_conclusion(context, conclusion)
            logger.debug(f"{debug_prefix}contradiction is derived; added {ExprFormatter(context).pretty_expr(conclusion)}")
        else:
            msg = "conradiction has not been deried"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)

    def check_contradict(self, node: Contradict, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if not goal_in_context(node.contradiction, context):
            msg = f"Cannot derive {ExprFormatter(context).pretty_expr(node.contradiction)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        if not goal_in_context(Not(node.contradiction), context):
            msg = f"Cannot derive {ExprFormatter(context).pretty_expr(Not(node.contradiction))}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}Derived contradiction: {ExprFormatter(context).pretty_expr(node.contradiction)}, {ExprFormatter(context).pretty_expr(Not(node.contradiction))}")
        conclusion = Bottom()
        node.proofinfo.premises = [node.contradiction, Not(node.contradiction)]
        node.proofinfo.conclusions = [conclusion]
        add_conclusion(context, conclusion)

    def check_explode(self, node: Explode, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if goal_in_context(Bottom(), context):
            node.proofinfo.premises = [Bottom()]
            node.proofinfo.conclusions = [node.conclusion]
            add_conclusion(context, node.conclusion)
            logger.debug(f"{debug_prefix}added {ExprFormatter(context).pretty_expr(node.conclusion)}")
        else:
            msg = "contradiction has not been derived"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)

    def check_apply(self, node: Apply, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context):
                msg = f"Cannot derive fact: {ExprFormatter(context).pretty_expr(node.fact)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Drivable fact: {ExprFormatter(context).pretty_expr(node.fact)}")
        fact = get_fact(node.fact, context, self.unit.tokens[self.unit.node_to_token[id(node)][0]], True)
        items, body = strip_forall_vars(fact)
        body = make_forall_vars(body, [item for item, term in zip(items, node.terms) if term is None])
        mapping: dict[Term, Term] = {}
        for item, term in zip(items, node.terms):
            if term is None:
                continue
            mapping[item] = term
        renamed_body, renamed_map = alpha_safe_formula(body, mapping, context)
        logger.debug(f"{debug_prefix}Instantiable: mapping={mapping}")
        instantiation = Substitutor(renamed_map, context).substitute_formula(renamed_body)
        logger.debug(f"{debug_prefix}\\forall-elimination is done: instantiation={ExprFormatter(context).pretty_expr(instantiation)}")
        if node.invoke == "none":
            node.proofinfo.premises = [node.fact]
            node.proofinfo.conclusions = [instantiation]
            add_conclusion(context, instantiation)
            logger.debug(f"{debug_prefix}Added {ExprFormatter(context).pretty_expr(instantiation)}")
        elif node.invoke == "invoke":
            if not isinstance(instantiation, Implies):
                msg = "instantiation is not Implies object"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}instantiation is Implies object")
            if not goal_in_context(instantiation.left, context):
                msg = f"Left of instantiation is not derivable: {ExprFormatter(context).pretty_expr(instantiation.left)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Left of instantiation is derivable: {ExprFormatter(context).pretty_expr(instantiation.left)}")
            node.proofinfo.premises = [node.fact, instantiation.left]
            node.proofinfo.conclusions = [instantiation.right]
            add_conclusion(context, instantiation.right)
            logger.debug(f"{debug_prefix}Added {ExprFormatter(context).pretty_expr(instantiation.right)}")
        elif node.invoke == "invoke-rightward":
            if not isinstance(instantiation, Iff):
                msg = "instantiation is not Iff object"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}instantiation is Iff object")
            if not goal_in_context(instantiation.left, context):
                msg = f"Left of instantiation is not derivable: {ExprFormatter(context).pretty_expr(instantiation.left)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Left of instantiation is derivable: {ExprFormatter(context).pretty_expr(instantiation.left)}")
            node.proofinfo.premises = [node.fact, instantiation.left]
            node.proofinfo.conclusions = [instantiation.right]
            add_conclusion(context, instantiation.right)
            logger.debug(f"{debug_prefix}Added {ExprFormatter(context).pretty_expr(instantiation.right)}")
        elif node.invoke == "invoke-leftward":
            if not isinstance(instantiation, Iff):
                msg = "instantiation is not Iff object"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}instantiation is Iff object")
            if not goal_in_context(instantiation.right, context):
                msg = f"Right of instantiation is not derivable: {ExprFormatter(context).pretty_expr(instantiation.right)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Right of instantiation is derivable: {ExprFormatter(context).pretty_expr(instantiation.right)}")
            node.proofinfo.premises = [node.fact, instantiation.right]
            node.proofinfo.conclusions = [instantiation.left]
            add_conclusion(context, instantiation.left)
            logger.debug(f"{debug_prefix}Added {ExprFormatter(context).pretty_expr(instantiation.left)}")
        else:
            msg = f"Unexpected invoke option {node.invoke}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)

    def check_lift(self, node: Lift, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}Target conclusion: {ExprFormatter(context).pretty_expr(node.conclusion)}")
        items, body = strip_exists_vars(node.conclusion, Exists)
        body = make_exists_vars(body, Exists, [item for item, term in zip(items, node.varterms) if term is None])
        mapping: dict[Term, Term] = {item: term for item, term in zip(items, node.varterms) if term is not None}
        renamed_body, renamed_mapping = alpha_safe_formula(body, mapping, context)
        fact = Substitutor(renamed_mapping, context).substitute_formula(renamed_body)
        if not goal_in_context(fact, context):
            msg = f"Not fact: {ExprFormatter(context).pretty_expr(fact)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}Fact: {ExprFormatter(context).pretty_expr(fact)}")
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)

    def check_characterize(self, node: Characterize, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        _, used_bound_vars, _, used_bound_pred_tmpls, _, used_bound_fun_tmpls = collect_vars(node.conclusion.body)
        fv, bv, fpt, bpt, fft, bft = collect_vars(node.varterm)
        vardash = fresh_var(Var(node.conclusion.var.name + "'"), used_bound_vars | used_bound_pred_tmpls | used_bound_fun_tmpls | fv | bv | fpt | bpt | fft | bft, context)
        renamed_conclusion, _ = alpha_safe_formula(node.conclusion, {node.conclusion.var: node.varterm}, context)
        if not isinstance(renamed_conclusion, ExistsUniq):
            msg = f"renamed_conclusion is not ExistsUniq object: {ExprFormatter(context).pretty_expr(renamed_conclusion)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        existence = Substitutor(({renamed_conclusion.var: node.varterm}, {}, {}), context).substitute_formula(renamed_conclusion.body)
        existence_dash = Substitutor(({renamed_conclusion.var: vardash}, {}, {}), context).substitute_formula(renamed_conclusion.body)
        if context.decl.equality is None:
            msg = "equality has not been declared yet"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        fact = And(existence, Forall(vardash, Implies(existence_dash, AtomicFormula(RefEquality(context.decl.equality.ref.name), (vardash, node.varterm)))))
        if not goal_in_context(fact, context):
            msg = f"Not fact: {ExprFormatter(context).pretty_expr(fact)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}Fact: {ExprFormatter(context).pretty_expr(fact)}")
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)

    def check_invoke(self, node: Invoke, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if not goal_in_context(node.fact, context):
            msg = f"Not fact: {ExprFormatter(context).pretty_expr(node.fact)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}fact: {ExprFormatter(context).pretty_expr(node.fact)}")
        if node.direction == "none":
            if not isinstance(node.fact, Implies):
                msg = f"Not Implies object: {ExprFormatter(context).pretty_expr(node.fact)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Implies object: {ExprFormatter(context).pretty_expr(node.fact)}")
            if not goal_in_context(node.fact.left, context):
                msg = f"Left of Implies object not derived: {ExprFormatter(context).pretty_expr(node.fact.left)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Left of Implies object derived: {ExprFormatter(context).pretty_expr(node.fact.left)}")
            node.proofinfo.premises = [node.fact, node.fact.left]
            node.proofinfo.conclusions = [node.fact.right]
            add_conclusion(context, node.fact.right)
            logger.debug(f"{debug_prefix}Right of Implies object added: {ExprFormatter(context).pretty_expr(node.fact.right)}")
        elif node.direction == "rightward":
            if not isinstance(node.fact, Iff):
                msg = f"Not Iff object: {ExprFormatter(context).pretty_expr(node.fact)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Iff object: {ExprFormatter(context).pretty_expr(node.fact)}")
            if not goal_in_context(node.fact.left, context):
                msg = f"Left of Iff object not derived: {ExprFormatter(context).pretty_expr(node.fact.left)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Left of Iff object derived: {ExprFormatter(context).pretty_expr(node.fact.left)}")
            node.proofinfo.premises = [node.fact, node.fact.left]
            node.proofinfo.conclusions = [node.fact.right]
            add_conclusion(context, node.fact.right)
            logger.debug(f"{debug_prefix}Right of Iff object added: {ExprFormatter(context).pretty_expr(node.fact.right)}")
        elif node.direction == "leftward":
            if not isinstance(node.fact, Iff):
                msg = f"Not Iff object: {ExprFormatter(context).pretty_expr(node.fact)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Iff object: {ExprFormatter(context).pretty_expr(node.fact)}")
            if not goal_in_context(node.fact.right, context):
                msg = f"Right of Iff object not derived: {ExprFormatter(context).pretty_expr(node.fact.right)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Right of Iff object derived: {ExprFormatter(context).pretty_expr(node.fact.right)}")
            node.proofinfo.premises = [node.fact, node.fact.right]
            node.proofinfo.conclusions = [node.fact.left]
            add_conclusion(context, node.fact.left)
            logger.debug(f"{debug_prefix}Left of Iff object added: {ExprFormatter(context).pretty_expr(node.fact.left)}")
        else:
            msg = f"Unexpected direction: {node.direction}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)

    def check_expand(self, node: Expand, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context):
                msg = f"Not fact: {ExprFormatter(context).pretty_expr(node.fact)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}fact: {ExprFormatter(context).pretty_expr(node.fact)}")
        fact = get_fact(node.fact, context, self.unit.tokens[self.unit.node_to_token[id(node)][0]])
        conclusion = DefExpander(node.defs, node.indexes).expand_defs_formula(fact, context)
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [conclusion]
        add_conclusion(context, conclusion)
        logger.debug(f"{debug_prefix}Added: {ExprFormatter(context).pretty_expr(conclusion)}")

    def check_fold(self, node: Fold, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        fact = DefExpander(node.defs, node.indexes).expand_defs_formula(node.conclusion, context)
        if not goal_in_context(fact, context):
            msg = f"Not fact: {ExprFormatter(context).pretty_expr(fact)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}fact: {ExprFormatter(context).pretty_expr(fact)}")
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        logger.debug(f"{debug_prefix}Added: {ExprFormatter(context).pretty_expr(node.conclusion)}")

    def check_pad(self, node: Pad, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context):
                msg = f"Not derivable: {ExprFormatter(context).pretty_expr(node.fact)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Derivable: {ExprFormatter(context).pretty_expr(node.fact)}")
        fact = get_fact(node.fact, context, self.unit.tokens[self.unit.node_to_token[id(node)][0]])
        fact_parts = flatten_op(fact, Or)
        conclusion_parts = flatten_op(node.conclusion, Or)
        if not all(any(alpha_equiv_with_defs(c, f, context) for c in conclusion_parts) for f in fact_parts):
            msg = f"neither left or right not derivable: {ExprFormatter(context).pretty_expr(node.conclusion)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        logger.debug(f"{debug_prefix}Derivable, added {ExprFormatter(context).pretty_expr(node.conclusion)}")

    def check_split(self, node: Split, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context):
                msg = f"Not derivable: {ExprFormatter(context).pretty_expr(node.fact)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        fact = get_fact(node.fact, context, self.unit.tokens[self.unit.node_to_token[id(node)][0]], True)
        logger.debug(f"{debug_prefix}Derivable: {ExprFormatter(context).pretty_expr(fact)}")
        if isinstance(fact, And):
            logger.debug(f"{debug_prefix}And object: {ExprFormatter(context).pretty_expr(fact)}")
            fact_parts = flatten_op(fact, And)
            node.proofinfo.premises = [fact]
            if node.index is None:
                node.proofinfo.conclusions = fact_parts
                for f in fact_parts:
                    add_conclusion(context, f)
                    logger.debug(f"{debug_prefix}added {ExprFormatter(context).pretty_expr(f)}")
            else:
                if node.index <= 0 or node.index > len(fact_parts):
                    msg = f"index out of range, index: {node.index}, len(fact_parts): {len(fact_parts)}"
                    raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
                f = fact_parts[node.index - 1]
                node.proofinfo.conclusions = [f]
                add_conclusion(context, f)
                logger.debug(f"{debug_prefix}added {ExprFormatter(context).pretty_expr(f)}")
        elif isinstance(fact, Iff):
            logger.debug(f"{debug_prefix}Iff object: {ExprFormatter(context).pretty_expr(fact)}")
            implication_rightward = Implies(fact.left, fact.right)
            implication_leftward = Implies(fact.right, fact.left)
            node.proofinfo.premises = [fact]
            node.proofinfo.conclusions = [implication_rightward, implication_leftward]
            add_conclusion(context, implication_rightward)
            add_conclusion(context, implication_leftward)
            logger.debug(f"{debug_prefix}added {ExprFormatter(context).pretty_expr(implication_rightward)}")
            logger.debug(f"{debug_prefix}added {ExprFormatter(context).pretty_expr(implication_leftward)}")
        else:
            msg = f"Not And or Iff object: {ExprFormatter(context).pretty_expr(fact)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)

    def check_connect(self, node: Connect, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.conclusion, AtomicFormula):
            if not isinstance(node.conclusion.pred, RefDefPred):
                raise Exception(f"Unexpected type: {type(node.conclusion.pred)}")
            conclusion = DefExpander([node.conclusion.pred.name]).expand_defs_formula(node.conclusion, context)
        else:
            conclusion = node.conclusion
        if isinstance(conclusion, And):
            logger.debug(f"{debug_prefix}And object: {ExprFormatter(context).pretty_expr(conclusion)}")
            conclusion_parts = flatten_op(conclusion, And)
            for c in conclusion_parts:
                if not goal_in_context(c, context):
                    msg = f"Not derivable: {ExprFormatter(context).pretty_expr(c)}"
                    raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            node.proofinfo.premises = conclusion_parts
            node.proofinfo.conclusions = [node.conclusion]
            add_conclusion(context, node.conclusion)
            logger.debug(f"{debug_prefix}Derivable, added {ExprFormatter(context).pretty_expr(node.conclusion)}")
        elif isinstance(conclusion, Iff):
            logger.debug(f"{debug_prefix}Iff object: {ExprFormatter(context).pretty_expr(conclusion)}")
            implication_rightward = Implies(conclusion.left, conclusion.right)
            if not goal_in_context(implication_rightward, context):
                msg = f"Not derivable: {ExprFormatter(context).pretty_expr(implication_rightward)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            implication_leftward = Implies(conclusion.right, conclusion.left)
            if not goal_in_context(implication_leftward, context):
                msg = f"Not derivable: {ExprFormatter(context).pretty_expr(implication_leftward)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            node.proofinfo.premises = [implication_rightward, implication_leftward]
            node.proofinfo.conclusions = [node.conclusion]
            add_conclusion(context, node.conclusion)
            logger.debug(f"{debug_prefix}derivable, added {ExprFormatter(context).pretty_expr(node.conclusion)}")
        else:
            msg = f"Not And or Iff object: {ExprFormatter(context).pretty_expr(node.conclusion)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)

    def check_substitute(self, node: Substitute, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.fact, (Bottom, Formula)):
            if not goal_in_context(node.fact, context):
                msg = f"Not fact: {ExprFormatter(context).pretty_expr(node.fact)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Fact: {ExprFormatter(context).pretty_expr(node.fact)}")
        fact = get_fact(node.fact, context, self.unit.tokens[self.unit.node_to_token[id(node)][0]])
        if context.decl.equality is None:
            msg = "equality has not been declared yet"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        premises_equal: list[AtomicFormula] = []
        for k, v in node.env.items():
            if not isinstance(k, VarTerm):
                raise Exception(f"Unexpected type: {type(k)}")
            if not isinstance(v, VarTerm):
                raise Exception(f"Unexpected type: {type(v)}")
            equation = AtomicFormula(RefEquality(context.decl.equality.ref.name), (k, v))
            if not goal_in_context(equation, context):
                msg = f"Not fact: {ExprFormatter(context).pretty_expr(equation)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Fact: {ExprFormatter(context).pretty_expr(equation)}")
            premises_equal.append(equation)
        renamed_fact, mapping = alpha_safe_formula(fact, node.env, context, True)
        conclusion = Substitutor(mapping, context, node.indexes).substitute_formula(renamed_fact)
        logger.debug(f"{debug_prefix}conclusion: {ExprFormatter(context).pretty_expr(conclusion)}")
        logger.debug(f"{debug_prefix}Matched")
        node.proofinfo.premises = [fact] + premises_equal
        node.proofinfo.conclusions = [conclusion]
        add_conclusion(context, conclusion)
        logger.debug(f"{debug_prefix}Added {ExprFormatter(context).pretty_expr(conclusion)}")

    def check_show(self, node: Show, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        logger.debug(f"{debug_prefix}Target conclusion: {ExprFormatter(context).pretty_expr(node.conclusion)}")
        local_ctx = context.copy_ctrl()
        for stmt in node.body:
            self.check_control(stmt, local_ctx, indent+1)
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            msg = "Local context must extend the parent context"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {ExprFormatter(context).pretty_expr(goal)}")
        if not alpha_equiv_with_defs(node.conclusion, goal, context):
            msg = f"Not matched with target conclusion: {ExprFormatter(context).pretty_expr(node.conclusion)}"
            raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
        logger.debug(f"{debug_prefix}Matched with target conclusion: {ExprFormatter(context).pretty_expr(node.conclusion)}")
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, goal)
        logger.debug(f"{debug_prefix}Added {ExprFormatter(context).pretty_expr(goal)}")

    def check_assert(self, node: Assert, context: Context, indent: int) -> None:
        debug_prefix = make_debug_prefix(node, indent)
        if isinstance(node.reference, (Bottom, Formula)):
            if not goal_in_context(node.reference, context):
                msg = f"Not fact: {ExprFormatter(context).pretty_expr(node.reference)}"
                raise CheckError(self.unit.tokens[self.unit.node_to_token[id(node)][0]], msg)
            logger.debug(f"{debug_prefix}Fact: {ExprFormatter(context).pretty_expr(node.reference)}")
        formula = get_fact(node.reference, context, self.unit.tokens[self.unit.node_to_token[id(node)][0]])
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [formula]
        add_conclusion(context, formula)
        logger.debug(f"{debug_prefix}Added {ExprFormatter(context).pretty_expr(formula)}")

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
