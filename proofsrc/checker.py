from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, Symbol, And, Or, Implies, Forall, Exists, Not, Bottom, Iff, Axiom, Invoke, Expand, PrimPred, DefPred, DefCon, Pad, Split, Connect, ExistsUniq, Compound, Fun, Con, DefFun, DefFunTerm, Equality, Var, Substitute, Characterize, Show, Pred, Control, Formula, Declaration, Template, Term, Lambda, DefConExist, DefConUniq, DefFunExist, DefFunUniq, EqualityReflection, EqualityReplacement, Include, DeclarationSupport, Assert, Fold
from logic_utils import Substitutor, DefExpander, expr_in_context, collect_quantifier_vars, collect_vars, flatten_op, fresh_var, alpha_equiv_with_defs, pretty_expr, alpha_rename_formula
from copy import deepcopy

import logging
logger = logging.getLogger("proof")

def goal_in_context(goal: str | Bottom | Formula, context: Context) -> bool:
    if isinstance(goal, str):
        return context.decl.has_reference(goal)
    elif isinstance(goal, Symbol) and context.decl.equality is not None and goal.pred.name == context.decl.equality.equal.name and goal.args[0] == goal.args[1]:
        return True
    else:
        return expr_in_context(goal, context)

def get_fact(fact: str | Formula, context: Context) -> Formula:
    if isinstance(fact, str):
        return context.decl.get_reference(fact)
    elif isinstance(fact, Formula):
        return fact
    else:
        raise Exception(f"Unexpected type {type(fact)}")

def add_conclusion(context: Context, conclusion: Bottom | Formula) -> None:
    context.ctrl.formulas.append(conclusion)

def make_debug_prefix(node: Declaration | DeclarationSupport | Control, indent: int) -> str:
    return "  " * indent + f"[{node.__class__.__name__}] "

def make_error_prefix(node: Declaration | DeclarationSupport | Control, indent: int) -> str:
    return "  " * indent + f"❌ [{node.__class__.__name__}] {node.token.info()} "

def check_ast(ast: list[Include | Declaration], context: Context) -> tuple[bool, list[Include | Declaration], Context]:
    return all(check_declaration(node, context) for node in ast if isinstance(node, Declaration)), ast, context

# === 証明チェッカー ===
def check_declaration(node: Declaration, context: Context, indent: int = 0) -> bool:
    error_prefix = make_error_prefix(node, indent)

    node.proofinfo.ctrl_ctx = deepcopy(context.ctrl)

    if isinstance(node, PrimPred):
        return check_primpred(node, context, indent)
    elif isinstance(node, Axiom):
        return check_axiom(node, context, indent)
    elif isinstance(node, Theorem):
        return check_theorem(node, context, indent)
    elif isinstance(node, DefPred):
        return check_defpred(node, context, indent)
    elif isinstance(node, DefCon):
        return check_defcon(node, context, indent)
    elif isinstance(node, DefConExist):
        return check_defconexist(node, context, indent)
    elif isinstance(node, DefConUniq):
        return check_defconuniq(node, context, indent)
    elif isinstance(node, DefFun):
        return check_deffun(node, context, indent)
    elif isinstance(node, DefFunExist):
        return check_deffunexist(node, context, indent)
    elif isinstance(node, DefFunUniq):
        return check_deffununiq(node, context, indent)
    elif isinstance(node, DefFunTerm):
        return check_deffunterm(node, context, indent)
    elif isinstance(node, Equality):
        return check_equality(node, context, indent)
    else:
        logger.error(f"{error_prefix}Unsupported node {node}")
        return False

def check_primpred(node: PrimPred, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, arity: {node.arity}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_axiom(node: Axiom, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, conclusion: {pretty_expr(node.conclusion, context)}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_theorem(node: Theorem, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}{node.name}: {pretty_expr(node.conclusion, context)}")
    local_ctx = context.copy_ctrl()
    for stmt in node.proof:
        if not check_control(stmt, local_ctx, indent+1):
            logger.error(f"{error_prefix}{node.name} not proved: {pretty_expr(node.conclusion, context)}")
            node.proofinfo.status = "ERROR"
            return False
    if goal_in_context(node.conclusion, local_ctx):
        logger.debug(f"{debug_prefix}{node.name} proved: {pretty_expr(node.conclusion, context)}")
        context.add_decl(node)
        node.proofinfo.status = "OK"
        return True
    else:
        logger.error(f"{error_prefix}{node.name} not proved: {pretty_expr(node.conclusion, context)}")
        node.proofinfo.status = "ERROR"
        return False    

def check_defpred(node: DefPred, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, args: {node.args}, formula: {pretty_expr(node.formula, context)}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_defcon(node: DefCon, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, theorem: {node.theorem}")
    existsuniq = context.decl.theorems[node.theorem].conclusion
    if not isinstance(existsuniq, ExistsUniq):
        logger.error(f"{error_prefix}Not ExistsUniq object: {pretty_expr(existsuniq, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}ExistsUniq object: {pretty_expr(existsuniq, context)}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_defconexist(node: DefConExist, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, con_name: {node.con_name}")
    existsuniq = context.decl.theorems[context.decl.defcons[node.con_name].theorem].conclusion
    if not isinstance(existsuniq, ExistsUniq):
        logger.error(f"{error_prefix}Not ExistsUniq object: {pretty_expr(existsuniq, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}ExistsUniq object: {pretty_expr(existsuniq, context)}")
    subst = Substitutor({existsuniq.var: Con(node.con_name)})
    existence_formula = subst.substitute_formula(existsuniq.body)
    if not alpha_equiv_with_defs(node.formula, existence_formula, context):
        logger.error(f"{error_prefix}existence_formula is not matched with theorem: {pretty_expr(node.formula, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}existence_formula is matched with theorem: {pretty_expr(node.formula, context)}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_defconuniq(node: DefConUniq, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, con_name: {node.con_name}")
    existsuniq = context.decl.theorems[context.decl.defcons[node.con_name].theorem].conclusion
    if not isinstance(existsuniq, ExistsUniq):
        logger.error(f"{error_prefix}Not ExistsUniq object: {pretty_expr(existsuniq, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}ExistsUniq object: {pretty_expr(existsuniq, context)}")
    free, bound = collect_vars(existsuniq.body)
    var = fresh_var(existsuniq.var, free | bound)
    subst = Substitutor({existsuniq.var: var})
    body = subst.substitute_formula(existsuniq.body)
    if context.decl.equality is None:
        logger.error(f"{error_prefix}equality has not been declared yet")
        node.proofinfo.status = "ERROR"
        return False
    uniqueness_formula = Forall(var, Implies(body, Symbol(Pred(context.decl.equality.equal.name), (var, Con(node.con_name)))))
    if not alpha_equiv_with_defs(node.formula, uniqueness_formula, context):
        logger.error(f"{error_prefix}uniqueness_formula is not matched with theorem: {pretty_expr(node.formula, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}uniqueness_formula is matched with theorem: {pretty_expr(node.formula, context)}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_deffun(node: DefFun, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, theorem: {node.theorem}")
    _, existsuniq = collect_quantifier_vars(context.decl.theorems[node.theorem].conclusion, Forall)
    if not isinstance(existsuniq, ExistsUniq):
        logger.error(f"{error_prefix}Not ExistsUniq object: {pretty_expr(existsuniq, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}ExistsUniq object: {pretty_expr(existsuniq, context)}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_deffunexist(node: DefFunExist, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, fun_name: {node.fun_name}")
    args, existsuniq = collect_quantifier_vars(context.decl.theorems[context.decl.deffuns[node.fun_name].theorem].conclusion, Forall)
    if not isinstance(existsuniq, ExistsUniq):
        logger.error(f"{error_prefix}Not ExistsUniq object: {pretty_expr(existsuniq, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}ExistsUniq object: {pretty_expr(existsuniq, context)}")
    subst = Substitutor({existsuniq.var: Compound(Fun(node.fun_name), tuple(args))})
    existence_formula = subst.substitute_formula(existsuniq.body)
    for arg in reversed(args):
        existence_formula = Forall(arg, existence_formula)
    if not alpha_equiv_with_defs(node.formula, existence_formula, context):
        logger.error(f"{error_prefix}existence_formula is not matched with theorem: {pretty_expr(node.formula, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}existence_formula is matched with theorem: {pretty_expr(node.formula, context)}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_deffununiq(node: DefFunUniq, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, fun_name: {node.fun_name}")
    args, existsuniq = collect_quantifier_vars(context.decl.theorems[context.decl.deffuns[node.fun_name].theorem].conclusion, Forall)
    if not isinstance(existsuniq, ExistsUniq):
        logger.error(f"{error_prefix}Not ExistsUniq object: {pretty_expr(existsuniq, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}ExistsUniq object: {pretty_expr(existsuniq, context)}")
    if context.decl.equality is None:
        logger.error(f"{error_prefix}equality has not been declared yet")
        node.proofinfo.status = "ERROR"
        return False
    uniqueness_formula = Forall(existsuniq.var, Implies(existsuniq.body, Symbol(Pred(context.decl.equality.equal.name), (Var(existsuniq.var.name), Compound(Fun(node.fun_name), tuple(args))))))
    for arg in reversed(args):
        uniqueness_formula = Forall(arg, uniqueness_formula)
    if not alpha_equiv_with_defs(node.formula, uniqueness_formula, context):
        logger.error(f"{error_prefix}uniqueness_formula is not matched with theorem: {pretty_expr(node.formula, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}uniqueness_formula is matched with theorem: {pretty_expr(node.formula, context)}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_deffunterm(node: DefFunTerm, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, args: {node.args}, term: {pretty_expr(node.term, context)}")
    free, _ = collect_vars(node.term)
    if set(node.args) != set(free):
        logger.error(f"{error_prefix}args are not matched with free vars: {free}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}args are mathced with free vars of term: {free}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_equality(node: Equality, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.equal.name}")
    if not check_equality_reflection(node.reflection, context, indent+1):
        node.proofinfo.status = "ERROR"
        return False
    if not check_equality_replacement(node.replacement, context, indent+1):
        node.proofinfo.status = "ERROR"
        return False
    context.add_decl(node)
    logger.debug(f"{debug_prefix}{node.equal.name} is registered as equality")
    node.proofinfo.status = "OK"
    return True

def check_equality_reflection(node: EqualityReflection, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}Checking {node.equal.name} reflection theorem: {pretty_expr(node.evidence.conclusion, context)}")
    reflection = Forall(Var("x"), Symbol(Pred(node.equal.name), (Var("x"), Var("x"))))
    if not alpha_equiv_with_defs(node.evidence.conclusion, reflection, context):
        logger.error(f"{error_prefix}Not matched with expected formula: {pretty_expr(reflection, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Matched with expected formula: {pretty_expr(reflection, context)}")
    node.proofinfo.status = "OK"
    return True

def check_equality_replacement(node: EqualityReplacement, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    for predicate in node.evidence:
        logger.debug(f"{debug_prefix}Checking {predicate} replacement theorem: {pretty_expr(node.evidence[predicate].conclusion, context)}")
        if predicate == node.equal.name:
            if isinstance(node.equal, PrimPred):
                arity = node.equal.arity
            elif isinstance(node.equal, DefPred):
                arity = len(node.equal.args)
            else:
                raise Exception("node.equal is not PrimPred or DefPred")
        else:
            arity = context.decl.primpreds[predicate].arity
        args_x: list[Var] = []
        args_y: list[Var] = []
        for i in range(arity):
            args_x.append(Var(f"x_{i}"))
            args_y.append(Var(f"y_{i}"))
        premise = Symbol(Pred(node.equal.name), (args_x[0], args_y[0]))
        for i in range(1, arity):
            premise = And(premise, Symbol(Pred(node.equal.name), (args_x[i], args_y[i])))
        conclusion = Implies(Symbol(Pred(predicate), tuple(args_x)), Symbol(Pred(predicate), tuple(args_y)))
        replacement = Implies(premise, conclusion)
        for arg in reversed(args_y):
            replacement = Forall(arg, replacement)
        for arg in reversed(args_x):
            replacement = Forall(arg, replacement)
        if not alpha_equiv_with_defs(node.evidence[predicate].conclusion, replacement, context):
            logger.error(f"{error_prefix}Not matched with expected formula: {pretty_expr(replacement, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Matched with expected formula: {pretty_expr(replacement, context)}")
    node.proofinfo.status = "OK"
    return True

def check_control(node: Control, context: Context, indent: int):
    error_prefix = make_error_prefix(node, indent)

    node.proofinfo.ctrl_ctx = deepcopy(context.ctrl)

    if isinstance(node, Any):
        return check_any(node, context, indent)
    elif isinstance(node, Assume):
        return check_assume(node, context, indent)
    elif isinstance(node, Divide):
        return check_divide(node, context, indent)
    elif isinstance(node, Some):
        return check_some(node, context, indent)
    elif isinstance(node, Deny):
        return check_deny(node, context, indent)
    elif isinstance(node, Contradict):
        return check_contradict(node, context, indent)
    elif isinstance(node, Explode):
        return check_explode(node, context, indent)
    elif isinstance(node, Apply):
        return check_apply(node, context, indent)
    elif isinstance(node, Lift):
        return check_lift(node, context, indent)
    elif isinstance(node, Characterize):
        return check_characterize(node, context, indent)
    elif isinstance(node, Invoke):
        return check_invoke(node, context, indent)
    elif isinstance(node, Expand):
        return check_expand(node, context, indent)
    elif isinstance(node, Fold):
        return check_fold(node, context, indent)
    elif isinstance(node, Pad):
        return check_pad(node, context, indent)
    elif isinstance(node, Split):
        return check_split(node, context, indent)
    elif isinstance(node, Connect):
        return check_connect(node, context, indent)
    elif isinstance(node, Substitute):
        return check_substitute(node, context, indent)
    elif isinstance(node, Show):
        return check_show(node, context, indent)
    elif isinstance(node, Assert):
        return check_assert(node, context, indent)
    else:
        logger.error(f"{error_prefix}Unsupported node {node}")
        return False

def check_any(node: Any, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    local_vars = [item for item in node.items if isinstance(item, Var)]
    for var in local_vars:
        if var in context.ctrl.vars:
            logger.error(f"{error_prefix}{pretty_expr(var, context)} is already used")
            node.proofinfo.status = "ERROR"
            return False
    local_templates = [item for item in node.items if isinstance(item, Template)]
    for template in local_templates:
        if template in context.ctrl.templates:
            logger.error(f"{error_prefix}{pretty_expr(template, context)} is already used")
            node.proofinfo.status = "ERROR"
            return False
    logger.debug(f"{debug_prefix}Taking {node.items}")
    local_ctx = context.add_ctrl(local_vars, [], local_templates)
    for stmt in node.body:
        if not check_control(stmt, local_ctx, indent+1):
            node.proofinfo.status = "ERROR"
            return False
    if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
        logger.error(f"{error_prefix}Local context must extend the parent context")
        node.proofinfo.status = "ERROR"
        return False
    local_goal = local_ctx.ctrl.formulas[-1]
    if isinstance(local_goal, Bottom):
        logger.error(f"{error_prefix}Bottom cannot be generalized")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}derived local_goal: {pretty_expr(local_goal, context)}")
    goal = local_goal
    for item in reversed(node.items):
        goal = Forall(item, goal)
    node.proofinfo.status = "OK"
    node.proofinfo.premises = []
    node.proofinfo.conclusions = [goal]
    node.proofinfo.local_vars = local_vars
    node.proofinfo.local_premise = []
    node.proofinfo.local_conclusion = [local_goal]
    add_conclusion(context, goal)
    logger.debug(f"{debug_prefix}Generalized to {pretty_expr(goal, context)}")
    return True

def check_assume(node: Assume, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}premise={pretty_expr(node.premise, context)}")
    local_ctx = context.add_ctrl([], [node.premise], [])
    for stmt in node.body:
        if not check_control(stmt, local_ctx, indent+1):
            node.proofinfo.status = "ERROR"
            return False
    if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
        logger.error(f"{error_prefix}Local context must extend the parent context")
        node.proofinfo.status = "ERROR"
        return False
    goal = local_ctx.ctrl.formulas[-1]
    if isinstance(goal, Bottom):
        logger.error(f"{error_prefix}Bottom is not allowed as goal")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}derived goal: {pretty_expr(goal, context)}")
    implication = Implies(node.premise, goal)
    node.proofinfo.status = "OK"
    node.proofinfo.premises = []
    node.proofinfo.conclusions = [implication]
    node.proofinfo.local_vars = []
    node.proofinfo.local_premise = [node.premise]
    node.proofinfo.local_conclusion = [goal]
    add_conclusion(context, implication)
    logger.debug(f"{debug_prefix}Added implication {pretty_expr(implication, context)}")
    return True

def check_divide(node: Divide, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if not goal_in_context(node.fact, context):
        logger.error(f"{error_prefix}Not fact: {pretty_expr(node.fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    fact = get_fact(node.fact, context)
    connected_premise = Or(node.cases[0].premise, node.cases[1].premise)
    i = 2
    while i < len(node.cases):
        connected_premise = Or(connected_premise, node.cases[i].premise)
        i += 1
    if alpha_equiv_with_defs(connected_premise, fact, context):
        logger.debug(f"{debug_prefix}mathched: fact={pretty_expr(fact, context)}, connected_premise={pretty_expr(connected_premise, context)}")
    else:
        logger.error(f"{error_prefix}not matched: fact={pretty_expr(fact, context)}, conected_premise={pretty_expr(connected_premise, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}fact={pretty_expr(fact, context)}")
    local_ctx = context.copy_ctrl()
    goals: list[Bottom | Formula] = []
    for stmt in node.cases:
        if not check_case(stmt, local_ctx, indent+1):
            node.proofinfo.status = "ERROR"
            return False
        if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
            logger.error(f"{error_prefix}Local context must extend the parent context")
            node.proofinfo.status = "ERROR"
            return False
        goal = local_ctx.ctrl.formulas[-1]
        logger.debug(f"{debug_prefix}derived goal: {pretty_expr(goal, context)}")
        goals.append(goal)
    for i in range(len(goals) - 1):
        if not alpha_equiv_with_defs(goals[i], goals[i + 1], context):
            logger.error(f"{error_prefix}Not matched: goals[{i}]: {pretty_expr(goals[i], context)}, goals[{i + 1}]: {pretty_expr(goals[i + 1], context)}")
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

def check_case(node: Case, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}premise={pretty_expr(node.premise, context)}")
    local_ctx = context.add_ctrl([], [node.premise], [])
    for stmt in node.body:
        if not check_control(stmt, local_ctx, indent+1):
            node.proofinfo.status = "ERROR"
            return False
    if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
        logger.error(f"{error_prefix}Local context must extend the parent context")
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

def check_some(node: Some, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if not goal_in_context(node.fact, context):
        logger.error(f"{error_prefix}not derivable: {pretty_expr(node.fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}derivable: {pretty_expr(node.fact, context)}")
    fact = get_fact(node.fact, context)
    if not isinstance(fact, Exists):
        logger.error(f"{error_prefix}Exists object: {pretty_expr(node.fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    vars, body = collect_quantifier_vars(fact, Exists)
    if not set(node.env.keys()).issubset(set(vars)):
        logger.error(f"{error_prefix}invalid vars: node.env.keys()={node.env.keys()}, vars={vars}")
        node.proofinfo.status = "ERROR"
        return False
    for var in node.env.values():
        if var in context.ctrl.vars:
            node.proofinfo.status = "ERROR"
            logger.error(f"{error_prefix}{pretty_expr(var, context)} is already used")
    subst = Substitutor(node.env)
    premise = subst.substitute_formula(body)
    logger.debug(f"{debug_prefix}Taking {node.env.values()}, premise={pretty_expr(premise, context)}")
    local_ctx = context.add_ctrl(list(node.env.values()), [premise], [])
    for stmt in node.body:
        if not check_control(stmt, local_ctx, indent+1):
            node.proofinfo.status = "ERROR"
            return False
    if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
        logger.error(f"{error_prefix}Local context must extend the parent context")
        node.proofinfo.status = "ERROR"
        return False
    goal = local_ctx.ctrl.formulas[-1]
    logger.debug(f"{debug_prefix}derived goal: {pretty_expr(goal, context)}")
    node.proofinfo.status = "OK"
    node.proofinfo.premises = [node.fact]
    node.proofinfo.conclusions = [goal]
    node.proofinfo.local_vars = list(node.env.values())
    node.proofinfo.local_premise = [premise]
    node.proofinfo.local_conclusion = [goal]
    add_conclusion(context, goal)
    logger.debug(f"{debug_prefix}Added goal {pretty_expr(goal, context)}")
    return True

def check_deny(node: Deny, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}premise={pretty_expr(node.premise, context)}")
    local_ctx = context.add_ctrl([], [node.premise], [])
    for stmt in node.body:
        if not check_control(stmt, local_ctx, indent+1):
            node.proofinfo.status = "ERROR"
            return False
    if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
        logger.error(f"{error_prefix}Local context must extend the parent context")
        node.proofinfo.status = "ERROR"
        return False
    goal = local_ctx.ctrl.formulas[-1]
    logger.debug(f"{debug_prefix}derived goal: {pretty_expr(goal, context)}")
    if isinstance(goal, Bottom):
        if isinstance(node.premise, Not):
            conclusion = node.premise.body
        else:
            conclusion = Not(node.premise)
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
        logger.error(f"{error_prefix}conradiction has not been deried")
        node.proofinfo.status = "ERROR"
        return False

def check_contradict(node: Contradict, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if not goal_in_context(node.contradiction, context):
        logger.error(f"{error_prefix}Cannot derive {pretty_expr(node.contradiction, context)}")
        node.proofinfo.status = "ERROR"
        return False
    if not goal_in_context(Not(node.contradiction), context):
        logger.error(f"{error_prefix}Cannot derive {pretty_expr(Not(node.contradiction), context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Derived contradiction: {pretty_expr(node.contradiction, context)}, {pretty_expr(Not(node.contradiction), context)}")
    conclusion = Bottom()
    node.proofinfo.status = "OK"
    node.proofinfo.premises = [node.contradiction, Not(node.contradiction)]
    node.proofinfo.conclusions = [conclusion]
    add_conclusion(context, conclusion)
    return True

def check_explode(node: Explode, context: Context, indent: int):
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
        logger.error(f"{error_prefix}contradiction has not been derived")
        node.proofinfo.status = "ERROR"
        return False

def check_apply(node: Apply, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if not goal_in_context(node.fact, context):
        logger.error(f"{error_prefix}Cannot derive fact: {pretty_expr(node.fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Drivable fact: {pretty_expr(node.fact, context)}")
    fact = get_fact(node.fact, context)
    items, body = collect_quantifier_vars(fact, Forall)
    env: dict[Term, Term] = {}
    for k, v in node.env.items():
        if not any(item.name == k for item in items):
            logger.error(f"{error_prefix}Key {k} is not found in fact")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Key {k} is found in fact")
        item = next(item for item in items if item.name == k)
        if isinstance(item, Template) and isinstance(v, Lambda):
            if item.arity != len(v.args):
                logger.error(f"{error_prefix}arity of {item.name} is {item.arity}, args of Lambda are {",".join([arg.name for arg in v.args])}")
                node.proofinfo.status = "ERROR"
                return False
            logger.debug(f"{debug_prefix}arity of {item.name} is {item.arity}, args of Lambda are {",".join([arg.name for arg in v.args])}")
        env[item] = v
    used_vars: set[Var | Template] = set()
    for value in env.values():
        used_vars.update(collect_vars(value)[0])
    rename_map: dict[Term, Term] = {}
    new_env: dict[Term, Term] = {}
    for item in env:
        if item in used_vars:
            new_item = fresh_var(item, used_vars)
            used_vars.add(new_item)
            rename_map[item] = new_item
            new_env[new_item] = env[item]
        else:
            new_env[item] = env[item]
    if rename_map:
        body = alpha_rename_formula(body, rename_map)
    logger.debug(f"{debug_prefix}Instantiable: env={env}")
    subst = Substitutor(new_env)
    instantiation = subst.substitute_formula(body)
    logger.debug(f"{debug_prefix}\\forall-elimination is done: instantiation={pretty_expr(instantiation, context)}")
    if node.invoke == "none":
        node.proofinfo.premises = [node.fact]
        node.proofinfo.conclusions = [instantiation]
        add_conclusion(context, instantiation)
        logger.debug(f"{debug_prefix}Added {pretty_expr(instantiation, context)}")
    elif node.invoke == "invoke":
        if not isinstance(instantiation, Implies):
            logger.error(f"{error_prefix}instantiation is not Implies object")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}instantiation is Implies object")
        if not goal_in_context(instantiation.left, context):
            logger.error(f"{error_prefix}Left of instantiation is not derivable: {pretty_expr(instantiation.left, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Left of instantiation is derivable: {pretty_expr(instantiation.left, context)}")
        node.proofinfo.premises = [node.fact, instantiation.left]
        node.proofinfo.conclusions = [instantiation.right]
        add_conclusion(context, instantiation.right)
        logger.debug(f"{debug_prefix}Added {pretty_expr(instantiation.right, context)}")
    elif node.invoke == "invoke-rightward":
        if not isinstance(instantiation, Iff):
            logger.error(f"{error_prefix}instantiation is not Iff object")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}instantiation is Iff object")
        if not goal_in_context(instantiation.left, context):
            logger.error(f"{error_prefix}Left of instantiation is not derivable: {pretty_expr(instantiation.left, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Left of instantiation is derivable: {pretty_expr(instantiation.left, context)}")
        node.proofinfo.premises = [node.fact, instantiation.left]
        node.proofinfo.conclusions = [instantiation.right]
        add_conclusion(context, instantiation.right)
        logger.debug(f"{debug_prefix}Added {pretty_expr(instantiation.right, context)}")
    elif node.invoke == "invoke-leftward":
        if not isinstance(instantiation, Iff):
            logger.error(f"{error_prefix}instantiation is not Iff object")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}instantiation is Iff object")
        if not goal_in_context(instantiation.right, context):
            logger.error(f"{error_prefix}Right of instantiation is not derivable: {pretty_expr(instantiation.right, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Right of instantiation is derivable: {pretty_expr(instantiation.right, context)}")
        node.proofinfo.premises = [node.fact, instantiation.right]
        node.proofinfo.conclusions = [instantiation.left]
        add_conclusion(context, instantiation.left)
        logger.debug(f"{debug_prefix}Added {pretty_expr(instantiation.left, context)}")
    else:
        logger.error(f"{error_prefix}Unexpected invoke option {node.invoke}")
        node.proofinfo.status = "ERROR"
        return False
    node.proofinfo.status = "OK"
    return True

def check_lift(node: Lift, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}Target conclusion: {pretty_expr(node.conclusion, context)}")
    vars, body = collect_quantifier_vars(node.conclusion, Exists)
    if set(vars) != set(node.env):
        logger.error(f"{error_prefix}Not matched: vars: {vars}, node.env: {node.env}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Matched: vars: {vars}, node.env: {node.env}")
    subst = Substitutor(node.env)
    fact = subst.substitute_formula(body)
    if not goal_in_context(fact, context):
        logger.error(f"{error_prefix}Not fact: {pretty_expr(fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Fact: {pretty_expr(fact, context)}")
    node.proofinfo.status = "OK"
    node.proofinfo.premises = [fact]
    node.proofinfo.conclusions = [node.conclusion]
    add_conclusion(context, node.conclusion)
    logger.debug(f"{debug_prefix}Added {pretty_expr(node.conclusion, context)}")
    return True

def check_characterize(node: Characterize, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if not isinstance(node.conclusion, ExistsUniq):
        logger.error(f"{error_prefix}Target conclusion is not ExistsUniq object: {pretty_expr(node.conclusion, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Target conclusion is ExistsUniq object: {pretty_expr(node.conclusion, context)}")
    if node.conclusion.var != list(node.env.keys())[0]:
        logger.error(f"{error_prefix}node.conclusion.var {node.conclusion.var} is not matched with node.env {node.env}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}node.conclusion.var {node.conclusion.var} is matched with node.env {node.env}")
    free, bound = collect_vars(node.conclusion.body)
    vardash = fresh_var(Var(node.conclusion.var.name + "'"), free | bound)
    if context.decl.equality is None:
        logger.error(f"{error_prefix}equality has not been declared yet")
        node.proofinfo.status = "ERROR"
        return False
    subst = Substitutor(node.env)
    existence = subst.substitute_formula(node.conclusion.body)
    subst = Substitutor({node.conclusion.var: vardash})
    existence_dash = subst.substitute_formula(node.conclusion.body)
    fact = And(existence, Forall(vardash, Implies(existence_dash, Symbol(Pred(context.decl.equality.equal.name), (vardash, list(node.env.values())[0])))))
    if not goal_in_context(fact, context):
        logger.error(f"{error_prefix}Not fact: {pretty_expr(fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Fact: {pretty_expr(fact, context)}")
    node.proofinfo.status = "OK"
    node.proofinfo.premises = [fact]
    node.proofinfo.conclusions = [node.conclusion]
    add_conclusion(context, node.conclusion)
    return True

def check_invoke(node: Invoke, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if not goal_in_context(node.fact, context):
        logger.error(f"{error_prefix}Not fact: {pretty_expr(node.fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}fact: {pretty_expr(node.fact, context)}")
    if node.direction == "none":
        if not isinstance(node.fact, Implies):
            logger.error(f"{error_prefix}Not Implies object: {pretty_expr(node.fact, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Implies object: {pretty_expr(node.fact, context)}")
        if not goal_in_context(node.fact.left, context):
            logger.error(f"{error_prefix}Left of Implies object not derived: {pretty_expr(node.fact.left, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Left of Implies object derived: {pretty_expr(node.fact.left, context)}")
        node.proofinfo.premises = [node.fact, node.fact.left]
        node.proofinfo.conclusions = [node.fact.right]
        add_conclusion(context, node.fact.right)
        logger.debug(f"{debug_prefix}Right of Implies object added: {pretty_expr(node.fact.right, context)}")
    elif node.direction == "rightward":
        if not isinstance(node.fact, Iff):
            logger.error(f"{error_prefix}Not Iff object: {pretty_expr(node.fact, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Iff object: {pretty_expr(node.fact, context)}")
        if not goal_in_context(node.fact.left, context):
            logger.error(f"{error_prefix}Left of Iff object not derived: {pretty_expr(node.fact.left, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Left of Iff object derived: {pretty_expr(node.fact.left, context)}")
        node.proofinfo.premises = [node.fact, node.fact.left]
        node.proofinfo.conclusions = [node.fact.right]
        add_conclusion(context, node.fact.right)
        logger.debug(f"{debug_prefix}Right of Iff object added: {pretty_expr(node.fact.right, context)}")
    elif node.direction == "leftward":
        if not isinstance(node.fact, Iff):
            logger.error(f"{error_prefix}Not Iff object: {pretty_expr(node.fact, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Iff object: {pretty_expr(node.fact, context)}")
        if not goal_in_context(node.fact.right, context):
            logger.error(f"{error_prefix}Right of Iff object not derived: {pretty_expr(node.fact.right, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Right of Iff object derived: {pretty_expr(node.fact.right, context)}")
        node.proofinfo.premises = [node.fact, node.fact.right]
        node.proofinfo.conclusions = [node.fact.left]
        add_conclusion(context, node.fact.left)
        logger.debug(f"{debug_prefix}Left of Iff object added: {pretty_expr(node.fact.left, context)}")
    else:
        logger.error(f"{error_prefix}Unexpected direction: {node.direction}")
        node.proofinfo.status = "ERROR"
        return False
    node.proofinfo.status = "OK"
    return True

def check_expand(node: Expand, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if not goal_in_context(node.fact, context):
        logger.error(f"{error_prefix}Not fact: {pretty_expr(node.fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}fact: {pretty_expr(node.fact, context)}")
    fact = get_fact(node.fact, context)
    exp = DefExpander(context, node.defs, node.indexes)
    conclusion = exp.expand_defs_formula(fact)
    node.proofinfo.status = "OK"
    node.proofinfo.premises = [fact]
    node.proofinfo.conclusions = [conclusion]
    add_conclusion(context, conclusion)
    logger.debug(f"{debug_prefix}Added: {pretty_expr(conclusion, context)}")
    return True

def check_fold(node: Fold, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    exp = DefExpander(context, node.defs, node.indexes)
    fact = exp.expand_defs_formula(node.conclusion)
    if not goal_in_context(fact, context):
        logger.error(f"{error_prefix}Not fact: {pretty_expr(fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}fact: {pretty_expr(fact, context)}")
    node.proofinfo.status = "OK"
    node.proofinfo.premises = [fact]
    node.proofinfo.conclusions = [node.conclusion]
    add_conclusion(context, node.conclusion)
    logger.debug(f"{debug_prefix}Added: {pretty_expr(node.conclusion, context)}")
    return True

def check_pad(node: Pad, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if not goal_in_context(node.fact, context):
        logger.error(f"{error_prefix}Not derivable: {pretty_expr(node.fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Derivable: {pretty_expr(node.fact, context)}")
    fact = get_fact(node.fact, context)
    if not isinstance(node.conclusion, Or):
        logger.error(f"{error_prefix}Not Or object: {pretty_expr(node.conclusion, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Or object: {pretty_expr(node.conclusion, context)}")
    fact_parts = flatten_op(fact, Or)
    conclusion_parts = flatten_op(node.conclusion, Or)
    if not all(any(alpha_equiv_with_defs(c, f, context) for c in conclusion_parts) for f in fact_parts):
        logger.error(f"{error_prefix}neither left or right not derivable: {pretty_expr(node.conclusion, context)}")
        node.proofinfo.status = "ERROR"
        return False
    node.proofinfo.status = "OK"
    node.proofinfo.premises = [fact]
    node.proofinfo.conclusions = [node.conclusion]
    add_conclusion(context, node.conclusion)
    logger.debug(f"{debug_prefix}Derivable, added {pretty_expr(node.conclusion, context)}")
    return True

def check_split(node: Split, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if not goal_in_context(node.fact, context):
        logger.error(f"{error_prefix}Not derivable: {pretty_expr(node.fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Derivable: {pretty_expr(node.fact, context)}")
    if isinstance(node.fact, And):
        logger.debug(f"{debug_prefix}And object: {pretty_expr(node.fact, context)}")
        fact_parts = flatten_op(node.fact, And)
        node.proofinfo.premises = [node.fact]
        if node.index is None:
            node.proofinfo.conclusions = fact_parts
            for f in fact_parts:
                add_conclusion(context, f)
                logger.debug(f"{debug_prefix}added {pretty_expr(f, context)}")
        else:
            if node.index <= 0 or node.index > len(fact_parts):
                logger.error(f"{error_prefix}index out of range, index: {node.index}, len(fact_parts): {len(fact_parts)}")
                node.proofinfo.status = "ERROR"
                return False
            f = fact_parts[node.index - 1]
            node.proofinfo.conclusions = [f]
            add_conclusion(context, f)
            logger.debug(f"{debug_prefix}added {pretty_expr(f, context)}")
        node.proofinfo.status = "OK"
        return True
    elif isinstance(node.fact, Iff):
        logger.debug(f"{debug_prefix}Iff object: {pretty_expr(node.fact, context)}")
        implication_rightward = Implies(node.fact.left, node.fact.right)
        implication_leftward = Implies(node.fact.right, node.fact.left)
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [node.fact]
        node.proofinfo.conclusions = [implication_rightward, implication_leftward]
        add_conclusion(context, implication_rightward)
        add_conclusion(context, implication_leftward)
        logger.debug(f"{debug_prefix}added {pretty_expr(implication_rightward, context)}")
        logger.debug(f"{debug_prefix}added {pretty_expr(implication_leftward, context)}")
        return True
    else:
        logger.error(f"{error_prefix}Not And or Iff object: {pretty_expr(node.fact, context)}")
        node.proofinfo.status = "ERROR"
        return False

def check_connect(node: Connect, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if isinstance(node.conclusion, And):
        logger.debug(f"{debug_prefix}And object: {pretty_expr(node.conclusion, context)}")
        conclusion_parts = flatten_op(node.conclusion, And)
        for c in conclusion_parts:
            if not goal_in_context(c, context):
                logger.error(f"{error_prefix}Not derivable: {pretty_expr(c, context)}")
                node.proofinfo.status = "ERROR"
                return False
        node.proofinfo.status = "OK"
        node.proofinfo.premises = conclusion_parts
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        logger.debug(f"{debug_prefix}Derivable, added {pretty_expr(node.conclusion, context)}")
        return True
    elif isinstance(node.conclusion, Iff):
        logger.debug(f"{debug_prefix}Iff object: {pretty_expr(node.conclusion, context)}")
        implication_rightward = Implies(node.conclusion.left, node.conclusion.right)
        if not goal_in_context(implication_rightward, context):
            logger.error(f"{error_prefix}Not derivable: {pretty_expr(implication_rightward, context)}")
            node.proofinfo.status = "ERROR"
            return False
        implication_leftward = Implies(node.conclusion.right, node.conclusion.left)
        if not goal_in_context(implication_leftward, context):
            logger.error(f"{error_prefix}Not derivable: {pretty_expr(implication_leftward, context)}")
            node.proofinfo.status = "ERROR"
            return False
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [implication_rightward, implication_leftward]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        logger.debug(f"{debug_prefix}derivable, added {pretty_expr(node.conclusion, context)}")
        return True
    else:
        logger.error(f"{error_prefix}Not And or Iff object: {pretty_expr(node.conclusion, context)}")
        node.proofinfo.status = "ERROR"
        return False

def check_substitute(node: Substitute, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if not goal_in_context(node.fact, context):
        logger.error(f"{error_prefix}Not fact: {pretty_expr(node.fact, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Fact: {pretty_expr(node.fact, context)}")
    fact = get_fact(node.fact, context)
    if context.decl.equality is None:
        logger.error(f"{error_prefix}equality has not been declared yet")
        node.proofinfo.status = "ERROR"
        return False
    premises_equal: list[str | Symbol] = []
    for k, v in node.env.items():
        equation = Symbol(Pred(context.decl.equality.equal.name), (k, v))
        if not goal_in_context(equation, context):
            logger.error(f"{error_prefix}Not fact: {pretty_expr(equation, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Fact: {pretty_expr(equation, context)}")
        premises_equal.append(equation)
    subst = Substitutor(node.env, node.indexes)
    conclusion = subst.substitute_formula(fact)
    logger.debug(f"{debug_prefix}conclusion: {pretty_expr(conclusion, context)}")
    logger.debug(f"{debug_prefix}Matched")
    node.proofinfo.status = "OK"
    node.proofinfo.premises = [fact] + premises_equal
    node.proofinfo.conclusions = [conclusion]
    add_conclusion(context, conclusion)
    logger.debug(f"{debug_prefix}Added {pretty_expr(conclusion, context)}")
    return True

def check_show(node: Show, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}Target conclusion: {pretty_expr(node.conclusion, context)}")
    local_ctx = context.copy_ctrl()
    for stmt in node.body:
        if not check_control(stmt, local_ctx, indent+1):
            node.proofinfo.status = "ERROR"
            return False
    if not (len(context.ctrl.formulas) < len(local_ctx.ctrl.formulas) and context.ctrl.formulas == local_ctx.ctrl.formulas[:len(context.ctrl.formulas)]):
        logger.error(f"{error_prefix}[Show] Local context must extend the parent context")
        node.proofinfo.status = "ERROR"
        return False
    goal = local_ctx.ctrl.formulas[-1]
    logger.debug(f"{debug_prefix}derived goal: {pretty_expr(goal, context)}")
    if not alpha_equiv_with_defs(node.conclusion, goal, context):
        logger.error(f"{error_prefix}[Show] Not matched with target conclusion: {pretty_expr(node.conclusion, context)}")
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

def check_assert(node: Assert, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if not goal_in_context(node.reference, context):
        logger.error(f"{error_prefix}Not fact: {pretty_expr(node.reference, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Fact: {pretty_expr(node.reference, context)}")
    formula = get_fact(node.reference, context)
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
    parser_context = Context.init()
    checker_context = Context.init()
    for file in resolved_files:
        from parser import Parser
        parser = Parser(tokens_cache[file])
        ast, parser_context = parser.parse_file(parser_context)
        result, _, checker_context = check_ast(ast, checker_context)
        if result:
            print("All theorems proved")
        else:
            print("❌ Not all theorems proved")
