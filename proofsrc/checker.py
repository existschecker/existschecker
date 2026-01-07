from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, AtomicFormula, And, Or, Implies, Forall, Exists, Not, Bottom, Iff, Axiom, Invoke, Expand, PrimPred, DefPred, DefCon, Pad, Split, Connect, ExistsUniq, Compound, Fun, Con, DefFun, DefFunTerm, Equality, Var, Substitute, Characterize, Show, Pred, Control, Formula, Declaration, PredTemplate, Term, DefConExist, DefConUniq, DefFunExist, DefFunUniq, EqualityReflection, EqualityReplacement, Include, DeclarationSupport, Assert, Fold, Membership, MembershipLambda, VarTerm, PredTerm, DefFunTemplateTerm, CompoundPredTerm, FunTemplate
from logic_utils import Substitutor, DefExpander, expr_in_context, collect_quantifier_vars, make_quantifier_vars, collect_vars, flatten_op, fresh_var, alpha_equiv_with_defs, pretty_expr, alpha_safe_formula, type_safe
from copy import deepcopy

import logging
logger = logging.getLogger("proof")

def goal_in_context(goal: str | Bottom | Formula, context: Context) -> bool:
    if isinstance(goal, str):
        return context.decl.has_reference(goal)
    elif isinstance(goal, AtomicFormula) and context.decl.equality is not None and isinstance(goal.pred, Pred) and goal.pred.name == context.decl.equality.equal.name and goal.args[0] == goal.args[1]:
        return True
    else:
        return expr_in_context(goal, context)

def get_fact(fact: str | Formula, context: Context, expand_symbol: bool = False) -> Formula:
    if isinstance(fact, str):
        fact = context.decl.get_reference(fact)
    elif not isinstance(fact, Formula):
        raise Exception(f"Unexpected type {type(fact)}")
    if expand_symbol and isinstance(fact, AtomicFormula) and isinstance(fact.pred, Pred):
        if not fact.pred.name in context.decl.defpreds:
            raise Exception(f"Unexpected {fact.pred.name}")
        fact = DefExpander([fact.pred.name]).expand_defs_formula(fact, context)
    if expand_symbol and isinstance(fact, AtomicFormula) and isinstance(fact.pred, CompoundPredTerm):
        if not fact.pred.fun.name in context.decl.deffuntemplateterms:
            raise Exception(f"Unexpected {fact.pred.fun.name}")
        fact = DefExpander([fact.pred.fun.name]).expand_defs_formula(fact, context)
    return fact

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
    elif isinstance(node, DefFunTemplateTerm):
        return check_deffuntemplateterm(node, context, indent)
    elif isinstance(node, Equality):
        return check_equality(node, context, indent)
    elif isinstance(node, Membership):
        return check_membership(node, context, indent)
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
    existence_formula = Substitutor({existsuniq.var: Con(node.con_name)}, context).substitute_formula(existsuniq.body)
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
    if not isinstance(existsuniq.var, Var):
        logger.error(f"{error_prefix}Unexpected type: {type(existsuniq.var)}")
        node.proofinfo.status = "ERROR"
        return False
    fv, bv, ft, bt = collect_vars(existsuniq.body)
    var = fresh_var(existsuniq.var, fv | bv | ft | bt, context)
    body = Substitutor({existsuniq.var: var}, context).substitute_formula(existsuniq.body)
    if context.decl.equality is None:
        logger.error(f"{error_prefix}equality has not been declared yet")
        node.proofinfo.status = "ERROR"
        return False
    uniqueness_formula = Forall(var, Implies(body, AtomicFormula(Pred(context.decl.equality.equal.name), (MembershipLambda(var), MembershipLambda(Con(node.con_name))))))
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
    logger.debug(f"{debug_prefix}name: {node.name}, theorem: {node.theorem}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_deffunexist(node: DefFunExist, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, fun_name: {node.fun_name}")
    args, body = collect_quantifier_vars(context.decl.theorems[context.decl.deffuns[node.fun_name].theorem].conclusion, Forall)
    if isinstance(body, ExistsUniq):
        existence_formula = Substitutor({body.var: Compound(Fun(node.fun_name), tuple(args))}, context).substitute_formula(body.body)
    elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
        existence_formula = Implies(body.left, Substitutor({body.right.var: Compound(Fun(node.fun_name), tuple(args))}, context).substitute_formula(body.right.body))
    else:
        logger.error(f"{error_prefix}Unexpected formula: {pretty_expr(body, context)}")
        node.proofinfo.status = "ERROR"
        return False
    existence_formula = make_quantifier_vars(existence_formula, Forall ,args)
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
    if context.decl.equality is None:
        logger.error(f"{error_prefix}equality has not been declared yet")
        node.proofinfo.status = "ERROR"
        return False
    args, body = collect_quantifier_vars(context.decl.theorems[context.decl.deffuns[node.fun_name].theorem].conclusion, Forall)
    if isinstance(body, ExistsUniq):
        uniqueness_formula = Forall(body.var, Implies(body.body, AtomicFormula(Pred(context.decl.equality.equal.name), (MembershipLambda(Var(body.var.name)), MembershipLambda(Compound(Fun(node.fun_name), tuple(args)))))))
    elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
        uniqueness_formula = Implies(body.left, Forall(body.right.var, Implies(body.right.body, AtomicFormula(Pred(context.decl.equality.equal.name), (MembershipLambda(Var(body.right.var.name)), MembershipLambda(Compound(Fun(node.fun_name), tuple(args))))))))
    else:
        logger.error(f"{error_prefix}Unexpected formula: {pretty_expr(body, context)}")
        node.proofinfo.status = "ERROR"
        return False
    uniqueness_formula = make_quantifier_vars(uniqueness_formula, Forall, args)
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
    fv, _, ft, _ = collect_vars(node.term)
    if set(node.args) != set(fv) | set(ft):
        logger.error(f"{error_prefix}args are not matched with free vars: {set(fv) | set(ft)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}args are mathced with free vars of term: {set(fv) | set(ft)}")
    context.add_decl(node)
    node.proofinfo.status = "OK"
    return True

def check_deffuntemplateterm(node: DefFunTemplateTerm, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.name}, args: {node.args}, term: {pretty_expr(node.term, context)}")
    fv, _, ft, _ = collect_vars(node.term)
    if set(node.args) != set(fv) | set(ft):
        logger.error(f"{error_prefix}args are not matched with free vars: {set(fv) | set(ft)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}args are mathced with free vars of term: {set(fv) | set(ft)}")
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
    reflection = Forall(Var("x"), AtomicFormula(Pred(node.equal.name), (MembershipLambda(Var("x")), MembershipLambda(Var("x")))))
    if not alpha_equiv_with_defs(node.evidence.conclusion, reflection, context):
        logger.error(f"{error_prefix}Not matched with expected formula: {pretty_expr(reflection, context)}")
        node.proofinfo.status = "ERROR"
        return False
    logger.debug(f"{debug_prefix}Matched with expected formula: {pretty_expr(reflection, context)}")
    node.proofinfo.status = "OK"
    return True

def check_equality_replacement(node: EqualityReplacement, context: Context, indent: int):
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

def check_membership(node: Membership, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    logger.debug(f"{debug_prefix}name: {node.membership.name}")
    context.add_decl(node)
    logger.debug(f"{debug_prefix}{node.membership.name} is registered as membership")
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
    for item in node.items:
        if item.name in context.ctrl.used_names or item.name in context.decl.used_names:
            logger.error(f"{error_prefix}{pretty_expr(item, context)} is already used")
            node.proofinfo.status = "ERROR"
            return False
    logger.debug(f"{debug_prefix}Taking {node.items}")
    local_vars = [item for item in node.items if isinstance(item, Var)]
    local_pred_tmpls = [item for item in node.items if isinstance(item, PredTemplate)]
    local_fun_tmpls = [item for item in node.items if isinstance(item, FunTemplate)]
    local_ctx = context.add_ctrl(local_vars, [], local_pred_tmpls, local_fun_tmpls)
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
    local_ctx = context.add_ctrl([], [node.premise], [], [])
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
    fact = get_fact(node.fact, context, True)
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
    local_ctx = context.add_ctrl([], [node.premise], [], [])
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
    fact = get_fact(node.fact, context, True)
    if isinstance(fact, Exists):
        vars, body = collect_quantifier_vars(fact, Exists)
        body = make_quantifier_vars(body, Exists, [bound for bound, free in zip(vars, node.items) if free is None])
    elif isinstance(fact, ExistsUniq):
        vars, body= collect_quantifier_vars(fact, ExistsUniq)
        if len(vars) != 1:
            logger.error(f"{error_prefix}Unexpected len(vars): {len(vars)}")
            node.proofinfo.status = "ERROR"
            return False
    else:
        logger.error(f"{error_prefix}Unexpected type: {type(fact)}")
        node.proofinfo.status = "ERROR"
        return False
    if len(vars) != len(node.items):
        logger.error(f"{error_prefix}len(vars): {len(vars)}, len(node.items): {len(node.items)}")
        node.proofinfo.status = "ERROR"
        return False
    for item in node.items:
        if item is None:
            continue
        if item.name in context.ctrl.used_names or item.name in context.decl.used_names:
            logger.error(f"{error_prefix}{pretty_expr(item, context)} is already used")
            node.proofinfo.status = "ERROR"
            return False
    mapping: dict[Term, Term] = {bound: free for bound, free in zip(vars, node.items) if free is not None}
    renamed_body, renamed_mapping = alpha_safe_formula(body, mapping, context)
    if not type_safe(renamed_mapping, context, True):
        logger.error(f"{error_prefix}type_safe() failed")
        node.proofinfo.status = "ERROR"
        return False
    existence = Substitutor(renamed_mapping, context).substitute_formula(renamed_body)
    if isinstance(fact, Exists):
        premises: list[Bottom | Formula] = [existence]
    else:
        fv, bv, ft, bt = collect_vars(existence)
        if not isinstance(vars[0], Var):
            logger.error(f"{error_prefix}Unexpected type: {type(vars[0])}")
            node.proofinfo.status = "ERROR"
            return False
        var = fresh_var(vars[0], fv | bv | ft | bt, context)
        body = Substitutor({vars[0]: var}, context).substitute_formula(existence)
        if context.decl.equality is None:
            logger.error(f"{error_prefix}equality has not been declared yet")
            node.proofinfo.status = "ERROR"
            return False
        uniqueness = Forall(var, Implies(body, AtomicFormula(Pred(context.decl.equality.equal.name), (MembershipLambda(var), MembershipLambda(vars[0])))))
        premises: list[Bottom | Formula] = [existence, uniqueness]
    logger.debug(f"{debug_prefix}Taking {node.items}, premise={pretty_expr(existence, context)}")
    local_vars = [item for item in node.items if isinstance(item, Var)]
    local_ctx = context.add_ctrl(local_vars, premises, [], [])
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
    if isinstance(goal, Formula):
        goal_fv, _, _, _ = collect_vars(goal)
        for fv in goal_fv:
            if fv in local_vars:
                logger.error(f"{error_prefix}Conclusion depends on local variable {pretty_expr(fv, context)}")
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

def check_deny(node: Deny, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    logger.debug(f"{debug_prefix}premise={pretty_expr(node.premise, context)}")
    local_ctx = context.add_ctrl([], [node.premise], [], [])
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
    fact = get_fact(node.fact, context, True)
    items, body = collect_quantifier_vars(fact, Forall)
    body = make_quantifier_vars(body, Forall, [item for item, term in zip(items, node.terms) if term is None])
    mapping: dict[Term, Term] = {}
    for item, term in zip(items, node.terms):
        if term is None:
            continue
        if isinstance(item, PredTerm) and item.arity == 1 and isinstance(term, VarTerm):
            mapping[item] = MembershipLambda(term)
        else:
            mapping[item] = term
    renamed_body, renamed_map = alpha_safe_formula(body, mapping, context)
    if not type_safe(renamed_map, context):
        logger.error(f"{error_prefix}type_safe() failed")
        node.proofinfo.status = "ERROR"
        return False
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
    items, body = collect_quantifier_vars(node.conclusion, Exists)
    body = make_quantifier_vars(body, Exists, [item for item, term in zip(items, node.terms) if term is None])
    mapping: dict[Term, Term] = {item: term for item, term in zip(items, node.terms) if term is not None}
    renamed_body, renamed_mapping = alpha_safe_formula(body, mapping, context)
    if not type_safe(renamed_mapping, context):
        logger.error(f"{error_prefix}type_safe() failed")
        node.proofinfo.status = "ERROR"
        return False
    fact = Substitutor(renamed_mapping, context).substitute_formula(renamed_body)
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
    _, used_bound_vars, _, used_bound_pred_tmpls = collect_vars(node.conclusion.body)
    fv, bv, ft, bt = collect_vars(node.term)
    vardash = fresh_var(Var(node.conclusion.var.name + "'"), used_bound_vars | used_bound_pred_tmpls | fv | bv | ft | bt, context)
    renamed_conclusion, _ = alpha_safe_formula(node.conclusion, {node.conclusion.var: node.term}, context)
    if not isinstance(renamed_conclusion, ExistsUniq):
        logger.error(f"{error_prefix}renamed_conclusion is not ExistsUniq object: {pretty_expr(renamed_conclusion, context)}")
        node.proofinfo.status = "ERROR"
        return False
    existence = Substitutor({renamed_conclusion.var: node.term}, context).substitute_formula(renamed_conclusion.body)
    existence_dash = Substitutor({renamed_conclusion.var: vardash}, context).substitute_formula(renamed_conclusion.body)
    if context.decl.equality is None:
        logger.error(f"{error_prefix}equality has not been declared yet")
        node.proofinfo.status = "ERROR"
        return False
    if not isinstance(node.term, VarTerm):
        logger.error(f"{error_prefix}Unexpected type: {type(node.term)}")
        node.proofinfo.status = "ERROR"
        return False
    fact = And(existence, Forall(vardash, Implies(existence_dash, AtomicFormula(Pred(context.decl.equality.equal.name), (MembershipLambda(vardash), MembershipLambda(node.term))))))
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
    conclusion = DefExpander(node.defs, node.indexes).expand_defs_formula(fact, context)
    node.proofinfo.status = "OK"
    node.proofinfo.premises = [fact]
    node.proofinfo.conclusions = [conclusion]
    add_conclusion(context, conclusion)
    logger.debug(f"{debug_prefix}Added: {pretty_expr(conclusion, context)}")
    return True

def check_fold(node: Fold, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    fact = DefExpander(node.defs, node.indexes).expand_defs_formula(node.conclusion, context)
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
    fact = get_fact(node.fact, context, True)
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
                logger.error(f"{error_prefix}index out of range, index: {node.index}, len(fact_parts): {len(fact_parts)}")
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
        implication_rightward = Implies(fact.left, fact.right)
        implication_leftward = Implies(fact.right, fact.left)
        node.proofinfo.status = "OK"
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [implication_rightward, implication_leftward]
        add_conclusion(context, implication_rightward)
        add_conclusion(context, implication_leftward)
        logger.debug(f"{debug_prefix}added {pretty_expr(implication_rightward, context)}")
        logger.debug(f"{debug_prefix}added {pretty_expr(implication_leftward, context)}")
        return True
    else:
        logger.error(f"{error_prefix}Not And or Iff object: {pretty_expr(fact, context)}")
        node.proofinfo.status = "ERROR"
        return False

def check_connect(node: Connect, context: Context, indent: int):
    debug_prefix = make_debug_prefix(node, indent)
    error_prefix = make_error_prefix(node, indent)
    if isinstance(node.conclusion, AtomicFormula):
        if not isinstance(node.conclusion.pred, Pred):
            raise Exception(f"Unexpected type: {type(node.conclusion.pred)}")
        if not node.conclusion.pred.name in context.decl.defpreds:
            raise Exception(f"Unexpected {node.conclusion.pred.name}")
        conclusion = DefExpander([node.conclusion.pred.name]).expand_defs_formula(node.conclusion, context)
    else:
        conclusion = node.conclusion
    if isinstance(conclusion, And):
        logger.debug(f"{debug_prefix}And object: {pretty_expr(conclusion, context)}")
        conclusion_parts = flatten_op(conclusion, And)
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
    elif isinstance(conclusion, Iff):
        logger.debug(f"{debug_prefix}Iff object: {pretty_expr(conclusion, context)}")
        implication_rightward = Implies(conclusion.left, conclusion.right)
        if not goal_in_context(implication_rightward, context):
            logger.error(f"{error_prefix}Not derivable: {pretty_expr(implication_rightward, context)}")
            node.proofinfo.status = "ERROR"
            return False
        implication_leftward = Implies(conclusion.right, conclusion.left)
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
    premises_equal: list[str | AtomicFormula] = []
    for k, v in node.env.items():
        if not isinstance(k, VarTerm):
            raise Exception(f"Unexpected type: {type(k)}")
        if not isinstance(v, VarTerm):
            raise Exception(f"Unexpected type: {type(v)}")
        equation = AtomicFormula(Pred(context.decl.equality.equal.name), (MembershipLambda(k), MembershipLambda(v)))
        if not goal_in_context(equation, context):
            logger.error(f"{error_prefix}Not fact: {pretty_expr(equation, context)}")
            node.proofinfo.status = "ERROR"
            return False
        logger.debug(f"{debug_prefix}Fact: {pretty_expr(equation, context)}")
        premises_equal.append(equation)
    renamed_fact, _ = alpha_safe_formula(fact, node.env, context, True)
    conclusion = Substitutor(node.env, context, node.indexes).substitute_formula(renamed_fact)
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
            break
