from ast_types import Context, Theorem, Any, Assume, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, Symbol, And, Or, Implies, Forall, Exists, Not, Bottom, Iff, Axiom, Invoke, Expand, PrimPred, DefPred, DefCon, Pad, Split, Connect, ExistsUniq, DefConExist, DefConUniq, Compound, Fun, Con, DefFun, DefFunExist, DefFunUniq, DefFunTerm, Equality, Var, Substitute, Symbol, Characterize, Show, Pred, Control, ProofInfo, Formula, Declaration, Template, pretty_expr
from logic_utils import expr_in_context, collect_quantifier_vars, substitute, collect_vars, flatten_op, fresh_var, alpha_equiv, alpha_equiv_with_defs
from copy import deepcopy

import logging
logger = logging.getLogger("proof")

def goal_in_context(goal: str | Bottom | Formula, context: Context) -> bool:
    if isinstance(goal, str):
        return context.has_reference(goal)
    elif isinstance(goal, Symbol) and context.equality is not None and goal.pred.name == context.equality.equal.name and goal.args[0] == goal.args[1]:
        return True
    else:
        return expr_in_context(goal, context)

def get_fact(fact: str | Formula, context: Context) -> Formula:
    if isinstance(fact, str):
        return context.get_reference(fact)
    elif isinstance(fact, Formula):
        return fact
    else:
        raise Exception(f"Unexpected type {type(fact)}")

def add_conclusion(context: Context, conclusion) -> None:
    context.formulas.append(conclusion)

def check_ast(ast: list[Declaration]) -> tuple[bool, list[Declaration], Context]:
    context = Context.init()
    return all(check_proof(node, context) for node in ast), ast, context

# === 証明チェッカー ===
def check_proof(node: Declaration | Control, context: Context, indent: int = 0) -> bool:
    sp = "  " * indent

    if isinstance(node, PrimPred):
        logger.debug(f"{sp}[PrimPred] type: {node.type}, name: {node.name}, arity: {node.arity}")
        context.primpreds[node.name] = node
        return True

    if isinstance(node, Axiom):
        logger.debug(f"{sp}[Axiom] name: {node.name}, conclusion: {pretty_expr(node.conclusion, context)}")
        context.axioms[node.name] = node
        return True

    # --- Theorem ---
    if isinstance(node, Theorem):
        logger.debug(f"{sp}[Theorem] {node.name}: {pretty_expr(node.conclusion, context)}")
        local_ctx = context.copy([], [], [])
        for stmt in node.proof:
            if not check_proof(stmt, local_ctx, indent+1):
                logger.error(f"{sp}❌ [Theorem] {node.name} not proved: {pretty_expr(node.conclusion, context)}")
                return False
        if goal_in_context(node.conclusion, local_ctx):
            logger.debug(f"{sp}[Theorem] {node.name} proved: {pretty_expr(node.conclusion, context)}")
            context.theorems[node.name] = node
            return True
        else:
            logger.error(f"{sp}❌ [Theorem] {node.name} not proved: {pretty_expr(node.conclusion, context)}")
            return False

    if isinstance(node, DefPred):
        logger.debug(f"{sp}[DefPred] name: {node.name}, args: {node.args}, formula: {pretty_expr(node.formula, context)}")
        context.defpreds[node.name] = node
        return True

    if isinstance(node, DefCon):
        logger.debug(f"{sp}[DefCon] name: {node.name}, theorem: {node.theorem}")
        context.defcons[node.name] = DefCon(node.name, node.theorem, node.tex, None, None)
        existsuniq = context.theorems[node.theorem].conclusion
        if not isinstance(existsuniq, ExistsUniq):
            logger.error(f"{sp}❌ [DefCon] Theorem conclusion is not ExistsUniq object: {pretty_expr(existsuniq, context)}")
            return False
        logger.debug(f"{sp}[DefCon] Theorem conclusion is ExistsUniq object: {pretty_expr(existsuniq, context)}")
        existence_formula = substitute(existsuniq.body, {existsuniq.var: Con(node.name)})
        if not alpha_equiv_with_defs(node.existence.formula, existence_formula, context):
            logger.error(f"{sp}❌ [DefCon] existence_formula is not matched with theorem: {pretty_expr(node.existence.formula, context)}")
            return False
        logger.debug(f"{sp}[DefCon] existence_formula is matched with theorem: {pretty_expr(node.existence.formula, context)}")
        var = fresh_var(existsuniq.var, [Con(node.name)])
        body = substitute(existsuniq.body, {existsuniq.var: var})
        if context.equality is None:
            logger.error(f"{sp}❌ [DefCon] equality has not been declared yet")
            return False
        uniqueness_formula = Forall(var, Implies(body, Symbol(Pred(context.equality.equal.name), [var, Con(node.name)])))
        if not alpha_equiv_with_defs(node.uniqueness.formula, uniqueness_formula, context):
            logger.error(f"{sp}❌ [DefCon] uniqueness_formula is not matched with theorem: {pretty_expr(node.uniqueness.formula, context)}")
            return False
        logger.debug(f"{sp}[DefCon] uniqueness_formula is matched with theorem: {pretty_expr(node.uniqueness.formula, context)}")
        context.defcons[node.name] = node
        return True

    if isinstance(node, DefFun):
        logger.debug(f"{sp}[DefFun] name: {node.name}, theorem: {node.theorem}")
        context.deffuns[node.name] = DefFun(node.name, node.arity, node.theorem, node.tex, None, None)
        args, existsuniq = collect_quantifier_vars(context.theorems[node.theorem].conclusion, Forall)
        if not isinstance(existsuniq, ExistsUniq):
            logger.error(f"{sp}❌ [DefFun] Not ExistsUniq object: {pretty_expr(existsuniq, context)}")
            return False
        logger.debug(f"{sp}[DefFun] ExistsUniq object: {pretty_expr(existsuniq, context)}")
        existence_formula = substitute(existsuniq.body, {existsuniq.var: Compound(Fun(node.name), args)})
        for arg in reversed(args):
            existence_formula = Forall(arg, existence_formula)
        if not alpha_equiv_with_defs(node.existence.formula, existence_formula, context):
            logger.error(f"{sp}❌ [DefFun] existence_formula is not matched with theorem: {pretty_expr(node.existence.formula, context)}")
            return False
        logger.debug(f"{sp}[DefFun] existence_formula is matched with theorem: {pretty_expr(node.existence.formula, context)}")
        if context.equality is None:
            logger.error(f"{sp}❌ [DefFun] equality has not been declared yet")
            return False
        uniqueness_formula = Forall(existsuniq.var, Implies(existsuniq.body, Symbol(Pred(context.equality.equal.name), [existsuniq.var, Compound(Fun(node.name), args)])))
        for arg in reversed(args):
            uniqueness_formula = Forall(arg, uniqueness_formula)
        if not alpha_equiv_with_defs(node.uniqueness.formula, uniqueness_formula, context):
            logger.error(f"{sp}❌ [DefFun] uniqueness_formula is not matched with theorem: {pretty_expr(node.uniqueness.formula, context)}")
            return False
        logger.debug(f"{sp}[DefFun] uniqueness_formula is matched with theorem: {pretty_expr(node.uniqueness.formula, context)}")
        context.deffuns[node.name] = node
        return True

    if isinstance(node, DefFunTerm):
        logger.debug(f"{sp}[DefFunTerm] name: {node.name}, args: {node.args}, term: {pretty_expr(node.term, context)}")
        free, _ = collect_vars(node.term)
        if set(node.args) != set(free):
            logger.error(f"{sp}❌ [DefFunTerm] args are not matched with free vars: {free}")
            return False
        logger.debug(f"{sp}[DefFunTerm] args are mathced with free vars of term: {free}")
        context.deffunterms[node.name] = node
        return True

    if isinstance(node, Equality):
        logger.debug(f"{sp}[Equality] name: {node.equal.name}")
        logger.debug(f"{sp}[Equality] Checking {node.equal.name} reflection theorem: {pretty_expr(node.reflection.evidence.conclusion, context)}")
        reflection = Forall(Var("x"), Symbol(Pred(node.equal.name), [Var("x"), Var("x")]))
        if not alpha_equiv_with_defs(node.reflection.evidence.conclusion, reflection, context):
            logger.error(f"{sp}❌ [Equality] Not matched with expected formula: {pretty_expr(reflection, context)}")
            return False
        logger.debug(f"{sp}[Equality] Matched with expected formula: {pretty_expr(reflection, context)}")
        for predicate in node.replacement.evidence:
            logger.debug(f"{sp}[Equality] Checking {predicate} replacement theorem: {pretty_expr(node.replacement.evidence[predicate].conclusion, context)}")
            if predicate == node.equal.name:
                if isinstance(node.equal, PrimPred):
                    arity = node.equal.arity
                elif isinstance(node.equal, DefPred):
                    arity = len(node.equal.args)
                else:
                    raise Exception("node.equal is not PrimPred or DefPred")
            else:
                arity = context.primpreds[predicate].arity
            args_x = []
            args_y = []
            for i in range(arity):
                args_x.append(Var(f"x_{i}"))
                args_y.append(Var(f"y_{i}"))
            premise = Symbol(Pred(node.equal.name), [args_x[0], args_y[0]])
            for i in range(1, arity):
                premise = And(premise, Symbol(Pred(node.equal.name), [args_x[i], args_y[i]]))
            conclusion = Implies(Symbol(Pred(predicate), args_x), Symbol(Pred(predicate), args_y))
            replacement = Implies(premise, conclusion)
            for arg in reversed(args_y):
                replacement = Forall(arg, replacement)
            for arg in reversed(args_x):
                replacement = Forall(arg, replacement)
            if not alpha_equiv_with_defs(node.replacement.evidence[predicate].conclusion, replacement, context):
                logger.error(f"{sp}❌ [Equality] Not matched with expected formula: {pretty_expr(replacement, context)}")
                return False
            logger.debug(f"{sp}[Equality] Matched with expected formula: {pretty_expr(replacement, context)}")
        context.equality = node
        logger.debug(f"{sp}[Equality] {node.equal.name} is registered as equality")
        return True

    if isinstance(node, Control):
        node.proofinfo = ProofInfo()
        node.proofinfo.context_vars = deepcopy(context.vars)
        node.proofinfo.context_formulas = deepcopy(context.formulas)
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = []

    # --- Any ---
    if isinstance(node, Any):
        local_vars = [item for item in node.items if isinstance(item, Var)]
        for var in local_vars:
            if var in context.vars:
                logger.error(f"{sp}❌ [Any] {pretty_expr(var, context)} is already used")
                return False
        local_templates = [item for item in node.items if isinstance(item, Template)]
        for template in local_templates:
            if template in context.templates:
                logger.error(f"{sp}❌ [Any] {pretty_expr(template, context)} is already used")
                return False
        logger.debug(f"{sp}[Any] Taking {node.items}")
        local_ctx = context.copy(list(context.vars + local_vars), list(context.formulas), list(context.templates + local_templates))
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if not (len(context.formulas) < len(local_ctx.formulas) and context.formulas == local_ctx.formulas[:len(context.formulas)]):
            logger.error(f"{sp}❌ [Any] Local context must extend the parent context")
            return False
        local_goal = local_ctx.formulas[-1]
        logger.debug(f"{sp}[Any] derived local_goal: {pretty_expr(local_goal, context)}")
        if node.conclusion is not None:
            if alpha_equiv_with_defs(node.conclusion, local_goal, context):
                logger.debug(f"{sp}[Any] Mathched with conclusion: {pretty_expr(node.conclusion, context)}")
            else:
                logger.error(f"{sp}❌ [Any] Not matched with conclusion: {pretty_expr(node.conclusion, context)}")
                return False
        goal = local_goal
        for item in reversed(node.items):
            goal = Forall(item, goal)
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = local_vars
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [local_goal]
        add_conclusion(context, goal)
        logger.debug(f"{sp}[Any] Generalized to {pretty_expr(goal, context)}")
        return True

    # --- Assume ---
    if isinstance(node, Assume):
        logger.debug(f"{sp}[Assume] premise={pretty_expr(node.premise, context)}")
        local_ctx = context.copy(list(context.vars), list(context.formulas + [node.premise]), list(context.templates))
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if not (len(context.formulas) < len(local_ctx.formulas) and context.formulas == local_ctx.formulas[:len(context.formulas)]):
            logger.error(f"{sp}❌ [Assume] Local context must extend the parent context")
            return False
        goal = local_ctx.formulas[-1]
        logger.debug(f"{sp}[Assume] derived goal: {pretty_expr(goal, context)}")
        if node.conclusion is not None:
            if alpha_equiv_with_defs(node.conclusion, goal, context):
                logger.debug(f"{sp}[Assume] Matched with conclusion: {pretty_expr(node.conclusion, context)}")
            else:
                logger.error(f"{sp}❌ [Assume] Not matched with conclusion: {pretty_expr(node.conclusion, context)}")
                return False
        implication = Implies(node.premise, goal)
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [implication]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = [node.premise]
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, implication)
        logger.debug(f"{sp}[Assume] Added implication {pretty_expr(implication, context)}")
        return True

    if isinstance(node, Divide):
        if not goal_in_context(node.fact, context):
            logger.error(f"{sp}❌ [Divide] Not fact: {pretty_expr(node.fact, context)}")
            return False
        fact = get_fact(node.fact, context)
        connected_premise = Or(node.cases[0].premise, node.cases[1].premise)
        i = 2
        while i < len(node.cases):
            connected_premise = Or(connected_premise, node.cases[i].premise)
            i += 1
        if alpha_equiv_with_defs(connected_premise, fact, context):
            logger.debug(f"{sp}[Divide] mathched: fact={pretty_expr(fact, context)}, connected_premise={pretty_expr(connected_premise, context)}")
        else:
            logger.error(f"{sp}❌ [Divide] not matched: fact={pretty_expr(fact, context)}, conected_premise={pretty_expr(connected_premise, context)}")
            return False
        logger.debug(f"{sp}[Divide] fact={pretty_expr(fact, context)}")
        local_ctx = context.copy(list(context.vars), list(context.formulas), list(context.templates))
        goals = []
        for stmt in node.cases:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
            if not (len(context.formulas) < len(local_ctx.formulas) and context.formulas == local_ctx.formulas[:len(context.formulas)]):
                logger.error(f"{sp}❌ [Divide] Local context must extend the parent context")
                return False
            goal = local_ctx.formulas[-1]
            logger.debug(f"{sp}[Divide] derived goal: {pretty_expr(goal, context)}")
            goals.append(goal)
        if node.conclusion is None:
            for i in range(len(goals) - 1):
                if not alpha_equiv_with_defs(goals[i], goals[i + 1], context):
                    logger.error(f"{sp}❌ [Divide] Not matched: goals[{i}]={pretty_expr(goals[i], context)}, goals[{i + 1}]={pretty_expr(goals[i + 1], context)}")
                    return False
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [goals[0]]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [goals[0]]
        add_conclusion(context, goals[0])
        logger.debug(f"{sp}[Divide] derived in all cases: {pretty_expr(goals[0], context)}")
        return True

    if isinstance(node, Case):
        logger.debug(f"{sp}[Case] premise={pretty_expr(node.premise, context)}")
        local_ctx = context.copy(list(context.vars), list(context.formulas + [node.premise]), list(context.templates))
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if not (len(context.formulas) < len(local_ctx.formulas) and context.formulas == local_ctx.formulas[:len(context.formulas)]):
            logger.error(f"{sp}❌ [Case] Local context must extend the parent context")
            return False
        goal = local_ctx.formulas[-1]
        logger.debug(f"{sp}[Case] derived goal: {pretty_expr(goal, context)}")
        if node.conclusion is not None:
            if not alpha_equiv_with_defs(node.conclusion, goal, context):
                logger.error(f"{sp}❌ [Case] Not matched with conclusion: {pretty_expr(node.conclusion, context)}")
                return False
            logger.debug(f"{sp}[Case] Mathched with conclusion: {pretty_expr(node.conclusion, context)}")
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = [node.premise]
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, goal)
        logger.debug(f"{sp}[Case] Added goal {pretty_expr(goal, context)}")
        return True

    if isinstance(node, Some):
        if not goal_in_context(node.fact, context):
            logger.error(f"{sp}❌ [Some] not derivable: {pretty_expr(node.fact, context)}")
            return False
        logger.debug(f"{sp}[Some] derivable: {pretty_expr(node.fact, context)}")
        fact = get_fact(node.fact, context)
        if not isinstance(fact, Exists):
            logger.error(f"{sp}❌ Not Exists object: {pretty_expr(node.fact, context)}")
            return False
        vars, body = collect_quantifier_vars(fact, Exists)
        if not set(node.env.keys()).issubset(set(vars)):
            logger.error(f"{sp}❌ invalid vars: node.env.keys()={node.env.keys()}, vars={vars}")
            return False
        for var in node.env.values():
            if var in context.vars:
                logger.error(f"{sp}❌ [Some] {pretty_expr(var, context)} is already used")
        premise = substitute(body, node.env)
        logger.debug(f"{sp}[Some] Taking {node.env.values()}, premise={pretty_expr(premise, context)}")
        local_ctx = context.copy(list(context.vars + list(node.env.values())), list(context.formulas + [premise]), list(context.templates))
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if not (len(context.formulas) < len(local_ctx.formulas) and context.formulas == local_ctx.formulas[:len(context.formulas)]):
            logger.error(f"{sp}❌ [Some] Local context must extend the parent context")
            return False
        goal = local_ctx.formulas[-1]
        logger.debug(f"{sp}[Some] derived goal: {pretty_expr(goal, context)}")
        if node.conclusion is not None:
            if not alpha_equiv_with_defs(node.conclusion, goal, context):
                logger.error(f"{sp}❌ [Some] Not matched with conclusion: {pretty_expr(node.conclusion, context)}")
                return False
            logger.debug(f"{sp}[Some] Mathched with conclusion: {pretty_expr(node.conclusion, context)}")
        node.proofinfo.premises = [node.fact]
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = list(node.env.values())
        node.proofinfo.local_premise = [premise]
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, goal)
        logger.debug(f"{sp}[Some] Added goal {pretty_expr(goal, context)}")
        return True
    
    if isinstance(node, Deny):
        logger.debug(f"{sp}[Deny] premise={pretty_expr(node.premise, context)}")
        local_ctx = context.copy(list(context.vars), list(context.formulas + [node.premise]), list(context.templates))
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if not (len(context.formulas) < len(local_ctx.formulas) and context.formulas == local_ctx.formulas[:len(context.formulas)]):
            logger.error(f"{sp}❌ [Deny] Local context must extend the parent context")
            return False
        goal = local_ctx.formulas[-1]
        logger.debug(f"{sp}[Deny] derived goal: {pretty_expr(goal, context)}")
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
            logger.debug(f"{sp}[Deny] contradiction is derived; added {pretty_expr(conclusion, context)}")
            return True
        else:
            logger.error(f"{sp}❌ [Deny] conradiction has not been deried")
            return False
    
    if isinstance(node, Contradict):
        if not goal_in_context(node.contradiction, context):
            logger.error(f"{sp}❌ [Contradict] Cannot derive {pretty_expr(node.contradiction, context)}")
            return False
        if not goal_in_context(Not(node.contradiction), context):
            logger.error(f"{sp}❌ [Contradict] Cannot derive {pretty_expr(Not(node.contradiction), context)}")
            return False
        logger.debug(f"{sp}[Contradict] Derived contradiction: {pretty_expr(node.contradiction, context)}, {pretty_expr(Not(node.contradiction), context)}")
        conclusion = Bottom()
        node.proofinfo.premises = [node.contradiction, Not(node.contradiction)]
        node.proofinfo.conclusions = [conclusion]
        add_conclusion(context, conclusion)
        return True
    
    if isinstance(node, Explode):
        if goal_in_context(Bottom(), context):
            node.proofinfo.premises = [Bottom()]
            node.proofinfo.conclusions = [node.conclusion]
            add_conclusion(context, node.conclusion)
            logger.debug(f"{sp}[Explode] added {pretty_expr(node.conclusion, context)}")
            return True
        else:
            logger.error(f"{sp}❌ [Explode] contradiction has not been derived")
            return False
        
    if isinstance(node, Apply):
        if not goal_in_context(node.fact, context):
            logger.error(f"{sp}❌ [Apply] Cannot derive fact: {pretty_expr(node.fact, context)}")
            return False
        logger.debug(f"{sp}[Apply] Drivable fact: {pretty_expr(node.fact, context)}")
        fact = get_fact(node.fact, context)
        items, body = collect_quantifier_vars(fact, Forall)
        if set(items) != set(node.env.keys()):
            logger.error(f"{sp}❌ [Apply] Not matched: items={items}, env={node.env}")
            return False
        logger.debug(f"{sp}[Apply] Instantiable: items={items}, env={node.env}")
        instantiation = substitute(body, node.env)
        logger.debug(f"{sp}[Apply] \\forall-elimination is done: instantiation={pretty_expr(instantiation, context)}")
        if node.conclusion is not None:
            if not alpha_equiv_with_defs(node.conclusion, instantiation, context):
                logger.error(f"{sp}❌ [Apply] Not matched: node.conclusion={pretty_expr(node.conclusion, context)}, instantiation={pretty_expr(instantiation, context)}")
                return False
            logger.debug(f"{sp}[Apply] Matched: node.conclusion={pretty_expr(node.conclusion, context)}, instantiation={pretty_expr(instantiation, context)}")
        logger.debug(f"{sp}[Apply] Added {pretty_expr(instantiation, context)}")
        node.proofinfo.premises = [node.fact]
        node.proofinfo.conclusions = [instantiation]
        add_conclusion(context, instantiation)
        return True

    if isinstance(node, Lift):
        logger.debug(f"{sp}[Lift] Target conclusion: {pretty_expr(node.conclusion, context)}")
        vars, body = collect_quantifier_vars(node.conclusion, Exists)
        if set(vars) != set(node.env):
            logger.error(f"{sp}❌ [Lift] Not matched: vars: {vars}, node.env: {node.env}")
            return False
        logger.debug(f"{sp}[Lift] Matched: vars: {vars}, node.env: {node.env}")
        fact = substitute(body, node.env)
        if not goal_in_context(fact, context):
            logger.error(f"{sp}❌ [Lift] Not fact: {pretty_expr(fact, context)}")
            return False
        logger.debug(f"{sp}[Lift] Fact: {pretty_expr(fact, context)}")
        if node.fact is not None:
            if not alpha_equiv_with_defs(node.fact, fact, context):
                logger.error(f"{sp}❌ [Lift] Not matched: node.fact={pretty_expr(node.fact, context)}, fact={pretty_expr(fact, context)}")
                return False
            logger.debug(f"{sp}[Lift] Matched: node.fact={pretty_expr(node.fact, context)}, fact={pretty_expr(fact, context)}")
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Lift] Added {pretty_expr(node.conclusion, context)}")
        return True

    if isinstance(node, Characterize):
        if not isinstance(node.conclusion, ExistsUniq):
            logger.error(f"{sp}❌ [Characterize] Target conclusion is not ExistsUniq object: {pretty_expr(node.conclusion, context)}")
            return False
        logger.debug(f"{sp}[Characterize] Target conclusion is ExistsUniq object: {pretty_expr(node.conclusion, context)}")
        if node.conclusion.var != list(node.env.keys())[0]:
            logger.error(f"{sp}❌ [Characterize] node.conclusion.var {node.conclusion.var} is not matched with node.env {node.env}")
            return False
        logger.debug(f"{sp}[Characterize] node.conclusion.var {node.conclusion.var} is matched with node.env {node.env}")
        free, bound = collect_vars(node.conclusion.body)
        vardash = fresh_var(Var(node.conclusion.var.name + "'"), free | bound)
        if context.equality is None:
            logger.error(f"{sp}❌ [Characterize] equality has not been declared yet")
            return False
        fact = And(substitute(node.conclusion.body, node.env), Forall(vardash, Implies(substitute(node.conclusion.body, {node.conclusion.var: vardash}), Symbol(Pred(context.equality.equal.name), [vardash, list(node.env.values())[0]]))))
        if not goal_in_context(fact, context):
            logger.error(f"{sp}❌ [Characterize] Not fact: {pretty_expr(fact, context)}")
            return False
        logger.debug(f"{sp}[Characterize] Fact: {pretty_expr(fact, context)}")
        if node.fact is not None:
            if not alpha_equiv_with_defs(node.fact, fact, context):
                logger.error(f"{sp}❌ [Characterize] Not matched with node.fact: {pretty_expr(node.fact, context)}")
                return False
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        return True

    if isinstance(node, Invoke):
        if not goal_in_context(node.fact, context):
            logger.error(f"{sp}❌ [Invoke] Not fact: {pretty_expr(node.fact, context)}")
            return False
        logger.debug(f"{sp}[Invoke] fact: {pretty_expr(node.fact, context)}")
        if not isinstance(node.fact, Implies):
            logger.error(f"{sp}❌ [Invoke] Not Implies object: {pretty_expr(node.fact, context)}")
            return False
        logger.debug(f"{sp}[Invoke] Implies object: {pretty_expr(node.fact, context)}")
        if not goal_in_context(node.fact.left, context):
            logger.error(f"{sp}❌ [Invoke] Left of Implies object not derived: {pretty_expr(node.fact.left, context)}")
            return False
        logger.debug(f"{sp}[Invoke] Left of Implies object derived: {pretty_expr(node.fact.left, context)}")
        if node.conclusion is not None:
            if not alpha_equiv_with_defs(node.conclusion, node.fact.right, context):
                logger.error(f"{sp}❌ [Invoke] Not matched: node.conclusion={pretty_expr(node.conclusion, context)}, node.fact.right={pretty_expr(node.fact.right, context)}")
                return False
            logger.debug(f"{sp}[Invoke] Matched: node.conclusion={pretty_expr(node.conclusion, context)}, node.fact.right={pretty_expr(node.fact.right, context)}")
        node.proofinfo.premises = [node.fact, node.fact.left]
        node.proofinfo.conclusions = [node.fact.right]
        add_conclusion(context, node.fact.right)
        logger.debug(f"{sp}[Invoke] Right of Implies object added: {pretty_expr(node.fact.right, context)}")
        return True

    if isinstance(node, Expand):
        if not goal_in_context(node.fact, context):
            logger.error(f"{sp}❌ [Expand] Not fact: {pretty_expr(node.fact, context)}")
            return False
        logger.debug(f"{sp}[Expand] fact: {pretty_expr(node.fact, context)}")
        fact = get_fact(node.fact, context)
        if not alpha_equiv_with_defs(node.conclusion, fact, context, True):
            logger.error(f"{sp}❌ [Expand] Not matched: node.conclusion={pretty_expr(node.conclusion, context)}")
            return False
        logger.debug(f"{sp}[Expand] Matched: node.conclusion={pretty_expr(node.conclusion, context)}")
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Expand] Added: {pretty_expr(node.conclusion, context)}")
        return True

    if isinstance(node, Pad):
        if not goal_in_context(node.fact, context):
            logger.error(f"{sp}❌ [Pad] Not derivable: {pretty_expr(node.fact, context)}")
            return False
        logger.debug(f"{sp}[Pad] Derivable: {pretty_expr(node.fact, context)}")
        fact = get_fact(node.fact, context)
        if not isinstance(node.conclusion, Or):
            logger.error(f"{sp}❌ [Pad] Not Or object: {pretty_expr(node.conclusion, context)}")
            return False
        logger.debug(f"{sp}[Pad] Or object: {pretty_expr(node.conclusion, context)}")
        fact_parts = flatten_op(fact, Or)
        conclusion_parts = flatten_op(node.conclusion, Or)
        if not all(any(alpha_equiv_with_defs(c, f, context) for c in conclusion_parts) for f in fact_parts):
            logger.error(f"{sp}❌ [Pad] neither left or right not derivable: {pretty_expr(node.conclusion, context)}")
            return False
        node.proofinfo.premises = [fact]
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Pad] Derivable, added {pretty_expr(node.conclusion, context)}")
        return True

    if isinstance(node, Split):
        if not goal_in_context(node.fact, context):
            logger.error(f"{sp}❌ [Split] Not derivable: {pretty_expr(node.fact, context)}")
            return False
        logger.debug(f"{sp}[Split] Derivable: {pretty_expr(node.fact, context)}")
        if isinstance(node.fact, And):
            logger.debug(f"{sp}[Split] And object: {pretty_expr(node.fact, context)}")
            fact_parts = flatten_op(node.fact, And)
            node.proofinfo.premises = [node.fact]
            if node.index is None:
                node.proofinfo.conclusions = fact_parts
                for f in fact_parts:
                    add_conclusion(context, f)
                    logger.debug(f"{sp}[Split] added {pretty_expr(f, context)}")
            else:
                if node.index <= 0 or node.index > len(fact_parts):
                    logger.error(f"{sp}❌ [Split] index out of range, index: {node.index}, len(fact_parts): {len(fact_parts)}")
                    return False
                f = fact_parts[node.index - 1]
                node.proofinfo.conclusions = [f]
                add_conclusion(context, f)
                logger.debug(f"{sp}[Split] added {pretty_expr(f, context)}")
            return True
        elif isinstance(node.fact, Iff):
            logger.debug(f"{sp}[Split] Iff object: {pretty_expr(node.fact, context)}")
            implication_rightward = Implies(node.fact.left, node.fact.right)
            implication_leftward = Implies(node.fact.right, node.fact.left)
            node.proofinfo.premises = [node.fact]
            node.proofinfo.conclusions = [implication_rightward, implication_leftward]
            add_conclusion(context, implication_rightward)
            add_conclusion(context, implication_leftward)
            logger.debug(f"{sp}[Split] added {pretty_expr(implication_rightward, context)}")
            logger.debug(f"{sp}[Split] added {pretty_expr(implication_leftward, context)}")
            return True
        else:
            logger.error(f"{sp}❌ [Split] Not And or Iff object: {pretty_expr(node.fact, context)}")
            return False

    if isinstance(node, Connect):
        if isinstance(node.conclusion, And):
            logger.debug(f"{sp}[Connect] And object: {pretty_expr(node.conclusion, context)}")
            conclusion_parts = flatten_op(node.conclusion, And)
            for c in conclusion_parts:
                if not goal_in_context(c, context):
                    logger.error(f"{sp}❌ [Connect] Not derivable: {pretty_expr(c, context)}")
                    return False
            node.proofinfo.premises = conclusion_parts
            node.proofinfo.conclusions = [node.conclusion]
            add_conclusion(context, node.conclusion)
            logger.debug(f"{sp}[Connect] Derivable, added {pretty_expr(node.conclusion, context)}")
            return True
        elif isinstance(node.conclusion, Iff):
            logger.debug(f"{sp}[Connect] Iff object: {pretty_expr(node.conclusion, context)}")
            implication_rightward = Implies(node.conclusion.left, node.conclusion.right)
            if not goal_in_context(implication_rightward, context):
                logger.error(f"{sp}❌ [Connect] Not derivable: {pretty_expr(implication_rightward, context)}")
                return False
            implication_leftward = Implies(node.conclusion.right, node.conclusion.left)
            if not goal_in_context(implication_leftward, context):
                logger.error(f"{sp}❌ [Connect] Not derivable: {pretty_expr(implication_leftward, context)}")
                return False
            node.proofinfo.premises = [implication_rightward, implication_leftward]
            node.proofinfo.conclusions = [node.conclusion]
            add_conclusion(context, node.conclusion)
            logger.debug(f"{sp}[Connect] derivable, added {pretty_expr(node.conclusion, context)}")
            return True
        else:
            logger.error(f"{sp}❌ [Connect] Not And or Iff object: {pretty_expr(node.conclusion, context)}")
            return False

    if isinstance(node, Substitute):
        if not goal_in_context(node.fact, context):
            logger.error(f"{sp}❌ [Substitute] Not fact: {pretty_expr(node.fact, context)}")
            return False
        logger.debug(f"{sp}[Substitute] Fact: {pretty_expr(node.fact, context)}")
        fact = get_fact(node.fact, context)
        if context.equality is None:
            logger.error(f"{sp}❌ [Substitute] equality has not been declared yet")
            return False
        equations = [Symbol(Pred(context.equality.equal.name), [k, v]) for k, v in node.env.items()]
        for equation in equations:
            if not goal_in_context(equation, context):
                logger.error(f"{sp}❌ [Substitute] Not fact: {pretty_expr(equation, context)}")
                return False
            logger.debug(f"{sp}[Substitute] Fact: {pretty_expr(equation, context)}")
        fact_subst = substitute(fact, node.env)
        conclusion_subst = substitute(node.conclusion, node.env)
        logger.debug(f"{sp}[Substitute] fact_subst: {pretty_expr(fact_subst, context)}")
        logger.debug(f"{sp}[Substitute] conclusion_subst: {pretty_expr(conclusion_subst, context)}")
        if not alpha_equiv_with_defs(conclusion_subst, fact_subst, context):
            logger.error(f"{sp}❌ [Substitute] Not matched")
            return False
        logger.debug(f"{sp}[Substitute] Matched")
        node.proofinfo.premises = [fact] + equations
        node.proofinfo.conclusions = [node.conclusion]
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Substitute] Added {pretty_expr(node.conclusion, context)}")
        return True

    if isinstance(node, Show):
        logger.debug(f"{sp}[Show] Target conclusion: {pretty_expr(node.conclusion, context)}")
        local_ctx = context.copy(list(context.vars), list(context.formulas), list(context.templates))
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if not (len(context.formulas) < len(local_ctx.formulas) and context.formulas == local_ctx.formulas[:len(context.formulas)]):
            logger.error(f"{sp}❌ [Show] Local context must extend the parent context")
            return False
        goal = local_ctx.formulas[-1]
        logger.debug(f"{sp}[Show] derived goal: {pretty_expr(goal, context)}")
        if not alpha_equiv_with_defs(node.conclusion, goal, context):
            logger.error(f"{sp}❌ [Show] Not matched with target conclusion: {pretty_expr(node.conclusion, context)}")
            return False
        logger.debug(f"{sp}[Show] Matched with target conclusion: {pretty_expr(node.conclusion, context)}")
        node.proofinfo.premises = []
        node.proofinfo.conclusions = [goal]
        node.proofinfo.local_vars = []
        node.proofinfo.local_premise = []
        node.proofinfo.local_conclusion = [goal]
        add_conclusion(context, goal)
        logger.debug(f"{sp}[Show] Added {pretty_expr(goal, context)}")
        return True

    logger.error(f"{sp}❌ Unsupported node {node}")
    return False

if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    f = open(path)
    src = f.read()
    f.close()

    import os
    import logging

    logger = logging.getLogger("proof")
    logger.setLevel(logging.DEBUG)

    # 標準出力用ハンドラ
    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.DEBUG)

    # ファイル出力用ハンドラ
    file_handler = logging.FileHandler(os.path.join("logs", os.path.basename(path).replace(".proof", ".log")), mode='w', encoding='utf-8')
    file_handler.setLevel(logging.DEBUG)

    # 共通フォーマット
    formatter = logging.Formatter("[%(filename)s] %(message)s")
    console_handler.setFormatter(formatter)
    file_handler.setFormatter(formatter)

    # ハンドラ登録
    logger.addHandler(console_handler)
    logger.addHandler(file_handler)

    from lexer import lex
    tokens = lex(src)
    from parser import Parser
    parser = Parser(tokens)
    ast, _ = parser.parse_file()
    result, _, _ = check_ast(ast)
    if result:
        print("All theorems proved")
    else:
        print("❌ Not all theorems proved")
