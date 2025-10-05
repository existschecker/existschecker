# checker.py
from ast_types import Context, Theorem, Any, Assume, Check, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, Symbol, And, Or, Implies, Forall, Exists, Not, Bottom, Iff, Axiom, Invoke, Expand, ExistsUniq, Characterize, Atom, Definition, DefCon, Identify, pretty, pretty_expr

# === α同値判定 ===
from itertools import permutations

# 依存する AST ノード: Symbol, Forall, Implies, And, Or, Exists? を想定
from typing import List

import logging
logger = logging.getLogger("proof")

def flatten_or(expr) -> List:
    """Or を平坦化して葉のリストを返す"""
    if isinstance(expr, Or):
        return flatten_or(expr.left) + flatten_or(expr.right)
    else:
        return [expr]

# alpha_equiv 内の Or 判定をこれに置き換える例
def or_equiv(e1, e2, env=None):
    """Or の順序と α同値を同時に無視して比較"""
    if env is None:
        env = {}

    # flatten してリスト化
    parts1 = flatten_or(e1)
    parts2 = flatten_or(e2)

    if len(parts1) != len(parts2):
        return False

    # 外側の env に従って α同値判定
    matched = [False] * len(parts2)
    for p1 in parts1:
        found = False
        for i, p2 in enumerate(parts2):
            if not matched[i] and alpha_equiv(p1, p2, env):
                matched[i] = True
                found = True
                break
        if not found:
            return False

    return True

def normalize_neg(e):
    if isinstance(e, Not) and isinstance(e.body, Not):
        return normalize_neg(e.body.body)
    else:
        return e

def alpha_equiv(e1, e2, env=None):
    """束縛変数の順序も無視して α同値判定"""
    if env is None:
        env = {}

    e1 = normalize_neg(e1)
    e2 = normalize_neg(e2)

    # e1, e2 が両方 Not の場合は中身を再帰的に比較
    if isinstance(e1, Not) and isinstance(e2, Not):
        return alpha_equiv(e1.body, e2.body, env)
    # 片方が Not で片方が違う場合は不一致
    if isinstance(e1, Not) != isinstance(e2, Not):
        return False

    for quantifier_type in (Forall, Exists, ExistsUniq):
        if isinstance(e1, quantifier_type) and isinstance(e2, quantifier_type):
            vars1, body1 = collect_quantifier_vars(e1, quantifier_type)
            vars2, body2 = collect_quantifier_vars(e2, quantifier_type)

            if len(vars1) != len(vars2):
                return False

            for perm in permutations(vars2):
                newenv = env.copy()
                for v1, v2 in zip(vars1, perm):
                    newenv[v1] = v2
                if alpha_equiv(body1, body2, newenv):
                    return True
            return False

    if isinstance(e1, Implies) and isinstance(e2, Implies):
        return alpha_equiv(e1.left, e2.left, env) and alpha_equiv(e1.right, e2.right, env)
    
    if isinstance(e1, Iff) and isinstance(e2, Iff):
        return alpha_equiv(e1.left, e2.left, env) and alpha_equiv(e1.right, e2.right, env)

    if isinstance(e1, And) and isinstance(e2, And):
        return alpha_equiv(e1.left, e2.left, env) and alpha_equiv(e1.right, e2.right, env)

    if isinstance(e1, Or) and isinstance(e2, Or):
        return or_equiv(e1, e2, env)

    if isinstance(e1, Symbol) and isinstance(e2, Symbol):
        if e1.name != e2.name or len(e1.args) != len(e2.args):
            return False
        for a, b in zip(e1.args, e2.args):
            mapped = env.get(a, a)
            if mapped != b:
                return False
        return True

    return False

def collect_quantifier_vars(e, quantifier_type):
    vars_ = []
    body = e
    while isinstance(body, quantifier_type):
        vars_.append(body.var)
        body = body.body
    return vars_, body

def collect_vars(expr, bound=None):
    """
    式 expr から自由変数と束縛変数の集合を返す
    戻り値: (free_vars, bound_vars)
    """
    if bound is None:
        bound = set()

    if isinstance(expr, Symbol):
        return set(arg for arg in expr.args if arg not in bound), set()

    elif isinstance(expr, Not):
        return collect_vars(expr.body, bound)

    elif isinstance(expr, (And, Or, Implies)):
        f1, b1 = collect_vars(expr.left, bound)
        f2, b2 = collect_vars(expr.right, bound)
        return f1 | f2, b1 | b2

    elif isinstance(expr, (Forall, Exists)):
        f_body, b_body = collect_vars(expr.body, bound | {expr.var})
        return f_body, b_body | {expr.var}

    else:
        return set(), set()

# === コンテキスト中の式検索 ===
def expr_in_context(expr, context):
    return any(alpha_equiv(expr, c) for c in context)

# And を分解
def split_conjunction(expr):
    if isinstance(expr, And):
        return split_conjunction(expr.left) + split_conjunction(expr.right)
    if isinstance(expr, Iff):
        return [Implies(expr.left, expr.right), Implies(expr.right, expr.left)]
    else:
        return [expr]

def derivable_flat(goal, flat_ctx):
    # goal が And のとき
    if isinstance(goal, And):
        return derivable_flat(goal.left, flat_ctx) and derivable_flat(goal.right, flat_ctx)
    if isinstance(goal, Or):
        return derivable_flat(goal.left, flat_ctx) or derivable_flat(goal.right, flat_ctx) or expr_in_context(goal, flat_ctx)
    if isinstance(goal, Iff):
        return derivable_flat(Implies(goal.left, goal.right), flat_ctx) and derivable_flat(Implies(goal.right, goal.left), flat_ctx)
    # α同値チェック
    return expr_in_context(goal, flat_ctx)

def expand_definitions(expr, context):
    if isinstance(expr, Symbol):
        if expr.name in context.definitions:
            definition = context.definitions[expr.name].formula
            vars, body = collect_quantifier_vars(definition, Forall)
            expanded = substitute(body, dict(zip(vars, expr.args))).right
            return expand_definitions(expanded, context)
        else:
            return expr
    elif isinstance(expr, Not):
        return Not(expand_definitions(expr.body, context))
    elif isinstance(expr, (And, Or, Implies, Iff)):
        left = expand_definitions(expr.left, context)
        right = expand_definitions(expr.right, context)
        return type(expr)(left, right)
    elif isinstance(expr, (Forall, Exists)):
        body = expand_definitions(expr.body, context)
        return type(expr)(expr.var, body)
    else:
        return expr

def derivable(goal, context, indent):
    sp = '  ' * indent
    logger.debug(f"{sp}[derivable] goal: {pretty_expr(goal)}")
    logger.debug(f"{sp}[derivable] context.formulas: {",".join([pretty_expr(c) for c in context.formulas])}")
    if isinstance(goal, Bottom):
        return context.bot_derived
    elif isinstance(goal, Axiom):
        return goal.name in context.axioms
    elif isinstance(goal, Theorem):
        return goal.name in context.theorems
    else:
        flat_ctx = []
        for c in context.formulas:
            flat_ctx.extend(split_conjunction(c))
        expanded_ctx = [expand_definitions(c, context) for c in flat_ctx]
        expanded_goal = expand_definitions(goal, context)
        return derivable_flat(expanded_goal, expanded_ctx)

def fresh_var(var, used):
    """used に含まれない新しい変数名を作る"""
    i = 0
    new_var = f"{var}_{i}"
    while new_var in used:
        i += 1
        new_var = f"{var}_{i}"
    return new_var

def substitute(expr, mapping, used_vars=None):
    """
    expr の自由変数を mapping で置換
    束縛変数は mapping に衝突しないよう自動リネーム
    """
    if used_vars is None:
        used_vars = collect_vars(expr)[0] | set(mapping.values())

    if isinstance(expr, Symbol):
        new_args = [mapping.get(arg, arg) for arg in expr.args]
        return Symbol(expr.name, new_args)

    if isinstance(expr, Not):
        return Not(substitute(expr.body, mapping, used_vars))

    if isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(substitute(expr.left, mapping, used_vars), substitute(expr.right, mapping, used_vars))

    if isinstance(expr, (Forall, Exists)):
        var = expr.var
        # 衝突する場合は束縛変数をリネーム
        if var in mapping.values() or var in used_vars:
            new_var = fresh_var(var, used_vars)
            used_vars.add(new_var)
            body = substitute(rename_var(expr.body, var, new_var), mapping, used_vars)
            return type(expr)(new_var, body)
        else:
            used_vars.add(var)
            return type(expr)(var, substitute(expr.body, mapping, used_vars))

    return expr

def rename_var(expr, old_var, new_var):
    """式 expr 内の束縛変数 old_var を new_var にリネーム"""
    if isinstance(expr, Symbol):
        new_args = [new_var if a == old_var else a for a in expr.args]
        return Symbol(expr.name, new_args)
    elif isinstance(expr, Not):
        return Not(rename_var(expr.body, old_var, new_var))
    elif isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(rename_var(expr.left, old_var, new_var), rename_var(expr.right, old_var, new_var))
    elif isinstance(expr, (Forall, Exists)):
        v = new_var if expr.var == old_var else expr.var
        return type(expr)(v, rename_var(expr.body, old_var, new_var))
    return expr

def add_conclusion(context, conclusion):
    if isinstance(conclusion, Bottom):
        context.bot_derived = True
    else:
        context.formulas.append(conclusion)

def check_ast(ast):
    context = Context.init()
    return all(check_proof(node, context) for node in ast)

# === 証明チェッカー ===
def check_proof(node, context: Context, indent=0):
    sp = "  " * indent

    if isinstance(node, Atom):
        logger.debug(f"{sp}[Atom] type: {node.type}, name: {node.name}, arity: {node.arity}")
        context.atoms[node.name] = node
        return True

    if isinstance(node, Axiom):
        logger.debug(f"{sp}[Axiom] name: {node.name}, conclusion: {pretty_expr(node.conclusion)}")
        context.axioms[node.name] = node
        return True

    # --- Theorem ---
    if isinstance(node, Theorem):
        logger.debug(f"{sp}[Theorem] {node.name}: {pretty_expr(node.conclusion)}")
        local_ctx = context.copy([], False)
        for stmt in node.proof:
            if not check_proof(stmt, local_ctx, indent+1):
                logger.error(f"{sp}❌ [Theorem] Failed")
                return False
        if derivable(node.conclusion, local_ctx, indent+1):
            logger.debug(f"{sp}[Theorem] {node.name} proved: {pretty_expr(node.conclusion)}")
            context.theorems[node.name] = node
            return True
        else:
            logger.error(f"{sp}❌ [Theorem] {node.name} not proved: {pretty_expr(node.conclusion)}")
            return False

    # --- Check ---
    if isinstance(node, Check):
        logger.debug(f"{sp}[Check] Checking {pretty_expr(node.conclusion)}")
        if derivable(node.conclusion, context, indent+1):
            logger.debug(f"{sp}[Check] goal {pretty_expr(node.conclusion)} derived")
            return True
        else:
            logger.error(f"{sp}❌ [Check] goal {pretty_expr(node.conclusion)} not derivable")
            return False

    # --- Assume ---
    if isinstance(node, Assume):
        logger.debug(f"{sp}[Assume] premise={pretty_expr(node.premise)}, conclusion={pretty_expr(node.conclusion)}")
        local_ctx = context.copy(list(context.formulas + [node.premise]), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if derivable(node.conclusion, local_ctx, indent+1):
            logger.debug(f"{sp}[Assume] Derived conclusion {pretty_expr(node.conclusion)}")
        else:
            logger.error(f"{sp}❌ [Assume] Cannot derive {pretty_expr(node.conclusion)}")
            return False
        implication = Implies(node.premise, node.conclusion)
        add_conclusion(context, implication)
        logger.debug(f"{sp}[Assume] Added implication {pretty_expr(implication)}")
        return True

    # --- Any ---
    if isinstance(node, Any):
        logger.debug(f"{sp}[Any] Taking {node.vars}")
        local_ctx = context.copy(list(context.formulas), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if derivable(node.conclusion, local_ctx, indent+1):
            logger.debug(f"{sp}[Any] Derived conclusion {pretty_expr(node.conclusion)}")
        else:
            logger.error(f"{sp}❌ [Any] Cannot derive {pretty_expr(node.conclusion)}")
            return False
        goal = node.conclusion
        for v in reversed(node.vars):
            goal = Forall(v, goal)
        add_conclusion(context, goal)
        logger.debug(f"{sp}[Any] Generalized to {pretty_expr(goal)}")
        return True

    if isinstance(node, Divide):
        if not derivable(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Divide] Not fact: {pretty_expr(node.fact)}")
            return False
        connected_premise = Or(node.cases[0].premise, node.cases[1].premise)
        i = 2
        while i < len(node.cases):
            connected_premise = Or(connected_premise, node.cases[i].premise)
            i += 1
        if alpha_equiv(connected_premise, node.fact):
            logger.debug(f"{sp}[Divide] mathched: fact={pretty_expr(node.fact)}, connected_premise={pretty_expr(connected_premise)}")
        else:
            logger.error(f"{sp}❌ [Divide] not matched: fact={pretty_expr(node.fact)}, conected_premise={pretty_expr(connected_premise)}")
            return False
        logger.debug(f"{sp}[Divide] fact={pretty_expr(node.fact)}, goal={pretty_expr(node.conclusion)}")
        local_ctx = context.copy(list(context.formulas), False)
        for stmt in node.cases:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Divide] derived in all cases: {pretty_expr(node.conclusion)}")
        return True

    if isinstance(node, Case):
        logger.debug(f"{sp}[Case] premise={pretty_expr(node.premise)}")
        local_ctx = context.copy(list(context.formulas + [node.premise]), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if derivable(node.conclusion, local_ctx, indent+1):
            logger.debug(f"{sp}[Case] derived conclusion {pretty_expr(node.conclusion)}")
            return True
        else:
            logger.error(f"{sp}❌ [Case] Cannot derive {pretty_expr(node.conclusion)}")
            return False

    if isinstance(node, Some):
        if not derivable(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Some] not derivable: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Some] derivable: {pretty_expr(node.fact)}")
        if isinstance(node.fact, Axiom):
            fact = node.fact.conclusion
        elif isinstance(node.fact, Theorem):
            fact = node.fact.conclusion
        else:
            fact = node.fact
        if not isinstance(fact, Exists):
            logger.error(f"{sp}❌ Not Exists object: {pretty_expr(node.fact)}")
            return False
        vars, body = collect_quantifier_vars(fact, Exists)
        if not set(node.env.keys()).issubset(set(vars)):
            logger.error(f"{sp}❌ invalid vars: node.env.keys()={node.env.keys()}, vars={vars}")
            return False
        premise = substitute(body, node.env)
        logger.debug(f"{sp}[Some] Taking {node.env.values()}, premise={pretty_expr(premise)}")
        local_ctx = context.copy(list(context.formulas + [premise]), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if not derivable(node.conclusion, local_ctx, indent+1):
            logger.error(f"{sp}❌ [Some] Cannot derive {pretty_expr(node.conclusion)}")
            return False
        logger.debug(f"{sp}[Some] derived conclusion {pretty_expr(node.conclusion)}")
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Some] Added {pretty_expr(node.conclusion)}")
        return True
    
    if isinstance(node, Deny):
        logger.debug(f"{sp}[Deny] premise={pretty_expr(node.premise)}")
        local_ctx = context.copy(list(context.formulas + [node.premise]), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if local_ctx.bot_derived:
            add_conclusion(context, Not(node.premise))
            logger.debug(f"{sp}[Deny] contradiction is derived; added {pretty_expr(Not(node.premise))}")
            return True
        else:
            logger.error(f"{sp}❌ [Deny] conradiction has not been deried")
            return False
    
    if isinstance(node, Contradict):
        if not derivable(node.contradiction, context, indent+1):
            logger.error(f"{sp}❌ [Contradict] Cannot derive {pretty_expr(node.contradiction)}")
            return False
        if not derivable(Not(node.contradiction), context, indent+1):
            logger.error(f"{sp}❌ [Contradict] Cannot derive {pretty_expr(Not(node.contradiction))}")
            return False
        logger.debug(f"{sp}[Contradict] Derived contradiction: {pretty_expr(node.contradiction)}, {pretty_expr(Not(node.contradiction))}")
        context.bot_derived = True
        return True
    
    if isinstance(node, Explode):
        if context.bot_derived:
            add_conclusion(context, node.conclusion)
            logger.debug(f"{sp}[Explode] added {pretty_expr(node.conclusion)}")
            return True
        else:
            logger.error(f"{sp}❌ [Explode] contradiction has not been derived")
            return False
        
    if isinstance(node, Apply):
        if not derivable(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Apply] Cannot derive fact: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Apply] Drivable fact: {pretty_expr(node.fact)}")
        if isinstance(node.fact, Axiom):
            fact = node.fact.conclusion
        elif isinstance(node.fact, Theorem):
            fact = node.fact.conclusion
        elif isinstance(node.fact, Symbol):
            if node.fact.name not in context.definitions:
                logger.error(f"{sp}❌ [Apply] Undefined name: {node.fact.name}")
                return False
            vars, body = collect_quantifier_vars(context.definitions[node.fact.name].formula, Forall)
            if len(vars) != len(node.fact.args):
                logger.error(f"{sp}❌ [Apply] not matched: len(vars)={len(vars)}, len(node.fact.args)={len(node.fact.args)}")
                return False
            fact = substitute(body, dict(zip(vars, node.fact.args))).right
            logger.debug(f"{sp}[Apply] replace {pretty_expr(node.fact)} to {pretty_expr(fact)}")
        else:
            fact = node.fact
        if node.env is not None:
            vars, body = collect_quantifier_vars(fact, Forall)
            if set(vars) != set(node.env.keys()):
                logger.error(f"{sp}❌ [Apply] matched: vars={vars}, env={node.env}")
                return False
            logger.debug(f"{sp}[Apply] Instantiable: vars={vars}, env={node.env}")
            instantiation = substitute(body, node.env)
            logger.debug(f"{sp}[Apply] \\forall-elimination is done: instantiation={pretty_expr(instantiation)}")
            if node.premise is None:
                if not alpha_equiv(node.conclusion, instantiation):
                    logger.error(f"{sp}❌ [Apply] Not matched: node.conclusion={pretty_expr(node.conclusion)}, instantiation={pretty_expr(instantiation)}")
                    return False
                logger.debug(f"{sp}[Apply] Matched: node.conclusion={pretty_expr(node.conclusion)}, instantiation={pretty_expr(instantiation)}")
                logger.debug(f"{sp}[Apply] Added node.conclusion={pretty_expr(node.conclusion)}")
                add_conclusion(context, node.conclusion)
                return True
            else:
                implication = instantiation
        else:
            implication = fact
        if not isinstance(implication, Implies):
            logger.error(f"{sp}❌ [Apply] Not Implies object: {pretty_expr(implication)}")
            return False
        logger.debug(f"{sp}[Apply] Implies object: {pretty_expr(implication)}")
        if not derivable(node.premise, context, indent+1):
            logger.error(f"{sp}❌ [Apply] Cannot derive premise: {pretty_expr(node.premise)}")
            return False
        logger.debug(f"{sp}[Apply] Derivable premise: {pretty_expr(node.premise)}")
        if not alpha_equiv(implication.left, node.premise):
            logger.error(f"{sp}❌ [Apply] Not matched: implication.left={pretty_expr(implication.left)}, node.premise={pretty_expr(node.premise)}")
            return False
        logger.debug(f"{sp}[Apply] Matched: implication.left={pretty_expr(implication.left)}, node.premise={pretty_expr(node.premise)}")
        logger.debug(f"{sp}[Apply] \\to-elimination is done: {pretty_expr(implication.right)}")
        if not alpha_equiv(node.conclusion, implication.right):
            logger.error(f"{sp}❌ [Apply] Not matched: node.conclusion={pretty_expr(node.conclusion)}, implication.right={pretty_expr(implication.right)}")
            return False
        logger.debug(f"{sp}[Apply] Matched: node.conclusion={pretty_expr(node.conclusion)}, implication.right={pretty_expr(implication.right)}")
        logger.debug(f"{sp}[Apply] Added node.conclusion={pretty_expr(node.conclusion)}")
        add_conclusion(context, node.conclusion)
        return True
    
    if isinstance(node, Lift):
        if not derivable(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Lift] Not fact: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Lift] fact: {pretty_expr(node.fact)}")
        free_vars, _ = collect_vars(node.fact)
        if not set(node.env.values()).issubset(free_vars):
            logger.error(f"{sp}❌ [Lift] Cannot be lifted: vars={sorted(free_vars)}, env={node.env}")
            return False
        logger.debug(f"{sp}[Lift] Can be lifted: vars={sorted(free_vars)}, env={node.env}")
        lifted = substitute(node.fact, {v: k for k, v in node.env.items()})
        for k in reversed(list(node.env.keys())):
            lifted = Exists(k, lifted)
        logger.debug(f"{sp}[Lift] lifted formula: {pretty_expr(lifted)}")
        if not alpha_equiv(node.conclusion, lifted):
            logger.error(f"{sp}❌ [Lift] Not matched: node.conclusion={pretty_expr(node.conclusion)}, lifted={pretty_expr(lifted)}")
            return False
        logger.debug(f"{sp}[Lift] Matched: node.conclusion={pretty_expr(node.conclusion)}, lifted={pretty_expr(lifted)}")        
        add_conclusion(context, node.conclusion)
        return True

    if isinstance(node, Invoke):
        if not derivable(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Invoke] Not fact: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Invoke] fact: {pretty_expr(node.fact)}")
        if not isinstance(node.fact, Implies):
            logger.error(f"{sp}❌ [Invoke] Not Implies object: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Invoke] Implies object: {pretty_expr(node.fact)}")
        if not derivable(node.fact.left, context, indent+1):
            logger.error(f"{sp}❌ [Invoke] Left of Implies object not derived: {pretty_expr(node.fact.left)}")
            return False
        logger.debug(f"{sp}[Invoke] Left of Implies object derived: {pretty_expr(node.fact.left)}")
        if not alpha_equiv(node.conclusion, node.fact.right):
            logger.error(f"{sp}❌ [Invoke] Not matched: node.conclusion={pretty_expr(node.conclusion)}, node.fact.right={pretty_expr(node.fact.right)}")
            return False
        logger.debug(f"{sp}[Invoke] Matched: node.conclusion={pretty_expr(node.conclusion)}, node.fact.right={pretty_expr(node.fact.right)}")
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Invoke] conclusion added: {pretty_expr(node.conclusion)}")
        return True

    if isinstance(node, Expand):
        if not derivable(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Expand] Not fact: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Expand] fact: {pretty_expr(node.fact)}")
        if not isinstance(node.fact, Symbol):
            logger.error(f"{sp}❌ [Expand] Not Symbol object: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Expand] Symbol object: {pretty_expr(node.fact)}")
        if node.fact.name not in context.definitions:
            logger.error(f"{sp}❌ [Expand] Not defined: {node.fact.name}")
            return False
        logger.debug(f"{sp}[Expand] Defined: {node.fact.name}")
        vars, body = collect_quantifier_vars(context.definitions[node.fact.name].formula, Forall)
        if len(vars) != len(node.fact.args):
            logger.error(f"{sp}❌ [Expand] Length not matched: vars={vars}, node.fact.args={node.fact.args}")
            return False
        logger.debug(f"{sp}[Expand] Length matched: vars={vars}, node.fact.args={node.fact.args}")
        expanded = substitute(body, dict(zip(vars, node.fact.args))).right
        logger.debug(f"{sp}[Expand] Expanded: {pretty_expr(expanded)}")
        if not alpha_equiv(node.conclusion, expanded):
            logger.error(f"{sp}❌ [Expand] Not matched: node.conclusion={pretty_expr(node.conclusion)}, expanded={pretty_expr(expanded)}")
            return False
        logger.debug(f"{sp}[Expand] Matched: node.conclusion={pretty_expr(node.conclusion)}, expanded={pretty_expr(expanded)}")
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Expand] Added: {pretty_expr(node.conclusion)}")
        return True

    if isinstance(node, Characterize):
        if not derivable(node.fact.left, context, indent+1):
            logger.error(f"{sp}❌ [Characterize] Not derived: {pretty_expr(node.fact.left)}")
            return False
        logger.debug(f"{sp}[Characterize] Derived: {pretty_expr(node.fact.left)}")
        free_vars, _ = collect_vars(node.fact.left)
        if not set(node.env.values()).issubset(free_vars):
            logger.error(f"{sp}❌ [Characterize] Invalid env: vars={sorted(free_vars)}, env={node.env}")
            return False
        logger.debug(f"{sp}[Characterize] Valid env: vars={sorted(free_vars)}, env={node.env}")
        if not alpha_equiv(substitute(node.fact.left, {list(node.env.values())[0]: node.fact.right.var}), node.fact.right.body.left):
            logger.error(f"{sp}❌ [Characterize] Not matched: node.fact.left={pretty_expr(node.fact.left)}, node.fact.right.body.left={pretty_expr(node.fact.right.body.left)}")
            return False
        logger.debug(f"{sp}[Characterize] Matched: node.fact.left={pretty_expr(node.fact.left)}, node.fact.right.body.left={pretty_expr(node.fact.right.body.left)}")
        if not (node.fact.right.body.right.name == "equal" and set(node.fact.right.body.right.args) == set([list(node.env.values())[0], node.fact.right.var])):
            logger.error(f"{sp}❌ [Characterized] Unexpected: node.fact.right.body.right={pretty_expr(node.fact.right.body.right)}")
            return False
        logger.debug(f"{sp}[Characterized] Expected: node.fact.right.body.right={pretty_expr(node.fact.right.body.right)}")
        characterized = ExistsUniq(list(node.env.keys())[0], substitute(node.fact.left, {v: k for k, v in node.env.items()}))
        logger.debug(f"{sp}[Characterize] derived formula: {pretty_expr(characterized)}")
        if not alpha_equiv(node.conclusion, characterized):
            logger.error(f"{sp}❌ [Characterize] Not matched: node.conclusion={pretty_expr(node.conclusion)}, derived={pretty_expr(characterized)}")
            return False
        logger.debug(f"{sp}[Characterize] Matched: node.conclusion={pretty_expr(node.conclusion)}, derived={pretty_expr(characterized)}")
        add_conclusion(context, node.conclusion)
        return True

    if isinstance(node, Identify):
        if not derivable(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Identify] Not derivable: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Identify] Derivable: {pretty_expr(node.fact)}")
        logger.debug(f"{sp}[Identify] Add conclusion: {pretty_expr(node.conclusion)}")
        add_conclusion(context, node.conclusion)
        return True

    if isinstance(node, Definition):
        logger.debug(f"{sp}[Definition] type: {node.type}, name: {node.name}, arity: {node.arity}, formula: {pretty_expr(node.formula)}")
        context.definitions[node.name] = node
        return True

    if isinstance(node, DefCon):
        logger.debug(f"{sp}[DefCon] name: {node.name}, theorem: {node.theorem}, formula: {node.formula}")
        context.defcons[node.name] = node
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
    ast = parser.parse_file()
    if check_ast(ast):
        print("All theorems proved")
    else:
        print("❌ Not all theorems proved")
