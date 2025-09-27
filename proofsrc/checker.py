# checker.py
from parser import Theorem, Any, Assume, Check, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, parse_file_from_source, pretty
from expr_parser import Symbol, And, Or, Implies, Forall, Exists, Not, Bottom
from expr_parser import pretty_expr

# === α同値判定 ===
from itertools import permutations

# 依存する AST ノード: Symbol, Forall, Implies, And, Or, Exists? を想定
from typing import List

import logging

from dataclasses import dataclass

@dataclass
class Context:
    formulas: list        # 通常の論理式
    bot_derived: bool = False  # 矛盾導出フラグ

logger = logging.getLogger(__name__)

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

    # e1, e2 が両方 Not の場合は中身を再帰的に比較
    if isinstance(e1, Not) and isinstance(e2, Not):
        return alpha_equiv(e1.body, e2.body, env)
    # 片方が Not で片方が違う場合は不一致
    if isinstance(e1, Not) != isinstance(e2, Not):
        return False

    if isinstance(e1, Forall) and isinstance(e2, Forall):
        vars1, body1 = collect_forall_vars(e1)
        vars2, body2 = collect_forall_vars(e2)

        if len(vars1) != len(vars2):
            return False

        # vars2 の順列ごとに試す
        for perm in permutations(vars2):
            newenv = env.copy()
            for v1, v2 in zip(vars1, perm):
                newenv[v1] = v2
            if alpha_equiv(body1, body2, newenv):
                return True
        return False
    
    if isinstance(e1, Exists) and isinstance(e2, Exists):
        vars1, body1 = collect_exists_vars(e1)
        vars2, body2 = collect_exists_vars(e2)

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

# --- ヘルパー関数 ---
def collect_forall_vars(e):
    """連続する Forall をリストにして本体と返す"""
    vars_ = []
    body = e
    while isinstance(body, Forall):
        vars_.append(body.var)
        body = body.body
    return vars_, body

def collect_exists_vars(e):
    vars_ = []
    body = e
    while isinstance(body, Exists):
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
        if expr.name == "in":
            return set(arg for arg in expr.args if arg not in bound), set()
        else:
            raise TypeError("Unexpected Symbol")

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
    else:
        return [expr]

def derivable_flat(goal, flat_ctx):
    # goal が And のとき
    if isinstance(goal, And):
        return derivable_flat(goal.left, flat_ctx) and derivable_flat(goal.right, flat_ctx)
    if isinstance(goal, Or):
        return derivable_flat(goal.left, flat_ctx) or derivable_flat(goal.right, flat_ctx) or expr_in_context(goal, flat_ctx)
    # α同値チェック
    return expr_in_context(goal, flat_ctx)

def derivable(goal, context):
    if isinstance(goal, Bottom):
        return context.bot_derived
    else:
        flat_ctx = []
        for c in context.formulas:
            flat_ctx.extend(split_conjunction(c))
        return derivable_flat(goal, flat_ctx)

def substitute(expr, mapping):
    if isinstance(expr, Symbol):
        # Symbol("in", ["x", "y"]) の形しかない想定
        if expr.name == "in":
            new_args = [mapping.get(arg, arg) for arg in expr.args]
            return Symbol("in", new_args)
        return expr

    if isinstance(expr, Not):
        return Not(substitute(expr.body, mapping))

    if isinstance(expr, And):
        return And(substitute(expr.left, mapping), substitute(expr.right, mapping))

    if isinstance(expr, Or):
        return Or(substitute(expr.left, mapping), substitute(expr.right, mapping))

    if isinstance(expr, Implies):
        return Implies(substitute(expr.left, mapping), substitute(expr.right, mapping))

    if isinstance(expr, Forall):
        # 束縛変数は mapping から除外
        new_mapping = {k: v for k, v in mapping.items() if k != expr.var}
        return Forall(expr.var, substitute(expr.body, new_mapping))

    if isinstance(expr, Exists):
        new_mapping = {k: v for k, v in mapping.items() if k != expr.var}
        return Exists(expr.var, substitute(expr.body, new_mapping))

    return expr

def add_conclusion(context, conclusion):
    if isinstance(conclusion, Bottom):
        context.bot_derived = True
    else:
        context.formulas.append(conclusion)

# === 証明チェッカー ===
def check_proof(node, context=None, indent=0):
    if context is None:
        context = Context([], False)

    sp = "  " * indent

    # --- Theorem ---
    if isinstance(node, Theorem):
        logger.debug(f"{sp}[Theorem] {node.name}: {pretty_expr(node.conclusion)}")
        local_ctx = Context([], False)
        for stmt in node.proof:
            if not check_proof(stmt, local_ctx, indent+1):
                logger.error(f"{sp}❌ [Theorem] Failed")
                return False
        if derivable(node.conclusion, local_ctx):
            logger.debug(f"{sp}[Theorem] {node.name} proved: {pretty_expr(node.conclusion)}")
            return True
        else:
            logger.error(f"{sp}❌ [Theorem] {node.name} not proved: {pretty_expr(node.conclusion)}")
            return False

    # --- Check ---
    if isinstance(node, Check):
        logger.debug(f"{sp}[Check] Checking {pretty_expr(node.conclusion)}")
        if derivable(node.conclusion, context):
            logger.debug(f"{sp}[Check] goal {pretty_expr(node.conclusion)} derived")
            return True
        else:
            logger.error(f"{sp}❌ [Check] goal {pretty_expr(node.conclusion)} not derivable")
            return False

    # --- Assume ---
    if isinstance(node, Assume):
        logger.debug(f"{sp}[Assume] premise={pretty_expr(node.premise)}, conclusion={pretty_expr(node.conclusion)}")
        local_ctx = Context(list(context.formulas + [node.premise]), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if derivable(node.conclusion, local_ctx):
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
        local_ctx = Context(list(context.formulas), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if derivable(node.conclusion, local_ctx):
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
        if not derivable(node.fact, context):
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
        local_ctx = Context(list(context.formulas), False)
        for stmt in node.cases:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Divide] derived in all cases: {pretty_expr(node.conclusion)}")
        return True

    if isinstance(node, Case):
        logger.debug(f"{sp}[Case] premise={pretty_expr(node.premise)}")
        local_ctx = Context(list(context.formulas + [node.premise]), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if derivable(node.conclusion, local_ctx):
            logger.debug(f"{sp}[Case] derived conclusion {pretty_expr(node.conclusion)}")
            return True
        else:
            logger.error(f"{sp}❌ [Case] Cannot derive {pretty_expr(node.conclusion)}")
            return False

    if isinstance(node, Some):
        fact = node.premise
        for v in reversed(node.vars):
            fact = Exists(v, fact)
        if not derivable(fact, context):
            logger.error(f"{sp}❌ [Some] not derivable: {pretty_expr(fact)}")
            return False
        logger.debug(f"{sp}[Some] derivable: {pretty_expr(fact)}")
        logger.debug(f"{sp}[Some] Taking {node.vars}, premise={pretty_expr(node.premise)}")
        local_ctx = Context(list(context.formulas + [node.premise]), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if not derivable(node.conclusion, local_ctx):
            logger.error(f"{sp}❌ [Some] Cannot derive {pretty_expr(node.conclusion)}")
            return False
        logger.debug(f"{sp}[Some] derived conclusion {pretty_expr(node.conclusion)}")
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Some] Added {pretty_expr(node.conclusion)}")
        return True
    
    if isinstance(node, Deny):
        logger.debug(f"{sp}[Deny] premise={pretty_expr(node.premise)}")
        local_ctx = Context(list(context.formulas + [node.premise]), False)
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
        if not derivable(node.contradiction, context):
            logger.error(f"{sp}❌ [Contradict] Cannot derive {pretty_expr(node.contradiction)}")
            return False
        if not derivable(Not(node.contradiction), context):
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
        if not derivable(node.fact, context):
            logger.error(f"{sp}❌ [Apply] Cannot derive {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Apply] Drivable fact: {pretty_expr(node.fact)}")
        if node.env is not None:
            vars, body = collect_forall_vars(node.fact)
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
            implication = node.fact
        if not isinstance(implication, Implies):
            logger.error(f"{sp}❌ [Apply] Not Implies object: {pretty_expr(implication)}")
            return False
        logger.debug(f"{sp}[Apply] Implies object: {pretty_expr(implication)}")
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
        if not derivable(node.fact, context):
            logger.error(f"{sp}❌ [Lift] Not fact: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Lift] fact: {pretty_expr(node.fact)}")
        free_vars, _ = collect_vars(node.fact)
        if not set(node.env.values()).issubset(free_vars):
            logger.error(f"{sp}❌ [Lift] Cannot be lifted: vars={free_vars}, env={node.env}")
            return False
        logger.debug(f"{sp}[Lift] Can be lifted: vars={free_vars}, env={node.env}")
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

    logger.error(f"{sp}❌ Unsupported node {node}")
    return False

if __name__ == "__main__":
    logging.basicConfig(level=logging.DEBUG, format="%(message)s")
    import sys
    path = sys.argv[1]
    f = open(path)
    src = f.read()
    f.close()
    ast = parse_file_from_source(src)
    for node in ast:
        pretty(node)
        if hasattr(node, "proof"):
            result = check_proof(node)
            print(f"✔ theorem {node.name}: OK" if result else "❌ theorem {node.name}: Failed")
