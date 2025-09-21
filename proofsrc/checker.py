# checker.py
from parser import Theorem, Any, Assume, Conclude, Symbol, And, Implies, Forall

# === α同値判定 ===
from itertools import permutations

def alpha_equiv(e1, e2, env=None):
    """束縛変数の順序も無視して α同値判定"""
    if env is None:
        env = {}

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

    if isinstance(e1, Implies) and isinstance(e2, Implies):
        return alpha_equiv(e1.left, e2.left, env) and alpha_equiv(e1.right, e2.right, env)

    if isinstance(e1, And) and isinstance(e2, And):
        return alpha_equiv(e1.left, e2.left, env) and alpha_equiv(e1.right, e2.right, env)

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
        return derivable(goal.left, flat_ctx) and derivable(goal.right, flat_ctx)
    # α同値チェック
    return expr_in_context(goal, flat_ctx)

def derivable(goal, context):
    flat_ctx = []
    for c in context:
        flat_ctx.extend(split_conjunction(c))
    return derivable_flat(goal, flat_ctx)

# === 証明チェッカー ===
def check_proof(node, context=None, indent=0):
    if context is None:
        context = []

    sp = "  " * indent

    # --- Theorem ---
    if isinstance(node, Theorem):
        print(f"{sp}Theorem {node.name}:")
        local_ctx = []
        for stmt in node.proof:
            if not check_proof(stmt, local_ctx, indent+1):
                print(f"{sp}❌ Failed")
                return False
        if derivable(node.conclusion, local_ctx):
            print(f"{sp}✔ Theorem {node.name} proved: {node.conclusion}")
            return True
        else:
            print(f"{sp}❌ Theorem {node.name} failed")
            return False

    # --- Conclude ---
    if isinstance(node, Conclude):
        print(f"{sp}>> Checking Conclude {node.conclusion}")
        if derivable(node.conclusion, context):
            print(f"{sp}✔ Conclude goal {node.conclusion} derived")
            return True
        else:
            print(f"{sp}❌ Conclude goal {node.conclusion} not derivable")
            return False

    # --- Assume ---
    if isinstance(node, Assume):
        print(f"{sp}>> Checking Assume premise={node.premise}, goal={node.conclusion}")
        local_ctx = list(context + [node.premise])
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if derivable(node.conclusion, local_ctx):
            print(f"{sp}✔ Derived conclusion {node.conclusion}")
        else:
            print(f"{sp}❌ Cannot derive {node.conclusion}")
            return False
        implication = Implies(node.premise, node.conclusion)
        context.append(implication)
        print(f"{sp}✔ Discharged {node.premise}, added {implication}")
        return True

    # --- Any ---
    if isinstance(node, Any):
        print(f"{sp}>> Entering Any {node.vars}")
        local_ctx = list(context)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if derivable(node.conclusion, local_ctx):
            print(f"{sp}✔ [Any] Derived conclusion {node.conclusion}")
        else:
            print(f"{sp}❌ [Any] Cannot derive {node.conclusion}")
            return False
        goal = node.conclusion
        for v in reversed(node.vars):
            goal = Forall(v, goal)
        context.append(goal)
        print(f"{sp}✔ [Any] Generalized to {goal}")
        return True

    print(f"{sp}⚠ Unsupported node {node}")
    return False
