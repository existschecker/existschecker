# checker.py
from parser import Theorem, Any, Assume, Conclude, Symbol, And, Implies, Forall

# === α同値判定 ===
def alpha_equiv(e1, e2, env=None):
    """束縛変数の違いを無視して式を比較"""
    if env is None:
        env = {}

    if isinstance(e1, Forall) and isinstance(e2, Forall):
        newenv = env.copy()
        newenv[e1.var] = e2.var
        return alpha_equiv(e1.body, e2.body, newenv)

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

# === コンテキスト中の式検索 ===
def expr_in_context(expr, context):
    return any(alpha_equiv(expr, c) for c in context)

# And を分解
def split_conjunction(expr):
    if isinstance(expr, And):
        return split_conjunction(expr.left) + split_conjunction(expr.right)
    else:
        return [expr]

def derivable(goal, context):
    # α同値チェック
    if expr_in_context(goal, context):
        return True

    # goal が And のとき
    if isinstance(goal, And):
        return derivable(goal.left, context) and derivable(goal.right, context)

    # context にある And を分解して使えるようにする
    for c in context:
        if isinstance(c, And):
            if derivable(goal, [c.left] + context):
                return True
            if derivable(goal, [c.right] + context):
                return True
    return False

# === 証明チェッカー ===
def check_proof(node, context=None, indent=0):
    if context is None:
        context = []

    sp = "  " * indent

    # --- Theorem ---
    if isinstance(node, Theorem):
        print(f"{sp}Theorem {node.name}:")
        local_ctx = []
        if not check_proof(node.proof, local_ctx, indent+1):
            print(f"{sp}❌ Failed")
            return False
        goal = node.proof.conclusion
        if expr_in_context(goal, local_ctx):
            print(f"{sp}✔ Theorem {node.name} proved: {goal}")
            return True
        else:
            print(f"{sp}❌ Theorem {node.name} failed")
            return False

    # --- Conclude ---
    if isinstance(node, Conclude):
        print(f"{sp}>> Checking Conclude {node.conclusion}")
        local_ctx = list(context)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if derivable(node.conclusion, local_ctx):  # ← 置き換え
            context.append(node.conclusion)
            print(f"{sp}✔ Conclude goal {node.conclusion} derived")
            return True
        else:
            print(f"{sp}❌ Conclude goal {node.conclusion} not derivable")
            return False

    # --- Assume ---
    if isinstance(node, Assume):
        print(f"{sp}>> Checking Assume premise={node.premise}, goal={node.conclusion}")
        new_ctx = context + split_conjunction(node.premise)

        if not node.body:
            goal = node.conclusion
            if derivable(goal, new_ctx):  # ← 置き換え
                implication = Implies(node.premise, goal)
                context.append(implication)
                print(f"{sp}✔ Derived implication {implication}")
                return True
            else:
                print(f"{sp}❌ Cannot derive {goal}")
                return False
        else:
            local_ctx = list(new_ctx)
            for stmt in node.body:
                if not check_proof(stmt, local_ctx, indent+1):
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
        if local_ctx:
            formula = local_ctx[-1]
            for v in reversed(node.vars):
                formula = Forall(v, formula)
            context.append(formula)
            print(f"{sp}✔ Generalized to {formula}")
        return True

    print(f"{sp}⚠ Unsupported node {node}")
    return False
