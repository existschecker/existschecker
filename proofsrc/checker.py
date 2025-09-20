from parser import Theorem, Any, Assume, Conclude, Expr, And, Implies, Forall, Symbol

def alpha_equiv(e1, e2, env=None):
    if env is None:
        env = {}
    # Forall: 束縛変数名を対応付けて再帰
    if isinstance(e1, Forall) and isinstance(e2, Forall):
        newenv = env.copy()
        newenv[e1.var] = e2.var
        return alpha_equiv(e1.body, e2.body, newenv)
    # Implies / And
    if isinstance(e1, Implies) and isinstance(e2, Implies):
        return alpha_equiv(e1.left, e2.left, env) and alpha_equiv(e1.right, e2.right, env)
    if isinstance(e1, And) and isinstance(e2, And):
        return alpha_equiv(e1.left, e2.left, env) and alpha_equiv(e1.right, e2.right, env)
    # Symbol: 名前一致 + 引数ごとに env を考慮して比較
    if isinstance(e1, Symbol) and isinstance(e2, Symbol):
        if e1.name != e2.name or len(e1.args) != len(e2.args):
            return False
        for a, b in zip(e1.args, e2.args):
            mapped = env.get(a, a)  # env にあれば置換してから比較
            if mapped != b:
                return False
        return True
    return False

def expr_in_context(expr, context):
    return any(alpha_equiv(expr, c) for c in context)

def derivable(goal, context):
    # まず context に α同値な式があれば可
    if expr_in_context(goal, context):
        return True
    # goal が And のときは左右を導けるか
    if isinstance(goal, And):
        return derivable(goal.left, context) and derivable(goal.right, context)
    # context にある And を分解して探す（A∧B があれば A, B が使える）
    for c in context:
        if isinstance(c, And):
            if derivable(goal, [c.left] + context):
                return True
            if derivable(goal, [c.right] + context):
                return True
    return False

# --- 証明チェッカー本体 ---
def check_proof(node, context=None, indent=0):
    """
    シンプルに context を1つだけ回す設計。
    各ブロック内で導出された式は local_context に溜め、必要に応じて
    Conclude や Any が context に追加して外へ出す。

    標準出力は英語、コメントは日本語。
    """
    if context is None:
        context = []

    sp = "  " * indent

    # --- Theorem ---
    if isinstance(node, Theorem):
        print(f"{sp}Theorem {node.name}")
        # 定理は新しいトップレベルの context を使って検証
        top_ctx: list[Expr] = []
        if not check_proof(node.proof, top_ctx, indent + 1):
            print(f"{sp}❌ Failed")
            return False
        goal = node.proof.conclusion
        if derivable(goal, top_ctx):
            print(f"{sp}✔ Theorem {node.name} proved: {goal}")
            return True
        else:
            print(f"{sp}❌ Theorem {node.name} failed: goal {goal} not derivable from {top_ctx}")
            return False

    # --- Conclude ---
    if isinstance(node, Conclude):
        print(f"{sp}>> Checking Conclude {node.conclusion}")
        # このブロック専用のローカル context を作る
        local_ctx = list(context)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent + 1):
                return False
        # ボディを検証した後にゴールが local_ctx から導けるか確認
        if derivable(node.conclusion, local_ctx):
            # Conclude は成功したゴールを外側の context にエクスポートする
            context.append(node.conclusion)
            print(f"{sp}✔ Conclude goal {node.conclusion} derived")
            return True
        else:
            print(f"{sp}❌ Conclude goal {node.conclusion} not derivable from {local_ctx}")
            return False

    # --- Assume ---
    if isinstance(node, Assume):
        print(f"{sp}>> Checking Assume premise={node.premise}, goal={node.conclusion}")
        # 前提はそのまま追加（split_conjunction は使わない）
        new_ctx = context + [node.premise]
        if not node.body:
            # ボディが無ければ前提から直接ゴールが導けるか
            if derivable(node.conclusion, new_ctx):
                implication = Implies(node.premise, node.conclusion)
                context.append(implication)
                print(f"{sp}✔ Derived implication {implication}")
                return True
            else:
                print(f"{sp}❌ Cannot derive {node.conclusion} from {new_ctx}")
                return False
        else:
            # ボディをローカルコンテキストで検証
            local_ctx = list(new_ctx)
            for stmt in node.body:
                if not check_proof(stmt, local_ctx, indent + 1):
                    return False
            implication = Implies(node.premise, node.conclusion)
            context.append(implication)
            print(f"{sp}✔ Discharged {node.premise}, added {implication} to context")
            return True

    # --- Any (universal intro) ---
    if isinstance(node, Any):
        print(f"{sp}>> Entering Any {node.vars}")
        local_ctx = list(context)
        before_len = len(local_ctx)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent + 1):
                return False
        # body の結果として追加された最後の式を一般化して外側に出す
        new_items = local_ctx[before_len:]
        if new_items:
            last = new_items[-1]
            formula = last
            for v in reversed(node.vars):
                formula = Forall(v, formula)
            context.append(formula)
            print(f"{sp}✔ Generalized to {formula}")
        else:
            print(f"{sp}⚠ No new derivation inside Any {node.vars}")
        return True

    # 未対応ノード
    print(f"{sp}⚠ Unsupported node {node}")
    return False