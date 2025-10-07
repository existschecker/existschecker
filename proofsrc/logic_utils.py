from ast_types import Or, Not, Forall, Exists, ExistsUniq, Implies, Iff, And, Symbol, Context, pretty_expr
from itertools import permutations
from typing import List

def flatten_op(expr, op) -> List:
    if isinstance(expr, op):
        return flatten_op(expr.left, op) + flatten_op(expr.right, op)
    else:
        return [expr]

def op_equiv(e1, e2, env, op):
    parts1 = flatten_op(e1, op)
    parts2 = flatten_op(e2, op)

    if len(parts1) != len(parts2):
        return False

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
        return op_equiv(e1, e2, env, And)

    if isinstance(e1, Or) and isinstance(e2, Or):
        return op_equiv(e1, e2, env, Or)

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

    elif isinstance(expr, (And, Or, Implies, Iff)):
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
    return any(logic_equiv(expr, f, context) for f in context.formulas)

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

def to_nnf(expr, context: Context):
    if isinstance(expr, Symbol):
        if expr.name in context.atoms:
            return expr
        elif expr.name in context.definitions:
            return to_nnf(expand_definitions(expr, context), context)
        else:
            raise Exception(f"Unexpected expr (Symbol): {pretty_expr(expr)}")
    elif isinstance(expr, Not):
        body = expr.body
        if isinstance(body, Symbol):
            if body.name in context.atoms:
                return expr
            elif body.name in context.definitions:
                return to_nnf(Not(expand_definitions(body, context)), context)
            else:
                raise Exception(f"Unexpected expr (Not -> Symbol): {pretty_expr(expr)}")
        elif isinstance(body, Not):
            return to_nnf(body.body, context)
        elif isinstance(body, And):
            return Or(to_nnf(Not(body.left), context), to_nnf(Not(body.right), context))
        elif isinstance(body, Or):
            return And(to_nnf(Not(body.left), context), to_nnf(Not(body.right), context))
        elif isinstance(body, (Implies, Iff)):
            return Not(to_nnf(body, context))
        elif isinstance(body, Exists):
            return Forall(body.var, to_nnf(Not(body.body), context))
        elif isinstance(body, Forall):
            return Exists(body.var, to_nnf(Not(body.body), context))
        else:
            raise Exception(f"Unexpected expr (Not): {pretty_expr(expr)}")
    elif isinstance(expr, (And, Or)):
        return type(expr)(to_nnf(expr.left, context), to_nnf(expr.right, context))
    elif isinstance(expr, Implies):
        return to_nnf(Or(Not(expr.left), expr.right), context)
    elif isinstance(expr, Iff):
        return to_nnf(And(Implies(expr.left, expr.right), Implies(expr.right, expr.left)), context)
    elif isinstance(expr, (Exists, Forall)):
        return type(expr)(expr.var, to_nnf(expr.body, context))
    elif isinstance(expr, ExistsUniq):
        used_vars = {expr.var} | collect_vars(expr.body)[0] | collect_vars(expr.body)[1]
        vardash = fresh_var(expr.var + "'", used_vars)
        body_subst = substitute(expr.body, {expr.var: vardash})
        expanded = And(Exists(expr.var, expr.body), Implies(Forall(vardash, body_subst), Symbol("equal", [vardash, expr.var])))
        return to_nnf(expanded, context)
    else:
        raise Exception(f"Unexpected expr: {pretty_expr(expr)}")

def normalize_neg2(expr):
    if isinstance(expr, Symbol):
        return expr
    elif isinstance(expr, Not):
        if isinstance(expr.body, Not):
            return normalize_neg2(expr.body.body)
        else:
            return Not(normalize_neg2(expr.body))
    elif isinstance(expr, (And, Or)):
        return type(expr)(normalize_neg2(expr.left), normalize_neg2(expr.right))
    elif isinstance(expr, (Exists, Forall)):
        return type(expr)(expr.var, normalize_neg2(expr.body))
    else:
        Exception(f"Unexpected e: {pretty_expr(expr)}")

def forall_to_exists(expr):
    if isinstance(expr, Symbol):
        return expr
    if isinstance(expr, Not):
        return Not(forall_to_exists(expr.body))
    if isinstance(expr, (And, Or)):
        return type(expr)(forall_to_exists(expr.left), forall_to_exists(expr.right))
    if isinstance(expr, Exists):
        return Exists(expr.var, forall_to_exists(expr.body))
    if isinstance(expr, Forall):
        return Not(Exists(expr.var, Not(forall_to_exists(expr.body))))

def vee_to_neg_wedge(expr):
    if isinstance(expr, Symbol):
        return expr
    if isinstance(expr, Not):
        return Not(vee_to_neg_wedge(expr.body))
    if isinstance(expr, And):
        return And(vee_to_neg_wedge(expr.left), vee_to_neg_wedge(expr.right))
    if isinstance(expr, Or):
        return Not(And(Not(vee_to_neg_wedge(expr.left)), Not(vee_to_neg_wedge(expr.right))))
    if isinstance(expr, (Exists, Forall)):
        return type(expr)(expr.var, vee_to_neg_wedge(expr.body))

def strip_quantifiers(expr):
    qs = []
    body = expr
    while isinstance(body, (Exists, Forall)):
        qs.append(type(body)(body.var, None))
        body = body.body
    return qs, body

def make_quantifiers(qs, body):
    expr = body
    for q in reversed(qs):
        expr = type(q)(q.var, expr)
    return expr

def to_pnf(expr, context: Context):
    if (isinstance(expr, Symbol) and expr.name in context.atoms) or isinstance(expr, Not):
        return expr

    if isinstance(expr, And) or isinstance(expr, Or):
        left_pnf = to_pnf(expr.left, context)
        right_pnf = to_pnf(expr.right, context)
        qs_left, core_left = strip_quantifiers(left_pnf)
        qs_right, core_right = strip_quantifiers(right_pnf)
        core = And(core_left, core_right) if isinstance(expr, And) else Or(core_left, core_right)
        return make_quantifiers(qs_left + qs_right, core)

    if isinstance(expr, Implies):
        return to_pnf(Or(Not(expr.left), expr.right), context)

    if isinstance(expr, Iff):
        return to_pnf(And(Implies(expr.left, expr.right), Implies(expr.right, expr.left)), context)

    if isinstance(expr, (Exists, Forall)):
        return type(expr)(expr.var, to_pnf(expr.body, context))

def to_neg_wedge_exists(expr, context):
    expr_norm = expand_definitions(expr, context)
    expr_norm = to_nnf(expr_norm, context)
    expr_norm = vee_to_neg_wedge(expr_norm)
    expr_norm = forall_to_exists(expr_norm)
    expr_norm = to_pnf(expr_norm, context)
    expr_norm = normalize_neg2(expr_norm)
    return expr_norm

def logic_equiv(expr1, expr2, context):
    expr1_norm = to_neg_wedge_exists(expr1, context)
    expr2_norm = to_neg_wedge_exists(expr2, context)
    return alpha_equiv(expr1_norm, expr2_norm)

if __name__ == "__main__":
    from ast_types import Atom
    expr1 = Or(Symbol("in", ["x", "y"]), Symbol("in", ["y", "x"]))
    expr2 = Or(Symbol("in", ["y", "x"]), Symbol("in", ["x", "y"]))
    context = Context([], False, {"in": Atom("PREDICATE", "in", 2)}, {}, {}, {}, {})
    expr1_norm = to_neg_wedge_exists(expr1, context)
    expr2_norm = to_neg_wedge_exists(expr2, context)
    print(f"expr1: {pretty_expr(expr1)}")
    print(f"expr1_norm: {pretty_expr(expr1_norm)}")
    print(f"expr2: {pretty_expr(expr2)}")
    print(f"expr2_norm: {pretty_expr(expr2_norm)}")
    print(f"alpha_equiv(expr1_norm, expr2_norm): {alpha_equiv(expr1_norm, expr2_norm)}")
