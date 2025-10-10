from ast_types import Or, Not, Forall, Exists, ExistsUniq, Implies, Iff, And, Symbol, Context, pretty_expr
from itertools import permutations
from typing import List
from dataclasses import dataclass

@dataclass
class BoolTrue:
    pass

@dataclass
class BoolFalse:
    pass

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

def alpha_equiv(e1, e2, env=None):
    if env is None:
        env = {}

    if isinstance(e1, Not) and isinstance(e2, Not):
        return alpha_equiv(e1.body, e2.body, env)

    for quantifier_type in (Forall, Exists):
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

    if isinstance(e1, BoolTrue) and isinstance(e2, BoolTrue):
        return True

    if isinstance(e1, BoolFalse) and isinstance(e2, BoolFalse):
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

    elif isinstance(expr, (BoolTrue, BoolFalse)):
        return set(), set()

    else:
        raise Exception(f"Unexpected expr {pretty_expr(expr)}")

# === コンテキスト中の式検索 ===
def expr_in_context(expr, context):
    return any(logic_equiv(expr, f, context) for f in context.formulas)

def to_core_logic_form(expr, context):
    if isinstance(expr, Symbol):
        if expr.name in context.atoms:
            return expr
        if expr.name in context.definitions:
            definition = context.definitions[expr.name].formula
            vars, body = collect_quantifier_vars(definition, Forall)
            expanded = substitute(body, dict(zip(vars, expr.args))).right
            return to_core_logic_form(expanded, context)
        else:
            raise Exception(f"Unexpected expr (Symbol): {pretty_expr(expr)}")
    elif isinstance(expr, Not):
        return Not(to_core_logic_form(expr.body, context))
    elif isinstance(expr, (And, Or)):
        return type(expr)(to_core_logic_form(expr.left, context), to_core_logic_form(expr.right, context))
    elif isinstance(expr, Implies):
        return to_core_logic_form(Or(Not(expr.left), expr.right), context)
    elif isinstance(expr, Iff):
        return to_core_logic_form(And(Implies(expr.left, expr.right), Implies(expr.right, expr.left)), context)
    elif isinstance(expr, (Exists, Forall)):
        return type(expr)(expr.var, to_core_logic_form(expr.body, context))
    elif isinstance(expr, ExistsUniq):
        used_vars = {expr.var} | collect_vars(expr.body)[0] | collect_vars(expr.body)[1]
        vardash = fresh_var(expr.var + "'", used_vars)
        body_subst = substitute(expr.body, {expr.var: vardash})
        expanded = And(Exists(expr.var, expr.body), Forall(vardash, Implies(body_subst, Symbol("equal", [vardash, expr.var]))))
        return to_core_logic_form(expanded, context)
    else:
        raise Exception(f"Unexpected expr: {pretty_expr(expr)}")

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

def to_nnf(expr):
    if isinstance(expr, Symbol):
        return expr
    elif isinstance(expr, Not):
        body = expr.body
        if isinstance(body, Symbol):
            return expr
        elif isinstance(body, Not):
            return to_nnf(body.body)
        elif isinstance(body, And):
            return Or(to_nnf(Not(body.left)), to_nnf(Not(body.right)))
        elif isinstance(body, Or):
            return And(to_nnf(Not(body.left)), to_nnf(Not(body.right)))
        elif isinstance(body, Exists):
            return Forall(body.var, to_nnf(Not(body.body)))
        elif isinstance(body, Forall):
            return Exists(body.var, to_nnf(Not(body.body)))
        else:
            raise Exception(f"Unexpected expr (Not): {pretty_expr(expr)}")
    elif isinstance(expr, (And, Or)):
        return type(expr)(to_nnf(expr.left), to_nnf(expr.right))
    elif isinstance(expr, (Exists, Forall)):
        return type(expr)(expr.var, to_nnf(expr.body))
    else:
        raise Exception(f"Unexpected expr: {pretty_expr(expr)}")

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

def alpha_rename(expr, rename_map):
    if isinstance(expr, Symbol):
        return Symbol(expr.name, [rename_map.get(a, a) for a in expr.args])
    elif isinstance(expr, Not):
        return Not(alpha_rename(expr.body, rename_map))
    elif isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(alpha_rename(expr.left, rename_map), alpha_rename(expr.right, rename_map))
    elif isinstance(expr, (Exists, Forall)):
        var = rename_map.get(expr.var, expr.var)
        return type(expr)(var, alpha_rename(expr.body, rename_map))
    else:
        return expr

def rename_bound(expr, bound_vars, used):
    rename_map = {}
    for v in bound_vars:
        if v in used:
            rename_map[v] = fresh_var(v, used)
    return alpha_rename(expr, rename_map)

def to_pnf(expr):
    if isinstance(expr, Symbol):
        return expr
    elif isinstance(expr, Not):
        return Not(to_pnf(expr.body))
    elif isinstance(expr, And) or isinstance(expr, Or):
        left_pnf = to_pnf(expr.left)
        right_pnf = to_pnf(expr.right)
        left_free, left_bound = collect_vars(left_pnf)
        right_free, right_bound = collect_vars(right_pnf)
        left_pnf = rename_bound(left_pnf, left_bound, right_free)
        right_pnf = rename_bound(right_pnf, right_bound, left_free | left_bound)
        qs_left, core_left = strip_quantifiers(left_pnf)
        qs_right, core_right = strip_quantifiers(right_pnf)
        core = type(expr)(core_left, core_right)
        return make_quantifiers(qs_left + qs_right, core)
    elif isinstance(expr, (Exists, Forall)):
        return type(expr)(expr.var, to_pnf(expr.body))
    else:
        raise Exception(f"Unexpected expr: {pretty_expr(expr)}")

def to_cnf(expr):
    if isinstance(expr, Symbol):
        return expr
    elif isinstance(expr, Not):
        return Not(to_cnf(expr.body))
    elif isinstance(expr, And):
        return And(to_cnf(expr.left), to_cnf(expr.right))
    elif isinstance(expr, Or):
        left_cnf = to_cnf(expr.left)
        right_cnf = to_cnf(expr.right)
        if isinstance(left_cnf, And):
            return And(to_cnf(Or(left_cnf.left, right_cnf)), to_cnf(Or(left_cnf.right, right_cnf)))
        elif isinstance(right_cnf, And):
            return And(to_cnf(Or(left_cnf, right_cnf.left)), to_cnf(Or(left_cnf, right_cnf.right)))
        else:
            return Or(left_cnf, right_cnf)
    elif isinstance(expr, (Exists, Forall)):
        return type(expr)(expr.var, to_cnf(expr.body))
    else:
        raise Exception(f"Unexpected expr: {expr}")

def simplify_op(expr):
    if not isinstance(expr, (And, Or)):
        raise Exception(f"Unexpected expr: {pretty_expr(expr)}")
    parts = flatten_op(expr, type(expr))
    simplified_parts = []
    for p in parts:
        if isinstance(p, BoolTrue):
            if isinstance(expr, Or):
                return BoolTrue()
            else:
                continue
        elif isinstance(p, BoolFalse):
            if isinstance(expr, And):
                return BoolFalse()
            else:
                continue
        else:
            contradiction = False
            skip = False
            for q in simplified_parts:
                if alpha_equiv(p, Not(q)) or alpha_equiv(Not(p), q):
                    contradiction = True
                    break
                if alpha_equiv(p, q):
                    skip = True
                    break
            if contradiction:
                if isinstance(expr, And):
                    return BoolFalse()
                else:
                    return BoolTrue()
            if skip:
                continue
            simplified_parts.append(p)
    if len(simplified_parts) == 0:
        if isinstance(expr, And):
            return BoolTrue()
        else:
            return BoolFalse()
    elif len(simplified_parts) == 1:
        return simplified_parts[0]
    else:
        result = simplified_parts[0]
        for part in simplified_parts[1:]:
            result = type(expr)(result, part)
        return result

def simplify(expr):
    if isinstance(expr, (Symbol, Not)):
        return expr
    elif isinstance(expr, And):
        left_s = simplify(expr.left)
        right_s = simplify(expr.right)
        return simplify_op(And(left_s, right_s))
    elif isinstance(expr, Or):
        left_s = simplify(expr.left)
        right_s = simplify(expr.right)
        return simplify_op(Or(left_s, right_s))
    elif isinstance(expr, (Exists, Forall)):
        body_simplified = simplify(expr.body)
        if expr.var not in collect_vars(body_simplified)[0]:
            return body_simplified
        else:
            return type(expr)(expr.var, body_simplified)
    else:
        raise Exception(f"Unexpected expr: {expr}")

def to_canonical_form(expr, context):
    expr_norm = to_core_logic_form(expr, context)
    expr_norm = to_nnf(expr_norm)
    expr_norm = to_pnf(expr_norm)
    expr_norm = to_cnf(expr_norm)
    expr_norm = simplify(expr_norm)
    return expr_norm

def logic_equiv(expr1, expr2, context):
    expr1_norm = to_canonical_form(expr1, context)
    expr2_norm = to_canonical_form(expr2, context)
    return alpha_equiv(expr1_norm, expr2_norm)

def print_tree(expr, prefix="", is_root=True, is_last=True):
    print_prefix = prefix + ("" if is_root else ("└─" if is_last else "├─"))
    if isinstance(expr, Symbol):
        print(f"{print_prefix}Symbol({expr.name}, [{", ".join(expr.args)}])")
    elif isinstance(expr, Not):
        print(f"{print_prefix}Not")
        print_tree(expr.body, prefix + ("" if is_root else ("   " if is_last else "│  ")), False, True)
    elif isinstance(expr, (And, Or, Implies, Iff)):
        print(f"{print_prefix}{type(expr).__name__}")
        print_tree(expr.left, prefix + ("" if is_root else ("   " if is_last else "│  ")), False, False)
        print_tree(expr.right, prefix + ("" if is_root else ("   " if is_last else "│  ")), False, True)
    elif isinstance(expr, (Exists, Forall, ExistsUniq)):
        print(f"{print_prefix}{type(expr).__name__}({expr.var})")
        print_tree(expr.body, prefix + ("" if is_root else ("   " if is_last else "│  ")), False, True)
    else:
        raise Exception(f"Unexpected expr: {pretty_expr(expr)}")

if __name__ == "__main__":
    from ast_types import Atom, Definition
    context = Context([], False, {"in": Atom("PREDICATE", "in", 2)}, {}, {}, {"equal": Definition("PREDICATE", "equal", 2, Forall("x", Forall("y", Iff(Symbol("equal", ["x", "y"]), Forall("z", Iff(Symbol("in", ["z", "x"]), Symbol("in", ["z", "y"])))))))}, {})

    expr = Iff(Exists("x", Symbol("equal", ["x", "x"])), Exists("x", Symbol("equal", ["x", "x"])))
    print("expr")
    print()
    print_tree(expr)
    print()

    expr_norm = to_core_logic_form(expr, context)
    print("to_core_logic_form()")
    print()
    print_tree(expr_norm)
    print()

    expr_norm = to_nnf(expr_norm)
    print("to_nnf()")
    print()
    print_tree(expr_norm)
    print()

    expr_norm = to_pnf(expr_norm)
    print("to_pnf()")
    print()
    print_tree(expr_norm)
    print()

    expr_norm = to_cnf(expr_norm)
    print("to_cnf()")
    print()
    print_tree(expr_norm)
    print()

    print("simplify()")
    print()
    print(simplify(expr_norm))
    print()
