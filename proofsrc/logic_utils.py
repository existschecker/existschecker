from ast_types import Or, Not, Forall, Exists, ExistsUniq, Implies, Iff, And, Symbol, Context, Compound, Fun, Con, Var, Bottom, Term, Pred, pretty_expr
from itertools import permutations
from dataclasses import dataclass
from copy import deepcopy

@dataclass
class BoolTrue:
    pass

@dataclass
class BoolFalse:
    pass

def flatten_op(expr, op: type[And] | type[Or]) -> list:
    if isinstance(expr, op):
        return flatten_op(expr.left, op) + flatten_op(expr.right, op)
    else:
        return [expr]

def op_equiv(e1, e2, context: Context, env: dict[Var, Var], op: type[And] | type[Or]) -> bool:
    parts1 = flatten_op(e1, op)
    parts2 = flatten_op(e2, op)

    if len(parts1) != len(parts2):
        return False

    matched = [False] * len(parts2)
    for p1 in parts1:
        found = False
        for i, p2 in enumerate(parts2):
            if not matched[i] and alpha_equiv(p1, p2, context, env):
                matched[i] = True
                found = True
                break
        if not found:
            return False

    return True

def alpha_equiv(e1, e2, context: Context, env: dict[Var, Var] | None = None) -> bool:
    if env is None:
        env = {}

    if isinstance(e1, Not) and isinstance(e2, Not):
        return alpha_equiv(e1.body, e2.body, context, env)

    for quantifier_type in (Forall, Exists, ExistsUniq):
        if isinstance(e1, quantifier_type) and isinstance(e2, quantifier_type):
            vars1, body1 = collect_quantifier_vars(e1, quantifier_type)
            vars2, body2 = collect_quantifier_vars(e2, quantifier_type)

            if len(vars1) != len(vars2):
                return False

            free_vars2, _ = collect_vars(e2)
            for v1 in vars1:
                if v1 in free_vars2:
                    return False

            free_vars1, _ = collect_vars(e1)
            for v2 in vars2:
                if v2 in free_vars1:
                    return False

            for perm in permutations(vars2):
                newenv = env.copy()
                for v1, v2 in zip(vars1, perm):
                    newenv[v1] = v2
                if alpha_equiv(body1, body2, context, newenv):
                    return True
            return False

    if isinstance(e1, And) and isinstance(e2, And):
        return op_equiv(e1, e2, context, env, And)

    if isinstance(e1, Or) and isinstance(e2, Or):
        return op_equiv(e1, e2, context, env, Or)

    if isinstance(e1, Implies) and isinstance(e2, Implies):
        return alpha_equiv(e1.left, e2.left, context, env) and alpha_equiv(e1.right, e2.right, context, env)

    if isinstance(e1, Iff) and isinstance(e2, Iff):
        return alpha_equiv(e1.left, e2.left, context, env) and alpha_equiv(e1.right, e2.right, context, env)

    if isinstance(e1, Symbol) and isinstance(e2, Symbol):
        if not alpha_equiv(e1.pred, e2.pred, context, env):
            return False
        if len(e1.args) != len(e2.args):
            return False
        if context.equality is not None and e1.pred.name == context.equality.equal.name:
            a1, b1 = e1.args
            a2, b2 = e2.args
            return (alpha_equiv(a1, a2, context, env) and alpha_equiv(b1, b2, context, env)) or (alpha_equiv(a1, b2, context, env) and alpha_equiv(b1, a2, context, env))
        for a, b in zip(e1.args, e2.args):
            if not alpha_equiv(a, b, context, env):
                return False
        return True

    if isinstance(e1, Pred) and isinstance(e2, Pred):
        return e1.name == e2.name

    if isinstance(e1, Compound) and isinstance(e2, Compound):
        if not alpha_equiv(e1.fun, e2.fun, context, env):
            return False
        if len(e1.args) != len(e2.args):
            return False
        for a, b in zip(e1.args, e2.args):
            if not alpha_equiv(a, b, context, env):
                return False
        return True

    if isinstance(e1, Fun) and isinstance(e2, Fun):
        return e1.name == e2.name

    if isinstance(e1, Con) and isinstance(e2, Con):
        return e1.name == e2.name

    if isinstance(e1, Var) and isinstance(e2, Var):
        return env.get(e1, e1) == e2

    if isinstance(e1, BoolTrue) and isinstance(e2, BoolTrue):
        return True

    if isinstance(e1, BoolFalse) and isinstance(e2, BoolFalse):
        return True

    return False

def collect_quantifier_vars(e, quantifier_type: type[Forall] | type[Exists]) -> tuple[list[Var], object]:
    vars_ = []
    body = e
    while isinstance(body, quantifier_type):
        vars_.append(body.var)
        body = body.body
    return vars_, body

def collect_vars(expr, bound: set[Var] | None = None) -> tuple[set[Var], set[Var]]:
    """
    式 expr から自由変数と束縛変数の集合を返す
    戻り値: (free_vars, bound_vars)
    """
    if bound is None:
        bound = set()

    if isinstance(expr, (Symbol, Compound)):
        free = set()
        for arg in expr.args:
            f, _ = collect_vars(arg, bound)
            free.update(f)
        return free, set()

    elif isinstance(expr, (Fun, Con)):
        return set(), set()

    elif isinstance(expr, Var):
        if expr in bound:
            return set(), set()
        else:
            return {expr}, set()

    elif isinstance(expr, Not):
        return collect_vars(expr.body, bound)

    elif isinstance(expr, (And, Or, Implies, Iff)):
        f1, b1 = collect_vars(expr.left, bound)
        f2, b2 = collect_vars(expr.right, bound)
        return f1 | f2, b1 | b2

    elif isinstance(expr, (Forall, Exists, ExistsUniq)):
        f_body, b_body = collect_vars(expr.body, bound | {expr.var})
        return f_body, b_body | {expr.var}

    elif isinstance(expr, (BoolTrue, BoolFalse)):
        return set(), set()

    else:
        raise Exception(f"Unexpected expr {pretty_expr(expr)}")

# === コンテキスト中の式検索 ===
def expr_in_context(expr, context: Context) -> bool:
    return any(alpha_equiv_with_defs(expr, f, context) for f in context.formulas)

def alpha_equiv_with_defs(e1, e2, context: Context, expand_all: bool = False) -> bool:
    if isinstance(e1, Bottom) and isinstance(e2, Bottom):
        return True
    elif isinstance(e1, Bottom) and not isinstance(e2, Bottom):
        return False
    elif not isinstance(e1, Bottom) and isinstance(e2, Bottom):
        return False
    else:
        e1_exp = normalize_neg(expand_basic_defs(e1, context, expand_all))
        e2_exp = normalize_neg(expand_basic_defs(e2, context, expand_all))
        return alpha_equiv(e1_exp, e2_exp, context)

def expand_basic_defs(expr, context: Context, expand_all: bool):
    if isinstance(expr, Symbol):
        if expr.pred.name in context.atoms:
            return Symbol(expand_basic_defs(expr.pred, context, expand_all), [expand_basic_defs(arg, context, expand_all) for arg in expr.args])
        if expr.pred.name in context.defpres:
            defpre = context.defpres[expr.pred.name]
            if defpre.autoexpand or expand_all:
                expanded = substitute(defpre.formula, dict(zip(defpre.args, expr.args)))
                return expand_basic_defs(expanded, context, expand_all)
            else:
                return Symbol(expand_basic_defs(expr.pred, context, expand_all), [expand_basic_defs(arg, context, expand_all) for arg in expr.args])
        else:
            raise Exception(f"Unexpected expr (Symbol): {pretty_expr(expr)}")
    elif isinstance(expr, Compound):
        if expr.fun.name in context.deffuns:
            return Compound(expand_basic_defs(expr.fun, context, expand_all), [expand_basic_defs(arg, context, expand_all) for arg in expr.args])
        elif expr.fun.name in context.deffunterms:
            deffunterm = context.deffunterms[expr.fun.name]
            if expand_all:
                expanded = substitute(deffunterm.term, dict(zip(deffunterm.args, expr.args)))
                return expand_basic_defs(expanded, context, expand_all)
            else:
                return Compound(expand_basic_defs(expr.fun, context, expand_all), [expand_basic_defs(arg, context, expand_all) for arg in expr.args])
        else:
            raise Exception(f"Unexpected expr (Compound): {pretty_expr(expr)}")
    elif isinstance(expr, (Pred, Fun, Con, Var)):
        return expr
    elif isinstance(expr, Not):
        return Not(expand_basic_defs(expr.body, context, expand_all))
    elif isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(expand_basic_defs(expr.left, context, expand_all), expand_basic_defs(expr.right, context, expand_all))
    elif isinstance(expr, (Exists, Forall, ExistsUniq)):
        return type(expr)(expr.var, expand_basic_defs(expr.body, context, expand_all))
    else:
        raise Exception(f"Unexpected expr: {pretty_expr(expr)}")

def normalize_neg(expr):
    if isinstance(expr, Symbol):
        return expr
    elif isinstance(expr, Not):
        if isinstance(expr.body, Not):
            return expr.body.body
        else:
            return expr
    elif isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(normalize_neg(expr.left), normalize_neg(expr.right))
    elif isinstance(expr, (Exists, Forall, ExistsUniq)):
        return type(expr)(expr.var, normalize_neg(expr.body))
    else:
        raise Exception(f"Unexpected expr: {pretty_expr(expr)}")

def to_core_logic_form(expr, context: Context, expand_all: bool = False):
    if isinstance(expr, Symbol):
        if expr.name in context.atoms:
            return Symbol(expr.name, [to_core_logic_form(arg, context, expand_all) for arg in expr.args])
        if expr.name in context.defpres:
            defpre = context.defpres[expr.name]
            if defpre.autoexpand or expand_all:
                expanded = substitute(defpre.formula, dict(zip(defpre.args, expr.args)))
                return to_core_logic_form(expanded, context, expand_all)
            else:
                return Symbol(expr.name, [to_core_logic_form(arg, context, expand_all) for arg in expr.args])
        else:
            raise Exception(f"Unexpected expr (Symbol): {pretty_expr(expr)}")
    elif isinstance(expr, Compound):
        if expr.fun.name in context.deffuns:
            return Compound(to_core_logic_form(expr.fun, context, expand_all), [to_core_logic_form(arg, context, expand_all) for arg in expr.args])
        elif expr.fun.name in context.deffunterms:
            deffunterm = context.deffunterms[expr.fun.name]
            if expand_all:
                expanded = substitute(deffunterm.term, dict(zip(deffunterm.args, expr.args)))
                return to_core_logic_form(expanded, context, expand_all)
            else:
                return Compound(to_core_logic_form(expr.fun, context, expand_all), [to_core_logic_form(arg, context, expand_all) for arg in expr.args])
        else:
            raise Exception(f"Unexpected expr (Compound): {pretty_expr(expr)}")
    elif isinstance(expr, (Fun, Con, Var)):
        return expr
    elif isinstance(expr, Not):
        return Not(to_core_logic_form(expr.body, context, expand_all))
    elif isinstance(expr, (And, Or)):
        return type(expr)(to_core_logic_form(expr.left, context, expand_all), to_core_logic_form(expr.right, context, expand_all))
    elif isinstance(expr, Implies):
        return to_core_logic_form(Or(Not(expr.left), expr.right), context, expand_all)
    elif isinstance(expr, Iff):
        return to_core_logic_form(And(Implies(expr.left, expr.right), Implies(expr.right, expr.left)), context, expand_all)
    elif isinstance(expr, (Exists, Forall)):
        return type(expr)(expr.var, to_core_logic_form(expr.body, context, expand_all))
    elif isinstance(expr, ExistsUniq):
        used_vars = {expr.var} | collect_vars(expr.body)[0] | collect_vars(expr.body)[1]
        vardash = fresh_var(Var(expr.var.name + "'"), used_vars)
        body_subst = substitute(expr.body, {expr.var: vardash})
        expanded = Exists(expr.var, And(expr.body, Forall(vardash, Implies(body_subst, Symbol(context.equality.equal.name, [vardash, expr.var])))))
        return to_core_logic_form(expanded, context, expand_all)
    else:
        raise Exception(f"Unexpected expr: {pretty_expr(expr)}")

def fresh_var(var: Var, used: set[Var]) -> Var:
    if var in used:
        i = 0
        new_name = f"{var.name}_{i}"
        while any(new_name == u.name for u in used):
            i += 1
            new_name = f"{var.name}_{i}"
        return Var(new_name)
    else:
        return var

def substitute(expr, mapping: dict[Term, Term], used_vars: set[Var] | None = None):
    if used_vars is None:
        used_vars = collect_vars(expr)[0] | collect_vars(expr)[1] | {v for v in mapping.values() if isinstance(v, Var)}

    for k, v in mapping.items():
        if expr == k:
            return deepcopy(v)

    if isinstance(expr, Symbol):
        new_args = [substitute(arg, mapping, used_vars) for arg in expr.args]
        return Symbol(substitute(expr.pred, mapping, used_vars), new_args)

    if isinstance(expr, Compound):
        new_args = tuple(substitute(arg, mapping, used_vars) for arg in expr.args)
        return Compound(substitute(expr.fun, mapping, used_vars), new_args)

    if isinstance(expr, (Pred, Fun, Con, Var)):
        return expr

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
            body = substitute(alpha_rename(expr.body, {var: new_var}), mapping, used_vars)
            return type(expr)(new_var, body)
        else:
            used_vars.add(var)
            return type(expr)(var, substitute(expr.body, mapping, used_vars))

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

def strip_quantifiers(expr) -> tuple[list[Forall | Exists], object]:
    qs = []
    body = expr
    while isinstance(body, (Exists, Forall)):
        qs.append(type(body)(body.var, None))
        body = body.body
    return qs, body

def make_quantifiers(qs: list[Forall | Exists], body):
    expr = body
    for q in reversed(qs):
        expr = type(q)(q.var, expr)
    return expr

def alpha_rename(expr, rename_map: dict[Var, Var]):
    if isinstance(expr, Symbol):
        new_args = [alpha_rename(a, rename_map) for a in expr.args]
        return Symbol(alpha_rename(expr.pred, rename_map), new_args)
    elif isinstance(expr, Pred):
        return expr
    elif isinstance(expr, Compound):
        new_args = [alpha_rename(a, rename_map) for a in expr.args]
        return Compound(alpha_rename(expr.fun, rename_map), new_args)
    elif isinstance(expr, Fun):
        return expr
    elif isinstance(expr, Con):
        return expr
    elif isinstance(expr, Var):
        return rename_map.get(expr, expr)
    elif isinstance(expr, Not):
        return Not(alpha_rename(expr.body, rename_map))
    elif isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(alpha_rename(expr.left, rename_map), alpha_rename(expr.right, rename_map))
    elif isinstance(expr, (Exists, Forall)):
        var = rename_map.get(expr.var, expr.var)
        return type(expr)(var, alpha_rename(expr.body, rename_map))
    else:
        return expr

def rename_bound(expr, bound_vars: set[Var], used: set[Var]):
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

def to_canonical_form(expr, context: Context, expand_all: bool = False):
    expr_norm = to_core_logic_form(expr, context, expand_all)
    expr_norm = to_nnf(expr_norm)
    expr_norm = to_pnf(expr_norm)
    expr_norm = to_cnf(expr_norm)
    expr_norm = simplify(expr_norm)
    return expr_norm

def logic_equiv(expr1, expr2, context: Context, expand_all: bool = False) -> bool:
    if isinstance(expr1, Bottom) and isinstance(expr2, Bottom):
        return True
    elif isinstance(expr1, Bottom) and not isinstance(expr2, Bottom):
        return False
    elif not isinstance(expr1, Bottom) and isinstance(expr2, Bottom):
        return False
    else:
        expr1_norm = to_canonical_form(expr1, context, expand_all)
        expr2_norm = to_canonical_form(expr2, context, expand_all)
        return alpha_equiv(expr1_norm, expr2_norm)

def make_tree(expr, prefix: str = "", is_root: bool = True, is_last: bool = True) -> str:
    print_prefix = prefix + ("" if is_root else ("└─" if is_last else "├─"))
    child_pref = prefix + ("   " if is_last or is_root else "│  ")
    if isinstance(expr, Symbol):
        args_str = ", ".join(make_tree(arg, "", True) for arg in expr.args)
        return f"{print_prefix}Symbol({expr.name}, [{args_str}])"
    elif isinstance(expr, Compound):
        args_str = ", ".join(make_tree(arg, "", True) for arg in expr.args)
        return f"{print_prefix}Compound({make_tree(expr.fun, "", True)}, [{args_str}])"
    elif isinstance(expr, Fun):
        return f"{print_prefix}{expr.name}"
    elif isinstance(expr, Con):
        return f"{print_prefix}{expr.name}"
    elif isinstance(expr, Var):
        return f"{print_prefix}{expr.name}"
    elif isinstance(expr, Not):
        body_str = make_tree(expr.body, child_pref, False, True)
        return f"{print_prefix}Not\n{body_str}"
    elif isinstance(expr, (And, Or, Implies, Iff)):
        left_str = make_tree(expr.left, child_pref, False, False)
        right_str = make_tree(expr.right, child_pref, False, True)
        return f"{print_prefix}{type(expr).__name__}\n{left_str}\n{right_str}"
    elif isinstance(expr, (Exists, Forall, ExistsUniq)):
        body_str = make_tree(expr.body, child_pref, False, True)
        return f"{print_prefix}{type(expr).__name__}({expr.var.name})\n{body_str}"
    elif isinstance(expr, (BoolTrue, BoolFalse)):
        return type(expr).__name__
    else:
        raise Exception(f"Unexpected expr: {expr}")

if __name__ == "__main__":
    x = Var("x")
    y = Var("y")
    z = Var("z")
    w = Var("w")
    pair = Fun("pair")
    predin = Pred("in")
    e1 = Exists(w, And(Symbol(predin, [z, w]), Symbol(predin, [w, Compound(pair, [x, y])])))
    e2 = Exists(x, And(Symbol(predin, [z, x]), Symbol(predin, [x, Compound(pair, [x, y])])))
    print(f"e1: {pretty_expr(e1)}")
    print(f"e2: {pretty_expr(e2)}")
    print(f"alpha_equiv(e1, e2, Context.init()): {alpha_equiv(e1, e2, Context.init())}")
    print(f"alpha_equiv(e2, e1, Context.init()): {alpha_equiv(e2, e1, Context.init())}")
