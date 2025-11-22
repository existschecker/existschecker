from ast_types import Or, Not, Forall, Exists, ExistsUniq, Implies, Iff, And, Symbol, Context, Compound, Fun, Con, Var, Bottom, Term, Pred, Formula, Template, Lambda, TemplateCall
from itertools import permutations
from copy import deepcopy

def flatten_op(expr: Formula, op: type[And] | type[Or]) -> list:
    if isinstance(expr, op):
        return flatten_op(expr.left, op) + flatten_op(expr.right, op)
    else:
        return [expr]

def op_equiv(e1: Formula, e2: Formula, context: Context, env: dict[Var | Template, Var | Template], op: type[And] | type[Or]) -> bool:
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

def alpha_equiv(e1: Formula, e2: Formula, context: Context, env: dict[Var | Template, Var | Template] | None = None) -> bool:
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
                skip_perm = False
                for v1, v2 in zip(vars1, perm):
                    if isinstance(v1, Var) and isinstance(v2, Template):
                        skip_perm = True
                        break
                    if isinstance(v1, Template) and isinstance(v2, Var):
                        skip_perm = True
                        break
                    if isinstance(v1, Template) and isinstance(v2, Template):
                        if v1.arity != v2.arity:
                            skip_perm = True
                            break
                    newenv[v1] = v2
                if skip_perm:
                    continue
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

    if isinstance(e1, Template) and isinstance(e2, Template):
        return env.get(e1, e1) == e2

    if isinstance(e1, TemplateCall) and isinstance(e2, TemplateCall):
        if env.get(e1.template, e1.template) != e2.template:
            return False
        for a, b in zip(e1.args, e2.args):
            if not alpha_equiv(a, b, context, env):
                return False
        return True

    if isinstance(e1, Lambda) and isinstance(e2, Lambda):
        if len(e1.args) != len(e2.args):
            return False
        newenv = env.copy()
        for a, b in zip(e1.args, e2.args):
            newenv[a] = b
        return alpha_equiv(e1.body, e2.body, context, newenv)

    return False

def collect_quantifier_vars(e: Formula, quantifier_type: type[Forall] | type[Exists] | type[ExistsUniq]) -> tuple[list[Var | Template], Formula]:
    vars_: list[Var | Template] = []
    body = e
    while isinstance(body, quantifier_type):
        vars_.append(body.var)
        body = body.body
    return vars_, body

def collect_vars(expr: Formula | Term, bound: set[Var | Template] | None = None) -> tuple[set[Var | Template], set[Var | Template]]:
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

    elif isinstance(expr, (Var, Template)):
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

    elif isinstance(expr, TemplateCall):
        free = set()
        for var in expr.args:
            f, _ = collect_vars(var, bound)
            free.update(f)
        if expr.template in bound:
            return free, set()
        else:
            return free | {expr.template}, set()

    elif isinstance(expr, Lambda):
        f_body, b_body= collect_vars(expr.body, bound | set(expr.args))
        return f_body, b_body | set(expr.args)

    else:
        raise Exception(f"Unexpected type {type(expr)}")

# === コンテキスト中の式検索 ===
def expr_in_context(expr: Bottom | Formula, context: Context) -> bool:
    return any(alpha_equiv_with_defs(expr, f, context) for f in context.formulas)

def alpha_equiv_with_defs(e1: Bottom | Formula, e2: Bottom | Formula, context: Context, expand_all: bool = False) -> bool:
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

def expand_basic_defs(expr: Formula, context: Context, expand_all: bool, bound_templates: list[Template] | None = None) -> Formula:
    if bound_templates is None:
        bound_templates = []
    if isinstance(expr, Symbol):
        if expr.pred.name in context.primpreds:
            return Symbol(expand_basic_defs(expr.pred, context, expand_all, bound_templates), [expand_basic_defs(arg, context, expand_all, bound_templates) for arg in expr.args])
        if expr.pred.name in context.defpreds:
            defpred = context.defpreds[expr.pred.name]
            if defpred.autoexpand or expand_all:
                expanded = substitute(defpred.formula, dict(zip(defpred.args, expr.args)))
                return expand_basic_defs(expanded, context, expand_all, bound_templates)
            else:
                return Symbol(expand_basic_defs(expr.pred, context, expand_all, bound_templates), [expand_basic_defs(arg, context, expand_all, bound_templates) for arg in expr.args])
        else:
            raise Exception(f"Unexpected predicate name: {expr.pred.name}")
    elif isinstance(expr, Compound):
        if expr.fun.name in context.deffuns:
            return Compound(expand_basic_defs(expr.fun, context, expand_all, bound_templates), [expand_basic_defs(arg, context, expand_all, bound_templates) for arg in expr.args])
        elif expr.fun.name in context.deffunterms:
            deffunterm = context.deffunterms[expr.fun.name]
            if expand_all:
                expanded = substitute(deffunterm.term, dict(zip(deffunterm.args, expr.args)))
                return expand_basic_defs(expanded, context, expand_all, bound_templates)
            else:
                return Compound(expand_basic_defs(expr.fun, context, expand_all, bound_templates), [expand_basic_defs(arg, context, expand_all, bound_templates) for arg in expr.args])
        else:
            raise Exception(f"Unexpected function name: {expr.fun.name}")
    elif isinstance(expr, (Pred, Fun, Con, Var, Template)):
        return expr
    elif isinstance(expr, Not):
        return Not(expand_basic_defs(expr.body, context, expand_all, bound_templates))
    elif isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(expand_basic_defs(expr.left, context, expand_all, bound_templates), expand_basic_defs(expr.right, context, expand_all, bound_templates))
    elif isinstance(expr, (Exists, Forall, ExistsUniq)):
        if isinstance(expr, Forall) and isinstance(expr.var, Template):
            bound_templates.append(expr.var)
        return type(expr)(expr.var, expand_basic_defs(expr.body, context, expand_all, bound_templates))
    elif isinstance(expr, TemplateCall):
        if expr.template in context.templates or expr.template in bound_templates:
            return expr
        else:
            raise Exception(f"{expr.template} in {context.templates} or {expr.template} in {bound_templates}")
    elif isinstance(expr, Lambda):
        return Lambda(expr.args, expand_basic_defs(expr.body, context, expand_all, bound_templates))
    else:
        raise Exception(f"Unexpected type: {type(expr)}")

def normalize_neg(expr: Formula) -> Formula:
    if isinstance(expr, (Symbol, TemplateCall)):
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
        raise Exception(f"Unexpected type: {type(expr)}")

def fresh_var(var: Var | Template, used: set[Var | Template]) -> Var | Template:
    if var in used:
        i = 0
        new_name = f"{var.name}_{i}"
        while any(new_name == u.name for u in used):
            i += 1
            new_name = f"{var.name}_{i}"
        if isinstance(var, Var):
            return Var(new_name)
        elif isinstance(var, Template):
            return Template(new_name, var.arity)
        else:
            raise Exception(f"Unexpected type {type(var)}")
    else:
        return var

def substitute(expr: Formula, mapping: dict[Term, Term], used_vars: set[Var] | None = None) -> Formula:
    if used_vars is None:
        used_vars = collect_vars(expr)[0]
        for v in mapping.values():
            used_vars.update(collect_vars(v)[0])

    for k, v in mapping.items():
        if expr == k:
            return deepcopy(v)

    if isinstance(expr, Symbol):
        new_args = [substitute(arg, mapping, used_vars) for arg in expr.args]
        return Symbol(substitute(expr.pred, mapping, used_vars), new_args)

    if isinstance(expr, Compound):
        new_args = tuple(substitute(arg, mapping, used_vars) for arg in expr.args)
        return Compound(substitute(expr.fun, mapping, used_vars), new_args)

    if isinstance(expr, (Pred, Fun, Con, Var, Template)):
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

    if isinstance(expr, TemplateCall):
        new_template = substitute(expr.template, mapping, used_vars)
        if isinstance(new_template, Template):
            new_args = tuple(substitute(arg, mapping, used_vars) for arg in expr.args)
            return TemplateCall(substitute(expr.template, mapping, used_vars), new_args)
        elif isinstance(new_template, Lambda):
            lambda_mapping = {}
            for a, b in zip(new_template.args, expr.args):
                lambda_mapping[a] = b
            lambda_mapped = substitute(new_template.body, lambda_mapping)
            return substitute(lambda_mapped, mapping, used_vars)
        else:
            raise Exception(f"Unexpected type: {type(new_template)}")

    if isinstance(expr, Lambda):
        return Lambda(expr.args, substitute(expr.body, mapping, used_vars))

    return expr

def alpha_rename(expr: Formula, rename_map: dict[Var, Var]) -> Formula:
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
