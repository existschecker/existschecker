from ast_types import Or, Not, Forall, Exists, ExistsUniq, Implies, Iff, And, Symbol, Context, Compound, Fun, Con, Var, Bottom, Term, Pred, Formula, Template, Lambda, TemplateCall
from itertools import permutations
from copy import deepcopy
from typing import Mapping, TypeVar

def flatten_op(expr: Formula, op: type[And] | type[Or]) -> list[Formula]:
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

def alpha_equiv(e1: Formula | Term | Pred | Fun, e2: Formula | Term | Pred | Fun, context: Context, env: dict[Var | Template, Var | Template] | None = None) -> bool:
    if env is None:
        env = {}

    if isinstance(e1, Var) and isinstance(e2, Var):
        return env.get(e1, e1) == e2

    if isinstance(e1, Template) and isinstance(e2, Template):
        return env.get(e1, e1) == e2

    if isinstance(e1, Con) and isinstance(e2, Con):
        return e1.name == e2.name

    if isinstance(e1, Fun) and isinstance(e2, Fun):
        return e1.name == e2.name

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

    if isinstance(e1, Symbol) and isinstance(e2, Symbol):
        if not alpha_equiv(e1.pred, e2.pred, context, env):
            return False
        if len(e1.args) != len(e2.args):
            return False
        if context.decl.equality is not None and e1.pred.name == context.decl.equality.equal.name:
            a1, b1 = e1.args
            a2, b2 = e2.args
            return (alpha_equiv(a1, a2, context, env) and alpha_equiv(b1, b2, context, env)) or (alpha_equiv(a1, b2, context, env) and alpha_equiv(b1, a2, context, env))
        for a, b in zip(e1.args, e2.args):
            if not alpha_equiv(a, b, context, env):
                return False
        return True

    if isinstance(e1, TemplateCall) and isinstance(e2, TemplateCall):
        if not alpha_equiv(e1.template, e2.template, context, env):
            return False
        for a, b in zip(e1.args, e2.args):
            if not alpha_equiv(a, b, context, env):
                return False
        return True

    if isinstance(e1, Not) and isinstance(e2, Not):
        return alpha_equiv(e1.body, e2.body, context, env)

    if isinstance(e1, And) and isinstance(e2, And):
        return op_equiv(e1, e2, context, env, And)

    if isinstance(e1, Or) and isinstance(e2, Or):
        return op_equiv(e1, e2, context, env, Or)

    if isinstance(e1, Implies) and isinstance(e2, Implies):
        return alpha_equiv(e1.left, e2.left, context, env) and alpha_equiv(e1.right, e2.right, context, env)

    if isinstance(e1, Iff) and isinstance(e2, Iff):
        return alpha_equiv(e1.left, e2.left, context, env) and alpha_equiv(e1.right, e2.right, context, env)

    if isinstance(e1, Lambda) and isinstance(e2, Lambda):
        if len(e1.args) != len(e2.args):
            return False
        newenv = env.copy()
        for a, b in zip(e1.args, e2.args):
            newenv[a] = b
        return alpha_equiv(e1.body, e2.body, context, newenv)

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
        free: set[Var | Template] = set()
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
    return any(alpha_equiv_with_defs(expr, f, context) for f in context.ctrl.formulas)

def alpha_equiv_with_defs(e1: Bottom | Formula, e2: Bottom | Formula, context: Context, defs: list[str] | None = None) -> bool:
    if defs is None:
        defs = []
    if isinstance(e1, Bottom) or isinstance(e2, Bottom):
        return isinstance(e1, Bottom) and isinstance(e2, Bottom)
    else:
        e1_exp = normalize_neg(expand_defs_formula(e1, context, defs))
        e2_exp = normalize_neg(expand_defs_formula(e2, context, defs))
        return alpha_equiv(e1_exp, e2_exp, context)

def expand_defs_term(expr: Term, context: Context, defs: list[str], bound_templates: list[Template] | None = None) -> Term:
    if bound_templates is None:
        bound_templates = []
    if isinstance(expr, (Var, Con, Template)):
        return expr
    elif isinstance(expr, Compound):
        if expr.fun.name in context.decl.deffuns:
            return Compound(expr.fun, tuple(expand_defs_term(arg, context, defs, bound_templates) for arg in expr.args))
        elif expr.fun.name in context.decl.deffunterms:
            deffunterm = context.decl.deffunterms[expr.fun.name]
            if expr.fun.name in defs:
                expanded = substitute_term(deffunterm.term, dict(zip(deffunterm.args, expr.args)))
                return expand_defs_term(expanded, context, defs, bound_templates)
            else:
                return Compound(expr.fun, tuple(expand_defs_term(arg, context, defs, bound_templates) for arg in expr.args))
        else:
            raise Exception(f"Unexpected function name: {expr.fun.name}")
    elif isinstance(expr, Lambda):
        return Lambda(expr.args, expand_defs_formula(expr.body, context, defs, bound_templates))
    else:
        raise Exception(f"Unexpected type: {type(expr)}")

def expand_defs_formula(expr: Formula, context: Context, defs: list[str], bound_templates: list[Template] | None = None) -> Formula:
    if bound_templates is None:
        bound_templates = []
    if isinstance(expr, Symbol):
        if expr.pred.name in context.decl.primpreds:
            return Symbol(expr.pred, tuple(expand_defs_term(arg, context, defs, bound_templates) for arg in expr.args))
        if expr.pred.name in context.decl.defpreds:
            defpred = context.decl.defpreds[expr.pred.name]
            if defpred.autoexpand or expr.pred.name in defs:
                expanded = substitute_formula(defpred.formula, dict(zip(defpred.args, expr.args)))
                return expand_defs_formula(expanded, context, defs, bound_templates)
            else:
                return Symbol(expr.pred, tuple(expand_defs_term(arg, context, defs, bound_templates) for arg in expr.args))
        else:
            raise Exception(f"Unexpected predicate name: {expr.pred.name}")
    elif isinstance(expr, TemplateCall):
        if expr.template in context.ctrl.templates or expr.template in bound_templates:
            return TemplateCall(expr.template, tuple(expand_defs_term(arg, context, defs, bound_templates) for arg in expr.args))
        else:
            raise Exception(f"{expr.template} in {context.ctrl.templates} or {expr.template} in {bound_templates}")
    elif isinstance(expr, Not):
        return Not(expand_defs_formula(expr.body, context, defs, bound_templates))
    elif isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(expand_defs_formula(expr.left, context, defs, bound_templates), expand_defs_formula(expr.right, context, defs, bound_templates))
    elif isinstance(expr, (Exists, Forall, ExistsUniq)):
        if isinstance(expr.var, Template):
            bound_templates.append(expr.var)
        return type(expr)(expr.var, expand_defs_formula(expr.body, context, defs, bound_templates))
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

T_Key = TypeVar("T_Key", bound=Term)

def substitute_term(expr: Term, mapping: Mapping[T_Key, Term], used_vars: set[Var | Template] | None = None) -> Term:
    if used_vars is None:
        used_vars = collect_vars(expr)[0]
        for v in mapping.values():
            used_vars.update(collect_vars(v)[0])

    for k, v in mapping.items():
        if expr == k:
            return deepcopy(v)

    if isinstance(expr, (Var, Con, Template)):
        return expr

    elif isinstance(expr, Compound):
        return Compound(expr.fun, tuple(substitute_term(arg, mapping, used_vars) for arg in expr.args))

    elif isinstance(expr, Lambda):
        return Lambda(expr.args, substitute_formula(expr.body, mapping, used_vars))

    else:
        raise Exception(f"Unexpected type: {type(expr)}")

def substitute_formula(expr: Formula, mapping: Mapping[T_Key, Term], used_vars: set[Var | Template] | None = None) -> Formula:
    if used_vars is None:
        used_vars = collect_vars(expr)[0]
        for v in mapping.values():
            used_vars.update(collect_vars(v)[0])

    if isinstance(expr, Symbol):
        return Symbol(expr.pred, tuple(substitute_term(arg, mapping, used_vars) for arg in expr.args))

    elif isinstance(expr, Not):
        return Not(substitute_formula(expr.body, mapping, used_vars))

    elif isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(substitute_formula(expr.left, mapping, used_vars), substitute_formula(expr.right, mapping, used_vars))

    elif isinstance(expr, (Forall, Exists)):
        var = expr.var
        # 衝突する場合は束縛変数をリネーム
        if var in mapping.values() or var in used_vars:
            new_var = fresh_var(var, used_vars)
            used_vars.add(new_var)
            body = substitute_formula(alpha_rename_formula(expr.body, {var: new_var}), mapping, used_vars)
            return type(expr)(new_var, body)
        else:
            used_vars.add(var)
            return type(expr)(var, substitute_formula(expr.body, mapping, used_vars))

    elif isinstance(expr, TemplateCall):
        new_template = substitute_term(expr.template, mapping, used_vars)
        if isinstance(new_template, Template):
            return TemplateCall(new_template, tuple(substitute_term(arg, mapping, used_vars) for arg in expr.args))
        elif isinstance(new_template, Lambda):
            lambda_mapping: dict[Var, Term] = {}
            for a, b in zip(new_template.args, expr.args):
                lambda_mapping[a] = b
            lambda_mapped = substitute_formula(new_template.body, lambda_mapping)
            return substitute_formula(lambda_mapped, mapping, used_vars)
        else:
            raise Exception(f"Unexpected type: {type(new_template)}")

    else:
        raise Exception(f"Unexpected type: {type(expr)}")

def alpha_rename_var(expr: Var | Template, rename_map: dict[Var | Template, Var | Template]) -> Var | Template:
    return rename_map.get(expr, expr)    

def alpha_rename_term(expr: Term, rename_map: dict[Var | Template, Var | Template]) -> Term:
    if isinstance(expr, (Var, Template)):
        return alpha_rename_var(expr, rename_map)
    elif isinstance(expr, Con):
        return expr
    elif isinstance(expr, Compound):
        return Compound(expr.fun, tuple(alpha_rename_term(a, rename_map) for a in expr.args))
    else:
        raise Exception(f"Unexpected type: {type(expr)}")

def alpha_rename_formula(expr: Formula, rename_map: dict[Var | Template, Var | Template]) -> Formula:
    if isinstance(expr, Symbol):
        return Symbol(expr.pred, tuple(alpha_rename_term(a, rename_map) for a in expr.args))
    elif isinstance(expr, Not):
        return Not(alpha_rename_formula(expr.body, rename_map))
    elif isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(alpha_rename_formula(expr.left, rename_map), alpha_rename_formula(expr.right, rename_map))
    elif isinstance(expr, (Exists, Forall)):
        return type(expr)(alpha_rename_var(expr.var, rename_map), alpha_rename_formula(expr.body, rename_map))
    else:
        raise Exception(f"Unexpected type: {type(expr)}")
