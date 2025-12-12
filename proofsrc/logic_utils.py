from ast_types import Or, Not, Forall, Exists, ExistsUniq, Implies, Iff, And, Symbol, Context, Compound, Fun, Con, Var, Bottom, Term, Pred, Formula, Template, Lambda, TemplateCall
from itertools import permutations
from copy import deepcopy
from typing import Mapping
from dataclasses import dataclass, field

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
        exp = DefExpander(context, defs)
        e1_exp = normalize_neg(exp.expand_defs_formula(e1))
        exp = DefExpander(context, defs)
        e2_exp = normalize_neg(exp.expand_defs_formula(e2))
        return alpha_equiv(e1_exp, e2_exp, context)

@dataclass
class DefExpander:
    context: Context
    defs: list[str]
    indexes: dict[str, list[int]] = field(default_factory=dict[str, list[int]])
    counter: dict[str, int] = field(init=False, default_factory=dict[str, int])

    def expand_defs_term(self, expr: Term, bound_templates: list[Template] | None = None) -> Term:
        if bound_templates is None:
            bound_templates = []
        if isinstance(expr, (Var, Con, Template)):
            return expr
        elif isinstance(expr, Compound):
            if expr.fun.name in self.context.decl.deffuns:
                return Compound(expr.fun, tuple(self.expand_defs_term(arg, bound_templates) for arg in expr.args))
            elif expr.fun.name in self.context.decl.deffunterms:
                deffunterm = self.context.decl.deffunterms[expr.fun.name]
                should_expand = False
                if expr.fun.name in self.defs:
                    target_indexes = self.indexes.get(expr.fun.name, [])
                    self.counter[expr.fun.name] = self.counter.get(expr.fun.name, 0) + 1
                    if not target_indexes:
                        should_expand = True
                    elif self.counter[expr.fun.name] in target_indexes:
                        should_expand = True
                if should_expand:
                    subst = Substitutor(dict(zip(deffunterm.args, expr.args)))
                    expanded = subst.substitute_term(deffunterm.term)
                    return self.expand_defs_term(expanded, bound_templates)
                else:
                    return Compound(expr.fun, tuple(self.expand_defs_term(arg, bound_templates) for arg in expr.args))
            else:
                raise Exception(f"Unexpected function name: {expr.fun.name}")
        elif isinstance(expr, Lambda):
            return Lambda(expr.args, self.expand_defs_formula(expr.body, bound_templates))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def expand_defs_formula(self, expr: Formula, bound_templates: list[Template] | None = None) -> Formula:
        if bound_templates is None:
            bound_templates = []
        if isinstance(expr, Symbol):
            if expr.pred.name in self.context.decl.primpreds:
                return Symbol(expr.pred, tuple(self.expand_defs_term(arg, bound_templates) for arg in expr.args))
            elif expr.pred.name in self.context.decl.defpreds:
                defpred = self.context.decl.defpreds[expr.pred.name]
                should_expand = False
                if len(self.defs) == 0 and defpred.autoexpand:
                    should_expand = True
                elif expr.pred.name in self.defs:
                    target_indexes = self.indexes.get(expr.pred.name, [])
                    self.counter[expr.pred.name] = self.counter.get(expr.pred.name, 0) + 1
                    if not target_indexes:
                        should_expand = True
                    elif self.counter[expr.pred.name] in target_indexes:
                        should_expand = True
                if should_expand:
                    subst = Substitutor(dict(zip(defpred.args, expr.args)))
                    expanded = subst.substitute_formula(defpred.formula)
                    return self.expand_defs_formula(expanded, bound_templates)
                else:
                    return Symbol(expr.pred, tuple(self.expand_defs_term(arg, bound_templates) for arg in expr.args))
            else:
                raise Exception(f"Unexpected predicate name: {expr.pred.name}")
        elif isinstance(expr, TemplateCall):
            if expr.template in self.context.ctrl.templates or expr.template in bound_templates:
                return TemplateCall(expr.template, tuple(self.expand_defs_term(arg, bound_templates) for arg in expr.args))
            else:
                raise Exception(f"{expr.template} in {self.context.ctrl.templates} or {expr.template} in {bound_templates}")
        elif isinstance(expr, Not):
            return Not(self.expand_defs_formula(expr.body, bound_templates))
        elif isinstance(expr, (And, Or, Implies, Iff)):
            return type(expr)(self.expand_defs_formula(expr.left, bound_templates), self.expand_defs_formula(expr.right, bound_templates))
        elif isinstance(expr, (Exists, Forall, ExistsUniq)):
            if isinstance(expr.var, Template):
                new_bound_templates = list(bound_templates) 
                new_bound_templates.append(expr.var)
            else:
                new_bound_templates = bound_templates
            return type(expr)(expr.var, self.expand_defs_formula(expr.body, new_bound_templates))
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

@dataclass
class Substitutor:
    mapping: Mapping[Term, Term]
    indexes: Mapping[Term, list[int]] = field(default_factory=dict[Term, list[int]])
    counter: dict[Term, int] = field(init=False, default_factory=dict[Term, int])
    used_vars: set[Var | Template] | None = field(init=False, default=None)

    def substitute_term(self, expr: Term) -> Term:
        if self.used_vars is None:
            self.used_vars = collect_vars(expr)[0]
            for v in self.mapping.values():
                self.used_vars.update(collect_vars(v)[0])

        for k, v in self.mapping.items():
            if expr == k:
                target_indices_set = self.indexes.get(k, [])
                if not target_indices_set:
                    self.counter[k] = self.counter.get(k, 0) + 1
                    return deepcopy(v)
                else:
                    self.counter[k] = self.counter.get(k, 0) + 1
                    current_index = self.counter[k]
                    if current_index in target_indices_set:
                        return deepcopy(v)
                    else:
                        return expr

        if isinstance(expr, (Var, Con, Template)):
            return expr

        elif isinstance(expr, Compound):
            return Compound(expr.fun, tuple(self.substitute_term(arg) for arg in expr.args))

        elif isinstance(expr, Lambda):
            return Lambda(expr.args, self.substitute_formula(expr.body))

        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def substitute_formula(self, expr: Formula) -> Formula:
        if self.used_vars is None:
            self.used_vars = collect_vars(expr)[0]
            for v in self.mapping.values():
                self.used_vars.update(collect_vars(v)[0])

        if isinstance(expr, Symbol):
            return Symbol(expr.pred, tuple(self.substitute_term(arg) for arg in expr.args))

        elif isinstance(expr, Not):
            return Not(self.substitute_formula(expr.body))

        elif isinstance(expr, (And, Or, Implies, Iff)):
            return type(expr)(self.substitute_formula(expr.left), self.substitute_formula(expr.right))

        elif isinstance(expr, (Forall, Exists)):
            var = expr.var
            # 衝突する場合は束縛変数をリネーム
            if var in self.mapping.values() or var in self.used_vars:
                new_var = fresh_var(var, self.used_vars)
                self.used_vars.add(new_var)
                body = self.substitute_formula(alpha_rename_formula(expr.body, {var: new_var}))
                return type(expr)(new_var, body)
            else:
                self.used_vars.add(var)
                return type(expr)(var, self.substitute_formula(expr.body))

        elif isinstance(expr, TemplateCall):
            new_template = self.substitute_term(expr.template)
            if isinstance(new_template, Template):
                return TemplateCall(new_template, tuple(self.substitute_term(arg) for arg in expr.args))
            elif isinstance(new_template, Lambda):
                lambda_mapping: dict[Var, Term] = {}
                for a, b in zip(new_template.args, expr.args):
                    lambda_mapping[a] = b
                subst = Substitutor(lambda_mapping)
                lambda_mapped = subst.substitute_formula(new_template.body)
                return self.substitute_formula(lambda_mapped)
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
    elif isinstance(expr, TemplateCall):
        return TemplateCall(alpha_rename_var(expr.template, rename_map), tuple(alpha_rename_term(a, rename_map) for a in expr.args))
    else:
        raise Exception(f"Unexpected type: {type(expr)}")

TERM_PRECEDENCE = {
    "Lowest": 0,
    "CompoundInfix": 1,
    "CompoundFunction": 2
}

FORMULA_PRECEDENCE = {
    "Lowest": 0,
    "Iff": 1,
    "Implies": 1,
    "Or": 2,
    "And": 2,
    "Symbol": 3,
    "Not": 4,
    "Quantifier": 5,
}

def pretty_expr_fragments(expr: Pred | Fun, context: Context) -> list[str]:
    if isinstance(expr, Pred):
        if expr.name in context.decl.primpreds:
            tex = context.decl.primpreds[expr.name].tex
        elif expr.name in context.decl.defpreds:
            tex = context.decl.defpreds[expr.name].tex
        else:
            raise Exception(f"{expr.name} is not in primpreds or defpreds")
        return tex
    elif isinstance(expr, Fun):
        if expr.name in context.decl.deffuns:
            tex = context.decl.deffuns[expr.name].tex
        elif expr.name in context.decl.deffunterms:
            tex = context.decl.deffunterms[expr.name].tex
        else:
            raise Exception(f"{expr.name} is not in deffuns or deffunterms")
        return tex
    else:
        raise TypeError(f"Unsupported node type: {type(expr)}")

def pretty_term(expr: Term, context: Context, parent_prec: int = TERM_PRECEDENCE["Lowest"]) -> str:
    if isinstance(expr, Var):
        return expr.name
    elif isinstance(expr, Template):
        return f"{expr.name}[{str(expr.arity)}]"
    elif isinstance(expr, Con):
        if expr.name in context.decl.defcons:
            tex = context.decl.defcons[expr.name].tex
        else:
            raise Exception(f"{expr.name} is not in context.defcons")
        if len(tex) != 1:
            raise Exception("arity is different")
        return tex[0]
    elif isinstance(expr, Compound):
        tex = pretty_expr_fragments(expr.fun, context)
        if len(tex) != len(expr.args) + 1:
            raise Exception("arity is different")
        prec = TERM_PRECEDENCE["CompoundInfix"] if tex[0] == "" or tex[-1] == "" else TERM_PRECEDENCE["CompoundFunction"]
        text = ""
        for i in range(len(expr.args)):
            text += tex[i]
            text += " "
            text += pretty_term(expr.args[i], context, prec)
            text += " "
        text += tex[-1]
        return text if prec > parent_prec or parent_prec == TERM_PRECEDENCE["CompoundFunction"] else f"({text})"
    elif isinstance(expr, Lambda):
        return f"\\lambda {",".join([var.name for var in expr.args])}. {pretty_formula(expr.body, context)}"
    else:
        raise TypeError(f"Unsupported node type: {type(expr)}")

def pretty_formula(expr: Formula, context: Context, parent_prec: int = FORMULA_PRECEDENCE["Lowest"]) -> str:
    if isinstance(expr, Symbol):
        tex = pretty_expr_fragments(expr.pred, context)
        if len(tex) != len(expr.args) + 1:
            raise Exception("arity is different")
        text = ""
        for i in range(len(expr.args)):
            text += tex[i]
            text += " "
            text += pretty_term(expr.args[i], context)
            text += " "
        text += tex[-1]
        return text if FORMULA_PRECEDENCE["Symbol"] > parent_prec else f"({text})"
    elif isinstance(expr, TemplateCall):
        if expr.template.arity == 0:
            return expr.template.name
        else:
            return f"{expr.template.name}({",".join([pretty_term(arg, context) for arg in expr.args])})"
    elif isinstance(expr, Not):
        text = f"\\neg {pretty_formula(expr.body, context, FORMULA_PRECEDENCE["Not"])}"
        return text if FORMULA_PRECEDENCE["Not"] > parent_prec else f"({text})"
    elif isinstance(expr, And):
        parts = flatten_op(expr, And)
        text = " \\wedge ".join(pretty_formula(part, context, FORMULA_PRECEDENCE["And"]) for part in parts)
        return text if FORMULA_PRECEDENCE["And"] > parent_prec else f"({text})"
    elif isinstance(expr, Or):
        parts = flatten_op(expr, Or)
        text = " \\vee ".join(pretty_formula(part, context, FORMULA_PRECEDENCE["Or"]) for part in parts)
        return text if FORMULA_PRECEDENCE["Or"] > parent_prec else f"({text})"
    elif isinstance(expr, Implies):
        text = f"{pretty_formula(expr.left, context, FORMULA_PRECEDENCE["Implies"])} \\to {pretty_formula(expr.right, context, FORMULA_PRECEDENCE["Implies"])}"
        return text if FORMULA_PRECEDENCE["Implies"] > parent_prec else f"({text})"
    elif isinstance(expr, Iff):
        text = f"{pretty_formula(expr.left, context, FORMULA_PRECEDENCE["Iff"])} \\leftrightarrow {pretty_formula(expr.right, context, FORMULA_PRECEDENCE["Iff"])}"
        return text if FORMULA_PRECEDENCE["Iff"] > parent_prec else f"({text})"
    elif isinstance(expr, (Forall, Exists, ExistsUniq)):
        body = expr
        qvars_text = ""
        while True:
            if isinstance(body, Forall):
                qvars_text += "\\forall"
            elif isinstance(body, Exists):
                qvars_text += "\\exists"
            elif isinstance(body, ExistsUniq):
                qvars_text += "\\exists!"
            else:
                break
            if isinstance(body.var, Var):
                qvars_text += f" {pretty_term(body.var, context)}"
            elif isinstance(body.var, Template):
                qvars_text += f"^T {pretty_term(body.var, context)}"
            else:
                raise Exception(f"Unexpected type: {type(body.var)}")
            body = body.body
        text = f"{qvars_text} {pretty_formula(body, context, FORMULA_PRECEDENCE["Quantifier"])}"
        return text if FORMULA_PRECEDENCE["Quantifier"] > parent_prec else f"({text})"
    else:
        raise TypeError(f"Unsupported node type: {type(expr)}")

def pretty_expr(expr: str | Bottom | Formula | Term, context: Context) -> str:
    if isinstance(expr, str):
        return expr
    elif isinstance(expr, Bottom):
        return "\\bot"
    elif isinstance(expr, Formula):
        return pretty_formula(expr, context)
    elif isinstance(expr, Term):
        return pretty_term(expr, context)
    else:
        raise TypeError(f"Unsupported node type: {type(expr)}")
