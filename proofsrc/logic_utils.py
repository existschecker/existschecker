from ast_types import Or, Not, Forall, Exists, ExistsUniq, Implies, Iff, And, AtomicFormula, Context, Compound, Fun, Con, Var, Bottom, Term, Pred, Formula, PredTemplate, Lambda, MembershipLambda, VarTerm, PredTerm, CompoundPredTerm, FunTemplate, FunTerm
from itertools import permutations
from copy import deepcopy
from typing import Mapping
from dataclasses import dataclass, field
import re

def flatten_op(expr: Formula, op: type[And] | type[Or]) -> list[Formula]:
    if isinstance(expr, op):
        return flatten_op(expr.left, op) + flatten_op(expr.right, op)
    else:
        return [expr]

class AlphaEquiv:
    def __init__(self, context: Context):
        self.context = context

    def begin_log(self, depth: int, e1: Formula | Term, e2: Formula | Term, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate]):
        if False:
            print(f"{'  ' * depth}[{e1.__class__.__name__}] e1: {pretty_expr(e1, self.context)}")
            print(f"{'  ' * depth}[{e2.__class__.__name__}] e2: {pretty_expr(e2, self.context)}")
            print(f"{'  ' * depth}[env] {", ".join([pretty_expr(k, self.context) + ": " + pretty_expr(v, self.context) for k, v in env.items()])}")

    def end_log(self, depth: int, result: bool):
        if False:
            mark = "✅ True" if result else f"❌ False"
            print(f"{'  ' * depth}{mark}")

    def alpha_equiv_var(self, e1: Var | PredTemplate | FunTemplate, e2: Var | PredTemplate | FunTemplate, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        return env.get(e1, e1) == e2

    def alpha_equiv_con(self, e1: Con | Fun | Pred, e2: Con | Fun | Pred, depth: int) -> bool:
        return e1.name == e2.name

    def alpha_equiv_fun_term(self, e1: FunTerm, e2: FunTerm, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        if isinstance(e1, Fun) and isinstance(e2, Fun):
            return self.alpha_equiv_con(e1, e2, depth)
        elif isinstance(e1, FunTemplate) and isinstance(e2, FunTemplate):
            return self.alpha_equiv_var(e1, e2, env, depth)
        else:
            return False

    def alpha_equiv_compound(self, e1: Compound | CompoundPredTerm, e2: Compound | CompoundPredTerm, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        if type(e1) != type(e2):
            return False
        if not self.alpha_equiv_fun_term(e1.fun, e2.fun, env, depth+1):
            return False
        if len(e1.args) != len(e2.args):
            return False
        for a, b in zip(e1.args, e2.args):
            if not self.alpha_equiv_term(a, b, env, depth+1):
                return False
        return True

    def alpha_equiv_lambda(self, e1: Lambda, e2: Lambda, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        if len(e1.args) != len(e2.args):
            return False
        newenv = env.copy()
        for a, b in zip(e1.args, e2.args):
            newenv[a] = b
        return self.alpha_equiv_formula(e1.body, e2.body, newenv, depth+1)

    def alpha_equiv_membership_lambda(self, e1: MembershipLambda, e2: MembershipLambda, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        return self.alpha_equiv_term(e1.varterm, e2.varterm, env, depth+1)

    def alpha_equiv_term(self, e1: Term, e2: Term, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        self.begin_log(depth, e1, e2, env)
        if isinstance(e1, Var) and isinstance(e2, Var):
            result = self.alpha_equiv_var(e1, e2, env, depth)
        elif isinstance(e1, PredTemplate) and isinstance(e2, PredTemplate):
            result = self.alpha_equiv_var(e1, e2, env, depth)
        elif isinstance(e1, FunTemplate) and isinstance(e2, FunTemplate):
            result = self.alpha_equiv_var(e1, e2, env, depth)
        elif isinstance(e1, Con) and isinstance(e2, Con):
            result = self.alpha_equiv_con(e1, e2, depth)
        elif isinstance(e1, Fun) and isinstance(e2, Fun):
            result = self.alpha_equiv_con(e1, e2, depth)
        elif isinstance(e1, Pred) and isinstance(e2, Pred):
            result = self.alpha_equiv_con(e1, e2, depth)
        elif isinstance(e1, Compound) and isinstance(e2, Compound):
            result = self.alpha_equiv_compound(e1, e2, env, depth)
        elif isinstance(e1, Lambda) and isinstance(e2, Lambda):
            result = self.alpha_equiv_lambda(e1, e2, env, depth)
        elif isinstance(e1, MembershipLambda) and isinstance(e2, MembershipLambda):
            result = self.alpha_equiv_membership_lambda(e1, e2, env, depth)
        else:
            result = False
        self.end_log(depth, result)
        return result

    def alpha_equiv_pred_term(self, e1: PredTerm, e2: PredTerm, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        if isinstance(e1, Pred) and isinstance(e2, Pred):
            return self.alpha_equiv_con(e1, e2, depth)
        elif isinstance(e1, PredTemplate) and isinstance(e2, PredTemplate):
            return self.alpha_equiv_var(e1, e2, env, depth)
        elif isinstance(e1, CompoundPredTerm) and isinstance(e2, CompoundPredTerm):
            return self.alpha_equiv_compound(e1, e2, env, depth)
        else:
            return False

    def alpha_equiv_symbol(self, e1: AtomicFormula, e2: AtomicFormula, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        if not self.alpha_equiv_pred_term(e1.pred, e2.pred, env, depth+1):
            return False
        if len(e1.args) != len(e2.args):
            return False
        if self.context.decl.equality is not None and isinstance(e1.pred, Pred) and e1.pred.name == self.context.decl.equality.equal.name:
            a1, b1 = e1.args
            a2, b2 = e2.args
            return (self.alpha_equiv_term(a1, a2, env, depth+1) and self.alpha_equiv_term(b1, b2, env, depth+1)) or (self.alpha_equiv_term(a1, b2, env, depth+1) and self.alpha_equiv_term(b1, a2, env, depth+1))
        for a, b in zip(e1.args, e2.args):
            if not self.alpha_equiv_term(a, b, env, depth+1):
                return False
        return True

    def alpha_equiv_not(self, e1: Not, e2: Not, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        return self.alpha_equiv_formula(e1.body, e2.body, env, depth+1)

    def alpha_equiv_and(self, e1: Formula, e2: Formula, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], op: type[And] | type[Or], depth: int) -> bool:
        parts1 = flatten_op(e1, op)
        parts2 = flatten_op(e2, op)

        if len(parts1) != len(parts2):
            return False

        matched = [False] * len(parts2)
        for p1 in parts1:
            found = False
            for i, p2 in enumerate(parts2):
                if not matched[i] and self.alpha_equiv_formula(p1, p2, env, depth+1):
                    matched[i] = True
                    found = True
                    break
            if not found:
                return False

        return True

    def alpha_equiv_implies(self, e1: Implies | Iff, e2: Implies | Iff, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        return self.alpha_equiv_formula(e1.left, e2.left, env, depth+1) and self.alpha_equiv_formula(e1.right, e2.right, env, depth+1)

    def alpha_equiv_quantifier(self, e1: Forall | Exists | ExistsUniq, e2: Forall | Exists | ExistsUniq, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], quantifier_type: type[Forall] | type[Exists] | type[ExistsUniq], depth: int) -> bool:
        vars1, body1 = collect_quantifier_vars(e1, quantifier_type)
        vars2, body2 = collect_quantifier_vars(e2, quantifier_type)

        if len(vars1) != len(vars2):
            return False

        for perm in permutations(vars2):
            newenv = env.copy()
            skip_perm = False
            for v1, v2 in zip(vars1, perm):
                if type(v1) is not type(v2):
                    skip_perm = True
                    break
                if isinstance(v1, PredTemplate) and isinstance(v2, PredTemplate):
                    if v1.arity != v2.arity:
                        skip_perm = True
                        break
                if isinstance(v1, FunTemplate) and isinstance(v2, FunTemplate):
                    if v1.arity != v2.arity:
                        skip_perm = True
                        break
                newenv[v1] = v2
            if skip_perm:
                continue
            if self.alpha_equiv_formula(body1, body2, newenv, depth+1):
                return True
        return False

    def alpha_equiv_formula(self, e1: Formula, e2: Formula, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        self.begin_log(depth, e1, e2, env)
        if isinstance(e1, AtomicFormula) and isinstance(e2, AtomicFormula):
            result = self.alpha_equiv_symbol(e1, e2, env, depth)
        elif isinstance(e1, Not) and isinstance(e2, Not):
            result = self.alpha_equiv_not(e1, e2, env, depth)
        elif isinstance(e1, And) and isinstance(e2, And):
            result = self.alpha_equiv_and(e1, e2, env, And, depth)
        elif isinstance(e1, Or) and isinstance(e2, Or):
            result = self.alpha_equiv_and(e1, e2, env, Or, depth)
        elif isinstance(e1, Implies) and isinstance(e2, Implies):
            result = self.alpha_equiv_implies(e1, e2, env, depth)
        elif isinstance(e1, Iff) and isinstance(e2, Iff):
            result = self.alpha_equiv_implies(e1, e2, env, depth)
        elif isinstance(e1, Forall) and isinstance(e2, Forall):
            result = self.alpha_equiv_quantifier(e1, e2, env, Forall, depth)
        elif isinstance(e1, Exists) and isinstance(e2, Exists):
            result = self.alpha_equiv_quantifier(e1, e2, env, Exists, depth)
        elif isinstance(e1, ExistsUniq) and isinstance(e2, ExistsUniq):
            result = self.alpha_equiv_quantifier(e1, e2, env, ExistsUniq, depth)
        else:
            result = False
        self.end_log(depth, result)
        return result

    def alpha_equiv(self, e1: Formula, e2: Formula) -> bool:
        return self.alpha_equiv_formula(e1, e2, {}, 0)

def collect_quantifier_vars(e: Formula, quantifier_type: type[Forall] | type[Exists] | type[ExistsUniq]) -> tuple[list[Var | PredTemplate | FunTemplate], Formula]:
    vars_: list[Var | PredTemplate | FunTemplate] = []
    body = e
    while isinstance(body, quantifier_type):
        vars_.append(body.var)
        body = body.body
    return vars_, body

def make_quantifier_vars(e: Formula, quantifier_type: type[Forall] | type[Exists] | type[ExistsUniq], vars_: list[Var | PredTemplate | FunTemplate]) -> Formula:
    body = e
    for var in reversed(vars_):
        body = quantifier_type(var, body)
    return body

def collect_vars(expr: Formula | Term, used_bv: set[Var] | None = None, used_bt: set[PredTemplate] | None = None) -> tuple[set[Var], set[Var], set[PredTemplate], set[PredTemplate]]:
    if used_bv is None:
        used_bv = set()
    if used_bt is None:
        used_bt = set()

    if isinstance(expr, Var):
        if expr in used_bv:
            return set(), set(), set(), set()
        else:
            return {expr}, set(), set(), set()
    elif isinstance(expr, PredTemplate):
        if expr in used_bt:
            return set(), set(), set(), set()
        else:
            return set(), set(), {expr}, set()
    elif isinstance(expr, (Con, Pred)):
        return set(), set(), set(), set()
    elif isinstance(expr, (AtomicFormula, Compound, CompoundPredTerm)):
        if isinstance(expr, AtomicFormula):
            found_fv, found_bv, found_ft, found_bt = collect_vars(expr.pred, used_bv, used_bt)
        else:
            found_fv: set[Var] = set()
            found_bv: set[Var] = set()
            found_ft: set[PredTemplate] = set()
            found_bt: set[PredTemplate] = set()
        for arg in expr.args:
            fv, bv, ft, bt = collect_vars(arg, used_bv, used_bt)
            found_fv.update(fv)
            found_bv.update(bv)
            found_ft.update(ft)
            found_bt.update(bt)
        return found_fv, found_bv, found_ft, found_bt
    elif isinstance(expr, Not):
        return collect_vars(expr.body, used_bv, used_bt)
    elif isinstance(expr, (And, Or, Implies, Iff)):
        found_fv1, found_bv1, found_ft1, found_bt1 = collect_vars(expr.left, used_bv, used_bt)
        found_fv2, found_bv2, found_ft2, found_bt2 = collect_vars(expr.right, used_bv, used_bt)
        return found_fv1 | found_fv2, found_bv1 | found_bv2, found_ft1 | found_ft2, found_bt1 | found_bt2
    elif isinstance(expr, (Forall, Exists, ExistsUniq)):
        if isinstance(expr.var, Var):
            found_fv, found_bv, found_ft, found_bt = collect_vars(expr.body, used_bv | {expr.var}, used_bt)
            found_bv.add(expr.var)
        elif isinstance(expr.var, PredTemplate):
            found_fv, found_bv, found_ft, found_bt = collect_vars(expr.body, used_bv, used_bt | {expr.var})
            found_bt.add(expr.var)
        else:
            raise Exception(f"Unexpected type: {type(expr.var)}")
        return found_fv, found_bv, found_ft, found_bt
    elif isinstance(expr, Lambda):
        found_fv, found_bv, found_ft, found_bt = collect_vars(expr.body, used_bv | set(expr.args), used_bt)
        return found_fv, found_bv | set(expr.args), found_ft, found_bt
    elif isinstance(expr, MembershipLambda):
        return collect_vars(expr.varterm, used_bv, used_bt)
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
        e1_exp = normalize_neg(DefExpander(defs).expand_defs_formula(e1, context))
        e2_exp = normalize_neg(DefExpander(defs).expand_defs_formula(e2, context))
        return AlphaEquiv(context).alpha_equiv(e1_exp, e2_exp)

@dataclass
class DefExpander:
    defs: list[str]
    indexes: dict[str, list[int]] = field(default_factory=dict[str, list[int]])
    counter: dict[str, int] = field(init=False, default_factory=dict[str, int])

    def expand_defs_term(self, expr: Term, context: Context) -> Term:
        if isinstance(expr, (Var, Con, PredTemplate, FunTemplate)):
            return expr
        elif isinstance(expr, Compound):
            if isinstance(expr.fun, Fun):
                if expr.fun.name in context.decl.deffuns:
                    return Compound(expr.fun, tuple(self.expand_defs_term(arg, context.copy_form()) for arg in expr.args))
                elif expr.fun.name in context.decl.deffunterms:
                    deffunterm = context.decl.deffunterms[expr.fun.name]
                    should_expand = False
                    if expr.fun.name in self.defs:
                        target_indexes = self.indexes.get(expr.fun.name, [])
                        self.counter[expr.fun.name] = self.counter.get(expr.fun.name, 0) + 1
                        if not target_indexes:
                            should_expand = True
                        elif self.counter[expr.fun.name] in target_indexes:
                            should_expand = True
                    if should_expand:
                        renamed_term, renamed_mapping = alpha_safe_term(deffunterm.term, dict(zip(deffunterm.args, expr.args)), context)
                        if not type_safe(renamed_mapping, context):
                            raise Exception("type_safe() failed")
                        expanded = Substitutor(renamed_mapping, context).substitute_term(renamed_term)
                        return self.expand_defs_term(expanded, context.copy_form())
                    else:
                        return Compound(expr.fun, tuple(self.expand_defs_term(arg, context.copy_form()) for arg in expr.args))
                else:
                    raise Exception(f"Unexpected function name: {expr.fun.name}")
            elif isinstance(expr.fun, FunTemplate):
                if expr.fun in context.ctrl.fun_tmpls or expr.fun in context.form.fun_tmpls:
                    return Compound(expr.fun, tuple(self.expand_defs_term(arg, context.copy_form()) for arg in expr.args))
                else:
                    raise Exception(f"{expr.fun} in {context.ctrl.fun_tmpls}") # or {expr.fun} in {bound_pred_tmpls}")
            else:
                raise Exception(f"Unexpected type: {type(expr.fun)}")
        elif isinstance(expr, Lambda):
            return Lambda(expr.args, self.expand_defs_formula(expr.body, context.copy_form()))
        elif isinstance(expr, MembershipLambda):
            expanded = self.expand_defs_term(expr.varterm, context.copy_form())
            if not isinstance(expanded, VarTerm):
                raise Exception(f"Unexpected type: {type(expanded)}")
            return MembershipLambda(expanded)
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def expand_defs_formula(self, expr: Formula, context: Context) -> Formula:
        if isinstance(expr, AtomicFormula):
            if isinstance(expr.pred, Pred):
                if expr.pred.name in context.decl.primpreds:
                    return AtomicFormula(expr.pred, tuple(self.expand_defs_term(arg, context.copy_form()) for arg in expr.args))
                elif expr.pred.name in context.decl.defpreds:
                    defpred = context.decl.defpreds[expr.pred.name]
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
                        renamed_formula, renamed_mapping = alpha_safe_formula(defpred.formula, dict(zip(defpred.args, expr.args)), context)
                        if not type_safe(renamed_mapping, context):
                            raise Exception("type_safe() failed")
                        expanded = Substitutor(renamed_mapping, context).substitute_formula(renamed_formula)
                        return self.expand_defs_formula(expanded, context.copy_form())
                    else:
                        return AtomicFormula(expr.pred, tuple(self.expand_defs_term(arg, context.copy_form()) for arg in expr.args))
                else:
                    raise Exception(f"Unexpected predicate name: {expr.pred.name}")
            elif isinstance(expr.pred, PredTemplate):
                if expr.pred in context.ctrl.pred_tmpls or expr.pred in context.form.pred_tmpls:
                    return AtomicFormula(expr.pred, tuple(self.expand_defs_term(arg, context.copy_form()) for arg in expr.args))
                else:
                    raise Exception(f"{expr.pred} in {context.ctrl.pred_tmpls} or {expr.pred} in {context.form.pred_tmpls}")
            elif isinstance(expr.pred, CompoundPredTerm):
                if expr.pred.fun.name in context.decl.deffuntemplateterms:
                    should_expand = False
                    if expr.pred.fun.name in self.defs:
                        target_indexes = self.indexes.get(expr.pred.fun.name, [])
                        self.counter[expr.pred.fun.name] = self.counter.get(expr.pred.fun.name, 0) + 1
                        if not target_indexes:
                            should_expand = True
                        elif self.counter[expr.pred.fun.name] in target_indexes:
                            should_expand = True
                    if should_expand:
                        deffuntemplateterm = context.decl.deffuntemplateterms[expr.pred.fun.name]
                        renamed_term, renamed_mapping = alpha_safe_term(deffuntemplateterm.term, dict(zip(deffuntemplateterm.args, expr.pred.args)), context)
                        if not type_safe(renamed_mapping, context):
                            raise Exception("type_safe() failed")
                        expanded = Substitutor(renamed_mapping, context).substitute_term(renamed_term)
                        new_pred = self.expand_defs_term(expanded, context.copy_form())
                        if not isinstance(new_pred, PredTerm):
                            raise Exception(f"Unexpected type: {type(new_pred)}")
                        if isinstance(new_pred, Lambda):
                            renamed_body, final_mapping = alpha_safe_formula(new_pred.body, dict(zip(new_pred.args, expr.args)), context)
                            final_formula = Substitutor(final_mapping, context).substitute_formula(renamed_body)
                            return self.expand_defs_formula(final_formula, context.copy_form())
                        else:
                            return AtomicFormula(new_pred, tuple(self.expand_defs_term(arg, context.copy_form()) for arg in expr.args))
                    else:
                        return AtomicFormula(expr.pred, tuple(self.expand_defs_term(arg, context.copy_form()) for arg in expr.args))
                else:
                    raise Exception(f"Unexpected name: {expr.pred.fun.name}")
            else:
                raise Exception(f"Unexpected type: {type(expr.pred)}")
        elif isinstance(expr, Not):
            return Not(self.expand_defs_formula(expr.body, context.copy_form()))
        elif isinstance(expr, (And, Or, Implies, Iff)):
            return type(expr)(self.expand_defs_formula(expr.left, context.copy_form()), self.expand_defs_formula(expr.right, context.copy_form()))
        elif isinstance(expr, Forall):
            pred_tmpls: list[PredTemplate] = []
            fun_tmpls: list[FunTemplate] = []
            if isinstance(expr.var, PredTemplate):
                pred_tmpls.append(expr.var)
            elif isinstance(expr.var, FunTemplate):
                fun_tmpls.append(expr.var)
            return Forall(expr.var, self.expand_defs_formula(expr.body, context.add_form([], pred_tmpls, fun_tmpls)))
        elif isinstance(expr, (Exists, ExistsUniq)):
            return type(expr)(expr.var, self.expand_defs_formula(expr.body, context.copy_form()))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

def normalize_neg(expr: Formula) -> Formula:
    if isinstance(expr, AtomicFormula):
        return expr
    elif isinstance(expr, Not):
        if isinstance(expr.body, Not):
            return expr.body.body
        else:
            return expr
    elif isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(normalize_neg(expr.left), normalize_neg(expr.right))
    elif isinstance(expr, Forall):
        return Forall(expr.var, normalize_neg(expr.body))
    elif isinstance(expr, (Exists, ExistsUniq)):
        return type(expr)(expr.var, normalize_neg(expr.body))
    else:
        raise Exception(f"Unexpected type: {type(expr)}")

def fresh_name(item: Var | PredTemplate, used_items: set[Var | PredTemplate], context: Context) -> str:
    used_names = {item.name for item in used_items} | context.ctrl.used_names | context.decl.used_names
    if item.name not in used_names:
        return item.name
    match = re.match(r"^(.*)_(\d+)$", item.name)
    if match:
        base_name = match.group(1)
        i = int(match.group(2)) + 1
    else:
        base_name = item.name
        i = 0
    new_name = f"{base_name}_{i}"
    while new_name in used_names:
        i += 1
        new_name = f"{base_name}_{i}"
    return new_name

def fresh_var(var: Var, used_items: set[Var | PredTemplate], context: Context) -> Var:
    return Var(fresh_name(var, used_items, context))

def fresh_pred_tmpl(pred_tmpl: PredTemplate, used_items: set[Var | PredTemplate], context: Context) -> PredTemplate:
    return PredTemplate(fresh_name(pred_tmpl, used_items, context), pred_tmpl.arity)

@dataclass
class Substitutor:
    mapping: Mapping[Term, Term]
    context: Context
    indexes: Mapping[Term, list[int]] = field(default_factory=dict[Term, list[int]])
    counter: dict[Term, int] = field(init=False, default_factory=dict[Term, int])

    def substitute_term(self, expr: Term) -> Term:
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

        if isinstance(expr, (Var, Con, PredTemplate)):
            return expr

        elif isinstance(expr, Compound):
            return Compound(expr.fun, tuple(self.substitute_term(arg) for arg in expr.args))

        elif isinstance(expr, Lambda):
            return Lambda(expr.args, self.substitute_formula(expr.body))

        elif isinstance(expr, MembershipLambda):
            substituted = self.substitute_term(expr.varterm)
            if not isinstance(substituted, VarTerm):
                raise Exception(f"Unexpected type: {type(substituted)}")
            return MembershipLambda(substituted)

        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def substitute_formula(self, expr: Formula) -> Formula:
        if isinstance(expr, AtomicFormula):
            if isinstance(expr.pred, Pred):
                if expr.pred.name in self.context.decl.primpreds:
                    return AtomicFormula(expr.pred, tuple(self.substitute_term(arg) for arg in expr.args))
                elif expr.pred.name in self.context.decl.defpreds:
                    defpred = self.context.decl.defpreds[expr.pred.name]
                    resolved_args: list[Term] = []
                    for defarg, subarg in zip(defpred.args, expr.args):
                        if isinstance(defarg, VarTerm):
                            if isinstance(subarg, VarTerm):
                                resolved_args.append(subarg)
                            else:
                                raise Exception(f"VarTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted")
                        elif isinstance(defarg, PredTerm):
                            if isinstance(subarg, PredTerm):
                                resolved_args.append(subarg)
                            elif isinstance(subarg, VarTerm):
                                if defarg.arity == 1:
                                    if self.context.decl.membership is None:
                                        raise Exception(f"VarTerm is substituted into PredTerm with arity 1, but membership has not been declared")
                                    else:
                                        resolved_args.append(MembershipLambda(subarg))
                                else:
                                    raise Exception(f"VarTerm cannot be substituted into PredTerm with arity {defarg.arity}")
                            else:
                                raise Exception(f"Unexpected type: {type(subarg)}")
                        else:
                            raise Exception(f"Unexpected type: {type(defarg)}")
                    return AtomicFormula(expr.pred, tuple(self.substitute_term(arg) for arg in resolved_args))
                else:
                    raise Exception(f"{expr.pred.name} not found in primpreds or defpreds")
            elif isinstance(expr.pred, PredTemplate):
                new_pred_tmpl = self.substitute_term(expr.pred)
                if isinstance(new_pred_tmpl, PredTemplate):
                    return AtomicFormula(new_pred_tmpl, tuple(self.substitute_term(arg) for arg in expr.args))
                elif isinstance(new_pred_tmpl, Lambda):
                    lambda_mapping: dict[Term, Term] = {}
                    for a, b in zip(new_pred_tmpl.args, expr.args):
                        lambda_mapping[a] = b
                    subst = Substitutor(lambda_mapping, self.context)
                    lambda_mapped = subst.substitute_formula(new_pred_tmpl.body)
                    return self.substitute_formula(lambda_mapped)
                elif isinstance(new_pred_tmpl, MembershipLambda):
                    if self.context.decl.membership is None:
                        raise Exception(f"{type(new_pred_tmpl)} cannot be substituted into TemplateCall since membership has not been declared.")
                    if len(expr.args) != 1:
                        raise Exception(f"{type(new_pred_tmpl)} cannot be substituted into TemplateCall with {len(expr.args)} args")
                    return AtomicFormula(Pred(self.context.decl.membership.name), (self.substitute_term(expr.args[0]), new_pred_tmpl.varterm))
                else:
                    raise Exception(f"Unexpected type: {type(new_pred_tmpl)}")
            elif isinstance(expr.pred, CompoundPredTerm):
                return AtomicFormula(CompoundPredTerm(expr.pred.fun, tuple(self.substitute_term(arg) for arg in expr.pred.args)), tuple(self.substitute_term(arg) for arg in expr.args))
            else:
                raise Exception(f"Unexpected type: {type(expr.pred)}")

        elif isinstance(expr, Not):
            return Not(self.substitute_formula(expr.body))

        elif isinstance(expr, (And, Or, Implies, Iff)):
            return type(expr)(self.substitute_formula(expr.left), self.substitute_formula(expr.right))

        elif isinstance(expr, Forall):
            return Forall(expr.var, self.substitute_formula(expr.body))

        elif isinstance(expr, (Exists, ExistsUniq)):
            return type(expr)(expr.var, self.substitute_formula(expr.body))

        else:
            raise Exception(f"Unexpected type: {type(expr)}")

class AlphaRename:
    def __init__(self, rename_map_var: dict[Var, Var], rename_map_pred_tmpl: dict[PredTemplate, PredTemplate]) -> None:
        self.rename_map_var = rename_map_var
        self.rename_map_pred_tmpl = rename_map_pred_tmpl

    def alpha_rename_var(self, expr: Var) -> Var:
        return self.rename_map_var.get(expr, expr)

    def alpha_rename_pred_tmpl(self, expr: PredTemplate) -> PredTemplate:
        return self.rename_map_pred_tmpl.get(expr, expr)

    def alpha_rename_var_or_pred_tmpl(self, expr: Var | PredTemplate) -> Var | PredTemplate:
        if isinstance(expr, Var):
            return self.alpha_rename_var(expr)
        elif isinstance(expr, PredTemplate):
            return self.alpha_rename_pred_tmpl(expr)
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def alpha_rename_term(self, expr: Term) -> Term:
        if isinstance(expr, (Var, PredTemplate)):
            return self.alpha_rename_var_or_pred_tmpl(expr)
        elif isinstance(expr, Con):
            return expr
        elif isinstance(expr, Compound):
            return Compound(expr.fun, tuple(self.alpha_rename_term(a) for a in expr.args))
        elif isinstance(expr, Lambda):
            return Lambda(tuple(self.alpha_rename_var(a) for a in expr.args), self.alpha_rename_formula(expr.body))
        elif isinstance(expr, MembershipLambda):
            renamed = self.alpha_rename_term(expr.varterm)
            if not isinstance(renamed, VarTerm):
                raise Exception(f"Unexpected type: {type(renamed)}")
            return MembershipLambda(renamed)
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def alpha_rename_formula(self, expr: Formula) -> Formula:
        if isinstance(expr, AtomicFormula):
            if isinstance(expr.pred, Pred):
                new_pred = expr.pred
            elif isinstance(expr.pred, PredTemplate):
                new_pred = self.alpha_rename_pred_tmpl(expr.pred)
            elif isinstance(expr.pred, CompoundPredTerm):
                new_pred = CompoundPredTerm(expr.pred.fun, tuple(self.alpha_rename_term(a) for a in expr.pred.args))
            else:
                raise Exception(f"Unexpected type: {type(expr.pred)}")
            return AtomicFormula(new_pred, tuple(self.alpha_rename_term(a) for a in expr.args))
        elif isinstance(expr, Not):
            return Not(self.alpha_rename_formula(expr.body))
        elif isinstance(expr, (And, Or, Implies, Iff)):
            return type(expr)(self.alpha_rename_formula(expr.left), self.alpha_rename_formula(expr.right))
        elif isinstance(expr, Forall):
            return Forall(self.alpha_rename_var_or_pred_tmpl(expr.var), self.alpha_rename_formula(expr.body))
        elif isinstance(expr, (Exists, ExistsUniq)):
            return type(expr)(self.alpha_rename_var(expr.var), self.alpha_rename_formula(expr.body))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

def alpha_safe(expr: Formula | Term, mapping: dict[Term, Term], context: Context, skip_key: bool = False) -> tuple[AlphaRename, dict[Term, Term]]:
    items_to_substitute: set[Var | PredTemplate] = set()
    for term in mapping.values():
        fv, bv, ft, bt = collect_vars(term)
        items_to_substitute.update(fv | bv | ft | bt)
    _, used_bound_vars, _, used_bound_pred_tmpls = collect_vars(expr)
    keys: set[Term] = set() if skip_key else set(mapping.keys())
    rename_map_var: dict[Var, Var] = {}
    rename_map_pred_tmpl: dict[PredTemplate, PredTemplate] = {}
    for target in keys | used_bound_vars | used_bound_pred_tmpls:
        if isinstance(target, Var):
            new_v = fresh_var(target, items_to_substitute, context)
            if new_v != target:
                rename_map_var[target] = new_v
            items_to_substitute.add(new_v)
        elif isinstance(target, PredTemplate):
            new_t = fresh_pred_tmpl(target, items_to_substitute, context)
            if new_t != target:
                rename_map_pred_tmpl[target] = new_t
            items_to_substitute.add(new_t)
        else:
            raise Exception(f"Unexpected type: {type(target)}")
    renamer = AlphaRename(rename_map_var, rename_map_pred_tmpl)
    new_mapping: dict[Term, Term] = {}
    if skip_key:
        new_mapping = mapping
    else:
        for k, v in mapping.items():
            if isinstance(k, Var):
                new_k = rename_map_var.get(k, k)
            elif isinstance(k, PredTemplate):
                new_k = rename_map_pred_tmpl.get(k, k)
            else:
                raise Exception(f"Unexpected type: {type(k)}")
            new_mapping[new_k] = v
    return renamer, new_mapping

def alpha_safe_term(expr: Term, mapping: dict[Term, Term], context: Context, skip_key: bool = False) -> tuple[Term, dict[Term, Term]]:
    renamer, renamed_mapping = alpha_safe(expr, mapping, context, skip_key)
    return renamer.alpha_rename_term(expr), renamed_mapping

def alpha_safe_formula(expr: Formula, mapping: dict[Term, Term], context: Context, skip_key: bool = False) -> tuple[Formula, dict[Term, Term]]:
    renamer, renamed_mapping = alpha_safe(expr, mapping, context, skip_key)
    return renamer.alpha_rename_formula(expr), renamed_mapping

def type_safe(mapping: dict[Term, Term], context: Context, strict: bool = False) -> bool:
    for item, term in mapping.items():
        if isinstance(item, Var):
            allowed = Var if strict else VarTerm
            if not isinstance(term, allowed):
                return False
        elif isinstance(item, PredTemplate):
            allowed = PredTemplate if strict else PredTerm
            if not isinstance(term, allowed):
                return False
        else:
            return False
    return True

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

def pretty_expr_fragments(expr: AtomicFormula | Compound | CompoundPredTerm, context: Context) -> list[str]:
    if isinstance(expr, AtomicFormula) and isinstance(expr.pred, Pred):
        if expr.pred.name in context.decl.primpreds:
            tex = context.decl.primpreds[expr.pred.name].tex
        elif expr.pred.name in context.decl.defpreds:
            tex = context.decl.defpreds[expr.pred.name].tex
        else:
            raise Exception(f"{expr.pred.name} is not in primpreds or defpreds")
        return tex
    elif isinstance(expr, Compound) and isinstance(expr.fun, Fun):
        if expr.fun.name in context.decl.deffuns:
            tex = context.decl.deffuns[expr.fun.name].tex
        elif expr.fun.name in context.decl.deffunterms:
            tex = context.decl.deffunterms[expr.fun.name].tex
        else:
            raise Exception(f"{expr.fun.name} is not in deffuns or deffunterms")
        return tex
    elif isinstance(expr, CompoundPredTerm):
        if expr.fun.name in context.decl.deffuntemplateterms:
            tex = context.decl.deffuntemplateterms[expr.fun.name].tex
        else:
            raise Exception(f"{expr.fun.name} is not in deffuntemplateterms")
        return tex
    else:
        raise TypeError(f"Unsupported node type: {type(expr)}")

def pretty_term(expr: Term, context: Context, parent_prec: int = TERM_PRECEDENCE["Lowest"]) -> str:
    if isinstance(expr, Var):
        return expr.name
    elif isinstance(expr, (PredTemplate, FunTemplate)):
        return f"{expr.name}[{str(expr.arity)}]"
    elif isinstance(expr, Con):
        if expr.name in context.decl.defcons:
            tex = context.decl.defcons[expr.name].tex
        else:
            raise Exception(f"{expr.name} is not in context.defcons")
        if len(tex) != 1:
            raise Exception("arity is different")
        return tex[0]
    elif isinstance(expr, (Compound, CompoundPredTerm)):
        if isinstance(expr.fun, Fun):
            tex = pretty_expr_fragments(expr, context)
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
        elif isinstance(expr.fun, FunTemplate):
            if expr.fun.arity == 0:
                text = expr.fun.name
            else:
                text = f"{expr.fun.name}({",".join([pretty_term(arg, context) for arg in expr.args])})"
            return text if TERM_PRECEDENCE["CompoundFunction"] > parent_prec else f"({text})"
        else:
            raise Exception(f"Unexpected type: {type(expr.fun)}")
    elif isinstance(expr, Lambda):
        return f"\\lambda {",".join([var.name for var in expr.args])}. {pretty_formula(expr.body, context)}"
    elif isinstance(expr, MembershipLambda):
        return pretty_term(expr.varterm, context)
    else:
        raise TypeError(f"Unsupported node type: {type(expr)}")

def pretty_formula(expr: Formula, context: Context, parent_prec: int = FORMULA_PRECEDENCE["Lowest"]) -> str:
    if isinstance(expr, AtomicFormula):
        if isinstance(expr.pred, Pred):
            tex = pretty_expr_fragments(expr, context)
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
        elif isinstance(expr.pred, PredTemplate):
            if expr.pred.arity == 0:
                text = expr.pred.name
            else:
                text = f"{expr.pred.name}({",".join([pretty_term(arg, context) for arg in expr.args])})"
            return text if FORMULA_PRECEDENCE["Symbol"] > parent_prec else f"({text})"
        elif isinstance(expr.pred, CompoundPredTerm):
            if len(expr.args) == 0:
                text = pretty_term(expr.pred, context)
            else:
                text = f"{pretty_term(expr.pred, context)}({",".join([pretty_term(arg, context) for arg in expr.args])})"
            return text if FORMULA_PRECEDENCE["Symbol"] > parent_prec else f"({text})"
        else:
            raise Exception(f"Unexpected type: {type(expr.pred)}")
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
            elif isinstance(body.var, PredTemplate):
                qvars_text += f"^P {pretty_term(body.var, context)}"
            elif isinstance(body.var, FunTemplate):
                qvars_text += f"^F {pretty_term(body.var, context)}"
            else:
                raise Exception(f"Unexpected type: {type(body.var)}")
            body = body.body
        text = f"{qvars_text} {pretty_formula(body, context, FORMULA_PRECEDENCE["Quantifier"])}"
        return text if FORMULA_PRECEDENCE["Quantifier"] > parent_prec else f"({text})"
    else:
        raise TypeError(f"Unsupported node type: {type(expr)}")

def pretty_expr(expr: str | Bottom | Formula | Term | Pred | Fun, context: Context) -> str:
    if isinstance(expr, str):
        return expr
    elif isinstance(expr, Bottom):
        return "\\bot"
    elif isinstance(expr, Formula):
        return pretty_formula(expr, context)
    elif isinstance(expr, Term):
        return pretty_term(expr, context)
    elif isinstance(expr, (Pred, Fun)):
        return expr.name
    else:
        raise TypeError(f"Unsupported node type: {type(expr)}")
