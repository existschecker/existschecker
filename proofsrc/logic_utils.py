from ast_types import Or, Not, Forall, Exists, ExistsUniq, Implies, Iff, And, AtomicFormula, Context, Compound, RefDefCon, Var, Bottom, Term, Formula, PredTemplate, PredLambda, VarTerm, PredTerm, FunTemplate, FunTerm, FunLambda, RefPrimPred, RefDefPred, RefDefFun, RefDefFunTerm, RefEquality
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
            print(f"{'  ' * depth}[{e1.__class__.__name__}] e1: {ExprFormatter(self.context).pretty_expr(e1)}")
            print(f"{'  ' * depth}[{e2.__class__.__name__}] e2: {ExprFormatter(self.context).pretty_expr(e2)}")
            print(f"{'  ' * depth}[env] {", ".join([ExprFormatter(self.context).pretty_expr(k) + ": " + ExprFormatter(self.context).pretty_expr(v) for k, v in env.items()])}")

    def end_log(self, depth: int, result: bool):
        if False:
            mark = "✅ True" if result else f"❌ False"
            print(f"{'  ' * depth}{mark}")

    def alpha_equiv_var(self, e1: Var | PredTemplate | FunTemplate, e2: Var | PredTemplate | FunTemplate, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        if type(e1) is not type(e2):
            return False
        return env.get(e1, e1) == e2

    def alpha_equiv_con(self, e1: RefDefCon | RefPrimPred | RefDefPred | RefDefFun | RefDefFunTerm, e2: RefDefCon | RefPrimPred | RefDefPred | RefDefFun | RefDefFunTerm, depth: int) -> bool:
        if type(e1) is not type(e2):
            return False
        return e1.name == e2.name

    def alpha_equiv_compound(self, e1: Compound, e2: Compound, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        if not self.alpha_equiv_fun_term(e1.fun, e2.fun, env, depth+1):
            return False
        if len(e1.args) != len(e2.args):
            return False
        for a, b in zip(e1.args, e2.args):
            if not self.alpha_equiv_term(a, b, env, depth+1):
                return False
        return True

    def alpha_equiv_pred_lambda(self, e1: PredLambda, e2: PredLambda, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        newenv = env.copy()
        for a, b in zip(e1.args, e2.args):
            newenv[a] = b
        return self.alpha_equiv_formula(e1.body, e2.body, newenv, depth+1)

    def alpha_equiv_fun_lambda(self, e1: FunLambda, e2: FunLambda, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        if len(e1.args) != len(e2.args):
            return False
        newenv = env.copy()
        for a, b in zip(e1.args, e2.args):
            newenv[a] = b
        return self.alpha_equiv_var_term(e1.body, e2.body, newenv, depth+1)

    def alpha_equiv_var_term(self, e1: VarTerm, e2: VarTerm, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        self.begin_log(depth, e1, e2, env)
        if isinstance(e1, Var) and isinstance(e2, Var):
            result = self.alpha_equiv_var(e1, e2, env, depth)
        elif isinstance(e1, RefDefCon) and isinstance(e2, RefDefCon):
            result = self.alpha_equiv_con(e1, e2, depth)
        elif isinstance(e1, Compound) and isinstance(e2, Compound):
            result = self.alpha_equiv_compound(e1, e2, env, depth)
        else:
            result = False
        self.end_log(depth, result)
        return result

    def alpha_equiv_pred_term(self, e1: PredTerm, e2: PredTerm, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        self.begin_log(depth, e1, e2, env)
        if isinstance(e1, PredTemplate) and isinstance(e2, PredTemplate):
            result =  self.alpha_equiv_var(e1, e2, env, depth)
        elif isinstance(e1, RefEquality) and isinstance(e2, RefEquality):
            result = True
        elif isinstance(e1, RefPrimPred) and isinstance(e2, RefPrimPred):
            result = self.alpha_equiv_con(e1, e2, depth)
        elif isinstance(e1, RefDefPred) and isinstance(e2, RefDefPred):
            result = self.alpha_equiv_con(e1, e2, depth)
        elif isinstance(e1, PredLambda) and isinstance(e2, PredLambda):
            result = self.alpha_equiv_pred_lambda(e1, e2, env, depth)
        else:
            result = False
        self.end_log(depth, result)
        return result

    def alpha_equiv_fun_term(self, e1: FunTerm, e2: FunTerm, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        self.begin_log(depth, e1, e2, env)
        if isinstance(e1, RefDefFun) and isinstance(e2, RefDefFun):
            result = self.alpha_equiv_con(e1, e2, depth)
        elif isinstance(e1, RefDefFunTerm) and isinstance(e2, RefDefFunTerm):
            result = self.alpha_equiv_con(e1, e2, depth)
        elif isinstance(e1, FunTemplate) and isinstance(e2, FunTemplate):
            result = self.alpha_equiv_var(e1, e2, env, depth)
        elif isinstance(e1, FunLambda) and isinstance(e2, FunLambda):
            result = self.alpha_equiv_fun_lambda(e1, e2, env, depth)
        else:
            result = False
        self.end_log(depth, result)
        return result

    def alpha_equiv_term(self, e1: Term, e2: Term, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        if isinstance(e1, VarTerm) and isinstance(e2, VarTerm):
            result = self.alpha_equiv_var_term(e1, e2, env, depth)
        elif isinstance(e1, PredTerm) and isinstance(e2, PredTerm):
            result = self.alpha_equiv_pred_term(e1, e2, env, depth)
        elif isinstance(e1, FunTerm) and isinstance(e2, FunTerm):
            result = self.alpha_equiv_fun_term(e1, e2, env, depth)
        else:
            result = False
        return result

    def alpha_equiv_symbol(self, e1: AtomicFormula, e2: AtomicFormula, env: dict[Var | PredTemplate | FunTemplate, Var | PredTemplate | FunTemplate], depth: int) -> bool:
        if not self.alpha_equiv_pred_term(e1.pred, e2.pred, env, depth+1):
            return False
        if len(e1.args) != len(e2.args):
            return False
        if self.context.decl.equality is not None and isinstance(e1.pred, RefEquality):
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
        if type(e1) is not type(e2):
            return False
        if isinstance(e1, Forall):
            vars1, body1 = strip_forall_vars(e1)
            vars2, body2 = strip_forall_vars(e2)
        else:
            vars1, body1 = strip_exists_vars(e1, type(e1))
            vars2, body2 = strip_exists_vars(e2, type(e1))

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

def strip_forall_vars(e: Formula) -> tuple[list[Var | PredTemplate | FunTemplate], Formula]:
    vars_: list[Var | PredTemplate | FunTemplate] = []
    body = e
    while isinstance(body, Forall):
        vars_.append(body.var)
        body = body.body
    return vars_, body

def strip_exists_vars(e: Formula, quantifier_type: type[Exists] | type[ExistsUniq]) -> tuple[list[Var], Formula]:
    vars_: list[Var] = []
    body = e
    while isinstance(body, quantifier_type):
        vars_.append(body.var)
        body = body.body
    return vars_, body

def make_forall_vars(e: Formula, vars_: list[Var | PredTemplate | FunTemplate]) -> Formula:
    body = e
    for var in reversed(vars_):
        body = Forall(var, body)
    return body

def make_exists_vars(e: Formula, quantifier_type: type[Exists] | type[ExistsUniq], vars_: list[Var]) -> Formula:
    body = e
    for var in reversed(vars_):
        body = quantifier_type(var, body)
    return body

def collect_vars(expr: Formula | Term, used_bv: set[Var] | None = None, used_bpt: set[PredTemplate] | None = None, used_bft: set[FunTemplate] | None = None) -> tuple[set[Var], set[Var], set[PredTemplate], set[PredTemplate], set[FunTemplate], set[FunTemplate]]:
    if used_bv is None:
        used_bv = set()
    if used_bpt is None:
        used_bpt = set()
    if used_bft is None:
        used_bft = set()

    if isinstance(expr, Var):
        if expr in used_bv:
            return set(), set(), set(), set(), set(), set()
        else:
            return {expr}, set(), set(), set(), set(), set()
    elif isinstance(expr, PredTemplate):
        if expr in used_bpt:
            return set(), set(), set(), set(), set(), set()
        else:
            return set(), set(), {expr}, set(), set(), set()
    elif isinstance(expr, FunTemplate):
        if expr in used_bft:
            return set(), set(), set(), set(), set(), set()
        else:
            return set(), set(), set(), set(), {expr}, set()
    elif isinstance(expr, (RefDefCon, RefEquality, RefPrimPred, RefDefPred, RefDefFun, RefDefFunTerm)):
        return set(), set(), set(), set(), set(), set()
    elif isinstance(expr, (AtomicFormula, Compound)):
        if isinstance(expr, AtomicFormula):
            found_fv, found_bv, found_fpt, found_bpt, found_fft, found_bft = collect_vars(expr.pred, used_bv, used_bpt, used_bft)
        else:
            found_fv, found_bv, found_fpt, found_bpt, found_fft, found_bft = collect_vars(expr.fun, used_bv, used_bpt, used_bft)
        for arg in expr.args:
            fv, bv, fpt, bpt, fft, bft = collect_vars(arg, used_bv, used_bpt, used_bft)
            found_fv.update(fv)
            found_bv.update(bv)
            found_fpt.update(fpt)
            found_bpt.update(bpt)
            found_fft.update(fft)
            found_bft.update(bft)
        return found_fv, found_bv, found_fpt, found_bpt, found_fft, found_bft
    elif isinstance(expr, Not):
        return collect_vars(expr.body, used_bv, used_bpt, used_bft)
    elif isinstance(expr, (And, Or, Implies, Iff)):
        found_fv1, found_bv1, found_fpt1, found_bpt1, found_fft1, found_bft1 = collect_vars(expr.left, used_bv, used_bpt, used_bft)
        found_fv2, found_bv2, found_fpt2, found_bpt2, found_fft2, found_bft2 = collect_vars(expr.right, used_bv, used_bpt, used_bft)
        return found_fv1 | found_fv2, found_bv1 | found_bv2, found_fpt1 | found_fpt2, found_bpt1 | found_bpt2, found_fft1 | found_fft2, found_bft1 | found_bft2
    elif isinstance(expr, (Forall, Exists, ExistsUniq)):
        if isinstance(expr.var, Var):
            found_fv, found_bv, found_fpt, found_bpt, found_fft, found_bft = collect_vars(expr.body, used_bv | {expr.var}, used_bpt, used_bft)
            found_bv.add(expr.var)
        elif isinstance(expr.var, PredTemplate):
            found_fv, found_bv, found_fpt, found_bpt, found_fft, found_bft = collect_vars(expr.body, used_bv, used_bpt | {expr.var}, used_bft)
            found_bpt.add(expr.var)
        elif isinstance(expr.var, FunTemplate):
            found_fv, found_bv, found_fpt, found_bpt, found_fft, found_bft = collect_vars(expr.body, used_bv, used_bpt, used_bft | {expr.var})
            found_bft.add(expr.var)
        else:
            raise Exception(f"Unexpected type: {type(expr.var)}")
        return found_fv, found_bv, found_fpt, found_bpt, found_fft, found_bft
    elif isinstance(expr, (PredLambda, FunLambda)):
        found_fv, found_bv, found_fpt, found_bpt, found_fft, found_bft = collect_vars(expr.body, used_bv | set(expr.args), used_bpt, used_bft)
        return found_fv, found_bv | set(expr.args), found_fpt, found_bpt, found_fft, found_bft
    else:
        raise Exception(f"Unexpected type {type(expr)}")

def expr_in_context(expr: Bottom | Formula, context: Context) -> bool:
    return any(alpha_equiv_with_defs(expr, f, context) for f in context.ctrl.formulas)

def alpha_equiv_with_defs(e1: Bottom | Formula, e2: Bottom | Formula, context: Context, refs: list[RefDefFunTerm | RefDefPred] | None = None) -> bool:
    if refs is None:
        refs = []
    if isinstance(e1, Bottom) or isinstance(e2, Bottom):
        return isinstance(e1, Bottom) and isinstance(e2, Bottom)
    else:
        e1_exp = normalize_neg(DefExpander(refs).expand_defs_formula(e1, context))
        e2_exp = normalize_neg(DefExpander(refs).expand_defs_formula(e2, context))
        return AlphaEquiv(context).alpha_equiv(e1_exp, e2_exp)

@dataclass
class DefExpander:
    refs: list[RefDefFunTerm | RefDefPred]
    indexes: dict[RefDefFunTerm | RefDefPred, list[int]] = field(default_factory=dict[RefDefFunTerm | RefDefPred, list[int]])
    counter: dict[RefDefFunTerm | RefDefPred, int] = field(init=False, default_factory=dict[RefDefFunTerm | RefDefPred, int])

    def expand_defs_var_term(self, expr: VarTerm, context: Context) -> VarTerm:
        if isinstance(expr, (Var, RefDefCon)):
            return expr
        elif isinstance(expr, Compound):
            if isinstance(expr.fun, RefDefFunTerm):
                deffunterm = context.decl.deffunterms[expr.fun.name]
                should_expand = False
                if expr.fun in self.refs:
                    target_indexes = self.indexes.get(expr.fun, [])
                    self.counter[expr.fun] = self.counter.get(expr.fun, 0) + 1
                    if not target_indexes:
                        should_expand = True
                    elif self.counter[expr.fun] in target_indexes:
                        should_expand = True
                if should_expand:
                    renamed_term, renamed_mapping = alpha_safe_var_term(deffunterm.varterm, dict(zip(deffunterm.args, expr.args)), context)
                    expanded = Substitutor(renamed_mapping, context).substitute_var_term(renamed_term)
                    return self.expand_defs_var_term(expanded, context.copy_form())
            elif isinstance(expr.fun, FunLambda):
                renamed_body, renamed_mapping = alpha_safe_var_term(expr.fun.body, dict(zip(expr.fun.args, expr.args)), context)
                beta_reduced = Substitutor(renamed_mapping, context).substitute_var_term(renamed_body)
                return self.expand_defs_var_term(beta_reduced, context.copy_form())
            return Compound(expr.fun, tuple(self.expand_defs_term(arg, context.copy_form()) for arg in expr.args))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def expand_defs_pred_term(self, expr: PredTerm, context: Context) -> PredTerm:
        if isinstance(expr, (PredTemplate, RefPrimPred, RefDefPred)):
            return expr
        elif isinstance(expr, PredLambda):
            return PredLambda(expr.args, self.expand_defs_formula(expr.body, context.copy_form()))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def expand_defs_fun_term(self, expr: FunTerm, context: Context) -> FunTerm:
        if isinstance(expr, (FunTemplate, RefDefFun, RefDefFunTerm)):
            return expr
        elif isinstance(expr, FunLambda):
            return FunLambda(expr.args, self.expand_defs_var_term(expr.body, context.copy_form()))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def expand_defs_term(self, expr: Term, context: Context) -> Term:
        if isinstance(expr, VarTerm):
            return self.expand_defs_var_term(expr, context)
        elif isinstance(expr, PredTerm):
            return self.expand_defs_pred_term(expr, context)
        elif isinstance(expr, FunTerm):
            return self.expand_defs_fun_term(expr, context)
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def expand_defs_formula(self, expr: Formula, context: Context) -> Formula:
        if isinstance(expr, AtomicFormula):
            if isinstance(expr.pred, RefDefPred):
                defpred = context.decl.defpreds[expr.pred.name]
                should_expand = False
                if len(self.refs) == 0 and defpred.autoexpand:
                    should_expand = True
                elif expr.pred in self.refs:
                    target_indexes = self.indexes.get(expr.pred, [])
                    self.counter[expr.pred] = self.counter.get(expr.pred, 0) + 1
                    if not target_indexes:
                        should_expand = True
                    elif self.counter[expr.pred] in target_indexes:
                        should_expand = True
                if should_expand:
                    renamed_formula, renamed_mapping = alpha_safe_formula(defpred.formula, dict(zip(defpred.args, expr.args)), context)
                    expanded = Substitutor(renamed_mapping, context).substitute_formula(renamed_formula)
                    return self.expand_defs_formula(expanded, context.copy_form())
            return AtomicFormula(expr.pred, tuple(self.expand_defs_term(arg, context.copy_form()) for arg in expr.args))
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

def fresh_name(item: Var | PredTemplate | FunTemplate, used_items: set[Var | PredTemplate | FunTemplate], context: Context) -> str:
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

def fresh_var(var: Var, used_items: set[Var | PredTemplate | FunTemplate], context: Context) -> Var:
    return Var(fresh_name(var, used_items, context))

def fresh_pred_tmpl(pred_tmpl: PredTemplate, used_items: set[Var | PredTemplate | FunTemplate], context: Context) -> PredTemplate:
    return PredTemplate(fresh_name(pred_tmpl, used_items, context), pred_tmpl.arity)

def fresh_fun_tmpl(fun_tmpl: FunTemplate, used_items: set[Var | PredTemplate | FunTemplate], context: Context) -> FunTemplate:
    return FunTemplate(fresh_name(fun_tmpl, used_items, context), fun_tmpl.arity)

@dataclass
class Substitutor:
    mapping: tuple[Mapping[VarTerm, VarTerm], Mapping[PredTerm, PredTerm], Mapping[FunTerm, FunTerm]]
    context: Context
    indexes: Mapping[Term, list[int]] = field(default_factory=dict[Term, list[int]])
    counter: dict[Term, int] = field(init=False, default_factory=dict[Term, int])

    def _apply_substitute[T: Term](self, expr: T, mapping: Mapping[T, T]) -> T | None:
        for k, v in mapping.items():
            if expr == k:
                self.counter[k] = self.counter.get(k, 0) + 1
                target_indices = self.indexes.get(k, [])
                if not target_indices or self.counter[k] in target_indices:
                    return deepcopy(v)
                else:
                    return expr
        return None

    def substitute_var_term(self, expr: VarTerm) -> VarTerm:
        substituted = self._apply_substitute(expr, self.mapping[0])
        if substituted is not None:
            return substituted
        if isinstance(expr, (Var, RefDefCon)):
            return expr
        elif isinstance(expr, Compound):
            return Compound(self.substitute_fun_term(expr.fun), tuple(self.substitute_term(arg) for arg in expr.args))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def substitute_pred_term(self, expr: PredTerm) -> PredTerm:
        substituted = self._apply_substitute(expr, self.mapping[1])
        if substituted is not None:
            return substituted
        if isinstance(expr, (PredTemplate, RefEquality, RefPrimPred, RefDefPred)):
            return expr
        elif isinstance(expr, PredLambda):
            return PredLambda(expr.args, self.substitute_formula(expr.body))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def substitute_fun_term(self, expr: FunTerm) -> FunTerm:
        substituted = self._apply_substitute(expr, self.mapping[2])
        if substituted is not None:
            return substituted
        if isinstance(expr, (FunTemplate, RefDefFun, RefDefFunTerm)):
            return expr
        elif isinstance(expr, FunLambda):
            return FunLambda(expr.args, self.substitute_var_term(expr.body))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def substitute_term(self, expr: Term) -> Term:
        if isinstance(expr, VarTerm):
            return self.substitute_var_term(expr)
        elif isinstance(expr, PredTerm):
            return self.substitute_pred_term(expr)
        elif isinstance(expr, FunTerm):
            return self.substitute_fun_term(expr)
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def substitute_formula(self, expr: Formula) -> Formula:
        if isinstance(expr, AtomicFormula):
            new_pred = self.substitute_pred_term(expr.pred)
            if isinstance(new_pred, (PredTemplate, RefEquality, RefPrimPred)):
                return AtomicFormula(new_pred, tuple(self.substitute_term(arg) for arg in expr.args))
            elif isinstance(new_pred, RefDefPred):
                defpred = self.context.decl.defpreds[new_pred.name]
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
                        else:
                            raise Exception(f"PredTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted")
                    elif isinstance(defarg, FunTerm):
                        if isinstance(subarg, FunTerm):
                            resolved_args.append(subarg)
                        else:
                            raise Exception(f"FunTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted")
                    else:
                        raise Exception(f"Unexpected type: {type(defarg)}")
                return AtomicFormula(new_pred, tuple(self.substitute_term(arg) for arg in resolved_args))
            elif isinstance(new_pred, PredLambda):
                lambda_mapping: dict[VarTerm, VarTerm] = {}
                for a, b in zip(new_pred.args, expr.args):
                    if not isinstance(b, VarTerm):
                        raise Exception(f"Unexpected type: {type(b)}")
                    lambda_mapping[a] = b
                subst = Substitutor((lambda_mapping, {}, {}), self.context)
                lambda_mapped = subst.substitute_formula(new_pred.body)
                return self.substitute_formula(lambda_mapped)
            else:
                raise Exception(f"Unexpected type: {type(new_pred)}")

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
    def __init__(self, rename_map_var: dict[Var, Var], rename_map_pred_tmpl: dict[PredTemplate, PredTemplate], rename_map_fun_tmpl: dict[FunTemplate, FunTemplate]) -> None:
        self.rename_map_var = rename_map_var
        self.rename_map_pred_tmpl = rename_map_pred_tmpl
        self.rename_map_fun_tmpl = rename_map_fun_tmpl

    def alpha_rename_var(self, expr: Var) -> Var:
        return self.rename_map_var.get(expr, expr)

    def alpha_rename_pred_tmpl(self, expr: PredTemplate) -> PredTemplate:
        return self.rename_map_pred_tmpl.get(expr, expr)

    def alpha_rename_fun_tmpl(self, expr: FunTemplate) -> FunTemplate:
        return self.rename_map_fun_tmpl.get(expr, expr)

    def alpha_rename_var_or_pred_tmpl_or_fun_tmpl(self, expr: Var | PredTemplate | FunTemplate) -> Var | PredTemplate | FunTemplate:
        if isinstance(expr, Var):
            return self.alpha_rename_var(expr)
        elif isinstance(expr, PredTemplate):
            return self.alpha_rename_pred_tmpl(expr)
        elif isinstance(expr, FunTemplate):
            return self.alpha_rename_fun_tmpl(expr)
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def alpha_rename_var_term(self, expr: VarTerm) -> VarTerm:
        if isinstance(expr, Var):
            return self.alpha_rename_var(expr)
        elif isinstance(expr, RefDefCon):
            return expr
        elif isinstance(expr, Compound):
            return Compound(self.alpha_rename_fun_term(expr.fun), tuple(self.alpha_rename_term(a) for a in expr.args))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def alpha_rename_pred_term(self, expr: PredTerm) -> PredTerm:
        if isinstance(expr, PredTemplate):
            return self.alpha_rename_pred_tmpl(expr)
        elif isinstance(expr, (RefEquality, RefPrimPred, RefDefPred)):
            return expr
        elif isinstance(expr, PredLambda):
            return PredLambda(tuple(self.alpha_rename_var(a) for a in expr.args), self.alpha_rename_formula(expr.body))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def alpha_rename_fun_term(self, expr: FunTerm) -> FunTerm:
        if isinstance(expr, FunTemplate):
            return self.alpha_rename_fun_tmpl(expr)
        elif isinstance(expr, (RefDefFun, RefDefFunTerm)):
            return expr
        elif isinstance(expr, FunLambda):
            return FunLambda(tuple(self.alpha_rename_var(a) for a in expr.args), self.alpha_rename_var_term(expr.body))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def alpha_rename_term(self, expr: Term) -> Term:
        if isinstance(expr, VarTerm):
            return self.alpha_rename_var_term(expr)
        elif isinstance(expr, PredTerm):
            return self.alpha_rename_pred_term(expr)
        elif isinstance(expr, FunTerm):
            return self.alpha_rename_fun_term(expr)
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

    def alpha_rename_formula(self, expr: Formula) -> Formula:
        if isinstance(expr, AtomicFormula):
            return AtomicFormula(self.alpha_rename_pred_term(expr.pred), tuple(self.alpha_rename_term(a) for a in expr.args))
        elif isinstance(expr, Not):
            return Not(self.alpha_rename_formula(expr.body))
        elif isinstance(expr, (And, Or, Implies, Iff)):
            return type(expr)(self.alpha_rename_formula(expr.left), self.alpha_rename_formula(expr.right))
        elif isinstance(expr, Forall):
            return Forall(self.alpha_rename_var_or_pred_tmpl_or_fun_tmpl(expr.var), self.alpha_rename_formula(expr.body))
        elif isinstance(expr, (Exists, ExistsUniq)):
            return type(expr)(self.alpha_rename_var(expr.var), self.alpha_rename_formula(expr.body))
        else:
            raise Exception(f"Unexpected type: {type(expr)}")

def alpha_safe(expr: Formula | Term, mapping: dict[Term, Term], context: Context, skip_key: bool = False) -> tuple[AlphaRename, tuple[dict[VarTerm, VarTerm], dict[PredTerm, PredTerm], dict[FunTerm, FunTerm]]]:
    items_to_substitute: set[Var | PredTemplate | FunTemplate] = set()
    for term in mapping.values():
        fv, bv, fpt, bpt, fft, bft = collect_vars(term)
        items_to_substitute.update(fv | bv | fpt | bpt | fft | bft)
    _, used_bound_vars, _, used_bound_pred_tmpls, _, used_bound_fun_tmpls = collect_vars(expr)
    keys: set[Term] = set() if skip_key else set(mapping.keys())
    rename_map_var: dict[Var, Var] = {}
    rename_map_pred_tmpl: dict[PredTemplate, PredTemplate] = {}
    rename_map_fun_tmpl: dict[FunTemplate, FunTemplate] = {}
    for target in keys | used_bound_vars | used_bound_pred_tmpls | used_bound_fun_tmpls:
        if isinstance(target, Var):
            new_v = fresh_var(target, items_to_substitute, context)
            if new_v != target:
                rename_map_var[target] = new_v
            items_to_substitute.add(new_v)
        elif isinstance(target, PredTemplate):
            new_pt = fresh_pred_tmpl(target, items_to_substitute, context)
            if new_pt != target:
                rename_map_pred_tmpl[target] = new_pt
            items_to_substitute.add(new_pt)
        elif isinstance(target, FunTemplate):
            new_ft = fresh_fun_tmpl(target, items_to_substitute, context)
            if new_ft != target:
                rename_map_fun_tmpl[target] = new_ft
            items_to_substitute.add(new_ft)
        else:
            raise Exception(f"Unexpected type: {type(target)}")
    renamer = AlphaRename(rename_map_var, rename_map_pred_tmpl, rename_map_fun_tmpl)
    new_mapping_var: dict[VarTerm, VarTerm] = {}
    new_mapping_pred: dict[PredTerm, PredTerm] = {}
    new_mapping_fun: dict[FunTerm, FunTerm] = {}
    if skip_key:
        for k, v in mapping.items():
            if isinstance(k, VarTerm):
                if not isinstance(v, VarTerm):
                    raise Exception(f"Unexpected type: {type(v)}")
                new_mapping_var[k] = v
            elif isinstance(k, PredTerm):
                if not isinstance(v, PredTerm):
                    raise Exception(f"Unexpected type: {type(v)}")
                new_mapping_pred[k] = v
            elif isinstance(k, FunTerm):
                if not isinstance(v, FunTerm):
                    raise Exception(f"Unexpected type: {type(v)}")
                new_mapping_fun[k] = v
            else:
                raise Exception(f"Unexpected type: {type(k)}")
    else:
        for k, v in mapping.items():
            if isinstance(k, Var):
                if not isinstance(v, VarTerm):
                    raise Exception(f"Unexpected type: {type(v)}")
                new_k = rename_map_var.get(k, k)
                new_mapping_var[new_k] = v
            elif isinstance(k, PredTemplate):
                if not isinstance(v, PredTerm):
                    raise Exception(f"Unexpected type: {type(v)}")
                new_k = rename_map_pred_tmpl.get(k, k)
                new_mapping_pred[new_k] = v
            elif isinstance(k, FunTemplate):
                if not isinstance(v, FunTerm):
                    raise Exception(f"Unexpected type: {type(v)}")
                new_k = rename_map_fun_tmpl.get(k, k)
                new_mapping_fun[new_k] = v
            else:
                raise Exception(f"Unexpected type: {type(k)}")
    return renamer, (new_mapping_var, new_mapping_pred, new_mapping_fun)

def alpha_safe_var_term(expr: VarTerm, mapping: dict[Term, Term], context: Context, skip_key: bool = False) -> tuple[VarTerm, tuple[dict[VarTerm, VarTerm], dict[PredTerm, PredTerm], dict[FunTerm, FunTerm]]]:
    renamer, renamed_mapping = alpha_safe(expr, mapping, context, skip_key)
    return renamer.alpha_rename_var_term(expr), renamed_mapping

def alpha_safe_term(expr: Term, mapping: dict[Term, Term], context: Context, skip_key: bool = False) -> tuple[Term, tuple[dict[VarTerm, VarTerm], dict[PredTerm, PredTerm], dict[FunTerm, FunTerm]]]:
    renamer, renamed_mapping = alpha_safe(expr, mapping, context, skip_key)
    return renamer.alpha_rename_term(expr), renamed_mapping

def alpha_safe_formula(expr: Formula, mapping: dict[Term, Term], context: Context, skip_key: bool = False) -> tuple[Formula, tuple[dict[VarTerm, VarTerm], dict[PredTerm, PredTerm], dict[FunTerm, FunTerm]]]:
    renamer, renamed_mapping = alpha_safe(expr, mapping, context, skip_key)
    return renamer.alpha_rename_formula(expr), renamed_mapping
