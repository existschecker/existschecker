from ast_types import Term, Var, Con, Compound, Formula, Symbol, Not, And, Or, Implies, Iff, Forall, Exists, ExistsUniq, Template, TemplateCall, ForallTemplate
from dataclasses import dataclass
from typing import Callable

def alpha_rename(expr: Formula, rename_map: dict[Var, Var]) -> Formula:
    if isinstance(expr, Var):
        return rename_map.get(expr, expr)
    elif isinstance(expr, Con):
        return expr
    elif isinstance(expr, Compound):
        new_args = [alpha_rename(arg, rename_map) for arg in expr.args]
        return Compound(expr.fun, new_args)
    elif isinstance(expr, Symbol):
        new_args = [alpha_rename(arg, rename_map) for arg in expr.args]
        return Symbol(expr.pred, new_args)
    elif isinstance(expr, Not):
        return Not(alpha_rename(expr.body, rename_map))
    elif isinstance(expr, (And, Or, Implies, Iff)):
        return type(expr)(alpha_rename(expr.left, rename_map), alpha_rename(expr.right, rename_map))
    elif isinstance(expr, (Forall, Exists, ExistsUniq)):
        var = rename_map.get(expr.var, expr.var)
        return type(expr)(var, alpha_rename(expr.body, rename_map))
    elif isinstance(expr, ForallTemplate):
        return ForallTemplate(expr.template, alpha_rename(expr.body, rename_map))
    elif isinstance(expr, TemplateCall):
        new_args = [alpha_rename(arg, rename_map) for arg in expr.args]
        return TemplateCall(expr.template, new_args)
    else:
        raise Exception(f"Unexpected expr: {expr}")

def instantiate_templates(formula: Formula, env: dict[Template, Callable[[list[Term]], Formula]]) -> Formula:
    if isinstance(formula, Symbol):
        return formula
    elif isinstance(formula, Not):
        return Not(instantiate_templates(formula.body, env))
    elif isinstance(formula, (And, Or, Implies, Iff)):
        return type(formula)(instantiate_templates(formula.left, env), instantiate_templates(formula.right, env))
    elif isinstance(formula, (Forall, Exists, ExistsUniq)):
        return type(formula)(formula.var, instantiate_templates(formula.body, env))
    elif isinstance(formula, TemplateCall):
        if formula.template in env:
            func = env[formula.template]
            return func(formula.args)
        else:
            return formula
    else:
        raise Exception(f"Unexpected formula: {formula}")

def make_tree(expr: Formula | Term, prefix: str = "", is_root: bool = True, is_last: bool = True) -> str:
    print_prefix = prefix + ("" if is_root else ("└─" if is_last else "├─"))
    child_pref = prefix + ("   " if is_last or is_root else "│  ")
    if isinstance(expr, Var):
        return f"{print_prefix}{expr.name}"
    elif isinstance(expr, Con):
        return f"{print_prefix}{expr.name}"
    elif isinstance(expr, Compound):
        args_str = ", ".join(make_tree(arg, "", True) for arg in expr.args)
        return f"{print_prefix}{type(expr).__name__}({expr.fun.name}, [{args_str}])"
    elif isinstance(expr, Symbol):
        args_str = ", ".join(make_tree(arg, "", True) for arg in expr.args)
        return f"{print_prefix}{type(expr).__name__}({expr.pred.name}, [{args_str}])"
    elif isinstance(expr, Not):
        body_str = make_tree(expr.body, child_pref, False, True)
        return f"{print_prefix}{type(expr).__name__}\n{body_str}"
    elif isinstance(expr, (And, Or, Implies, Iff)):
        left_str = make_tree(expr.left, child_pref, False, False)
        right_str = make_tree(expr.right, child_pref, False, True)
        return f"{print_prefix}{type(expr).__name__}\n{left_str}\n{right_str}"
    elif isinstance(expr, (Exists, Forall, ExistsUniq)):
        body_str = make_tree(expr.body, child_pref, False, True)
        return f"{print_prefix}{type(expr).__name__}({expr.var.name})\n{body_str}"
    elif isinstance(expr, TemplateCall):
        args_str = ", ".join(make_tree(arg, "", True) for arg in expr.args)
        return f"{print_prefix}{type(expr).__name__}({expr.template.name}, [{args_str}])"
    elif isinstance(expr, ForallTemplate):
        body_str = make_tree(expr.body, child_pref, False, True)
        return f"{print_prefix}{type(expr).__name__}({expr.template.name})\n{body_str}"
    else:
        raise Exception(f"Unexpected expr: {expr}")

if __name__ == "__main__":
    from ast_types import Pred

    def phi_function(args: list[Var]):
        pred_in = Pred("in")
        x = args[0]
        a = Var("a")
        return Symbol(pred_in, [x, a])

    x = Var("x")
    y = Var("y")
    z = Var("z")
    u = Var("u")
    pred_in = Pred("in")

    phi = Template("phi", 1)
    separation_schema = ForallTemplate(phi, Forall(x, Exists(y, Forall(z, Iff(Symbol(pred_in, [z, y]), And(Symbol(pred_in, [z, x]), TemplateCall(phi, [z])))))))
    print(make_tree(separation_schema))

    mapping = {z: u}
    renamed_schema = alpha_rename(separation_schema, mapping)
    print(make_tree(renamed_schema))

    env = {phi: phi_function}
    instantiated = instantiate_templates(renamed_schema.body, env)
    print(make_tree(instantiated))
