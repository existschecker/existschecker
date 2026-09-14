from logic_utils import alpha_safe_formula, Substitutor
from ast_types import Term, Var, PredTemplate, PredLambda, AtomicFormula, Not

def test_predicate_lambda_substitution():
    x = Var("x")
    p = PredTemplate("p", 1)
    p_0 = PredTemplate("p_0", 1)
    formula = AtomicFormula(p, (x,))
    mapping: dict[Term, Term] = {p: PredLambda((x,), Not(AtomicFormula(p, (x,))))}

    renamed_formula, renamed_mapping = alpha_safe_formula(formula, mapping)
    substituted = Substitutor(renamed_mapping).substitute_formula(renamed_formula)

    assert renamed_formula == AtomicFormula(p_0, (x,))
    assert renamed_mapping == ({}, {p_0: PredLambda((x,), Not(AtomicFormula(p, (x,))))}, {})
    assert substituted == Not(AtomicFormula(p, (x,)))
