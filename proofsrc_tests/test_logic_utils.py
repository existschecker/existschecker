from logic_utils import alpha_safe_formula, Substitutor, beta_reduction_formula, mapping_adapter
from ast_types import Term, Var, PredTemplate, PredLambda, AtomicFormula, Not

def test_predicate_lambda_substitution():
    x = Var("x")
    p = PredTemplate("p", 1)
    formula = AtomicFormula(p, (x,))
    mapping: dict[Term, Term] = {p: PredLambda((x,), Not(AtomicFormula(p, (x,))))}

    renamed_formula = alpha_safe_formula(formula, mapping)
    substituted = beta_reduction_formula(Substitutor(mapping_adapter(mapping)).substitute_formula(renamed_formula))

    assert renamed_formula == AtomicFormula(p, (x,))
    assert substituted == Not(AtomicFormula(p, (x,)))
