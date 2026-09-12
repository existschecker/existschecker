from ast_types import RefFact, RefAxiom, RefTheorem, RefDefConExist, RefDefConUniq, RefDefFunExist, RefDefFunUniq, DeclarationContextNameSpace, Formula, Axiom, Theorem, DefCon, DefFun, ExistsUniq, RefDefCon, RefDefFun, Forall, Implies, AtomicFormula, Compound, Var, RefEquality
from logic_utils import Substitutor, collect_vars, fresh_var, strip_forall_vars, make_forall_vars

class DeclLogicError(Exception):
    def __init__(self, msg: str):
        self.msg = msg

def make_formula_from_fact(fact: RefFact, decl: DeclarationContextNameSpace) -> Formula:
    if isinstance(fact, RefAxiom):
        formula = decl.get_ast(Axiom, fact.name).conclusion
    elif isinstance(fact, RefTheorem):
        formula = decl.get_ast(Theorem, fact.name).conclusion
    elif isinstance(fact, RefDefConExist):
        existsuniq = decl.get_ast(Theorem, decl.get_ast(DefCon, fact.parent.name).ref_theorem.name).conclusion
        if not isinstance(existsuniq, ExistsUniq):
            raise DeclLogicError(f"conclusion of theorem for constant {fact.parent.name} is not a form of \\exists! ...")
        formula = Substitutor(({existsuniq.var: RefDefCon(fact.parent.name)}, {}, {})).substitute_formula(existsuniq.body)
    elif isinstance(fact, RefDefConUniq):
        existsuniq = decl.get_ast(Theorem, decl.get_ast(DefCon, fact.parent.name).ref_theorem.name).conclusion
        if not isinstance(existsuniq, ExistsUniq):
            raise DeclLogicError(f"conclusion of theorem for constant {fact.parent.name} is not a form of \\exists! ...")
        fv, bv, fpt, bpt, fft, bft = collect_vars(existsuniq.body)
        var = fresh_var(existsuniq.var, fv | bv | fpt | bpt | fft | bft)
        body = Substitutor(({existsuniq.var: var}, {}, {})).substitute_formula(existsuniq.body)
        equality = decl.get_equality()
        if equality is None:
            raise DeclLogicError("uniqueness requires equality, but equality has not been declared yet")
        formula = Forall(var, Implies(body, AtomicFormula(RefEquality(equality.ref.name), (var, RefDefCon(fact.parent.name)))))
    elif isinstance(fact, RefDefFunExist):
        args, body = strip_forall_vars(decl.get_ast(Theorem, decl.get_ast(DefFun, fact.parent.name).ref_theorem.name).conclusion)
        if isinstance(body, ExistsUniq):
            existence_formula = Substitutor(({body.var: Compound(RefDefFun(fact.parent.name), tuple(args))}, {}, {})).substitute_formula(body.body)
        elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
            existence_formula = Implies(body.left, Substitutor(({body.right.var: Compound(RefDefFun(fact.parent.name), tuple(args))}, {}, {})).substitute_formula(body.right.body))
        else:
            raise DeclLogicError(f"conclusion of theorem for function {fact.parent.name} is not a form of \\forall ... \\forall \\exists! ...")
        formula = make_forall_vars(existence_formula, args)
    elif isinstance(fact, RefDefFunUniq):
        args, body = strip_forall_vars(decl.get_ast(Theorem, decl.get_ast(DefFun, fact.parent.name).ref_theorem.name).conclusion)
        equality = decl.get_equality()
        if equality is None:
            raise DeclLogicError("uniqueness requires equality, but equality has not been declared yet")
        if isinstance(body, ExistsUniq):
            uniqueness_formula = Forall(body.var, Implies(body.body, AtomicFormula(RefEquality(equality.ref.name), (Var(body.var.name), Compound(RefDefFun(fact.parent.name), tuple(args))))))
        elif isinstance(body, Implies) and isinstance(body.right, ExistsUniq):
            uniqueness_formula = Implies(body.left, Forall(body.right.var, Implies(body.right.body, AtomicFormula(RefEquality(equality.ref.name), (Var(body.right.var.name), Compound(RefDefFun(fact.parent.name), tuple(args)))))))
        else:
            raise DeclLogicError(f"conclusion of theorem for function {fact.parent.name} is not a form of \\forall ... \\forall \\exists! ...")
        formula = make_forall_vars(uniqueness_formula, args)
    else:
        raise DeclLogicError(f"Unexpected type {type(fact)}")
    return formula
