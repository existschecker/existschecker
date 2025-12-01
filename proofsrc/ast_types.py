from dataclasses import dataclass, field
from typing import Sequence

import logging
logger = logging.getLogger("proof")

@dataclass(frozen=True)
class Term():
    pass

@dataclass(frozen=True)
class Fun:
    name: str

@dataclass(frozen=True)
class Compound(Term):
    fun: Fun
    args: tuple[Term, ...]

@dataclass(frozen=True)
class Con(Term):
    name: str

@dataclass(frozen=True)
class Var(Term):
    name: str

@dataclass(frozen=True)
class Formula:
    pass

@dataclass
class Pred:
    name: str

@dataclass(frozen=True)
class Symbol(Formula):
    pred: Pred
    args: tuple[Term, ...]

@dataclass(frozen=True)
class Template(Term):
    name: str
    arity: int

@dataclass(frozen=True)
class TemplateCall(Formula):
    template: Template
    args: tuple[Term, ...]

    def __post_init__(self):
        if len(self.args) != self.template.arity:
            raise Exception(f"arity of {self.template.name} is {self.template.arity}, but length of args is {len(self.args)}")

@dataclass(frozen=True)
class Lambda(Term):
    args: tuple[Var, ...]
    body: Formula

@dataclass(frozen=True)
class Forall(Formula):
    var: Var | Template
    body: Formula

@dataclass(frozen=True)
class Exists(Formula):
    var: Var | Template
    body: Formula

@dataclass(frozen=True)
class ExistsUniq(Formula):
    var: Var | Template
    body: Formula

@dataclass(frozen=True)
class Implies(Formula):
    left: Formula
    right: Formula

@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula

@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula

@dataclass(frozen=True)
class Not(Formula):
    body: Formula

@dataclass(frozen=True)
class Iff(Formula):
    left: Formula
    right: Formula

@dataclass(frozen=True)
class Bottom:
    pass

@dataclass
class ProofInfo:
    context_vars: Sequence[Var] = field(init=False)
    context_formulas: Sequence[Bottom | Formula] = field(init=False)
    premises: Sequence[str | Bottom | Formula] = field(init=False)
    conclusions: Sequence[Bottom | Formula] = field(init=False)
    local_vars: Sequence[Var] = field(init=False)
    local_premise: Sequence[Formula] = field(init=False)
    local_conclusion: Sequence[Bottom | Formula] = field(init=False)

@dataclass
class Control:
    proofinfo: ProofInfo = field(init=False)

@dataclass
class Assume(Control):
    premise: Formula
    body: list[Control]

@dataclass
class Any(Control):
    items: list[Var | Template]
    body: list[Control]

@dataclass
class Case(Control):
    premise: Formula
    body: list[Control]

@dataclass
class Divide(Control):
    fact: str | Formula
    cases: list[Case]

@dataclass
class Some(Control):
    env: dict[Var, Var]
    fact: str | Formula
    conclusion: Bottom | Formula | None
    body: list[Control]

@dataclass
class Deny(Control):
    premise: Formula
    body: list[Control]

@dataclass
class Contradict(Control):
    contradiction: Formula

@dataclass
class Explode(Control):
    conclusion: Formula

@dataclass
class Apply(Control):
    fact: str | Formula
    env: dict[str, Term]
    conclusion: Formula | None

@dataclass
class Lift(Control):
    fact: Formula | None
    env: dict[Var, Term]
    conclusion: Exists

@dataclass
class Characterize(Control):
    fact: Formula | None
    env: dict[Var, Term]
    conclusion: ExistsUniq

@dataclass
class Invoke(Control):
    fact: Implies
    conclusion: Formula | None

@dataclass
class Expand(Control):
    fact: str | Formula
    defs: list[str]
    conclusion: Formula

@dataclass
class Pad(Control):
    fact: str | Formula
    conclusion: Or

@dataclass
class Split(Control):
    index: int | None
    fact: And | Iff

@dataclass
class Connect(Control):
    conclusion: And | Iff

@dataclass
class Substitute(Control):
    fact: str | Formula
    env: dict[Term, Term]
    evidence: dict[Term, str]
    conclusion: Formula

@dataclass
class Show(Control):
    conclusion: Bottom | Formula
    body: list[Control]

@dataclass
class Declaration:
    pass

@dataclass
class DeclarationSupport:
    pass

@dataclass
class PrimPred(Declaration):
    name: str
    arity: int
    tex: list[str]

@dataclass
class Axiom(Declaration):
    name: str
    conclusion: Formula

@dataclass
class Theorem(Declaration):
    name: str
    conclusion: Formula
    proof: list[Control]

@dataclass
class DefPred(Declaration):
    name: str
    args: list[Var]
    formula: Formula
    autoexpand: bool
    tex: list[str]

@dataclass
class DefConExist(DeclarationSupport):
    name: str
    formula: Formula

@dataclass
class DefConUniq(DeclarationSupport):
    name: str
    formula: Formula

@dataclass
class DefCon(Declaration):
    name: str
    theorem: str
    tex: list[str]
    existence: DefConExist | None
    uniqueness: DefConUniq | None

@dataclass
class DefFunExist(DeclarationSupport):
    name: str
    formula: Formula

@dataclass
class DefFunUniq(DeclarationSupport):
    name: str
    formula: Formula

@dataclass
class DefFun(Declaration):
    name: str
    arity: int
    theorem: str
    tex: list[str]
    existence: DefFunExist | None
    uniqueness: DefFunUniq | None

@dataclass
class DefFunTerm(Declaration):
    name: str
    args: list[Var]
    term: Term
    tex: list[str]

@dataclass
class EqualityReflection(DeclarationSupport):
    evidence: Axiom | Theorem

@dataclass
class EqualityReplacement(DeclarationSupport):
    evidence: dict[str, Axiom | Theorem]

@dataclass
class Equality(Declaration):
    equal: PrimPred | DefPred
    reflection: EqualityReflection
    replacement: EqualityReplacement

@dataclass
class Context:
    vars: list[Var]
    formulas: list[Bottom | Formula]
    primpreds: dict[str, PrimPred]
    templates: list[Template]
    axioms: dict[str, Axiom]
    theorems: dict[str, Theorem]
    defpreds: dict[str, DefPred]
    defcons: dict[str, DefCon]
    deffuns: dict[str, DefFun]
    deffunterms: dict[str, DefFunTerm]
    equality: Equality | None

    @staticmethod
    def init() -> "Context":
        return Context(vars=[], formulas=[], templates=[], primpreds={}, axioms={}, theorems={}, defpreds={}, defcons={}, deffuns={}, deffunterms={}, equality=None)

    def copy(self, vars: list[Var], formulas: list[Bottom | Formula], templates: list[Template]) -> "Context":
        return Context(vars=vars, formulas=formulas, templates=templates, primpreds=self.primpreds, axioms=self.axioms, theorems=self.theorems, defpreds=self.defpreds, defcons=self.defcons, deffuns=self.deffuns, deffunterms=self.deffunterms, equality=self.equality)

    def has_reference(self, name: str) -> bool:
        return name in self.axioms or name in self.theorems or self.has_defcon_existence(name) or self.has_defcon_uniqueness(name) or self.has_deffun_existence(name) or self.has_deffun_uniqueness(name)

    def get_reference(self, name: str) -> Formula:
        if name in self.axioms:
            return self.axioms[name].conclusion
        elif name in self.theorems:
            return self.theorems[name].conclusion
        elif self.has_defcon_existence(name):
            return self.get_defcon_existence(name).formula
        elif self.has_defcon_uniqueness(name):
            return self.get_defcon_uniqueness(name).formula
        elif self.has_deffun_existence(name):
            return self.get_deffun_existence(name).formula
        elif self.has_deffun_uniqueness(name):
            return self.get_deffun_uniqueness(name).formula
        else:
            raise Exception(f"Unexpected name: {name}")

    def has_defcon_existence(self, existence_name: str) -> bool:
        for defcon in self.defcons.values():
            if defcon.existence is not None and defcon.existence.name == existence_name:
                return True
        return False

    def get_defcon_existence(self, existence_name: str):
        for defcon in self.defcons.values():
            if defcon.existence is not None and defcon.existence.name == existence_name:
                return defcon.existence
        raise KeyError(f"Unexpected existence_name: {existence_name}")

    def has_defcon_uniqueness(self, uniqueness_name: str) -> bool:
        for defcon in self.defcons.values():
            if defcon.uniqueness is not None and defcon.uniqueness.name == uniqueness_name:
                return True
        return False

    def get_defcon_uniqueness(self, uniqueness_name: str):
        for defcon in self.defcons.values():
            if defcon.uniqueness is not None and defcon.uniqueness.name == uniqueness_name:
                return defcon.uniqueness
        raise KeyError(f"Unexpected uniqueness_name: {uniqueness_name}")

    def has_deffun_existence(self, existence_name: str) -> bool:
        for deffun in self.deffuns.values():
            if deffun.existence is not None and deffun.existence.name == existence_name:
                return True
        return False

    def get_deffun_existence(self, existence_name: str):
        for deffun in self.deffuns.values():
            if deffun.existence is not None and deffun.existence.name == existence_name:
                return deffun.existence
        raise KeyError(f"Unexpected existence_name: {existence_name}")

    def has_deffun_uniqueness(self, uniqueness_name: str) -> bool:
        for deffun in self.deffuns.values():
            if deffun.uniqueness is not None and deffun.uniqueness.name == uniqueness_name:
                return True
        return False

    def get_deffun_uniqueness(self, uniqueness_name: str):
        for deffun in self.deffuns.values():
            if deffun.uniqueness is not None and deffun.uniqueness.name == uniqueness_name:
                return deffun.uniqueness
        raise KeyError(f"Unexpected uniqueness_name: {uniqueness_name}")

OP_PRECEDENCE = {
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
        if expr.name in context.primpreds:
            tex = context.primpreds[expr.name].tex
        elif expr.name in context.defpreds:
            tex = context.defpreds[expr.name].tex
        else:
            raise Exception(f"{expr.name} is not in primpreds or defpreds")
        return tex
    elif isinstance(expr, Fun):
        if expr.name in context.deffuns:
            tex = context.deffuns[expr.name].tex
        elif expr.name in context.deffunterms:
            tex = context.deffunterms[expr.name].tex
        else:
            raise Exception(f"{expr.name} is not in deffuns or deffunterms")
        return tex
    else:
        raise TypeError(f"Unsupported node type: {type(expr)}")

def pretty_expr(expr: str | Bottom | Formula | Term, context: Context, parent_prec: int = OP_PRECEDENCE["Lowest"]) -> str:
    if isinstance(expr, str):
        return expr
    elif isinstance(expr, Var):
        return expr.name
    elif isinstance(expr, Con):
        if expr.name in context.defcons:
            tex = context.defcons[expr.name].tex
        else:
            raise Exception(f"{expr.name} is not in context.defcons")
        if len(tex) != 1:
            raise Exception("arity is different")
        return tex[0]
    elif isinstance(expr, Compound):
        tex = pretty_expr_fragments(expr.fun, context)
        if len(tex) != len(expr.args) + 1:
            raise Exception("arity is different")
        text = ""
        for i in range(len(expr.args)):
            text += tex[i]
            text += " "
            text += pretty_expr(expr.args[i], context)
            text += " "
        text += tex[-1]
        return text
    elif isinstance(expr, Symbol):
        tex = pretty_expr_fragments(expr.pred, context)
        if len(tex) != len(expr.args) + 1:
            raise Exception("arity is different")
        text = ""
        for i in range(len(expr.args)):
            text += tex[i]
            text += " "
            text += pretty_expr(expr.args[i], context)
            text += " "
        text += tex[-1]
        return text if OP_PRECEDENCE["Symbol"] > parent_prec else f"({text})"
    elif isinstance(expr, Not):
        text = f"\\neg {pretty_expr(expr.body, context, OP_PRECEDENCE["Not"])}"
        return text if OP_PRECEDENCE["Not"] > parent_prec else f"({text})"
    elif isinstance(expr, And):
        text = f"{pretty_expr(expr.left, context, OP_PRECEDENCE["And"])} \\wedge {pretty_expr(expr.right, context, OP_PRECEDENCE["And"])}"
        return text if OP_PRECEDENCE["And"] > parent_prec else f"({text})"
    elif isinstance(expr, Or):
        text = f"{pretty_expr(expr.left, context, OP_PRECEDENCE["Or"])} \\vee {pretty_expr(expr.right, context, OP_PRECEDENCE["Or"])}"
        return text if OP_PRECEDENCE["Or"] > parent_prec else f"({text})"
    elif isinstance(expr, Implies):
        text = f"{pretty_expr(expr.left, context, OP_PRECEDENCE["Implies"])} \\to {pretty_expr(expr.right, context, OP_PRECEDENCE["Implies"])}"
        return text if OP_PRECEDENCE["Implies"] > parent_prec else f"({text})"
    elif isinstance(expr, Iff):
        text = f"{pretty_expr(expr.left, context, OP_PRECEDENCE["Iff"])} \\leftrightarrow {pretty_expr(expr.right, context, OP_PRECEDENCE["Iff"])}"
        return text if OP_PRECEDENCE["Iff"] > parent_prec else f"({text})"
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
                qvars_text += f" {pretty_expr(body.var, context)}"
            elif isinstance(body.var, Template):
                qvars_text += f"^T {pretty_expr(body.var, context)}"
            else:
                raise Exception(f"Unexpected type: {type(body.var)}")
            body = body.body
        text = f"{qvars_text} {pretty_expr(body, context, OP_PRECEDENCE["Quantifier"])}"
        return text if OP_PRECEDENCE["Quantifier"] > parent_prec else f"({text})"
    elif isinstance(expr, Bottom):
        return "\\bot"
    elif isinstance(expr, Template):
        return f"{expr.name}[{str(expr.arity)}]"
    elif isinstance(expr, TemplateCall):
        if expr.template.arity == 0:
            return expr.template.name
        else:
            return f"{expr.template.name}({",".join([pretty_expr(arg, context) for arg in expr.args])})"
    elif isinstance(expr, Lambda):
        return f"\\lambda {",".join([var.name for var in expr.args])}. {pretty_expr(expr.body, context)}"
    else:
        raise TypeError(f"Unsupported node type: {type(expr)}")
