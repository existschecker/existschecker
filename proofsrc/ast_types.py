from dataclasses import dataclass

import logging
logger = logging.getLogger("proof")

@dataclass
class Context:
    formulas: list        # 通常の論理式
    primpreds: dict[str, "PrimPred"]
    axioms: dict[str, "Axiom"]
    theorems: dict[str, "Theorem"]
    defpreds: dict[str, "DefPred"]
    defcons: dict[str, "DefCon"]
    deffuns: dict[str, "DefFun"]
    deffunterms: dict[str, "DefFunTerm"]
    equality: "Equality | None"

    @staticmethod
    def init() -> "Context":
        return Context(formulas=[], primpreds={}, axioms={}, theorems={}, defpreds={}, defcons={}, deffuns={}, deffunterms={}, equality=None)

    def copy(self, formulas) -> "Context":
        return Context(formulas=formulas, primpreds=self.primpreds, axioms=self.axioms, theorems=self.theorems, defpreds=self.defpreds, defcons=self.defcons, deffuns=self.deffuns, deffunterms=self.deffunterms, equality=self.equality)

    def has_defcon_existence(self, existence_name: str) -> bool:
        for defcon in self.defcons.values():
            if defcon.existence.name == existence_name:
                return True
        return False

    def get_defcon_existence(self, existence_name: str):
        for defcon in self.defcons.values():
            if defcon.existence.name == existence_name:
                return defcon.existence
        raise KeyError(f"Unexpected existence_name: {existence_name}")

    def has_defcon_uniqueness(self, uniqueness_name: str) -> bool:
        for defcon in self.defcons.values():
            if defcon.uniqueness.name == uniqueness_name:
                return True
        return False

    def get_defcon_uniqueness(self, uniqueness_name: str):
        for defcon in self.defcons.values():
            if defcon.uniqueness.name == uniqueness_name:
                return defcon.uniqueness
        raise KeyError(f"Unexpected uniqueness_name: {uniqueness_name}")

    def has_deffun_existence(self, existence_name: str) -> bool:
        for deffun in self.deffuns.values():
            if deffun.existence.name == existence_name:
                return True
        return False

    def get_deffun_existence(self, existence_name: str):
        for deffun in self.deffuns.values():
            if deffun.existence.name == existence_name:
                return deffun.existence
        raise KeyError(f"Unexpected existence_name: {existence_name}")

    def has_deffun_uniqueness(self, uniqueness_name: str) -> bool:
        for deffun in self.deffuns.values():
            if deffun.uniqueness.name == uniqueness_name:
                return True
        return False

    def get_deffun_uniqueness(self, uniqueness_name: str):
        for deffun in self.deffuns.values():
            if deffun.uniqueness.name == uniqueness_name:
                return deffun.uniqueness
        raise KeyError(f"Unexpected uniqueness_name: {uniqueness_name}")

# === DSL ノード定義 ===
@dataclass
class PrimPred:
    type: str
    name: str
    arity: int

@dataclass
class Axiom:
    name: str
    conclusion: object

@dataclass
class Theorem:
    name: str
    conclusion: object
    proof: list

@dataclass
class Check:
    conclusion: object   # Expr AST

@dataclass
class Assume:
    premise: object      # Expr AST
    conclusion: object | None  # Expr AST
    body: list

@dataclass
class Any:
    vars: list["Var"]
    conclusion: object | None
    body: list

@dataclass
class Divide:
    fact: object
    conclusion: object | None
    cases: list

@dataclass
class Case:
    premise: object
    conclusion: object | None
    body: list

@dataclass
class Some:
    env: dict["Var", "Var"]
    fact: object
    conclusion: object | None
    body: list

@dataclass
class Deny:
    premise: object
    body: list

@dataclass
class Contradict:
    contradiction: object

@dataclass
class Explode:
    conclusion: object

@dataclass
class Apply:
    fact: object
    env: dict["Var", "Compound | Con | Var"]
    conclusion: object | None

@dataclass
class Lift:
    fact: object | None
    env: dict["Var", "Term"]
    conclusion: object

@dataclass
class Characterize:
    fact: object
    env: dict["Var", "Term"]
    conclusion: object | None

@dataclass
class Invoke:
    fact: object
    conclusion: object | None

@dataclass
class Expand:
    fact: object
    conclusion: object

@dataclass
class Pad:
    fact: object
    conclusion: object

@dataclass
class Split:
    fact: object

@dataclass
class Connect:
    conclusion: object

@dataclass
class Substitute:
    fact: object
    env: dict["Term", "Term"]
    conclusion: object | None

@dataclass
class Show:
    conclusion: object
    body: list

@dataclass
class DefPred:
    name: str
    args: list["Var"]
    formula: object
    autoexpand: bool

@dataclass
class DefCon:
    name: str
    theorem: str
    existence: "DefConExist"
    uniqueness: "DefConUniq"

@dataclass
class DefConExist:
    name: str
    formula: object

@dataclass
class DefConUniq:
    name: str
    formula: object

@dataclass
class DefFun:
    name: str
    arity: int
    theorem: str
    existence: "DefFunExist"
    uniqueness: "DefFunUniq"

@dataclass
class DefFunExist:
    name: str
    formula: object

@dataclass
class DefFunUniq:
    name: str
    formula: object

@dataclass
class DefFunTerm:
    name: str
    args: list["Var"]
    term: object

@dataclass
class Equality:
    equal: PrimPred | DefPred
    reflection: Axiom | Theorem
    replacement: dict[str, Axiom | Theorem]

@dataclass(frozen=True)
class Term():
    pass

@dataclass
class Formula:
    pass

@dataclass
class Symbol(Formula):
    pred: "Pred"
    args: list[Term]

@dataclass
class Pred:
    name: str

@dataclass(frozen=True)
class Compound(Term):
    fun: "Fun"
    args: tuple[Term, ...]

@dataclass(frozen=True)
class Fun:
    name: str

@dataclass(frozen=True)
class Con(Term):
    name: str

@dataclass(frozen=True)
class Var(Term):
    name: str

@dataclass
class Forall(Formula):
    var: Var
    body: object

@dataclass
class Exists(Formula):
    var: Var
    body: object

@dataclass
class ExistsUniq(Formula):
    var: Var
    body: object

@dataclass
class Implies(Formula):
    left: object
    right: object

@dataclass
class And(Formula):
    left: object
    right: object

@dataclass
class Or(Formula):
    left: object
    right: object

@dataclass
class Not(Formula):
    body: object

@dataclass
class Iff(Formula):
    left: object
    right: object

@dataclass
class Bottom:
    pass

def pretty_expr(expr):
    if isinstance(expr, Axiom):
        return expr.name
    if isinstance(expr, Theorem):
        return expr.name
    if isinstance(expr, DefConExist):
        return expr.name
    if isinstance(expr, DefConUniq):
        return expr.name
    if isinstance(expr, DefFunExist):
        return expr.name
    if isinstance(expr, DefFunUniq):
        return expr.name
    if isinstance(expr, Symbol):
        return f"{pretty_expr(expr.pred)}({",".join([pretty_expr(arg) for arg in expr.args])})"
    if isinstance(expr, Pred):
        return expr.name
    if isinstance(expr, Compound):
        return f"{pretty_expr(expr.fun)}({','.join([pretty_expr(arg) for arg in expr.args])})"
    if isinstance(expr, Fun):
        return expr.name
    if isinstance(expr, Con):
        return expr.name
    if isinstance(expr, Var):
        return expr.name
    if isinstance(expr, Implies):
        return f"{pretty_expr(expr.left)} \\to {pretty_expr(expr.right)}"
    if isinstance(expr, Iff):
        return f"{pretty_expr(expr.left)} \\leftrightarrow {pretty_expr(expr.right)}"
    if isinstance(expr, And):
        return f"{pretty_expr(expr.left)} \\wedge {pretty_expr(expr.right)}"
    if isinstance(expr, Or):
        return f"{pretty_expr(expr.left)} \\vee {pretty_expr(expr.right)}"
    if isinstance(expr, Not):
        return f"\\neg({pretty_expr(expr.body)})"
    if isinstance(expr, Forall):
        return f"\\forall {expr.var.name}({pretty_expr(expr.body)})"
    if isinstance(expr, Exists):
        return f"\\exists {expr.var.name}({pretty_expr(expr.body)})"
    if isinstance(expr, ExistsUniq):
        return f"\\exists! {expr.var.name}({pretty_expr(expr.body)})"
    if isinstance(expr, Bottom):
        return "\\bot"
    raise TypeError(f"Unsupported node type: {type(expr)}")
