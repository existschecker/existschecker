from dataclasses import dataclass, field

import logging
logger = logging.getLogger("proof")

@dataclass
class Context:
    vars: list["Var"]
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
        return Context(vars=[], formulas=[], primpreds={}, axioms={}, theorems={}, defpreds={}, defcons={}, deffuns={}, deffunterms={}, equality=None)

    def copy(self, vars, formulas) -> "Context":
        return Context(vars=vars, formulas=formulas, primpreds=self.primpreds, axioms=self.axioms, theorems=self.theorems, defpreds=self.defpreds, defcons=self.defcons, deffuns=self.deffuns, deffunterms=self.deffunterms, equality=self.equality)

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
    tex: list[str]

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
class ProofInfo:
    context_vars: list = field(init=False)
    context_formulas: list = field(init=False)
    conclusions: list = field(init=False)

@dataclass
class Control:
    proofinfo: ProofInfo = field(init=False)

@dataclass
class Assume(Control):
    premise: object      # Expr AST
    conclusion: object | None  # Expr AST
    body: list

@dataclass
class Any(Control):
    vars: list["Var"]
    conclusion: object | None
    body: list

@dataclass
class Divide(Control):
    fact: object
    conclusion: object | None
    cases: list

@dataclass
class Case(Control):
    premise: object
    conclusion: object | None
    body: list

@dataclass
class Some(Control):
    env: dict["Var", "Var"]
    fact: object
    conclusion: object | None
    body: list

@dataclass
class Deny(Control):
    premise: object
    body: list

@dataclass
class Contradict(Control):
    contradiction: object

@dataclass
class Explode(Control):
    conclusion: object

@dataclass
class Apply(Control):
    fact: object
    env: dict["Var", "Compound | Con | Var"]
    conclusion: object | None

@dataclass
class Lift(Control):
    fact: object | None
    env: dict["Var", "Term"]
    conclusion: object

@dataclass
class Characterize(Control):
    fact: object | None
    env: dict["Var", "Term"]
    conclusion: object

@dataclass
class Invoke(Control):
    fact: object
    conclusion: object | None

@dataclass
class Expand(Control):
    fact: object
    conclusion: object

@dataclass
class Pad(Control):
    fact: object
    conclusion: object

@dataclass
class Split(Control):
    fact: object

@dataclass
class Connect(Control):
    conclusion: object

@dataclass
class Substitute(Control):
    fact: object
    env: dict["Term", "Term"]
    conclusion: object

@dataclass
class Show(Control):
    conclusion: object
    body: list

@dataclass
class DefPred:
    name: str
    args: list["Var"]
    formula: object
    autoexpand: bool
    tex: list[str]

@dataclass
class DefCon:
    name: str
    theorem: str
    tex: list[str]
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
    tex: list[str]
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
    tex: list[str]

@dataclass
class Equality:
    equal: PrimPred | DefPred
    reflection: "EqualityReflection"
    replacement: "EqualityReplacement"

@dataclass
class EqualityReflection:
    evidence: Axiom | Theorem

@dataclass
class EqualityReplacement:
    evidence: dict[str, Axiom | Theorem]

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

def pretty_expr(expr, context: Context, parent_prec: int = OP_PRECEDENCE["Lowest"]):
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
        tex = pretty_expr(expr.pred, context)
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
    if isinstance(expr, Pred):
        if expr.name in context.primpreds:
            tex = context.primpreds[expr.name].tex
        elif expr.name in context.defpreds:
            tex = context.defpreds[expr.name].tex
        else:
            raise Exception(f"{expr.name} is not in primpreds or defpreds")
        return tex
    if isinstance(expr, Compound):
        tex = pretty_expr(expr.fun, context)
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
    if isinstance(expr, Fun):
        if expr.name in context.deffuns:
            tex = context.deffuns[expr.name].tex
        elif expr.name in context.deffunterms:
            tex = context.deffunterms[expr.name].tex
        else:
            raise Exception(f"{expr.name} is not in deffuns or deffunterms")
        return tex
    if isinstance(expr, Con):
        if expr.name in context.defcons:
            tex = context.defcons[expr.name].tex
        else:
            raise Exception(f"{expr.name} is not in context.defcons")
        if len(tex) != 1:
            raise Exception("arity is different")
        return tex[0]
    if isinstance(expr, Var):
        return expr.name
    if isinstance(expr, Implies):
        text = f"{pretty_expr(expr.left, context, OP_PRECEDENCE["Implies"])} \\to {pretty_expr(expr.right, context, OP_PRECEDENCE["Implies"])}"
        return text if OP_PRECEDENCE["Implies"] > parent_prec else f"({text})"
    if isinstance(expr, Iff):
        text = f"{pretty_expr(expr.left, context, OP_PRECEDENCE["Iff"])} \\leftrightarrow {pretty_expr(expr.right, context, OP_PRECEDENCE["Iff"])}"
        return text if OP_PRECEDENCE["Iff"] > parent_prec else f"({text})"
    if isinstance(expr, And):
        text = f"{pretty_expr(expr.left, context, OP_PRECEDENCE["And"])} \\wedge {pretty_expr(expr.right, context, OP_PRECEDENCE["And"])}"
        return text if OP_PRECEDENCE["And"] > parent_prec else f"({text})"
    if isinstance(expr, Or):
        text = f"{pretty_expr(expr.left, context, OP_PRECEDENCE["Or"])} \\vee {pretty_expr(expr.right, context, OP_PRECEDENCE["Or"])}"
        return text if OP_PRECEDENCE["Or"] > parent_prec else f"({text})"
    if isinstance(expr, Not):
        text = f"\\neg {pretty_expr(expr.body, context, OP_PRECEDENCE["Not"])}"
        return text if OP_PRECEDENCE["Not"] > parent_prec else f"({text})"
    if isinstance(expr, (Forall, Exists, ExistsUniq)):
        body = expr
        qvars = []
        while True:
            if isinstance(body, (Forall, Exists, ExistsUniq)):
                qvars.append(type(body)(body.var, None))
                body = body.body
            else:
                break
        qvars_text = ""
        for qvar in qvars:
            if isinstance(qvar, Forall):
                q_text = "\\forall "
            elif isinstance(qvar, Exists):
                q_text = "\\exists "
            elif isinstance(qvar, ExistsUniq):
                q_text = "\\exists! "
            qvars_text += q_text + qvar.var.name
        text = f"{qvars_text} {pretty_expr(body, context, OP_PRECEDENCE["Quantifier"])}"
        return text if OP_PRECEDENCE["Quantifier"] > parent_prec else f"({text})"
    if isinstance(expr, Bottom):
        return "\\bot"
    raise TypeError(f"Unsupported node type: {type(expr)}")
