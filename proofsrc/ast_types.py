from lexer import Token
from dataclasses import dataclass, field
from typing import Sequence, Literal

import logging
logger = logging.getLogger("proof")

@dataclass(frozen=True)
class Term:
    pass

@dataclass(frozen=True)
class Formula:
    pass

@dataclass(frozen=True)
class VarTerm(Term):
    pass

@dataclass(frozen=True)
class Var(VarTerm):
    name: str

@dataclass(frozen=True)
class RefDefCon(VarTerm):
    name: str

@dataclass(frozen=True)
class FunTerm(Term):
    pass

@dataclass(frozen=True)
class RefDefFun(FunTerm):
    name: str

@dataclass(frozen=True)
class RefDefFunTerm(FunTerm):
    name: str

@dataclass(frozen=True)
class RefDefFunTemplateTerm(FunTerm):
    name: str

@dataclass(frozen=True)
class FunTemplate(FunTerm):
    name: str
    arity: int

@dataclass(frozen=True)
class FunLambda(FunTerm):
    args: tuple[Var, ...]
    body: VarTerm

@dataclass(frozen=True)
class Compound(VarTerm):
    fun: FunTerm
    args: tuple[Term, ...]

@dataclass(frozen=True)
class PredTerm(Term):
    pass

@dataclass(frozen=True)
class RefPrimPred(PredTerm):
    name: str

@dataclass(frozen=True)
class RefDefPred(PredTerm):
    name: str

@dataclass(frozen=True)
class CompoundPredTerm(PredTerm):
    fun: RefDefFunTemplateTerm
    args: tuple[Term, ...]

@dataclass(frozen=True)
class PredTemplate(PredTerm):
    name: str
    arity: int

@dataclass(frozen=True)
class PredLambda(PredTerm):
    args: tuple[Var, ...]
    body: Formula

@dataclass(frozen=True)
class MembershipLambda(PredTerm):
    varterm: VarTerm

@dataclass
class FormulaContext:
    vars: list[Var]
    pred_tmpls: list[PredTemplate]
    fun_tmpls: list[FunTemplate]
    used_names: set[str]

    @staticmethod
    def init() -> "FormulaContext":
        return FormulaContext(vars=[], pred_tmpls=[], fun_tmpls=[], used_names=set())

    def copy(self) -> "FormulaContext":
        return FormulaContext(list(self.vars), list(self.pred_tmpls), list(self.fun_tmpls), self.used_names.copy())

    def add(self, new_vars: list[Var], new_pred_tmpls: list[PredTemplate], new_fun_tmpls: list[FunTemplate]) -> "FormulaContext":
        new_used_names = self.used_names.copy()
        for item in new_vars + new_pred_tmpls + new_fun_tmpls:
            if item.name in new_used_names:
                raise Exception(f"{item.name} is already used")
            new_used_names.add(item.name)
        return FormulaContext(list(self.vars + new_vars), list(self.pred_tmpls + new_pred_tmpls), list(self.fun_tmpls + new_fun_tmpls), new_used_names)

@dataclass(frozen=True)
class AtomicFormula(Formula):
    pred: PredTerm
    args: tuple[Term, ...]

@dataclass(frozen=True)
class Not(Formula):
    body: Formula

@dataclass(frozen=True)
class And(Formula):
    left: Formula
    right: Formula

@dataclass(frozen=True)
class Or(Formula):
    left: Formula
    right: Formula

@dataclass(frozen=True)
class Implies(Formula):
    left: Formula
    right: Formula

@dataclass(frozen=True)
class Iff(Formula):
    left: Formula
    right: Formula

@dataclass(frozen=True)
class Forall(Formula):
    var: Var | PredTemplate | FunTemplate
    body: Formula

@dataclass(frozen=True)
class Exists(Formula):
    var: Var
    body: Formula

@dataclass(frozen=True)
class ExistsUniq(Formula):
    var: Var
    body: Formula

@dataclass(frozen=True)
class Bottom:
    pass

@dataclass
class ControlContext:
    vars: list[Var]
    formulas: list[Bottom | Formula]
    pred_tmpls: list[PredTemplate]
    fun_tmpls: list[FunTemplate]
    used_names: set[str]

    @staticmethod
    def init() -> "ControlContext":
        return ControlContext(vars=[], formulas=[], pred_tmpls=[], fun_tmpls=[], used_names=set())

    def copy(self) -> "ControlContext":
        return ControlContext(list(self.vars), list(self.formulas), list(self.pred_tmpls), list(self.fun_tmpls), self.used_names.copy())

    def add(self, new_vars: list[Var], new_formulas: list[Bottom | Formula], new_pred_tmpls: list[PredTemplate], new_fun_tmpls: list[FunTemplate]) -> "ControlContext":
        new_used_names = self.used_names.copy()
        for item in new_vars + new_pred_tmpls + new_fun_tmpls:
            if item.name in new_used_names:
                raise Exception(f"{item.name} is already used")
            new_used_names.add(item.name)
        return ControlContext(list(self.vars + new_vars), list(self.formulas + new_formulas), list(self.pred_tmpls + new_pred_tmpls), list(self.fun_tmpls + new_fun_tmpls), new_used_names)

@dataclass
class ProofInfo:
    status: Literal["UNCHECKED", "OK", "ERROR"] = field(init=False, default="UNCHECKED")
    ctrl_ctx: ControlContext = field(init=False, default_factory=ControlContext.init)
    premises: Sequence[str | Bottom | Formula] = field(init=False, default_factory=list[str | Bottom | Formula])
    conclusions: Sequence[Bottom | Formula] = field(init=False, default_factory=list[Bottom | Formula])
    local_vars: Sequence[Var] = field(init=False, default_factory=list[Var])
    local_premise: Sequence[Bottom | Formula] = field(init=False, default_factory=list[Formula])
    local_conclusion: Sequence[Bottom | Formula] = field(init=False, default_factory=list[Bottom | Formula])

@dataclass
class Control:
    token: Token
    proofinfo: ProofInfo = field(init=False, default_factory=ProofInfo)

@dataclass
class Assume(Control):
    premise: Formula
    body: list[Control]

@dataclass
class Any(Control):
    items: list[Var | PredTemplate | FunTemplate]
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
    items: list[Var | None]
    fact: str | Formula
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
    invoke: Literal["none", "invoke", "invoke-rightward", "invoke-leftward"]
    fact: str | Formula
    terms: list[Term | None]

@dataclass
class Lift(Control):
    terms: list[Term | None]
    conclusion: Exists

@dataclass
class Characterize(Control):
    term: Term
    conclusion: ExistsUniq

@dataclass
class Invoke(Control):
    direction: Literal["none", "rightward", "leftward"]
    fact: Implies | Iff

@dataclass
class Expand(Control):
    fact: str | Formula
    defs: list[str]
    indexes: dict[str, list[int]]

@dataclass
class Fold(Control):
    defs: list[str]
    indexes: dict[str, list[int]]
    conclusion: Formula

@dataclass
class Pad(Control):
    fact: str | Formula
    conclusion: Or

@dataclass
class Split(Control):
    index: int | None
    fact: str | Formula

@dataclass
class Connect(Control):
    conclusion: Formula

@dataclass
class Substitute(Control):
    fact: str | Formula
    env: dict[Term, Term]
    indexes: dict[Term, list[int]]

@dataclass
class Show(Control):
    conclusion: Bottom | Formula
    body: list[Control]

@dataclass
class Assert(Control):
    reference: str | Formula

@dataclass
class Declaration:
    name: str
    token: Token
    proofinfo: ProofInfo = field(init=False, default_factory=ProofInfo)

@dataclass
class DeclarationSupport:
    token: Token
    proofinfo: ProofInfo = field(init=False, default_factory=ProofInfo)

@dataclass
class PrimPred(Declaration):
    arity: int
    tex: list[str]

@dataclass
class Axiom(Declaration):
    conclusion: Formula

@dataclass
class Theorem(Declaration):
    conclusion: Formula
    proof: list[Control]

@dataclass
class DefPred(Declaration):
    args: list[Var | PredTemplate | FunTemplate]
    formula: Formula
    autoexpand: bool
    tex: list[str]

@dataclass
class DefConExist(Declaration):
    formula: Formula
    con_name: str

@dataclass
class DefConUniq(Declaration):
    formula: Formula
    con_name: str

@dataclass
class DefCon(Declaration):
    theorem: str
    tex: list[str]

@dataclass
class DefFunExist(Declaration):
    formula: Formula
    fun_name: str

@dataclass
class DefFunUniq(Declaration):
    formula: Formula
    fun_name: str

@dataclass
class DefFun(Declaration):
    args: list[Var | PredTemplate | FunTemplate]
    returned: Var | PredTemplate
    theorem: str
    tex: list[str]

@dataclass
class DefFunTerm(Declaration):
    args: list[Var | PredTemplate]
    term: Term
    tex: list[str]

@dataclass
class DefFunTemplateTerm(Declaration):
    args: list[Var | PredTemplate]
    term: PredLambda
    arity: int
    tex: list[str]

@dataclass
class EqualityReflection(DeclarationSupport):
    equal: RefPrimPred | RefDefPred
    evidence: Axiom | Theorem

@dataclass
class EqualityReplacement(DeclarationSupport):
    equal: RefPrimPred | RefDefPred
    evidence: dict[str, Axiom | Theorem]

@dataclass
class Equality(Declaration):
    equal: RefPrimPred | RefDefPred
    reflection: EqualityReflection
    replacement: EqualityReplacement

@dataclass
class Membership(Declaration):
    membership: RefPrimPred | RefDefPred

@dataclass
class DeclarationContext:
    primpreds: dict[str, PrimPred]
    axioms: dict[str, Axiom]
    theorems: dict[str, Theorem]
    defpreds: dict[str, DefPred]
    defcons: dict[str, DefCon]
    defconexists: dict[str, DefConExist]
    defconuniqs: dict[str, DefConUniq]
    deffuns: dict[str, DefFun]
    deffunexists: dict[str, DefFunExist]
    deffununiqs: dict[str, DefFunUniq]
    deffunterms: dict[str, DefFunTerm]
    deffuntemplateterms: dict[str, DefFunTemplateTerm]
    equality: Equality | None
    membership: Membership | None
    used_names: set[str]

    @staticmethod
    def init() -> "DeclarationContext":
        return DeclarationContext(primpreds={}, axioms={}, theorems={}, defpreds={}, defcons={}, defconexists={}, defconuniqs={}, deffuns={}, deffunexists={}, deffununiqs={}, deffunterms={}, deffuntemplateterms={}, equality=None, membership=None, used_names=set())

    def add(self, declaration: Declaration):
        if isinstance(declaration, Equality):
            if self.equality is not None:
                raise Exception("equality is already declared")
            self.equality = declaration
            return
        if isinstance(declaration, Membership):
            if self.membership is not None:
                raise Exception("membership is already declared")
            self.membership = declaration
            return
        if declaration.name in self.used_names:
            if not (isinstance(declaration, DefPred) and declaration.name in self.defpreds):
                raise Exception(f"{declaration.name} is already used")
        if isinstance(declaration, PrimPred):
            self.primpreds[declaration.name] = declaration
        elif isinstance(declaration, Axiom):
            self.axioms[declaration.name] = declaration
        elif isinstance(declaration, Theorem):
            self.theorems[declaration.name] = declaration
        elif isinstance(declaration, DefPred):
            self.defpreds[declaration.name] = declaration
        elif isinstance(declaration, DefCon):
            self.defcons[declaration.name] = declaration
        elif isinstance(declaration, DefConExist):
            self.defconexists[declaration.name] = declaration
        elif isinstance(declaration, DefConUniq):
            self.defconuniqs[declaration.name] = declaration
        elif isinstance(declaration, DefFun):
            self.deffuns[declaration.name] = declaration
        elif isinstance(declaration, DefFunExist):
            self.deffunexists[declaration.name] = declaration
        elif isinstance(declaration, DefFunUniq):
            self.deffununiqs[declaration.name] = declaration
        elif isinstance(declaration, DefFunTerm):
            self.deffunterms[declaration.name] = declaration
        elif isinstance(declaration, DefFunTemplateTerm):
            self.deffuntemplateterms[declaration.name] = declaration
        else:
            raise Exception(f"Unexpected type: {type(declaration)}")
        self.used_names.add(declaration.name)

    def has_reference(self, name: str) -> bool:
        return name in self.axioms or name in self.theorems or name in self.defconexists or name in self.defconuniqs or name in self.deffunexists or name in self.deffununiqs

    def get_reference(self, name: str) -> Formula:
        if name in self.axioms:
            return self.axioms[name].conclusion
        elif name in self.theorems:
            return self.theorems[name].conclusion
        elif name in self.defconexists:
            return self.defconexists[name].formula
        elif name in self.defconuniqs:
            return self.defconuniqs[name].formula
        elif name in self.deffunexists:
            return self.deffunexists[name].formula
        elif name in self.deffununiqs:
            return self.deffununiqs[name].formula
        else:
            raise Exception(f"Unexpected name: {name}")

@dataclass
class Context:
    decl: DeclarationContext
    ctrl: ControlContext
    form: FormulaContext

    @staticmethod
    def init() -> "Context":
        return Context(DeclarationContext.init(), ControlContext.init(), FormulaContext.init())

    def add_decl(self, declaration: Declaration):
        self.decl.add(declaration)

    def copy_ctrl(self):
        return Context(self.decl, self.ctrl.copy(), self.form)

    def add_ctrl(self, new_vars: list[Var], new_formulas: list[Bottom | Formula], new_pred_tmpls: list[PredTemplate], new_fun_tmpls: list[FunTemplate]):
        return Context(self.decl, self.ctrl.add(new_vars, new_formulas, new_pred_tmpls, new_fun_tmpls), self.form)

    def copy_form(self):
        return Context(self.decl, self.ctrl, self.form.copy())

    def add_form(self, new_vars: list[Var], new_pred_tmpls: list[PredTemplate], new_fun_tmpls: list[FunTemplate]):
        return Context(self.decl, self.ctrl, self.form.add(new_vars, new_pred_tmpls, new_fun_tmpls))

@dataclass
class Include:
    file: str
