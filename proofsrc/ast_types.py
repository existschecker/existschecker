from lexer import Token
from dataclasses import dataclass, field
from typing import Sequence, Literal

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

@dataclass(frozen=True)
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

@dataclass
class FormulaContext:
    vars: list[Var]
    templates: list[Template]
    used_names: set[str]

    @staticmethod
    def init() -> "FormulaContext":
        return FormulaContext(vars=[], templates=[], used_names=set())

    def copy(self) -> "FormulaContext":
        return FormulaContext(list(self.vars), list(self.templates), self.used_names.copy())

    def add(self, new_vars: list[Var], new_templates: list[Template]) -> "FormulaContext":
        new_used_names = self.used_names.copy()
        for item in new_vars + new_templates:
            if item.name in new_used_names:
                raise Exception(f"{item.name} is already used")
            new_used_names.add(item.name)
        return FormulaContext(list(self.vars + new_vars), list(self.templates + new_templates), new_used_names)

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
class ControlContext:
    vars: list[Var]
    formulas: list[Bottom | Formula]
    templates: list[Template]
    used_names: set[str]

    @staticmethod
    def init() -> "ControlContext":
        return ControlContext(vars=[], formulas=[], templates=[], used_names=set())

    def copy(self) -> "ControlContext":
        return ControlContext(list(self.vars), list(self.formulas), list(self.templates), self.used_names.copy())

    def add(self, new_vars: list[Var], new_formulas: list[Bottom | Formula], new_templates: list[Template]) -> "ControlContext":
        new_used_names = self.used_names.copy()
        for item in new_vars + new_templates:
            if item.name in new_used_names:
                raise Exception(f"{item.name} is already used")
            new_used_names.add(item.name)
        return ControlContext(list(self.vars + new_vars), list(self.formulas + new_formulas), list(self.templates + new_templates), new_used_names)

@dataclass
class ProofInfo:
    status: Literal["UNCHECKED", "OK", "ERROR"] = field(init=False, default="UNCHECKED")
    ctrl_ctx: ControlContext = field(init=False, default_factory=ControlContext.init)
    premises: Sequence[str | Bottom | Formula] = field(init=False, default_factory=list[str | Bottom | Formula])
    conclusions: Sequence[Bottom | Formula] = field(init=False, default_factory=list[Bottom | Formula])
    local_vars: Sequence[Var] = field(init=False, default_factory=list[Var])
    local_premise: Sequence[Formula] = field(init=False, default_factory=list[Formula])
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
    items: list[Var | Template | None]
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
    args: list[Var | Template]
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
    args: list[Var | Template]
    returned: Var | Template
    theorem: str
    tex: list[str]

@dataclass
class DefFunTerm(Declaration):
    args: list[Var | Template]
    term: Term
    tex: list[str]

@dataclass
class EqualityReflection(DeclarationSupport):
    equal: PrimPred | DefPred
    evidence: Axiom | Theorem

@dataclass
class EqualityReplacement(DeclarationSupport):
    equal: PrimPred | DefPred
    evidence: dict[str, Axiom | Theorem]

@dataclass
class Equality(Declaration):
    equal: PrimPred | DefPred
    reflection: EqualityReflection
    replacement: EqualityReplacement

@dataclass
class Membership(Declaration):
    membership: PrimPred | DefPred
    extensionality: str

@dataclass
class DeclarationContext:
    primpreds: dict[str, PrimPred]
    axioms: dict[str, Axiom]
    theorems: dict[str, Theorem]
    defpreds: dict[str, list[DefPred]]
    defcons: dict[str, DefCon]
    defconexists: dict[str, DefConExist]
    defconuniqs: dict[str, DefConUniq]
    deffuns: dict[str, DefFun]
    deffunexists: dict[str, DefFunExist]
    deffununiqs: dict[str, DefFunUniq]
    deffunterms: dict[str, DefFunTerm]
    equality: Equality | None
    membership: Membership | None
    used_names: set[str]

    @staticmethod
    def init() -> "DeclarationContext":
        return DeclarationContext(primpreds={}, axioms={}, theorems={}, defpreds={}, defcons={}, defconexists={}, defconuniqs={}, deffuns={}, deffunexists={}, deffununiqs={}, deffunterms={}, equality=None, membership=None, used_names=set())

    def get_type_of(self, item: Term) -> type[Var] | tuple[type[Template], int]:
        if isinstance(item, (Var, Con)):
            return Var
        elif isinstance(item, Template):
            return Template, item.arity
        elif isinstance(item, Lambda):
            return Template, len(item.args)
        elif isinstance(item, Compound):
            if item.fun.name in self.deffuns:
                return self.get_type_of(self.get_deffun(item.fun.name, item.args).returned)
            elif item.fun.name in self.deffunterms:
                return self.get_type_of(self.get_deffunterm(item.fun.name, item.args).term)
            else:
                raise Exception(f"Unexpected function name: {item.fun.name}")
        else:
            raise Exception(f"Unexpected type: {type(item)}")

    def match_signature(self, args1: Sequence[Term], args2: Sequence[Term]) -> bool:
        if len(args1) != len(args2):
            return False
        for arg1, arg2 in zip(args1, args2):
            if self.get_type_of(arg1) != self.get_type_of(arg2):
                return False
        return True

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
            if declaration.name in self.defpreds:
                for existing in self.defpreds[declaration.name]:
                    if self.match_signature(existing.args, declaration.args):
                        raise Exception(f"Overload of {declaration.name} with the same signature")
            else:
                self.defpreds[declaration.name] = []
            self.defpreds[declaration.name].append(declaration)
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

    def match_defpred(self, name: str, args: Sequence[Term]) -> bool:
        if name in self.defpreds:
            for existing in self.defpreds[name]:
                if self.match_signature(existing.args, args):
                    return True
            return False
        else:
            return False

    def get_defpred(self, name: str, args: Sequence[Term]) -> DefPred:
        if name in self.defpreds:
            for existing in self.defpreds[name]:
                if self.match_signature(existing.args, args):
                    return existing
            raise Exception(f"{name} is found in defpreds, but signature is not matched")
        else:
            raise Exception(f"{name} is not found in defpreds")

    def get_deffun(self, name: str, args: Sequence[Term]) -> DefFun:
        if name in self.deffuns:
            existing = self.deffuns[name]
            if self.match_signature(existing.args, args):
                return existing
            else:
                raise Exception(f"{name} is found in deffuns, but signature is not matched")
        else:
            raise Exception(f"{name} is not found in deffuns")

    def get_deffunterm(self, name: str, args: Sequence[Term]) -> DefFunTerm:
        if name in self.deffunterms:
            existing = self.deffunterms[name]
            if self.match_signature(existing.args, args):
                return existing
            else:
                raise Exception(f"{name} is found in deffunterms, but signature is not matched")
        else:
            raise Exception(f"{name} is not found in deffunterms")

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

    def add_ctrl(self, new_vars: list[Var], new_formulas: list[Bottom | Formula], new_templates: list[Template]):
        return Context(self.decl, self.ctrl.add(new_vars, new_formulas, new_templates), self.form)

    def copy_form(self):
        return Context(self.decl, self.ctrl, self.form.copy())

    def add_form(self, new_vars: list[Var], new_templates: list[Template]):
        return Context(self.decl, self.ctrl, self.form.add(new_vars, new_templates))

@dataclass
class Include:
    file: str
