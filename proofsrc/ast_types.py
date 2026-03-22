from lexer import Token
from dataclasses import dataclass, field
from lsprotocol import types as lsp
from typing import Sequence, Literal

import logging
logger = logging.getLogger("proof")

class ContextError(Exception):
    def __init__(self, msg: str) -> None:
        self.msg = msg

class LogicError(Exception):
    def __init__(self, msg: str) -> None:
        self.msg = msg

class FormatError(Exception):
    def __init__(self, msg: str) -> None:
        self.msg = msg

class RenderError(Exception):
    def __init__(self, msg: str) -> None:
        self.msg = msg

class TokenStreamError(Exception):
    def __init__(self, token: Token, msg: str) -> None:
        self.token = token
        self.msg = msg

class ParseError(Exception):
    def __init__(self, token: Token, msg: str):
        self.token = token
        self.msg = msg

class CheckError(Exception):
    def __init__(self, node: "Declaration | Control", msg: str) -> None:
        self.node = node
        self.msg = msg

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
class RefEquality(PredTerm):
    name: str

@dataclass(frozen=True)
class RefPrimPred(PredTerm):
    name: str

@dataclass(frozen=True)
class RefDefPred(PredTerm):
    name: str

@dataclass(frozen=True)
class PredTemplate(PredTerm):
    name: str
    arity: int

@dataclass(frozen=True)
class PredLambda(PredTerm):
    args: tuple[Var, ...]
    body: Formula

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
                msg = f"{item.name} is already used"
                raise ContextError(msg)
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
    symbols: list[Var | PredTemplate | FunTemplate]
    used_names: set[str]

    @staticmethod
    def init() -> "ControlContext":
        return ControlContext(vars=[], formulas=[], pred_tmpls=[], fun_tmpls=[], symbols=[], used_names=set())

    def copy(self) -> "ControlContext":
        return ControlContext(list(self.vars), list(self.formulas), list(self.pred_tmpls), list(self.fun_tmpls), list(self.symbols), self.used_names.copy())

    def add(self, new_vars: list[Var], new_formulas: list[Bottom | Formula], new_pred_tmpls: list[PredTemplate], new_fun_tmpls: list[FunTemplate], new_symbols: list[Var | PredTemplate | FunTemplate]) -> "ControlContext":
        new_used_names = self.used_names.copy()
        for item in new_vars + new_pred_tmpls + new_fun_tmpls:
            if item.name in new_used_names:
                msg = f"{item.name} is already used"
                raise ContextError(msg)
            new_used_names.add(item.name)
        return ControlContext(list(self.vars + new_vars), list(self.formulas + new_formulas), list(self.pred_tmpls + new_pred_tmpls), list(self.fun_tmpls + new_fun_tmpls), list(self.symbols + new_symbols), new_used_names)

@dataclass(frozen=True)
class RefFact:
    name: str

@dataclass(frozen=True)
class RefAxiom(RefFact):
    pass

@dataclass(frozen=True)
class RefTheorem(RefFact):
    pass

@dataclass(frozen=True)
class RefDefConExist(RefFact):
    pass

@dataclass(frozen=True)
class RefDefConUniq(RefFact):
    pass

@dataclass(frozen=True)
class RefDefFunExist(RefFact):
    pass

@dataclass(frozen=True)
class RefDefFunUniq(RefFact):
    pass

@dataclass
class ProofInfo:
    status: Literal["⚠️Unchecked", "✅Passed", "❌Failed"] = field(init=False, default="⚠️Unchecked")
    ctrl_ctx: ControlContext = field(init=False, default_factory=ControlContext.init)
    premises: Sequence[RefFact | Bottom | Formula] = field(init=False, default_factory=list[RefFact | Bottom | Formula])
    conclusions: Sequence[Bottom | Formula] = field(init=False, default_factory=list[Bottom | Formula])
    local_vars: Sequence[Var | PredTemplate | FunTemplate] = field(init=False, default_factory=list[Var | PredTemplate | FunTemplate])
    local_premise: Sequence[Bottom | Formula] = field(init=False, default_factory=list[Formula])
    local_conclusion: Sequence[Bottom | Formula] = field(init=False, default_factory=list[Bottom | Formula])

@dataclass
class Control:
    proofinfo: ProofInfo = field(init=False, default_factory=ProofInfo)

@dataclass
class InvalidControl(Control):
    pass

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
    fact: RefFact | Formula
    cases: list[Case]

@dataclass
class Some(Control):
    items: list[Var | None]
    fact: RefFact | Formula
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
    fact: RefFact | Formula
    terms: list[Term | None]

@dataclass
class Lift(Control):
    varterms: list[VarTerm | None]
    conclusion: Formula

@dataclass
class Characterize(Control):
    varterm: VarTerm
    conclusion: ExistsUniq

@dataclass
class Invoke(Control):
    direction: Literal["none", "rightward", "leftward"]
    fact: Implies | Iff

@dataclass
class Expand(Control):
    fact: RefFact | Formula
    refs: list[RefDefFunTerm | RefDefPred]
    indexes: dict[RefDefFunTerm | RefDefPred, list[int]]

@dataclass
class Fold(Control):
    refs: list[RefDefFunTerm | RefDefPred]
    indexes: dict[RefDefFunTerm | RefDefPred, list[int]]
    conclusion: Formula

@dataclass
class Pad(Control):
    fact: RefFact | Formula
    conclusion: Formula

@dataclass
class Split(Control):
    index: int | None
    fact: RefFact | Formula

@dataclass
class Connect(Control):
    conclusion: Formula

@dataclass
class Substitute(Control):
    fact: RefFact | Formula
    env: dict[Term, Term]
    indexes: dict[Term, list[int]]

@dataclass
class Show(Control):
    conclusion: Bottom | Formula
    body: list[Control]

@dataclass
class Assert(Control):
    reference: RefFact | Formula

@dataclass
class Declaration:
    name: str
    proofinfo: ProofInfo = field(init=False, default_factory=ProofInfo)

@dataclass
class InvalidDeclaration(Declaration):
    pass

@dataclass
class PrimPred(Declaration):
    ref: RefPrimPred
    arity: int
    tex: list[str]

@dataclass
class Axiom(Declaration):
    ref: RefAxiom
    conclusion: Formula

@dataclass
class Theorem(Declaration):
    ref: RefTheorem
    conclusion: Formula
    proof: list[Control]

@dataclass
class DefPred(Declaration):
    ref: RefDefPred
    args: list[Var | PredTemplate | FunTemplate]
    formula: Formula
    autoexpand: bool
    tex: list[str]

@dataclass
class DefConExist(Declaration):
    ref: RefDefConExist
    formula: Formula
    ref_con: RefDefCon

@dataclass
class DefConUniq(Declaration):
    ref: RefDefConUniq
    formula: Formula
    ref_con: RefDefCon

@dataclass
class DefCon(Declaration):
    ref: RefDefCon
    ref_theorem: RefTheorem
    tex: list[str]

@dataclass
class DefFunExist(Declaration):
    ref: RefDefFunExist
    formula: Formula
    ref_fun: RefDefFun

@dataclass
class DefFunUniq(Declaration):
    ref: RefDefFunUniq
    formula: Formula
    ref_fun: RefDefFun

@dataclass
class DefFun(Declaration):
    ref: RefDefFun
    args: list[Var | PredTemplate | FunTemplate]
    returned: Var | PredTemplate
    ref_theorem: RefTheorem
    tex: list[str]

@dataclass
class DefFunTerm(Declaration):
    ref: RefDefFunTerm
    args: list[Var | PredTemplate | FunTemplate]
    varterm: VarTerm
    tex: list[str]

@dataclass
class Equality(Declaration):
    ref: RefEquality
    tex: list[str]

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
    equality: Equality | None
    used_names: set[str]

    @staticmethod
    def init() -> "DeclarationContext":
        return DeclarationContext(primpreds={}, axioms={}, theorems={}, defpreds={}, defcons={}, defconexists={}, defconuniqs={}, deffuns={}, deffunexists={}, deffununiqs={}, deffunterms={}, equality=None, used_names=set())

    def add(self, declaration: Declaration):
        if isinstance(declaration, Equality):
            if self.equality is not None:
                msg = "equality is already declared"
                raise ContextError(msg)
            self.equality = declaration
            return
        if declaration.name in self.used_names:
            msg = f"{declaration.name} is already used"
            raise ContextError(msg)
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
        else:
            msg = f"Unexpected type: {type(declaration)}"
            raise ContextError(msg)
        self.used_names.add(declaration.name)

    def copy(self) -> "DeclarationContext":
        return DeclarationContext(self.primpreds.copy(), self.axioms.copy(), self.theorems.copy(), self.defpreds.copy(), self.defcons.copy(), self.defconexists.copy(), self.defconuniqs.copy(), self.deffuns.copy(), self.deffunexists.copy(), self.deffununiqs.copy(), self.deffunterms.copy(), self.equality, set(self.used_names))

@dataclass
class DeclarationContextNameSpace:
    namespace: dict[str, DeclarationContext]

    @staticmethod
    def init() -> "DeclarationContextNameSpace":
        return DeclarationContextNameSpace(namespace={})

    def add(self, path: str, declaration: Declaration) -> None:
        if path not in self.namespace:
            self.namespace[path] = DeclarationContext.init()
        self.namespace[path].add(declaration)

    def copy(self) -> "DeclarationContextNameSpace":
        return DeclarationContextNameSpace(namespace={path: file_decl.copy() for path, file_decl in self.namespace.items()})

    def merge(self, other: "DeclarationContextNameSpace") -> None:
        for path, file_decl in other.namespace.items():
            if path not in self.namespace:
                self.namespace[path] = file_decl

    def has_defcon(self, ref: str | RefDefCon) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            if name in file_decl.defcons:
                return True
        return False

    def get_defcon(self, ref: str | RefDefCon) -> DefCon:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefCon] = []
        for file_decl in self.namespace.values():
            if name in file_decl.defcons:
                candidates.append(file_decl.defcons[name])
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_primpred(self, ref: str | RefPrimPred) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            if name in file_decl.primpreds:
                return True
        return False

    def get_primpred(self, ref: str | RefPrimPred) -> PrimPred:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[PrimPred] = []
        for file_decl in self.namespace.values():
            if name in file_decl.primpreds:
                candidates.append(file_decl.primpreds[name])
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_defpred(self, ref: str | RefDefPred) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            if name in file_decl.defpreds:
                return True
        return False

    def get_defpred(self, ref: str | RefDefPred) -> DefPred:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefPred] = []
        for file_decl in self.namespace.values():
            if name in file_decl.defpreds:
                candidates.append(file_decl.defpreds[name])
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_deffun(self, ref: str | RefDefFun) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            if name in file_decl.deffuns:
                return True
        return False

    def get_deffun(self, ref: str | RefDefFun) -> DefFun:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefFun] = []
        for file_decl in self.namespace.values():
            if name in file_decl.deffuns:
                candidates.append(file_decl.deffuns[name])
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_deffunterm(self, ref: str | RefDefFunTerm) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            if name in file_decl.deffunterms:
                return True
        return False

    def get_deffunterm(self, ref: str | RefDefFunTerm) -> DefFunTerm:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefFunTerm] = []
        for file_decl in self.namespace.values():
            if name in file_decl.deffunterms:
                candidates.append(file_decl.deffunterms[name])
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_axiom(self, ref: str | RefAxiom) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            if name in file_decl.axioms:
                return True
        return False

    def get_axiom(self, ref: str | RefAxiom) -> Axiom:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[Axiom] = []
        for file_decl in self.namespace.values():
            if name in file_decl.axioms:
                candidates.append(file_decl.axioms[name])
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_theorem(self, ref: str | RefTheorem) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            if name in file_decl.theorems:
                return True
        return False

    def get_theorem(self, ref: str | RefTheorem) -> Theorem:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[Theorem] = []
        for file_decl in self.namespace.values():
            if name in file_decl.theorems:
                candidates.append(file_decl.theorems[name])
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_defconexist(self, ref: str | RefDefConExist) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            if name in file_decl.defconexists:
                return True
        return False

    def get_defconexist(self, ref: str | RefDefConExist) -> DefConExist:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefConExist] = []
        for file_decl in self.namespace.values():
            if name in file_decl.defconexists:
                candidates.append(file_decl.defconexists[name])
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_defconuniq(self, ref: str | RefDefConUniq) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            if name in file_decl.defconuniqs:
                return True
        return False

    def get_defconuniq(self, ref: str | RefDefConUniq) -> DefConUniq:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefConUniq] = []
        for file_decl in self.namespace.values():
            if name in file_decl.defconuniqs:
                candidates.append(file_decl.defconuniqs[name])
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_deffunexist(self, ref: str | RefDefFunExist) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            if name in file_decl.deffunexists:
                return True
        return False

    def get_deffunexist(self, ref: str | RefDefFunExist) -> DefFunExist:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefFunExist] = []
        for file_decl in self.namespace.values():
            if name in file_decl.deffunexists:
                candidates.append(file_decl.deffunexists[name])
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_deffununiq(self, ref: str | RefDefFunUniq) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            if name in file_decl.deffununiqs:
                return True
        return False

    def get_deffununiq(self, ref: str | RefDefFunUniq) -> DefFunUniq:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefFunUniq] = []
        for file_decl in self.namespace.values():
            if name in file_decl.deffununiqs:
                candidates.append(file_decl.deffununiqs[name])
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def get_equality(self) -> Equality | None:
        candidates: list[Equality] = []
        for file_decl in self.namespace.values():
            if file_decl.equality is not None:
                candidates.append(file_decl.equality)
        if len(candidates) == 0:
            return None
        elif len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for equality"
            raise ContextError(msg)

    def get_used_names(self) -> set[str]:
        names: set[str] = set()
        for ctx in self.namespace.values():
            names.update(ctx.used_names)
        return names

    def get_fact(self, ref: RefFact) -> Formula:
        if isinstance(ref, RefAxiom):
            return self.get_axiom(ref).conclusion
        elif isinstance(ref, RefTheorem):
            return self.get_theorem(ref).conclusion
        elif isinstance(ref, RefDefConExist):
            return self.get_defconexist(ref).formula
        elif isinstance(ref, RefDefConUniq):
            return self.get_defconuniq(ref).formula
        elif isinstance(ref, RefDefFunExist):
            return self.get_deffunexist(ref).formula
        elif isinstance(ref, RefDefFunUniq):
            return self.get_deffununiq(ref).formula
        else:
            msg = f"Unexpected type {type(ref)}"
            raise ContextError(msg)

@dataclass
class Context:
    decl: DeclarationContextNameSpace
    ctrl: ControlContext
    form: FormulaContext

    @staticmethod
    def init() -> "Context":
        return Context(DeclarationContextNameSpace.init(), ControlContext.init(), FormulaContext.init())

    def add_decl(self, path: str, declaration: Declaration):
        self.decl.add(path, declaration)

    def copy_ctrl(self):
        return Context(self.decl, self.ctrl.copy(), self.form)

    def add_ctrl(self, new_vars: list[Var], new_formulas: list[Bottom | Formula], new_pred_tmpls: list[PredTemplate], new_fun_tmpls: list[FunTemplate], new_symbols: list[Var | PredTemplate | FunTemplate]):
        return Context(self.decl, self.ctrl.add(new_vars, new_formulas, new_pred_tmpls, new_fun_tmpls, new_symbols), self.form)

    def copy_form(self):
        return Context(self.decl, self.ctrl, self.form.copy())

    def add_form(self, new_vars: list[Var], new_pred_tmpls: list[PredTemplate], new_fun_tmpls: list[FunTemplate]):
        return Context(self.decl, self.ctrl, self.form.add(new_vars, new_pred_tmpls, new_fun_tmpls))

    def copy(self):
        return Context(self.decl.copy(), self.ctrl.copy(), self.form.copy())

    def merge(self, context: "Context") -> None:
        self.decl.merge(context.decl)

@dataclass
class Include:
    file: str
    token: Token

@dataclass
class InvalidInclude(Include):
    pass

@dataclass
class DeclarationUnit:
    file: str
    tokens: list[Token]
    hash: str
    ast: Include | Declaration | None = None
    node_to_token: dict[int, tuple[int, int]] = field(default_factory=dict[int, tuple[int, int]])
    nodes: list[Include | Declaration | Control | Formula | Term | RefFact] = field(default_factory=list[Include | Declaration | Control | Formula | Term | RefFact])
    token_to_node: dict[int, Include | Declaration | Control | Formula | Term | RefFact] = field(default_factory=dict[int, Include | Declaration | Control | Formula | Term | RefFact])
    token_to_control: dict[int, Control] = field(default_factory=dict[int, Control])
    context: Context = field(default_factory=Context.init)
    diagnostics: list[lsp.Diagnostic] = field(default_factory=list[lsp.Diagnostic])
    decl_refs: dict[str, list[Token]] = field(default_factory=dict[str, list[Token]])
    ctrl_defs: dict[int, int] = field(default_factory=dict[int, int])
    ctrl_refs: dict[int, list[int]] = field(default_factory=dict[int, list[int]])

    def restore_from(self, old: "DeclarationUnit") -> None:
        self.ast = old.ast
        self.node_to_token = old.node_to_token
        self.nodes = old.nodes
        self.token_to_node = old.token_to_node
        self.token_to_control = old.token_to_control
        self.context = old.context
        self.diagnostics = old.diagnostics
        self.decl_refs = old.decl_refs
        self.ctrl_defs = old.ctrl_defs
        self.ctrl_refs = old.ctrl_refs

    def get_ctrl_def(self, ref_token: Token) -> Token | None:
        ref_node = self.token_to_node[ref_token.index]
        if id(ref_node) not in self.ctrl_defs:
            return None
        def_node_id = self.ctrl_defs[id(ref_node)]
        def_token_index = self.node_to_token[def_node_id][0]
        def_token = self.tokens[def_token_index]
        return def_token

    def get_ctrl_refs(self, ref_token: Token) -> list[Token]:
        ref_node = self.token_to_node[ref_token.index]
        if id(ref_node) not in self.ctrl_defs:
            return []
        def_node_id = self.ctrl_defs[id(ref_node)]
        ref_node_ids = self.ctrl_refs[def_node_id]
        ref_tokens: list[Token] = []
        for ref_node_id in ref_node_ids:
            ref_token_index = self.node_to_token[ref_node_id][0]
            ref_token = self.tokens[ref_token_index]
            ref_tokens.append(ref_token)
        return ref_tokens

    def build_token_to_node(self):
        for node in reversed(self.nodes):
            start, end = self.node_to_token[id(node)]
            for index in range(start, end + 1):
                self.token_to_node[index] = node
        for node in reversed(self.nodes):
            if isinstance(node, Control):
                start, end = self.node_to_token[id(node)]
                for index in range(start, end + 1):
                    self.token_to_control[index] = node

    def get_node_token(self, node: Declaration | Control) -> Token:
        return self.tokens[self.node_to_token[id(node)][0]]

class Workspace:
    def __init__(self, resolved_files: list[str], file_units: dict[str, list[DeclarationUnit]]):
        self.resolved_files: list[str] = resolved_files
        self.file_units: dict[str, list[DeclarationUnit]] = file_units

    def get_decl_def(self, name: str, order: list[str]) -> Token | None:
        for path in order:
            for unit in self.file_units[path]:
                if isinstance(unit.ast, (Equality, PrimPred, Axiom, Theorem, DefPred, DefConExist, DefConUniq, DefCon, DefFunExist, DefFunUniq, DefFun, DefFunTerm)) and name == unit.ast.name:
                    return unit.tokens[unit.node_to_token[id(unit.ast.ref)][0]]
        return None

    def get_all_decl_refs(self, name: str, affected_files: set[str]) -> list[Token]:
        all_decl_refs: list[Token] = []
        for path in affected_files:
            for unit in self.file_units[path]:
                if name in unit.decl_refs:
                    all_decl_refs.extend(unit.decl_refs[name])
        return all_decl_refs

    def merge(self, new: "Workspace") -> None:
        for file in new.resolved_files:
            if file not in self.resolved_files:
                self.resolved_files.append(file)
        for file, units in new.file_units.items():
            self.file_units[file] = units
