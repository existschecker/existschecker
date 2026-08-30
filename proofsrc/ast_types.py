from lexer import Token
from dataclasses import dataclass, field
from lsprotocol import types as lsp
from typing import Sequence, Literal
from resolved_ast_types import ResolvedInclude, ResolvedDeclaration, ResolvedControl, ResolvedFormula, ResolvedTerm, ResolvedRefFact, ResolvedRefStruct, ResolvedRefStructField, ResolvedRefStructCondition, ResolvedStructVar, ResolvedRefStructPred

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

@dataclass(frozen=True)
class RefStruct:
    name: str

@dataclass(frozen=True)
class RefStructCondition:
    name: str

@dataclass
class StructVar:
    name: str
    ref_struct: RefStruct

@dataclass
class Struct(Declaration):
    ref: RefStruct
    fields: list[Var | StructVar]
    conditions: dict[RefStructCondition, Formula]

@dataclass
class RefStructPred:
    name: str

@dataclass
class StructPred(Declaration):
    ref_struct: RefStruct
    ref: RefStructPred
    args: list[Var]
    formula: Formula

@dataclass
class DeclarationContext:
    declarations: dict[str, Declaration]

    @staticmethod
    def init() -> "DeclarationContext":
        return DeclarationContext(declarations={})

    def add(self, declaration: Declaration) -> "DeclarationContext":
        if declaration.name in self.declarations:
            msg = f"{declaration.name} is already used"
            raise ContextError(msg)
        if isinstance(declaration, Equality):
            if any(isinstance(decl, Equality) for decl in self.declarations.values()):
                msg = "equality is already declared"
                raise ContextError(msg)
        return DeclarationContext(self.declarations | {declaration.name: declaration})

@dataclass
class DeclarationContextNameSpace:
    namespace: dict[str, DeclarationContext]

    @staticmethod
    def init() -> "DeclarationContextNameSpace":
        return DeclarationContextNameSpace(namespace={})

    def add(self, path: str, declaration: Declaration) -> "DeclarationContextNameSpace":
        context = self.namespace.get(path, DeclarationContext.init()).add(declaration)
        return DeclarationContextNameSpace(self.namespace | {path: context})

    def merge(self, other: "DeclarationContextNameSpace") -> "DeclarationContextNameSpace":
        return DeclarationContextNameSpace(other.namespace | self.namespace)

    def has_defcon(self, ref: str | RefDefCon) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefCon):
                return True
        return False

    def get_defcon(self, ref: str | RefDefCon) -> DefCon:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefCon] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefCon):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_primpred(self, ref: str | RefPrimPred) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, PrimPred):
                return True
        return False

    def get_primpred(self, ref: str | RefPrimPred) -> PrimPred:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[PrimPred] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, PrimPred):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_defpred(self, ref: str | RefDefPred) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefPred):
                return True
        return False

    def get_defpred(self, ref: str | RefDefPred) -> DefPred:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefPred] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefPred):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_deffun(self, ref: str | RefDefFun) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefFun):
                return True
        return False

    def get_deffun(self, ref: str | RefDefFun) -> DefFun:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefFun] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefFun):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_deffunterm(self, ref: str | RefDefFunTerm) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefFunTerm):
                return True
        return False

    def get_deffunterm(self, ref: str | RefDefFunTerm) -> DefFunTerm:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefFunTerm] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefFunTerm):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_axiom(self, ref: str | RefAxiom) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, Axiom):
                return True
        return False

    def get_axiom(self, ref: str | RefAxiom) -> Axiom:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[Axiom] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, Axiom):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_theorem(self, ref: str | RefTheorem) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, Theorem):
                return True
        return False

    def get_theorem(self, ref: str | RefTheorem) -> Theorem:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[Theorem] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, Theorem):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_defconexist(self, ref: str | RefDefConExist) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefConExist):
                return True
        return False

    def get_defconexist(self, ref: str | RefDefConExist) -> DefConExist:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefConExist] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefConExist):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_defconuniq(self, ref: str | RefDefConUniq) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefConUniq):
                return True
        return False

    def get_defconuniq(self, ref: str | RefDefConUniq) -> DefConUniq:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefConUniq] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefConUniq):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_deffunexist(self, ref: str | RefDefFunExist) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefFunExist):
                return True
        return False

    def get_deffunexist(self, ref: str | RefDefFunExist) -> DefFunExist:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefFunExist] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefFunExist):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_deffununiq(self, ref: str | RefDefFunUniq) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefFunUniq):
                return True
        return False

    def get_deffununiq(self, ref: str | RefDefFunUniq) -> DefFunUniq:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[DefFunUniq] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, DefFunUniq):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def get_equality(self) -> Equality | None:
        candidates: list[Equality] = []
        for file_decl in self.namespace.values():
            for decl in file_decl.declarations.values():
                if isinstance(decl, Equality):
                    candidates.append(decl)
        if len(candidates) == 0:
            return None
        elif len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for equality"
            raise ContextError(msg)

    def has_struct(self, ref: str | RefStruct) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, Struct):
                return True
        return False

    def get_struct(self, ref: str | RefStruct) -> Struct:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[Struct] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, Struct):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def has_structpred(self, ref: str | RefStructPred) -> bool:
        name = ref if isinstance(ref, str) else ref.name
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, StructPred):
                return True
        return False

    def get_structpred(self, ref: str | RefStructPred) -> StructPred:
        name = ref if isinstance(ref, str) else ref.name
        candidates: list[StructPred] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if isinstance(decl, StructPred):
                candidates.append(decl)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {name}"
            raise ContextError(msg)

    def get_used_names(self) -> set[str]:
        names: set[str] = set()
        for ctx in self.namespace.values():
            names.update(ctx.declarations.keys())
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
    ctrl: ControlContext

    @staticmethod
    def init() -> "Context":
        return Context(ControlContext.init())

    def add_ctrl(self, new_vars: list[Var], new_formulas: list[Bottom | Formula], new_pred_tmpls: list[PredTemplate], new_fun_tmpls: list[FunTemplate], new_symbols: list[Var | PredTemplate | FunTemplate]):
        return Context(self.ctrl.add(new_vars, new_formulas, new_pred_tmpls, new_fun_tmpls, new_symbols))

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
    resolved_ast: ResolvedInclude | ResolvedDeclaration | None = None
    resolved_node_to_token: dict[int, tuple[int, int]] = field(default_factory=dict[int, tuple[int, int]])
    resolved_nodes: list[ResolvedInclude | ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedStructVar | ResolvedRefStructPred] = field(default_factory=list[ResolvedInclude | ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedStructVar | ResolvedRefStructPred])
    resolved_token_to_node: dict[int, ResolvedInclude | ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedStructVar | ResolvedRefStructPred] = field(default_factory=dict[int, ResolvedInclude | ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedStructVar | ResolvedRefStructPred])
    resolved_token_to_control: dict[int, ResolvedControl] = field(default_factory=dict[int, ResolvedControl])
    resolved_decl_refs: dict[str, list[Token]] = field(default_factory=dict[str, list[Token]])
    resolved_ctrl_defs: dict[int, tuple[str, int]] = field(default_factory=dict[int, tuple[str, int]])
    resolved_ctrl_refs: dict[int, list[int]] = field(default_factory=dict[int, list[int]])
    ast: Include | Declaration | None = None
    node_to_token: dict[int, tuple[int, int]] = field(default_factory=dict[int, tuple[int, int]])
    nodes: list[Include | Declaration | Control | Formula | Term | RefFact | RefStruct | RefStructCondition | StructVar | RefStructPred] = field(default_factory=list[Include | Declaration | Control | Formula | Term | RefFact | RefStruct | RefStructCondition | StructVar | RefStructPred])
    token_to_node: dict[int, Include | Declaration | Control | Formula | Term | RefFact | RefStruct | RefStructCondition | StructVar | RefStructPred] = field(default_factory=dict[int, Include | Declaration | Control | Formula | Term | RefFact | RefStruct | RefStructCondition | StructVar | RefStructPred])
    token_to_control: dict[int, Control] = field(default_factory=dict[int, Control])
    decl: DeclarationContextNameSpace = field(default_factory=DeclarationContextNameSpace.init)
    diagnostics: list[lsp.Diagnostic] = field(default_factory=list[lsp.Diagnostic])

    def restore_from(self, old: "DeclarationUnit") -> None:
        self.ast = old.ast
        self.resolved_ast = old.resolved_ast
        self.resolved_node_to_token = old.resolved_node_to_token
        self.resolved_nodes = old.resolved_nodes
        self.resolved_token_to_node = old.resolved_token_to_node
        self.resolved_token_to_control = old.resolved_token_to_control
        self.resolved_decl_refs = old.resolved_decl_refs
        self.resolved_ctrl_defs = old.resolved_ctrl_defs
        self.resolved_ctrl_refs = old.resolved_ctrl_refs
        self.node_to_token = old.node_to_token
        self.nodes = old.nodes
        self.token_to_node = old.token_to_node
        self.token_to_control = old.token_to_control
        self.decl = old.decl
        self.diagnostics = old.diagnostics

    def build_token_to_node(self):
        for node in reversed(self.resolved_nodes):
            start, end = self.resolved_node_to_token[id(node)]
            for index in range(start, end + 1):
                self.resolved_token_to_node[index] = node
        for node in reversed(self.resolved_nodes):
            if isinstance(node, ResolvedControl):
                start, end = self.resolved_node_to_token[id(node)]
                for index in range(start, end + 1):
                    self.resolved_token_to_control[index] = node
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
    def __init__(self, file_units: dict[str, list[DeclarationUnit]]):
        self.file_units: dict[str, list[DeclarationUnit]] = file_units

    def get_decl_def(self, name: str, order: list[str]) -> Token | None:
        for path in order:
            for unit in self.file_units[path]:
                if isinstance(unit.ast, (Equality, PrimPred, Axiom, Theorem, DefPred, DefConExist, DefConUniq, DefCon, DefFunExist, DefFunUniq, DefFun, DefFunTerm, Struct)) and name == unit.ast.name:
                    return unit.tokens[unit.node_to_token[id(unit.ast.ref)][0]]
        return None

    def get_all_decl_refs(self, name: str, affected_files: set[str]) -> list[Token]:
        all_decl_refs: list[Token] = []
        for path in affected_files:
            for unit in self.file_units[path]:
                if name in unit.resolved_decl_refs:
                    all_decl_refs.extend(unit.resolved_decl_refs[name])
        return all_decl_refs

    def get_ctrl_def(self, order: list[str], def_unit_name: str, def_node_id: int) -> Token | None:
        def_unit = None
        for path in order:
            for unit in self.file_units[path]:
                if isinstance(unit.ast, (Equality, PrimPred, Axiom, Theorem, DefPred, DefConExist, DefConUniq, DefCon, DefFunExist, DefFunUniq, DefFun, DefFunTerm, Struct, StructPred)) and def_unit_name == unit.ast.name:
                    def_unit = unit
        if def_unit is None:
            return None
        def_token_index = def_unit.resolved_node_to_token[def_node_id][0]
        def_token = def_unit.tokens[def_token_index]
        return def_token

    def get_ctrl_refs(self, affected_files: set[str], target_def_unit_name: str, target_def_node_id: int) -> list[Token]:
        refs: list[Token] = []
        for path in affected_files:
            for unit in self.file_units[path]:
                for ref_node_id, (def_unit_name, def_node_id) in unit.resolved_ctrl_defs.items():
                    if def_unit_name == target_def_unit_name and def_node_id == target_def_node_id:
                        ref_token_index = unit.resolved_node_to_token[ref_node_id][0]
                        refs.append(unit.tokens[ref_token_index])
        return refs

    def merge(self, new: "Workspace") -> None:
        for file, units in new.file_units.items():
            self.file_units[file] = units
