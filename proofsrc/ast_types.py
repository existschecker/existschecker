from lexer import Token
from dataclasses import dataclass
from lsprotocol import types as lsp
from typing import Literal
from enum import StrEnum
from immutables import Map
from resolved_ast_types import ResolvedUnit, ResolvedDeclaration, ResolvedEquality
from parsed_ast_types import ParsedUnit
from dependency import DependencyResult

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

@dataclass(frozen=True)
class ControlContext:
    formulas: tuple[Bottom | Formula, ...]
    symbols: tuple[Var | PredTemplate | FunTemplate, ...]

    @staticmethod
    def init() -> "ControlContext":
        return ControlContext(formulas=(), symbols=())

    def add(self, new_formulas: tuple[Bottom | Formula, ...], new_symbols: tuple[Var | PredTemplate | FunTemplate, ...]) -> "ControlContext":
        return ControlContext(self.formulas + new_formulas, self.symbols + new_symbols)

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
    parent: RefDefCon

@dataclass(frozen=True)
class RefDefConUniq(RefFact):
    parent: RefDefCon

@dataclass(frozen=True)
class RefDefFunExist(RefFact):
    parent: RefDefFun

@dataclass(frozen=True)
class RefDefFunUniq(RefFact):
    parent: RefDefFun

class ProofStatus(StrEnum):
    UNCHECKED = "⚠️Unchecked"
    PASSED = "✅Passed"
    FAILED = "❌Failed"

@dataclass(frozen=True)
class ProofInfo:
    status: ProofStatus = ProofStatus.UNCHECKED
    ctrl_ctx: ControlContext = ControlContext.init()
    premises: tuple[RefFact | Bottom | Formula, ...] = ()
    conclusions: tuple[Bottom | Formula, ...] = ()
    local_vars: tuple[Var | PredTemplate | FunTemplate, ...] = ()
    local_premise: tuple[Bottom | Formula, ...] = ()
    local_conclusion: tuple[Bottom | Formula, ...] = ()

@dataclass(frozen=True)
class Control:
    pass

@dataclass(frozen=True)
class InvalidControl(Control):
    pass

@dataclass(frozen=True)
class Assume(Control):
    premise: Formula
    body: tuple[Control, ...]

@dataclass(frozen=True)
class Any(Control):
    items: tuple[Var | PredTemplate | FunTemplate, ...]
    body: tuple[Control, ...]

@dataclass(frozen=True)
class Case(Control):
    premise: Formula
    body: tuple[Control, ...]

@dataclass(frozen=True)
class Divide(Control):
    fact: RefFact | Formula
    cases: tuple[Case, ...]

@dataclass(frozen=True)
class Some(Control):
    items: tuple[Var | None, ...]
    fact: RefFact | Formula
    body: tuple[Control, ...]

@dataclass(frozen=True)
class Deny(Control):
    premise: Formula
    body: tuple[Control, ...]

@dataclass(frozen=True)
class Contradict(Control):
    contradiction: Formula

@dataclass(frozen=True)
class Explode(Control):
    conclusion: Formula

@dataclass(frozen=True)
class Apply(Control):
    invoke: Literal["none", "invoke", "invoke-rightward", "invoke-leftward"]
    fact: RefFact | Formula
    terms: tuple[Term | None, ...]

@dataclass(frozen=True)
class Lift(Control):
    varterms: tuple[VarTerm | None, ...]
    conclusion: Formula

@dataclass(frozen=True)
class Characterize(Control):
    varterm: VarTerm
    conclusion: ExistsUniq

@dataclass(frozen=True)
class Invoke(Control):
    direction: Literal["none", "rightward", "leftward"]
    fact: Implies | Iff

@dataclass(frozen=True)
class Expand(Control):
    fact: RefFact | Formula
    refs: tuple[RefDefFunTerm | RefDefPred, ...]
    indexes: Map[RefDefFunTerm | RefDefPred, tuple[int, ...]]

@dataclass(frozen=True)
class Fold(Control):
    refs: tuple[RefDefFunTerm | RefDefPred, ...]
    indexes: Map[RefDefFunTerm | RefDefPred, tuple[int, ...]]
    conclusion: Formula

@dataclass(frozen=True)
class Pad(Control):
    fact: RefFact | Formula
    conclusion: Formula

@dataclass(frozen=True)
class Split(Control):
    index: int | None
    fact: RefFact | Formula

@dataclass(frozen=True)
class Connect(Control):
    conclusion: Formula

@dataclass(frozen=True)
class Substitute(Control):
    fact: RefFact | Formula
    env: Map[Term, Term]
    indexes: Map[Term, tuple[int, ...]]

@dataclass(frozen=True)
class Show(Control):
    conclusion: Bottom | Formula
    body: tuple[Control, ...]

@dataclass(frozen=True)
class Assert(Control):
    reference: RefFact | Formula

@dataclass(frozen=True)
class Declaration:
    name: str

@dataclass(frozen=True)
class InvalidDeclaration(Declaration):
    pass

@dataclass(frozen=True)
class PrimPred(Declaration):
    ref: RefPrimPred
    arity: int
    tex: tuple[str, ...]

@dataclass(frozen=True)
class Axiom(Declaration):
    ref: RefAxiom
    conclusion: Formula

@dataclass(frozen=True)
class Theorem(Declaration):
    ref: RefTheorem
    conclusion: Formula
    proof: tuple[Control, ...]

@dataclass(frozen=True)
class DefPred(Declaration):
    ref: RefDefPred
    args: tuple[Var | PredTemplate | FunTemplate, ...]
    formula: Formula
    autoexpand: bool
    tex: tuple[str, ...]

@dataclass(frozen=True)
class DefCon(Declaration):
    ref: RefDefCon
    ref_theorem: RefTheorem
    tex: tuple[str, ...]

@dataclass(frozen=True)
class DefFun(Declaration):
    ref: RefDefFun
    ref_theorem: RefTheorem
    tex: tuple[str, ...]

@dataclass(frozen=True)
class DefFunTerm(Declaration):
    ref: RefDefFunTerm
    args: tuple[Var | PredTemplate | FunTemplate, ...]
    varterm: VarTerm
    tex: tuple[str, ...]

@dataclass(frozen=True)
class Equality(Declaration):
    ref: RefEquality
    tex: tuple[str, ...]

@dataclass(frozen=True)
class RefStruct:
    name: str

@dataclass(frozen=True)
class RefStructCondition:
    name: str

@dataclass(frozen=True)
class StructVar:
    name: str
    ref_struct: RefStruct

@dataclass(frozen=True)
class Struct(Declaration):
    ref: RefStruct
    fields: tuple[Var | StructVar, ...]
    conditions: Map[RefStructCondition, Formula]

@dataclass(frozen=True)
class RefStructPred:
    name: str

@dataclass(frozen=True)
class StructPred(Declaration):
    ref_struct: RefStruct
    ref: RefStructPred
    args: tuple[Var, ...]
    formula: Formula

@dataclass(frozen=True)
class RefStructCon:
    name: str

@dataclass(frozen=True)
class StructCon(Declaration):
    ref_struct: RefStruct
    ref: RefStructCon
    ref_theorem: RefTheorem

@dataclass
class DeclarationContext:
    declarations: dict[str, "DeclarationUnit"]

    @staticmethod
    def init() -> "DeclarationContext":
        return DeclarationContext(declarations={})

    def add(self, declaration: "DeclarationUnit") -> "DeclarationContext":
        if not (isinstance(declaration.elaborated_unit.ast, Declaration) and declaration.success()):
            return self
        if declaration.elaborated_unit.ast.name in self.declarations:
            raise ContextError(f"{declaration.elaborated_unit.ast.name} is already used")
        if isinstance(declaration.elaborated_unit.ast, Equality):
            if any(isinstance(decl.elaborated_unit.ast, Equality) for decl in self.declarations.values()):
                msg = "equality is already declared"
                raise ContextError(msg)
        return DeclarationContext(self.declarations | {declaration.elaborated_unit.ast.name: declaration})

@dataclass
class DeclarationContextNameSpace:
    namespace: dict[str, DeclarationContext]

    @staticmethod
    def init() -> "DeclarationContextNameSpace":
        return DeclarationContextNameSpace(namespace={})

    def add(self, path: str, declaration: "DeclarationUnit") -> "DeclarationContextNameSpace":
        if not (isinstance(declaration.elaborated_unit.ast, Declaration) and declaration.success()):
            return self
        context = self.namespace.get(path, DeclarationContext.init()).add(declaration)
        return DeclarationContextNameSpace(self.namespace | {path: context})

    def merge(self, other: "DeclarationContextNameSpace") -> "DeclarationContextNameSpace":
        return DeclarationContextNameSpace(other.namespace | self.namespace)

    def get_equality(self) -> Equality | None:
        candidates: list[Equality] = []
        for file_decl in self.namespace.values():
            for decl in file_decl.declarations.values():
                if isinstance(decl.elaborated_unit.ast, Equality):
                    candidates.append(decl.elaborated_unit.ast)
        if len(candidates) == 0:
            return None
        elif len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for equality"
            raise ContextError(msg)

    def get_ast_candidates[T: Declaration](self, ast_type: type[T], name: str) -> list[T]:
        candidates: list[T] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if decl is not None and isinstance(decl.elaborated_unit.ast, ast_type):
                candidates.append(decl.elaborated_unit.ast)
        return candidates

    def has_ast[T: Declaration](self, ast_type: type[T], name: str) -> bool:
        candidates = self.get_ast_candidates(ast_type, name)
        if len(candidates) == 0:
            return False
        elif len(candidates) == 1:
            return True
        else:
            msg = f"{len(candidates)} candidates found for {ast_type} and {name}"
            raise ContextError(msg)

    def get_ast[T: Declaration](self, ast_type: type[T], name: str) -> T:
        candidates = self.get_ast_candidates(ast_type, name)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {ast_type} and {name}"
            raise ContextError(msg)

    def get_resolved_equality(self) -> ResolvedEquality | None:
        candidates: list[ResolvedEquality] = []
        for file_decl in self.namespace.values():
            for decl in file_decl.declarations.values():
                if isinstance(decl.resolved_unit.resolved_ast, ResolvedEquality):
                    candidates.append(decl.resolved_unit.resolved_ast)
        if len(candidates) == 0:
            return None
        elif len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for equality"
            raise ContextError(msg)

    def get_resolved_ast_candidates[T: ResolvedDeclaration](self, ast_type: type[T], name: str) -> list[T]:
        candidates: list[T] = []
        for file_decl in self.namespace.values():
            decl = file_decl.declarations.get(name)
            if decl is not None and isinstance(decl.resolved_unit.resolved_ast, ast_type):
                candidates.append(decl.resolved_unit.resolved_ast)
        return candidates

    def has_resolved_ast[T: ResolvedDeclaration](self, ast_type: type[T], name: str) -> bool:
        candidates = self.get_resolved_ast_candidates(ast_type, name)
        if len(candidates) == 0:
            return False
        elif len(candidates) == 1:
            return True
        else:
            msg = f"{len(candidates)} candidates found for {ast_type} and {name}"
            raise ContextError(msg)

    def get_resolved_ast[T: ResolvedDeclaration](self, ast_type: type[T], name: str) -> T:
        candidates = self.get_resolved_ast_candidates(ast_type, name)
        if len(candidates) == 1:
            return candidates[0]
        else:
            msg = f"{len(candidates)} candidates found for {ast_type} and {name}"
            raise ContextError(msg)

    def get_used_names(self) -> set[str]:
        names: set[str] = set()
        for ctx in self.namespace.values():
            names.update(ctx.declarations.keys())
        return names

@dataclass(frozen=True)
class Context:
    ctrl: ControlContext

    @staticmethod
    def init() -> "Context":
        return Context(ControlContext.init())

    def add_ctrl(self, new_formulas: tuple[Bottom | Formula, ...], new_symbols: tuple[Var | PredTemplate | FunTemplate, ...]):
        return Context(self.ctrl.add(new_formulas, new_symbols))

@dataclass
class Include:
    file: str
    token: Token

@dataclass
class InvalidInclude(Include):
    pass

@dataclass
class LexedUnit:
    file: str
    tokens: list[Token]
    hash: str

@dataclass
class ElaboratedUnit:
    ast: Include | Declaration
    node_to_token: dict[int, tuple[int, int]]
    nodes: list[Include | Declaration | Control | Formula | Term | RefFact | RefStruct | RefStructCondition | StructVar | RefStructPred | RefStructCon]
    token_to_node: dict[int, Include | Declaration | Control | Formula | Term | RefFact | RefStruct | RefStructCondition | StructVar | RefStructPred | RefStructCon]
    token_to_control: dict[int, Control]
    diagnostics: list[lsp.Diagnostic]

@dataclass
class CheckedUnit:
    diagnostics: list[lsp.Diagnostic]
    proofs: dict[int, ProofInfo]

@dataclass
class DeclarationUnit:
    lexed_unit: LexedUnit
    parsed_unit: ParsedUnit
    resolved_unit: ResolvedUnit
    elaborated_unit: ElaboratedUnit
    checked_unit: CheckedUnit
    decl: DeclarationContextNameSpace

    def success(self) -> bool:
        return len(self.parsed_unit.diagnostics) == 0 and len(self.resolved_unit.diagnostics) == 0 and len(self.elaborated_unit.diagnostics) == 0 and len(self.checked_unit.diagnostics) == 0

class Workspace:
    def __init__(self, file_units: dict[str, list[DeclarationUnit]], dependency_result: DependencyResult) -> None:
        self.file_units: dict[str, list[DeclarationUnit]] = file_units
        self.dependency_result: DependencyResult = dependency_result

    @staticmethod
    def empty() -> "Workspace":
        return Workspace({}, DependencyResult({}, {}, {}, {}))

    def get_decl_def(self, name: str, order: list[str]) -> Token | None:
        for path in order:
            for unit in self.file_units[path]:
                if isinstance(unit.elaborated_unit.ast, (Equality, PrimPred, Axiom, Theorem, DefPred, DefCon, DefFun, DefFunTerm, Struct)) and name == unit.elaborated_unit.ast.name:
                    return unit.lexed_unit.tokens[unit.elaborated_unit.node_to_token[id(unit.elaborated_unit.ast.ref)][0]]
        return None

    def get_all_decl_refs(self, name: str, affected_files: set[str]) -> list[Token]:
        all_decl_refs: list[Token] = []
        for path in affected_files:
            for unit in self.file_units[path]:
                if name in unit.resolved_unit.resolved_decl_refs:
                    all_decl_refs.extend(unit.resolved_unit.resolved_decl_refs[name])
        return all_decl_refs

    def get_ctrl_def(self, order: list[str], def_unit_name: str, def_node_id: int) -> Token | None:
        def_unit = None
        for path in order:
            for unit in self.file_units[path]:
                if isinstance(unit.elaborated_unit.ast, (Equality, PrimPred, Axiom, Theorem, DefPred, DefCon, DefFun, DefFunTerm, Struct, StructPred, StructCon)) and def_unit_name == unit.elaborated_unit.ast.name:
                    def_unit = unit
        if def_unit is None:
            return None
        def_token_index = def_unit.resolved_unit.resolved_node_to_token[def_node_id][0]
        def_token = def_unit.lexed_unit.tokens[def_token_index]
        return def_token

    def get_ctrl_refs(self, affected_files: set[str], target_def_unit_name: str, target_def_node_id: int) -> list[Token]:
        refs: list[Token] = []
        for path in affected_files:
            for unit in self.file_units[path]:
                for ref_node_id, (def_unit_name, def_node_id) in unit.resolved_unit.resolved_ctrl_defs.items():
                    if def_unit_name == target_def_unit_name and def_node_id == target_def_node_id:
                        ref_token_index = unit.resolved_unit.resolved_node_to_token[ref_node_id][0]
                        refs.append(unit.lexed_unit.tokens[ref_token_index])
        return refs

    def merge(self, file_units: dict[str, list[DeclarationUnit]], dependency_result: DependencyResult) -> "Workspace":
        return Workspace(self.file_units | file_units, dependency_result)
