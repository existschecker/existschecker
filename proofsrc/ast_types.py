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

    def has_reference(self, name: str) -> bool:
        return name in self.axioms or name in self.theorems or name in self.defconexists or name in self.defconuniqs or name in self.deffunexists or name in self.deffununiqs

    def get_reference(self, ref: RefFact, node: Declaration | Control) -> Formula:
        if isinstance(ref, RefAxiom):
            return self.axioms[ref.name].conclusion
        elif isinstance(ref, RefTheorem):
            return self.theorems[ref.name].conclusion
        elif isinstance(ref, RefDefConExist):
            return self.defconexists[ref.name].formula
        elif isinstance(ref, RefDefConUniq):
            return self.defconuniqs[ref.name].formula
        elif isinstance(ref, RefDefFunExist):
            return self.deffunexists[ref.name].formula
        elif isinstance(ref, RefDefFunUniq):
            return self.deffununiqs[ref.name].formula
        else:
            msg = f"Unexpected name: {ref}"
            raise CheckError(node, msg)

    def copy(self) -> "DeclarationContext":
        return DeclarationContext(self.primpreds.copy(), self.axioms.copy(), self.theorems.copy(), self.defpreds.copy(), self.defcons.copy(), self.defconexists.copy(), self.defconuniqs.copy(), self.deffuns.copy(), self.deffunexists.copy(), self.deffununiqs.copy(), self.deffunterms.copy(), self.equality, set(self.used_names))

    def merge(self, decl: "DeclarationContext") -> None:
        if self.used_names & decl.used_names:
            raise Exception("conflict of used_names in merge of Context")
        if self.equality is not None and decl.equality is not None:
            raise Exception("conflict of equality in merge of Context")
        self.primpreds |= decl.primpreds
        self.axioms |= decl.axioms
        self.theorems |= decl.theorems
        self.defpreds |= decl.defpreds
        self.defcons |= decl.defcons
        self.defconexists |= decl.defconexists
        self.defconuniqs |= decl.defconuniqs
        self.deffuns |= decl.deffuns
        self.deffunexists |= decl.deffunexists
        self.deffununiqs |= decl.deffununiqs
        self.deffunterms |= decl.deffunterms
        if self.equality is None and decl.equality is not None:
            self.equality = decl.equality
        self.used_names |= decl.used_names

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
