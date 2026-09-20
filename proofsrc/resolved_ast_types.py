from lexer import Token
from dataclasses import dataclass
from typing import Literal
from lsprotocol import types as lsp
from immutables import Map

@dataclass(frozen=True)
class ResolvedTerm:
    pass

@dataclass(frozen=True)
class ResolvedFormula:
    pass

@dataclass(frozen=True)
class ResolvedVarTerm(ResolvedTerm):
    pass

@dataclass(frozen=True)
class ResolvedVar(ResolvedVarTerm):
    name: str

@dataclass(frozen=True)
class ResolvedRefDefCon(ResolvedVarTerm):
    name: str

@dataclass(frozen=True)
class ResolvedFunTerm(ResolvedTerm):
    pass

@dataclass(frozen=True)
class ResolvedRefDefFun(ResolvedFunTerm):
    name: str

@dataclass(frozen=True)
class ResolvedRefDefFunTerm(ResolvedFunTerm):
    name: str

@dataclass(frozen=True)
class ResolvedFunTemplate(ResolvedFunTerm):
    name: str
    arity: int

@dataclass(frozen=True)
class ResolvedFunLambda(ResolvedFunTerm):
    args: tuple[ResolvedVar, ...]
    body: ResolvedVarTerm

@dataclass(frozen=True)
class ResolvedCompound(ResolvedVarTerm):
    fun: ResolvedFunTerm
    args: tuple[ResolvedTerm, ...]

@dataclass(frozen=True)
class ResolvedPredTerm(ResolvedTerm):
    pass

@dataclass(frozen=True)
class ResolvedRefEquality(ResolvedPredTerm):
    name: str

@dataclass(frozen=True)
class ResolvedRefPrimPred(ResolvedPredTerm):
    name: str

@dataclass(frozen=True)
class ResolvedRefDefPred(ResolvedPredTerm):
    name: str

@dataclass(frozen=True)
class ResolvedPredTemplate(ResolvedPredTerm):
    name: str
    arity: int

@dataclass(frozen=True)
class ResolvedPredLambda(ResolvedPredTerm):
    args: tuple[ResolvedVar, ...]
    body: ResolvedFormula

@dataclass(frozen=True)
class ResolvedAtomicFormula(ResolvedFormula):
    pred: ResolvedPredTerm
    args: tuple[ResolvedTerm, ...]

@dataclass(frozen=True)
class ResolvedNot(ResolvedFormula):
    body: ResolvedFormula

@dataclass(frozen=True)
class ResolvedAnd(ResolvedFormula):
    left: ResolvedFormula
    right: ResolvedFormula

@dataclass(frozen=True)
class ResolvedOr(ResolvedFormula):
    left: ResolvedFormula
    right: ResolvedFormula

@dataclass(frozen=True)
class ResolvedImplies(ResolvedFormula):
    left: ResolvedFormula
    right: ResolvedFormula

@dataclass(frozen=True)
class ResolvedIff(ResolvedFormula):
    left: ResolvedFormula
    right: ResolvedFormula

@dataclass(frozen=True)
class ResolvedForall(ResolvedFormula):
    var: "ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate"
    body: ResolvedFormula

@dataclass(frozen=True)
class ResolvedExists(ResolvedFormula):
    var: ResolvedVar
    body: ResolvedFormula

@dataclass(frozen=True)
class ResolvedExistsUniq(ResolvedFormula):
    var: ResolvedVar
    body: ResolvedFormula

@dataclass(frozen=True)
class ResolvedBottom:
    pass

@dataclass(frozen=True)
class ResolvedRefFact:
    name: str

@dataclass(frozen=True)
class ResolvedRefAxiom(ResolvedRefFact):
    pass

@dataclass(frozen=True)
class ResolvedRefTheorem(ResolvedRefFact):
    pass

@dataclass(frozen=True)
class ResolvedRefDefConExist(ResolvedRefFact):
    parent: ResolvedRefDefCon

@dataclass(frozen=True)
class ResolvedRefDefConUniq(ResolvedRefFact):
    parent: ResolvedRefDefCon

@dataclass(frozen=True)
class ResolvedRefDefFunExist(ResolvedRefFact):
    parent: ResolvedRefDefFun

@dataclass(frozen=True)
class ResolvedRefDefFunUniq(ResolvedRefFact):
    parent: ResolvedRefDefFun

@dataclass(frozen=True)
class ResolvedControl:
    pass

@dataclass(frozen=True)
class ResolvedInvalidControl(ResolvedControl):
    pass

@dataclass(frozen=True)
class ResolvedAssume(ResolvedControl):
    premise: ResolvedFormula
    body: tuple[ResolvedControl, ...]

@dataclass(frozen=True)
class ResolvedAny(ResolvedControl):
    items: tuple["ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate", ...]
    body: tuple[ResolvedControl, ...]

@dataclass(frozen=True)
class ResolvedCase(ResolvedControl):
    premise: ResolvedFormula
    body: tuple[ResolvedControl, ...]

@dataclass(frozen=True)
class ResolvedDivide(ResolvedControl):
    fact: ResolvedRefFact | ResolvedFormula
    cases: tuple[ResolvedCase, ...]

@dataclass(frozen=True)
class ResolvedSome(ResolvedControl):
    items: tuple[ResolvedVar | None, ...]
    fact: ResolvedRefFact | ResolvedFormula
    body: tuple[ResolvedControl, ...]

@dataclass(frozen=True)
class ResolvedDeny(ResolvedControl):
    premise: ResolvedFormula
    body: tuple[ResolvedControl, ...]

@dataclass(frozen=True)
class ResolvedContradict(ResolvedControl):
    contradiction: ResolvedFormula

@dataclass(frozen=True)
class ResolvedExplode(ResolvedControl):
    conclusion: ResolvedFormula

@dataclass(frozen=True)
class ResolvedApply(ResolvedControl):
    invoke: Literal["none", "invoke", "invoke-rightward", "invoke-leftward"]
    fact: ResolvedRefFact | ResolvedFormula
    terms: tuple[ResolvedTerm | None, ...]

@dataclass(frozen=True)
class ResolvedLift(ResolvedControl):
    varterms: tuple[ResolvedVarTerm | None, ...]
    conclusion: ResolvedFormula

@dataclass(frozen=True)
class ResolvedCharacterize(ResolvedControl):
    varterm: ResolvedVarTerm
    conclusion: ResolvedExistsUniq

@dataclass(frozen=True)
class ResolvedInvoke(ResolvedControl):
    direction: Literal["none", "rightward", "leftward"]
    fact: ResolvedImplies | ResolvedIff

@dataclass(frozen=True)
class ResolvedExpand(ResolvedControl):
    fact: ResolvedRefFact | ResolvedFormula
    refs: tuple[ResolvedRefDefFunTerm | ResolvedRefDefPred, ...]
    indexes: Map[ResolvedRefDefFunTerm | ResolvedRefDefPred, tuple[int, ...]]

@dataclass(frozen=True)
class ResolvedFold(ResolvedControl):
    refs: tuple[ResolvedRefDefFunTerm | ResolvedRefDefPred, ...]
    indexes: Map[ResolvedRefDefFunTerm | ResolvedRefDefPred, tuple[int, ...]]
    conclusion: ResolvedFormula

@dataclass(frozen=True)
class ResolvedPad(ResolvedControl):
    fact: ResolvedRefFact | ResolvedFormula
    conclusion: ResolvedFormula

@dataclass(frozen=True)
class ResolvedSplit(ResolvedControl):
    index: int | None
    fact: ResolvedRefFact | ResolvedFormula

@dataclass(frozen=True)
class ResolvedConnect(ResolvedControl):
    conclusion: ResolvedFormula

@dataclass(frozen=True)
class ResolvedSubstitute(ResolvedControl):
    fact: ResolvedRefFact | ResolvedFormula
    env: Map[ResolvedTerm, ResolvedTerm]
    indexes: Map[ResolvedTerm, tuple[int, ...]]

@dataclass(frozen=True)
class ResolvedShow(ResolvedControl):
    conclusion: ResolvedBottom | ResolvedFormula
    body: tuple[ResolvedControl, ...]

@dataclass(frozen=True)
class ResolvedAssert(ResolvedControl):
    reference: ResolvedRefFact | ResolvedFormula

@dataclass(frozen=True)
class ResolvedDeclaration:
    name: str

@dataclass(frozen=True)
class ResolvedInvalidDeclaration(ResolvedDeclaration):
    pass

@dataclass(frozen=True)
class ResolvedPrimPred(ResolvedDeclaration):
    ref: ResolvedRefPrimPred
    arity: int
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ResolvedAxiom(ResolvedDeclaration):
    ref: ResolvedRefAxiom
    conclusion: ResolvedFormula

@dataclass(frozen=True)
class ResolvedTheorem(ResolvedDeclaration):
    ref: ResolvedRefTheorem
    conclusion: ResolvedFormula
    proof: tuple[ResolvedControl, ...]

@dataclass(frozen=True)
class ResolvedDefPred(ResolvedDeclaration):
    ref: ResolvedRefDefPred
    args: tuple[ResolvedVar | ResolvedPredTemplate | ResolvedFunTemplate, ...]
    formula: ResolvedFormula
    autoexpand: bool
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ResolvedDefCon(ResolvedDeclaration):
    ref: ResolvedRefDefCon
    ref_theorem: ResolvedRefTheorem
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ResolvedDefFun(ResolvedDeclaration):
    ref: ResolvedRefDefFun
    ref_theorem: ResolvedRefTheorem
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ResolvedDefFunTerm(ResolvedDeclaration):
    ref: ResolvedRefDefFunTerm
    args: tuple[ResolvedVar | ResolvedPredTemplate | ResolvedFunTemplate, ...]
    varterm: ResolvedVarTerm
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ResolvedEquality(ResolvedDeclaration):
    ref: ResolvedRefEquality
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ResolvedInclude:
    file: str
    token: Token

@dataclass(frozen=True)
class ResolvedInvalidInclude(ResolvedInclude):
    pass

@dataclass(frozen=True)
class ResolvedRefStruct:
    name: str

@dataclass(frozen=True)
class ResolvedStructVar(ResolvedVarTerm):
    name: str
    ref_struct: ResolvedRefStruct

@dataclass(frozen=True)
class ResolvedRefStructField:
    name: str

@dataclass(frozen=True)
class ResolvedStructMemberField(ResolvedVarTerm):
    parent: "ResolvedStructVar | ResolvedStructMemberField"
    struct_field: ResolvedRefStructField
    ref_struct: ResolvedRefStruct | None

@dataclass(frozen=True)
class ResolvedRefStructCondition:
    name: str

@dataclass(frozen=True)
class ResolvedRefStructMemberCondition(ResolvedRefFact):
    parent: ResolvedStructVar | ResolvedStructMemberField
    struct_condition: ResolvedRefStructCondition

@dataclass(frozen=True)
class ResolvedStruct(ResolvedDeclaration):
    ref: ResolvedRefStruct
    fields: tuple["ResolvedVar | ResolvedStructVar", ...]
    conditions: Map[ResolvedRefStructCondition, ResolvedFormula]

@dataclass(frozen=True)
class ResolvedRefStructPred:
    name: str

@dataclass(frozen=True)
class ResolvedStructPred(ResolvedDeclaration):
    ref_struct: ResolvedRefStruct
    ref: ResolvedRefStructPred
    args: tuple[ResolvedVar, ...]
    formula: ResolvedFormula

@dataclass(frozen=True)
class ResolvedStructMemberPred(ResolvedPredTerm):
    parent: ResolvedStructVar | ResolvedStructMemberField
    struct_pred: ResolvedRefStructPred

@dataclass(frozen=True)
class ResolvedRefStructCon:
    name: str

@dataclass(frozen=True)
class ResolvedStructCon(ResolvedDeclaration):
    ref_struct: ResolvedRefStruct
    ref: ResolvedRefStructCon
    ref_theorem: ResolvedRefTheorem

@dataclass(frozen=True)
class ResolvedFormulaContext:
    items: tuple[ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate, ...]

    @staticmethod
    def init() -> "ResolvedFormulaContext":
        return ResolvedFormulaContext(())

    def add(self, new_items: tuple[ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate, ...]) -> "ResolvedFormulaContext":
        return ResolvedFormulaContext(self.items + new_items)

@dataclass(frozen=True)
class ResolvedControlContext:
    items: tuple[ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate, ...]

    @staticmethod
    def init() -> "ResolvedControlContext":
        return ResolvedControlContext(())

    def add(self, new_items: tuple[ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate, ...]) -> "ResolvedControlContext":
        return ResolvedControlContext(self.items + new_items)

@dataclass(frozen=True)
class ResolvedContext:
    ctrl: ResolvedControlContext
    form: ResolvedFormulaContext
    ref_struct: ResolvedRefStruct | None

    @staticmethod
    def init() -> "ResolvedContext":
        return ResolvedContext(ResolvedControlContext.init(), ResolvedFormulaContext.init(), None)

    def add_ctrl(self, new_items: tuple[ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate, ...]):
        return ResolvedContext(self.ctrl.add(new_items), self.form, self.ref_struct)

    def add_form(self, new_items: tuple[ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate, ...]):
        return ResolvedContext(self.ctrl, self.form.add(new_items), self.ref_struct)

    def add_ref_struct(self, ref_struct: ResolvedRefStruct):
        return ResolvedContext(self.ctrl, self.form, ref_struct)

@dataclass
class ResolvedUnit:
    resolved_ast: ResolvedInclude | ResolvedDeclaration
    resolved_node_to_token: dict[int, tuple[Token, Token]]
    resolved_nodes: list[ResolvedInclude | ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedStructVar | ResolvedRefStructPred | ResolvedRefStructCon]
    resolved_token_to_node: dict[Token, ResolvedInclude | ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedStructVar | ResolvedRefStructPred | ResolvedRefStructCon]
    resolved_token_to_control: dict[Token, ResolvedControl]
    resolved_decl_refs: dict[str, list[Token]]
    resolved_ctrl_defs: dict[int, tuple[str, int]]
    resolved_ctrl_refs: dict[int, list[int]]
    diagnostics: list[lsp.Diagnostic]
