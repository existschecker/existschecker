from lexer import Token
from dataclasses import dataclass
from typing import Literal

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
    pass

@dataclass(frozen=True)
class ResolvedRefDefConUniq(ResolvedRefFact):
    pass

@dataclass(frozen=True)
class ResolvedRefDefFunExist(ResolvedRefFact):
    pass

@dataclass(frozen=True)
class ResolvedRefDefFunUniq(ResolvedRefFact):
    pass

@dataclass
class ResolvedControl:
    pass

@dataclass
class ResolvedInvalidControl(ResolvedControl):
    pass

@dataclass
class ResolvedAssume(ResolvedControl):
    premise: ResolvedFormula
    body: list[ResolvedControl]

@dataclass
class ResolvedAny(ResolvedControl):
    items: list["ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate"]
    body: list[ResolvedControl]

@dataclass
class ResolvedCase(ResolvedControl):
    premise: ResolvedFormula
    body: list[ResolvedControl]

@dataclass
class ResolvedDivide(ResolvedControl):
    fact: ResolvedRefFact | ResolvedFormula
    cases: list[ResolvedCase]

@dataclass
class ResolvedSome(ResolvedControl):
    items: list[ResolvedVar | None]
    fact: ResolvedRefFact | ResolvedFormula
    body: list[ResolvedControl]

@dataclass
class ResolvedDeny(ResolvedControl):
    premise: ResolvedFormula
    body: list[ResolvedControl]

@dataclass
class ResolvedContradict(ResolvedControl):
    contradiction: ResolvedFormula

@dataclass
class ResolvedExplode(ResolvedControl):
    conclusion: ResolvedFormula

@dataclass
class ResolvedApply(ResolvedControl):
    invoke: Literal["none", "invoke", "invoke-rightward", "invoke-leftward"]
    fact: ResolvedRefFact | ResolvedFormula
    terms: list[ResolvedTerm | None]

@dataclass
class ResolvedLift(ResolvedControl):
    varterms: list[ResolvedVarTerm | None]
    conclusion: ResolvedFormula

@dataclass
class ResolvedCharacterize(ResolvedControl):
    varterm: ResolvedVarTerm
    conclusion: ResolvedExistsUniq

@dataclass
class ResolvedInvoke(ResolvedControl):
    direction: Literal["none", "rightward", "leftward"]
    fact: ResolvedImplies | ResolvedIff

@dataclass
class ResolvedExpand(ResolvedControl):
    fact: ResolvedRefFact | ResolvedFormula
    refs: list[ResolvedRefDefFunTerm | ResolvedRefDefPred]
    indexes: dict[ResolvedRefDefFunTerm | ResolvedRefDefPred, list[int]]

@dataclass
class ResolvedFold(ResolvedControl):
    refs: list[ResolvedRefDefFunTerm | ResolvedRefDefPred]
    indexes: dict[ResolvedRefDefFunTerm | ResolvedRefDefPred, list[int]]
    conclusion: ResolvedFormula

@dataclass
class ResolvedPad(ResolvedControl):
    fact: ResolvedRefFact | ResolvedFormula
    conclusion: ResolvedFormula

@dataclass
class ResolvedSplit(ResolvedControl):
    index: int | None
    fact: ResolvedRefFact | ResolvedFormula

@dataclass
class ResolvedConnect(ResolvedControl):
    conclusion: ResolvedFormula

@dataclass
class ResolvedSubstitute(ResolvedControl):
    fact: ResolvedRefFact | ResolvedFormula
    env: dict[ResolvedTerm, ResolvedTerm]
    indexes: dict[ResolvedTerm, list[int]]

@dataclass
class ResolvedShow(ResolvedControl):
    conclusion: ResolvedBottom | ResolvedFormula
    body: list[ResolvedControl]

@dataclass
class ResolvedAssert(ResolvedControl):
    reference: ResolvedRefFact | ResolvedFormula

@dataclass
class ResolvedDeclaration:
    name: str

@dataclass
class ResolvedInvalidDeclaration(ResolvedDeclaration):
    pass

@dataclass
class ResolvedPrimPred(ResolvedDeclaration):
    ref: ResolvedRefPrimPred
    arity: int
    tex: list[str]

@dataclass
class ResolvedAxiom(ResolvedDeclaration):
    ref: ResolvedRefAxiom
    conclusion: ResolvedFormula

@dataclass
class ResolvedTheorem(ResolvedDeclaration):
    ref: ResolvedRefTheorem
    conclusion: ResolvedFormula
    proof: list[ResolvedControl]

@dataclass
class ResolvedDefPred(ResolvedDeclaration):
    ref: ResolvedRefDefPred
    args: list[ResolvedVar | ResolvedPredTemplate | ResolvedFunTemplate]
    formula: ResolvedFormula
    autoexpand: bool
    tex: list[str]

@dataclass
class ResolvedDefConExist(ResolvedDeclaration):
    ref: ResolvedRefDefConExist
    formula: ResolvedFormula
    ref_con: ResolvedRefDefCon

@dataclass
class ResolvedDefConUniq(ResolvedDeclaration):
    ref: ResolvedRefDefConUniq
    formula: ResolvedFormula
    ref_con: ResolvedRefDefCon

@dataclass
class ResolvedDefCon(ResolvedDeclaration):
    ref: ResolvedRefDefCon
    ref_theorem: ResolvedRefTheorem
    tex: list[str]

@dataclass
class ResolvedDefFunExist(ResolvedDeclaration):
    ref: ResolvedRefDefFunExist
    formula: ResolvedFormula
    ref_fun: ResolvedRefDefFun

@dataclass
class ResolvedDefFunUniq(ResolvedDeclaration):
    ref: ResolvedRefDefFunUniq
    formula: ResolvedFormula
    ref_fun: ResolvedRefDefFun

@dataclass
class ResolvedDefFun(ResolvedDeclaration):
    ref: ResolvedRefDefFun
    ref_theorem: ResolvedRefTheorem
    tex: list[str]

@dataclass
class ResolvedDefFunTerm(ResolvedDeclaration):
    ref: ResolvedRefDefFunTerm
    args: list[ResolvedVar | ResolvedPredTemplate | ResolvedFunTemplate]
    varterm: ResolvedVarTerm
    tex: list[str]

@dataclass
class ResolvedEquality(ResolvedDeclaration):
    ref: ResolvedRefEquality
    tex: list[str]

@dataclass
class ResolvedInclude:
    file: str
    token: Token

@dataclass
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

@dataclass
class ResolvedStruct(ResolvedDeclaration):
    ref: ResolvedRefStruct
    fields: tuple["ResolvedVar | ResolvedStructVar", ...]
    conditions: dict[ResolvedRefStructCondition, ResolvedFormula]

@dataclass(frozen=True)
class ResolvedRefStructPred:
    name: str

@dataclass
class ResolvedStructPred(ResolvedDeclaration):
    ref_struct: ResolvedRefStruct
    ref: ResolvedRefStructPred
    args: tuple[ResolvedVar, ...]
    formula: ResolvedFormula

@dataclass(frozen=True)
class ResolvedStructMemberPred(ResolvedPredTerm):
    parent: ResolvedStructVar | ResolvedStructMemberField
    struct_pred: ResolvedRefStructPred

@dataclass
class ResolvedFormulaContext:
    vars: list[ResolvedVar]
    struct_vars: list[ResolvedStructVar]
    pred_tmpls: list[ResolvedPredTemplate]
    fun_tmpls: list[ResolvedFunTemplate]
    used_names: set[str]

    @staticmethod
    def init() -> "ResolvedFormulaContext":
        return ResolvedFormulaContext(vars=[], struct_vars=[], pred_tmpls=[], fun_tmpls=[], used_names=set())

    def add(self, new_vars: list[ResolvedVar], new_struct_vars: list[ResolvedStructVar], new_pred_tmpls: list[ResolvedPredTemplate], new_fun_tmpls: list[ResolvedFunTemplate]) -> "ResolvedFormulaContext":
        new_used_names = self.used_names.copy()
        for item in new_vars + new_struct_vars + new_pred_tmpls + new_fun_tmpls:
            if item.name in new_used_names:
                msg = f"{item.name} is already used"
                raise Exception(msg)
            new_used_names.add(item.name)
        return ResolvedFormulaContext(list(self.vars + new_vars), list(self.struct_vars + new_struct_vars), list(self.pred_tmpls + new_pred_tmpls), list(self.fun_tmpls + new_fun_tmpls), new_used_names)

@dataclass
class ResolvedControlContext:
    vars: list[ResolvedVar]
    struct_vars: list[ResolvedStructVar]
    pred_tmpls: list[ResolvedPredTemplate]
    fun_tmpls: list[ResolvedFunTemplate]
    used_names: set[str]

    @staticmethod
    def init() -> "ResolvedControlContext":
        return ResolvedControlContext(vars=[], struct_vars=[], pred_tmpls=[], fun_tmpls=[], used_names=set())

    def add(self, new_vars: list[ResolvedVar], new_struct_vars: list[ResolvedStructVar], new_pred_tmpls: list[ResolvedPredTemplate], new_fun_tmpls: list[ResolvedFunTemplate]) -> "ResolvedControlContext":
        new_used_names = self.used_names.copy()
        for item in new_vars + new_struct_vars + new_pred_tmpls + new_fun_tmpls:
            if item.name in new_used_names:
                msg = f"{item.name} is already used"
                raise Exception(msg)
            new_used_names.add(item.name)
        return ResolvedControlContext(list(self.vars + new_vars), list(self.struct_vars + new_struct_vars), list(self.pred_tmpls + new_pred_tmpls), list(self.fun_tmpls + new_fun_tmpls), new_used_names)

@dataclass
class ResolvedContext:
    ctrl: ResolvedControlContext
    form: ResolvedFormulaContext
    ref_struct: ResolvedRefStruct | None

    @staticmethod
    def init() -> "ResolvedContext":
        return ResolvedContext(ResolvedControlContext.init(), ResolvedFormulaContext.init(), None)

    def add_ctrl(self, new_vars: list[ResolvedVar], new_struct_vars: list[ResolvedStructVar], new_pred_tmpls: list[ResolvedPredTemplate], new_fun_tmpls: list[ResolvedFunTemplate]):
        return ResolvedContext(self.ctrl.add(new_vars, new_struct_vars, new_pred_tmpls, new_fun_tmpls), self.form, self.ref_struct)

    def add_form(self, new_vars: list[ResolvedVar], new_struct_vars: list[ResolvedStructVar], new_pred_tmpls: list[ResolvedPredTemplate], new_fun_tmpls: list[ResolvedFunTemplate]):
        return ResolvedContext(self.ctrl, self.form.add(new_vars, new_struct_vars, new_pred_tmpls, new_fun_tmpls), self.ref_struct)

    def add_ref_struct(self, ref_struct: ResolvedRefStruct):
        return ResolvedContext(self.ctrl, self.form, ref_struct)
