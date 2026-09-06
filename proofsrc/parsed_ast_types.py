from dataclasses import dataclass, field
from typing import Literal
from lsprotocol import types as lsp

from lexer import Token

@dataclass(frozen=True)
class ParsedExpr:
    pass

@dataclass(frozen=True)
class ParsedIdent(ParsedExpr):
    name: str

@dataclass(frozen=True)
class ParsedTypedIdent(ParsedExpr):
    name: ParsedIdent
    type: ParsedIdent

@dataclass(frozen=True)
class ParsedAccess(ParsedExpr):
    parent: "ParsedIdent | ParsedAccess"
    child: ParsedIdent

@dataclass(frozen=True)
class ParsedFunLambda(ParsedExpr):
    args: tuple[ParsedIdent, ...]
    body: ParsedExpr

@dataclass(frozen=True)
class ParsedFunTemplate(ParsedExpr):
    name: str
    arity: int

@dataclass(frozen=True)
class ParsedIdentArgs(ParsedExpr):
    name: ParsedIdent
    args: tuple[ParsedExpr, ...]

@dataclass(frozen=True)
class ParsedCall(ParsedExpr):
    callee: ParsedAccess
    args: tuple[ParsedExpr, ...]

@dataclass(frozen=True)
class ParsedPredTemplate(ParsedExpr):
    name: str
    arity: int

@dataclass(frozen=True)
class ParsedPredLambda(ParsedExpr):
    args: tuple[ParsedIdent, ...]
    body: ParsedExpr

@dataclass(frozen=True)
class ParsedNot(ParsedExpr):
    body: ParsedExpr

@dataclass(frozen=True)
class ParsedAnd(ParsedExpr):
    left: ParsedExpr
    right: ParsedExpr

@dataclass(frozen=True)
class ParsedOr(ParsedExpr):
    left: ParsedExpr
    right: ParsedExpr

@dataclass(frozen=True)
class ParsedImplies(ParsedExpr):
    left: ParsedExpr
    right: ParsedExpr

@dataclass(frozen=True)
class ParsedIff(ParsedExpr):
    left: ParsedExpr
    right: ParsedExpr

@dataclass(frozen=True)
class ParsedForall(ParsedExpr):
    var: ParsedIdent | ParsedTypedIdent | ParsedPredTemplate | ParsedFunTemplate
    body: ParsedExpr

@dataclass(frozen=True)
class ParsedExists(ParsedExpr):
    var: ParsedIdent
    body: ParsedExpr

@dataclass(frozen=True)
class ParsedExistsUniq(ParsedExpr):
    var: ParsedIdent
    body: ParsedExpr

@dataclass(frozen=True)
class ParsedBottom:
    pass

@dataclass
class ParsedControl:
    pass

@dataclass
class ParsedInvalidControl(ParsedControl):
    pass

@dataclass
class ParsedAssume(ParsedControl):
    premise: ParsedExpr
    body: list[ParsedControl]

@dataclass
class ParsedAny(ParsedControl):
    items: list[ParsedIdent | ParsedTypedIdent | ParsedPredTemplate | ParsedFunTemplate]
    body: list[ParsedControl]

@dataclass
class ParsedCase(ParsedControl):
    premise: ParsedExpr
    body: list[ParsedControl]

@dataclass
class ParsedDivide(ParsedControl):
    fact: ParsedExpr
    cases: list[ParsedCase]

@dataclass
class ParsedSome(ParsedControl):
    items: list[ParsedIdent | None]
    fact: ParsedExpr
    body: list[ParsedControl]

@dataclass
class ParsedDeny(ParsedControl):
    premise: ParsedExpr
    body: list[ParsedControl]

@dataclass
class ParsedContradict(ParsedControl):
    contradiction: ParsedExpr

@dataclass
class ParsedExplode(ParsedControl):
    conclusion: ParsedExpr

@dataclass
class ParsedApply(ParsedControl):
    invoke: Literal["none", "invoke", "invoke-rightward", "invoke-leftward"]
    fact: ParsedExpr
    terms: list[ParsedExpr | None]

@dataclass
class ParsedLift(ParsedControl):
    varterms: list[ParsedExpr | None]
    conclusion: ParsedExpr

@dataclass
class ParsedCharacterize(ParsedControl):
    varterm: ParsedExpr
    conclusion: ParsedExpr

@dataclass
class ParsedInvoke(ParsedControl):
    direction: Literal["none", "rightward", "leftward"]
    fact: ParsedExpr

@dataclass
class ParsedExpand(ParsedControl):
    fact: ParsedExpr
    refs: list[ParsedIdent]
    indexes: dict[ParsedIdent, list[int]]

@dataclass
class ParsedFold(ParsedControl):
    refs: list[ParsedIdent]
    indexes: dict[ParsedIdent, list[int]]
    conclusion: ParsedExpr

@dataclass
class ParsedPad(ParsedControl):
    fact: ParsedExpr
    conclusion: ParsedExpr

@dataclass
class ParsedSplit(ParsedControl):
    index: int | None
    fact: ParsedExpr

@dataclass
class ParsedConnect(ParsedControl):
    conclusion: ParsedExpr

@dataclass
class ParsedSubstitute(ParsedControl):
    fact: ParsedExpr
    env: dict[ParsedExpr, ParsedExpr]
    indexes: dict[ParsedExpr, list[int]]

@dataclass
class ParsedShow(ParsedControl):
    conclusion: ParsedBottom | ParsedExpr
    body: list[ParsedControl]

@dataclass
class ParsedAssert(ParsedControl):
    reference: ParsedExpr

@dataclass
class ParsedDeclaration:
    name: str

@dataclass
class ParsedInvalidDeclaration(ParsedDeclaration):
    pass

@dataclass
class ParsedPrimPred(ParsedDeclaration):
    ref: ParsedIdent
    arity: int
    tex: list[str]

@dataclass
class ParsedAxiom(ParsedDeclaration):
    ref: ParsedIdent
    conclusion: ParsedExpr

@dataclass
class ParsedTheorem(ParsedDeclaration):
    ref: ParsedIdent
    conclusion: ParsedExpr
    proof: list[ParsedControl]

@dataclass
class ParsedDefPred(ParsedDeclaration):
    ref: ParsedIdent
    args: list[ParsedIdent | ParsedPredTemplate | ParsedFunTemplate]
    formula: ParsedExpr
    autoexpand: bool
    tex: list[str]

@dataclass
class ParsedDefExist(ParsedDeclaration):
    ref: ParsedIdent
    formula: ParsedExpr
    ref_term: ParsedIdent

@dataclass
class ParsedDefUniq(ParsedDeclaration):
    ref: ParsedIdent
    formula: ParsedExpr
    ref_term: ParsedIdent

@dataclass
class ParsedDefCon(ParsedDeclaration):
    ref: ParsedIdent
    ref_theorem: ParsedIdent
    tex: list[str]

@dataclass
class ParsedDefFun(ParsedDeclaration):
    ref: ParsedIdent
    args: list[ParsedIdent | ParsedPredTemplate | ParsedFunTemplate]
    ref_theorem: ParsedIdent
    tex: list[str]

@dataclass
class ParsedDefFunTerm(ParsedDeclaration):
    ref: ParsedIdent
    args: list[ParsedIdent | ParsedPredTemplate | ParsedFunTemplate]
    varterm: ParsedExpr
    tex: list[str]

@dataclass
class ParsedEquality(ParsedDeclaration):
    ref: ParsedIdent
    tex: list[str]

@dataclass
class ParsedStruct(ParsedDeclaration):
    ref: ParsedIdent
    vars: list[ParsedIdent | ParsedTypedIdent]
    formulas: dict[ParsedIdent, ParsedExpr]

@dataclass
class ParsedStructPred(ParsedDeclaration):
    ref_struct: ParsedIdent
    ref: ParsedIdent
    args: tuple[ParsedIdent, ...]
    formula: ParsedExpr

@dataclass
class ParsedInclude:
    file: str
    token: Token

@dataclass
class ParsedInvalidInclude(ParsedInclude):
    pass

@dataclass
class ParsedUnit:
    ast: ParsedInclude | ParsedDeclaration | None = None
    node_to_token: dict[int, tuple[int, int]] = field(default_factory=dict[int, tuple[int, int]])
    diagnostics: list[lsp.Diagnostic] = field(default_factory=list[lsp.Diagnostic])
