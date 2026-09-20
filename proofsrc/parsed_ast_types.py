from dataclasses import dataclass
from typing import Literal
from lsprotocol import types as lsp
from immutables import Map
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
class ParsedExistence(ParsedExpr):
    pass

@dataclass(frozen=True)
class ParsedUniqueness(ParsedExpr):
    pass

@dataclass(frozen=True)
class ParsedAccess(ParsedExpr):
    parent: "ParsedIdent | ParsedAccess"
    child: ParsedIdent | ParsedExistence | ParsedUniqueness

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

@dataclass(frozen=True)
class ParsedControl:
    pass

@dataclass(frozen=True)
class ParsedInvalidControl(ParsedControl):
    pass

@dataclass(frozen=True)
class ParsedAssume(ParsedControl):
    premise: ParsedExpr
    body: tuple[ParsedControl, ...]

@dataclass(frozen=True)
class ParsedAny(ParsedControl):
    items: tuple[ParsedIdent | ParsedTypedIdent | ParsedPredTemplate | ParsedFunTemplate, ...]
    body: tuple[ParsedControl, ...]

@dataclass(frozen=True)
class ParsedCase(ParsedControl):
    premise: ParsedExpr
    body: tuple[ParsedControl, ...]

@dataclass(frozen=True)
class ParsedDivide(ParsedControl):
    fact: ParsedExpr
    cases: tuple[ParsedCase, ...]

@dataclass(frozen=True)
class ParsedSome(ParsedControl):
    items: tuple[ParsedIdent | None, ...]
    fact: ParsedExpr
    body: tuple[ParsedControl, ...]

@dataclass(frozen=True)
class ParsedDeny(ParsedControl):
    premise: ParsedExpr
    body: tuple[ParsedControl, ...]

@dataclass(frozen=True)
class ParsedContradict(ParsedControl):
    contradiction: ParsedExpr

@dataclass(frozen=True)
class ParsedExplode(ParsedControl):
    conclusion: ParsedExpr

@dataclass(frozen=True)
class ParsedApply(ParsedControl):
    invoke: Literal["none", "invoke", "invoke-rightward", "invoke-leftward"]
    fact: ParsedExpr
    terms: tuple[ParsedExpr | None, ...]

@dataclass(frozen=True)
class ParsedLift(ParsedControl):
    varterms: tuple[ParsedExpr | None, ...]
    conclusion: ParsedExpr

@dataclass(frozen=True)
class ParsedCharacterize(ParsedControl):
    varterm: ParsedExpr
    conclusion: ParsedExpr

@dataclass(frozen=True)
class ParsedInvoke(ParsedControl):
    direction: Literal["none", "rightward", "leftward"]
    fact: ParsedExpr

@dataclass(frozen=True)
class ParsedExpand(ParsedControl):
    fact: ParsedExpr
    refs: tuple[ParsedIdent, ...]
    indexes: Map[ParsedIdent, tuple[int, ...]]

@dataclass(frozen=True)
class ParsedFold(ParsedControl):
    refs: tuple[ParsedIdent, ...]
    indexes: Map[ParsedIdent, tuple[int, ...]]
    conclusion: ParsedExpr

@dataclass(frozen=True)
class ParsedPad(ParsedControl):
    fact: ParsedExpr
    conclusion: ParsedExpr

@dataclass(frozen=True)
class ParsedSplit(ParsedControl):
    index: int | None
    fact: ParsedExpr

@dataclass(frozen=True)
class ParsedConnect(ParsedControl):
    conclusion: ParsedExpr

@dataclass(frozen=True)
class ParsedSubstitute(ParsedControl):
    fact: ParsedExpr
    env: Map[ParsedExpr, ParsedExpr]
    indexes: Map[ParsedExpr, tuple[int, ...]]

@dataclass(frozen=True)
class ParsedShow(ParsedControl):
    conclusion: ParsedBottom | ParsedExpr
    body: tuple[ParsedControl, ...]

@dataclass(frozen=True)
class ParsedAssert(ParsedControl):
    reference: ParsedExpr

@dataclass(frozen=True)
class ParsedDeclaration:
    name: str

@dataclass(frozen=True)
class ParsedInvalidDeclaration(ParsedDeclaration):
    pass

@dataclass(frozen=True)
class ParsedPrimPred(ParsedDeclaration):
    ref: ParsedIdent
    arity: int
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ParsedAxiom(ParsedDeclaration):
    ref: ParsedIdent
    conclusion: ParsedExpr

@dataclass(frozen=True)
class ParsedTheorem(ParsedDeclaration):
    ref: ParsedIdent
    conclusion: ParsedExpr
    proof: tuple[ParsedControl, ...]

@dataclass(frozen=True)
class ParsedDefPred(ParsedDeclaration):
    ref: ParsedIdent
    args: tuple[ParsedIdent | ParsedPredTemplate | ParsedFunTemplate, ...]
    formula: ParsedExpr
    autoexpand: bool
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ParsedDefCon(ParsedDeclaration):
    ref: ParsedIdent
    ref_theorem: ParsedIdent
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ParsedDefFun(ParsedDeclaration):
    ref: ParsedIdent
    ref_theorem: ParsedIdent
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ParsedDefFunTerm(ParsedDeclaration):
    ref: ParsedIdent
    args: tuple[ParsedIdent | ParsedPredTemplate | ParsedFunTemplate, ...]
    varterm: ParsedExpr
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ParsedEquality(ParsedDeclaration):
    ref: ParsedIdent
    tex: tuple[str, ...]

@dataclass(frozen=True)
class ParsedStruct(ParsedDeclaration):
    ref: ParsedIdent
    vars: tuple[ParsedIdent | ParsedTypedIdent, ...]
    formulas: Map[ParsedIdent, ParsedExpr]

@dataclass(frozen=True)
class ParsedStructPred(ParsedDeclaration):
    ref_struct: ParsedIdent
    ref: ParsedIdent
    args: tuple[ParsedIdent, ...]
    formula: ParsedExpr

@dataclass(frozen=True)
class ParsedStructCon(ParsedDeclaration):
    ref_struct: ParsedIdent
    ref: ParsedIdent
    ref_theorem: ParsedIdent

@dataclass(frozen=True)
class ParsedInclude:
    file: str
    token: Token

@dataclass(frozen=True)
class ParsedInvalidInclude(ParsedInclude):
    pass

@dataclass(frozen=True)
class ParsedUnit:
    ast: ParsedInclude | ParsedDeclaration
    node_to_token: Map[int, tuple[Token, Token]]
    diagnostics: tuple[lsp.Diagnostic, ...]
