from dataclasses import dataclass
from typing import List, Dict

import logging
logger = logging.getLogger("proof")

@dataclass
class Context:
    formulas: list        # 通常の論理式
    bot_derived: bool  # 矛盾導出フラグ
    atoms: dict
    axioms: dict
    theorems: dict
    definitions: Dict[str, "Definition"]
    defcons: Dict[str, "DefCon"]

    @staticmethod
    def init():
        return Context(formulas=[], bot_derived=False, atoms={}, axioms={}, theorems={}, definitions={}, defcons={})

    def copy(self, formulas, bot_derived):
        return Context(formulas=formulas, bot_derived=bot_derived, atoms=self.atoms, axioms=self.axioms, theorems=self.theorems, definitions=self.definitions, defcons=self.defcons)

# === DSL ノード定義 ===
@dataclass
class Atom:
    type: str
    name: str
    arity: int

@dataclass
class Axiom:
    name: str
    conclusion: object

@dataclass
class Theorem:
    name: str
    conclusion: object
    proof: list

@dataclass
class Check:
    conclusion: object   # Expr AST

@dataclass
class Assume:
    premise: object      # Expr AST
    conclusion: object   # Expr AST
    body: list

@dataclass
class Any:
    vars: List[str]
    conclusion: object
    body: list

@dataclass
class Divide:
    fact: object
    conclusion: object
    cases: list

@dataclass
class Case:
    premise: object
    conclusion: object
    body: list

@dataclass
class Some:
    env: Dict[str, str]
    fact: object
    conclusion: object
    body: list

@dataclass
class Deny:
    premise: object
    body: list

@dataclass
class Contradict:
    contradiction: object

@dataclass
class Explode:
    conclusion: object

@dataclass
class Apply:
    fact: object
    env: dict
    premise: object
    conclusion: object

@dataclass
class Lift:
    fact: object
    env: dict
    conclusion: object

@dataclass
class Invoke:
    fact: object
    conclusion: object

@dataclass
class Expand:
    fact: object
    conclusion: object

@dataclass
class Characterize:
    fact: object
    env: dict
    conclusion: object

@dataclass
class Identify:
    fact: object
    env: dict
    conclusion: object

@dataclass
class Pad:
    fact: object
    conclusion: object

@dataclass
class Split:
    fact: object

@dataclass
class Connect:
    conclusion: object

@dataclass
class Definition:
    type: str
    name: str
    arity: int
    formula: object

@dataclass
class DefCon:
    name: str
    theorem: str
    formula: object

@dataclass
class Symbol:
    name: str
    args: list[str]

@dataclass
class Forall:
    var: str
    body: object

@dataclass
class Exists:
    var: str
    body: object

@dataclass
class ExistsUniq:
    var: str
    body: object

@dataclass
class Implies:
    left: object
    right: object

@dataclass
class And:
    left: object
    right: object

@dataclass
class Or:
    left: object
    right: object

@dataclass
class Not:
    body: object

@dataclass
class Iff:
    left: object
    right: object

@dataclass
class Bottom:
    pass

def pretty(node, indent=0):
    sp = "  " * indent  # インデント幅2スペース
    if isinstance(node, Atom):
        logger.debug(f"{sp}[Atom] type: {node.type}")
        logger.debug(f"{sp}       name: {node.name}")
        logger.debug(f"{sp}       arity: {node.arity}")

    elif isinstance(node, Theorem):
        logger.debug(f"{sp}[Theorem] name: {node.name}")
        logger.debug(f"{sp}          conclusion: {pretty_expr(node.conclusion)}")
        for stmt in node.proof:
            pretty(stmt, indent + 1)

    elif isinstance(node, Check):
        logger.debug(f"{sp}[Check] {pretty_expr(node.conclusion)}")

    elif isinstance(node, Any):
        logger.debug(f"{sp}[Any] vars: {', '.join(node.vars)}")
        logger.debug(f"{sp}      conclusion: {pretty_expr(node.conclusion)}")
        for stmt in node.body:
            pretty(stmt, indent + 1)

    elif isinstance(node, Assume):
        logger.debug(f"{sp}[Assume] premise: {pretty_expr(node.premise)}")
        logger.debug(f"{sp}         conclusion: {pretty_expr(node.conclusion)}")
        for stmt in node.body:
            pretty(stmt, indent + 1)
    
    elif isinstance(node, Divide):
        logger.debug(f"{sp}[Divide] fact: {pretty_expr(node.fact)}")
        logger.debug(f"{sp}         conclusion: {pretty_expr(node.conclusion)}")
        for stmt in node.cases:
            pretty(stmt, indent + 1)

    elif isinstance(node, Case):
        logger.debug(f"{sp}[Case] case: {pretty_expr(node.premise)}")
        logger.debug(f"{sp}       conclusion: {pretty_expr(node.conclusion)}")
        for stmt in node.body:
            pretty(stmt, indent + 1)
    
    elif isinstance(node, Some):
        logger.debug(f"{sp}[Some] vars: {','.join(node.vars)}")
        logger.debug(f"{sp}       premise: {pretty_expr(node.premise)}")
        logger.debug(f"{sp}       conclusion: {pretty_expr(node.conclusion)}")
        for stmt in node.body:
            pretty(stmt, indent + 1)
    
    elif isinstance(node, Deny):
        logger.debug(f"{sp}[Deny] premise: {pretty_expr(node.premise)}")
        for stmt in node.body:
            pretty(stmt, indent + 1)
    
    elif isinstance(node, Contradict):
        logger.debug(f"{sp}[Contradict] contradiction: {pretty_expr(node.contradiction)}")

    elif isinstance(node, Explode):
        logger.debug(f"{sp}[Explode] conclusion: {pretty_expr(node.conclusion)}")

    elif isinstance(node, Apply):
        logger.debug(f"{sp}[Apply] fact: {pretty_expr(node.conclusion)}")
        if node.env is not None:
            logger.debug(f"{sp}        env: {node.env}")
        if node.premise is not None:
            logger.debug(f"{sp}        premise: {pretty_expr(node.premise)}")
        logger.debug(f"{sp}        conclusion: {pretty_expr(node.conclusion)}")
    
    elif isinstance(node, Lift):
        logger.debug(f"{sp}[Lift] fact: {pretty_expr(node.fact)}")
        logger.debug(f"{sp}       env: {node.env}")
        logger.debug(f"{sp}       conclusion: {pretty_expr(node.conclusion)}")

    elif isinstance(node, Definition):
        logger.debug(f"{sp}Definition {node.name}: {node.body}")

    else:
        raise TypeError(f"Unsupported node type: {type(node)}")

def pretty_expr(expr):
    if isinstance(expr, Axiom):
        return expr.name
    if isinstance(expr, Theorem):
        return expr.name
    if isinstance(expr, Symbol):
        return f"{expr.name}({",".join(expr.args)})"
    if isinstance(expr, Implies):
        return f"{pretty_expr(expr.left)} \\to {pretty_expr(expr.right)}"
    if isinstance(expr, Iff):
        return f"{pretty_expr(expr.left)} \\leftrightarrow {pretty_expr(expr.right)}"
    if isinstance(expr, And):
        return f"{pretty_expr(expr.left)} \\wedge {pretty_expr(expr.right)}"
    if isinstance(expr, Or):
        return f"{pretty_expr(expr.left)} \\vee {pretty_expr(expr.right)}"
    if isinstance(expr, Not):
        return f"\\neg({pretty_expr(expr.body)})"
    if isinstance(expr, Forall):
        return f"\\forall {expr.var}({pretty_expr(expr.body)})"
    if isinstance(expr, Exists):
        return f"\\exists {expr.var}({pretty_expr(expr.body)})"
    if isinstance(expr, ExistsUniq):
        return f"\\exists! {expr.var}({pretty_expr(expr.body)})"
    if isinstance(expr, Bottom):
        return "\\bot"
    raise TypeError(f"Unsupported node type: {type(expr)}")
