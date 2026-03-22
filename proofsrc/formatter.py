from typing import Literal

from ast_types import Term, Formula, Var, RefDefCon, RefDefFun, RefDefFunTerm, FunTemplate, FunLambda, Compound, RefEquality, RefPrimPred, RefDefPred, PredTemplate, PredLambda, AtomicFormula, Not, And, Or, Implies, Iff, Forall, Exists, ExistsUniq, Bottom, RefFact, Context, FormatError
from logic_utils import flatten_op

class ExprFormatter:
    TERM_PRECEDENCE = {
        "Lowest": 0,
        "CompoundInfix": 1,
        "CompoundFunction": 2
    }

    FORMULA_PRECEDENCE = {
        "Lowest": 0,
        "Iff": 1,
        "Implies": 1,
        "Or": 2,
        "And": 2,
        "Symbol": 3,
        "Not": 4,
        "Quantifier": 5,
    }

    def __init__(self, context: Context, mode: Literal["source", "tex"] = "source") -> None:
        self.context = context
        self.mode = mode

    def get_tex_fragments(self, expr: AtomicFormula | Compound) -> list[str]:
        if isinstance(expr, AtomicFormula):
            if isinstance(expr.pred, RefEquality):
                if self.context.decl.equality is None:
                    raise FormatError(f"equality has not been declared yet")
                tex = self.context.decl.equality.tex
            elif isinstance(expr.pred, RefPrimPred):
                tex = self.context.decl.primpreds[expr.pred.name].tex
            elif isinstance(expr.pred, RefDefPred):
                tex = self.context.decl.defpreds[expr.pred.name].tex
            else:
                raise FormatError(f"Unexpected type: {type(expr.pred)}")
            return tex
        elif isinstance(expr, Compound):
            if isinstance(expr.fun, RefDefFun):
                tex = self.context.decl.deffuns[expr.fun.name].tex
            elif isinstance(expr.fun, RefDefFunTerm):
                tex = self.context.decl.deffunterms[expr.fun.name].tex
            else:
                raise FormatError(f"Unexpected type: {type(expr.fun)}")
            return tex
        else:
            raise FormatError(f"Unsupported node type: {type(expr)}")

    def pretty_term(self, expr: Term, parent_prec: int = TERM_PRECEDENCE["Lowest"]) -> str:
        if isinstance(expr, Var):
            return expr.name
        elif isinstance(expr, (RefPrimPred, RefDefPred, RefDefFun, RefDefFunTerm)):
            if self.mode == "source":
                return expr.name
            else:
                return f"\\mathrm{{{expr.name}}}"
        elif isinstance(expr, (PredTemplate, FunTemplate)):
            return expr.name
        elif isinstance(expr, RefDefCon):
            fragments = self.context.decl.defcons[expr.name].tex
            if len(fragments) != 1:
                raise FormatError("arity is different")
            return fragments[0]
        elif isinstance(expr, Compound):
            if isinstance(expr.fun, (RefDefFun, RefDefFunTerm)):
                if self.mode == "source":
                    fragments = [f"{expr.fun.name}("]
                    for i in range(len(expr.args) - 1):
                        fragments.append(",")
                    fragments.append(")")
                else:
                    fragments = self.get_tex_fragments(expr)
                    if len(fragments) != len(expr.args) + 1:
                        raise FormatError("arity is different")
                prec = self.__class__.TERM_PRECEDENCE["CompoundInfix"] if fragments[0] == "" or fragments[-1] == "" else self.__class__.TERM_PRECEDENCE["CompoundFunction"]
                text = ""
                for i in range(len(expr.args)):
                    text += fragments[i]
                    text += " "
                    text += self.pretty_term(expr.args[i], prec)
                    text += " "
                text += fragments[-1]
                return text if prec > parent_prec or parent_prec == self.__class__.TERM_PRECEDENCE["CompoundFunction"] else f"({text})"
            elif isinstance(expr.fun, FunTemplate):
                if expr.fun.arity == 0:
                    text = expr.fun.name
                else:
                    text = f"{expr.fun.name}({",".join([self.pretty_term(arg) for arg in expr.args])})"
                return text if self.__class__.TERM_PRECEDENCE["CompoundFunction"] > parent_prec else f"({text})"
            elif isinstance(expr.fun, FunLambda):
                if len(expr.fun.args) == 0:
                    text = self.pretty_term(expr.fun)
                else:
                    text = f"{self.pretty_term(expr.fun)}({",".join([self.pretty_term(arg) for arg in expr.args])})"
                return text if self.__class__.TERM_PRECEDENCE["CompoundFunction"] > parent_prec else f"({text})"
            else:
                raise FormatError(f"Unexpected type: {type(expr.fun)}")
        elif isinstance(expr, PredLambda):
            return f"\\lambda^P {",".join([var.name for var in expr.args])}. {self.pretty_formula(expr.body)}"
        elif isinstance(expr, FunLambda):
            return f"\\lambda^F {",".join([var.name for var in expr.args])}. {self.pretty_term(expr.body)}"
        else:
            raise FormatError(f"Unsupported node type: {type(expr)}")

    def pretty_formula(self, expr: Formula, parent_prec: int = FORMULA_PRECEDENCE["Lowest"]) -> str:
        if isinstance(expr, AtomicFormula):
            if isinstance(expr.pred, (RefEquality, RefPrimPred, RefDefPred)):
                if self.mode == "source":
                    fragments = [f"{expr.pred.name}("]
                    for i in range(len(expr.args) - 1):
                        fragments.append(",")
                    fragments.append(")")
                else:
                    fragments = self.get_tex_fragments(expr)
                    if len(fragments) != len(expr.args) + 1:
                        raise FormatError("arity is different")
                text = ""
                for i in range(len(expr.args)):
                    text += fragments[i]
                    text += " "
                    text += self.pretty_term(expr.args[i])
                    text += " "
                text += fragments[-1]
                return text if self.__class__.FORMULA_PRECEDENCE["Symbol"] > parent_prec else f"({text})"
            elif isinstance(expr.pred, PredTemplate):
                if expr.pred.arity == 0:
                    text = expr.pred.name
                else:
                    text = f"{expr.pred.name}({",".join([self.pretty_term(arg) for arg in expr.args])})"
                return text if self.__class__.FORMULA_PRECEDENCE["Symbol"] > parent_prec else f"({text})"
            else:
                raise FormatError(f"Unexpected type: {type(expr.pred)}")
        elif isinstance(expr, Not):
            text = f"\\neg {self.pretty_formula(expr.body, self.__class__.FORMULA_PRECEDENCE["Not"])}"
            return text if self.__class__.FORMULA_PRECEDENCE["Not"] > parent_prec else f"({text})"
        elif isinstance(expr, And):
            parts = flatten_op(expr, And)
            text = " \\wedge ".join(self.pretty_formula(part, self.__class__.FORMULA_PRECEDENCE["And"]) for part in parts)
            return text if self.__class__.FORMULA_PRECEDENCE["And"] > parent_prec else f"({text})"
        elif isinstance(expr, Or):
            parts = flatten_op(expr, Or)
            text = " \\vee ".join(self.pretty_formula(part, self.__class__.FORMULA_PRECEDENCE["Or"]) for part in parts)
            return text if self.__class__.FORMULA_PRECEDENCE["Or"] > parent_prec else f"({text})"
        elif isinstance(expr, Implies):
            text = f"{self.pretty_formula(expr.left, self.__class__.FORMULA_PRECEDENCE["Implies"])} \\to {self.pretty_formula(expr.right, self.__class__.FORMULA_PRECEDENCE["Implies"])}"
            return text if self.__class__.FORMULA_PRECEDENCE["Implies"] > parent_prec else f"({text})"
        elif isinstance(expr, Iff):
            text = f"{self.pretty_formula(expr.left, self.__class__.FORMULA_PRECEDENCE["Iff"])} \\leftrightarrow {self.pretty_formula(expr.right, self.__class__.FORMULA_PRECEDENCE["Iff"])}"
            return text if self.__class__.FORMULA_PRECEDENCE["Iff"] > parent_prec else f"({text})"
        elif isinstance(expr, (Forall, Exists, ExistsUniq)):
            body = expr
            qvars_text = ""
            while True:
                if isinstance(body, Forall):
                    qvars_text += "\\forall"
                elif isinstance(body, Exists):
                    qvars_text += "\\exists"
                elif isinstance(body, ExistsUniq):
                    qvars_text += "\\exists!"
                else:
                    break
                if isinstance(body.var, Var):
                    qvars_text += f" {self.pretty_term(body.var)}"
                elif isinstance(body.var, PredTemplate):
                    qvars_text += f"^P {self.pretty_term(body.var)}"
                elif isinstance(body.var, FunTemplate):
                    qvars_text += f"^F {self.pretty_term(body.var)}"
                else:
                    raise FormatError(f"Unexpected type: {type(body.var)}")
                body = body.body
            text = f"{qvars_text} {self.pretty_formula(body, self.__class__.FORMULA_PRECEDENCE["Quantifier"])}"
            return text if self.__class__.FORMULA_PRECEDENCE["Quantifier"] > parent_prec else f"({text})"
        else:
            raise FormatError(f"Unsupported node type: {type(expr)}")

    def pretty_expr(self, expr: RefFact | Bottom | Formula | Term) -> str:
        if isinstance(expr, RefFact):
            return expr.name
        elif isinstance(expr, Bottom):
            return "\\bot"
        elif isinstance(expr, Formula):
            return self.pretty_formula(expr)
        elif isinstance(expr, Term):
            return self.pretty_term(expr)
        else:
            raise FormatError(f"Unsupported node type: {type(expr)}")
