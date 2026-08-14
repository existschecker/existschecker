from lsprotocol import types as lsp
from pygls import uris
from typing import Sequence
from ast_types import Context, DeclarationUnit, Term, Declaration, PrimPred, Axiom, Theorem, DefPred, DefCon, DefConExist, DefConUniq, DefFun, DefFunExist, DefFunUniq, DefFunTerm, Equality, InvalidDeclaration, Formula, AtomicFormula, Not, And, Or, Implies, Iff, Forall, Exists, ExistsUniq, PredTemplate, Var, FunTemplate, RefEquality, Compound, RefPrimPred, RefDefPred, RefDefCon, RefDefFun, RefDefFunTerm, VarTerm, PredTerm, FunTerm, Control, Any, Assume, Divide, Some, Deny, Case, Contradict, Explode, Apply, Lift, Characterize, Invoke, Expand, Fold, Pad, Split, Connect, Substitute, Show, Assert, InvalidControl, RefAxiom, RefTheorem, RefDefConExist, RefDefConUniq, RefDefFunExist, RefDefFunUniq, RefFact, PredLambda, FunLambda, Bottom, ControlContext, FormulaContext, Include, InvalidInclude
from parsed_ast_types import ParsedExpr, ParsedIdent, ParsedIdentArgs, ParsedFunTemplate, ParsedFunLambda, ParsedPredTemplate, ParsedPredLambda, ParsedNot, ParsedAnd, ParsedOr, ParsedImplies, ParsedIff, ParsedForall, ParsedExists, ParsedExistsUniq, ParsedBottom, ParsedControl, ParsedInvalidControl, ParsedAny, ParsedAssume, ParsedDivide, ParsedSome, ParsedDeny, ParsedContradict, ParsedCase, ParsedExplode, ParsedApply, ParsedLift, ParsedCharacterize, ParsedInvoke, ParsedExpand, ParsedFold, ParsedPad, ParsedSplit, ParsedConnect, ParsedSubstitute, ParsedShow, ParsedAssert, ParsedDeclaration, ParsedInvalidDeclaration, ParsedPrimPred, ParsedAxiom, ParsedTheorem, ParsedDefPred, ParsedDefCon, ParsedDefFun, ParsedDefFunTerm, ParsedDefExist, ParsedDefUniq, ParsedEquality, ParsedInclude, ParsedInvalidInclude, ParsedUnit
from lexer import Token
from logic_utils import strip_forall_vars

class ResolveError(Exception):
    def __init__(self, node: ParsedDeclaration | ParsedControl | ParsedExpr, msg: str) -> None:
        self.node = node
        self.msg = msg

class NameResolver:
    def __init__(self, unit: DeclarationUnit, parsed_unit: ParsedUnit) -> None:
        self.unit = unit
        self.parsed_unit = parsed_unit

    def add_lsp_error(self, token: Token, message: str) -> None:
        uri = uris.from_fs_path(token.file)
        if uri is None:
            return
        diag = lsp.Diagnostic(
            range=lsp.Range(
                start=lsp.Position(line=token.line - 1, character=token.column - 1),
                end=lsp.Position(line=token.end_line - 1, character=token.end_column - 1)
            ),
            message=message,
            source="Resolver",
            severity=lsp.DiagnosticSeverity.Error
        )
        self.unit.diagnostics.append(diag)

    def get_node_token(self, node: ParsedDeclaration | ParsedControl | ParsedExpr) -> Token:
        return self.unit.tokens[self.parsed_unit.node_to_token[id(node)][0]]

    def add_node_to_token(self, node: Declaration | Control | Formula | Term | RefFact, parsed: ParsedDeclaration | ParsedControl | ParsedExpr) -> None:
        self.unit.node_to_token[id(node)] = self.parsed_unit.node_to_token[id(parsed)]
        self.unit.nodes.append(node)
        if isinstance(node, (RefFact, RefEquality, RefPrimPred, RefDefPred, RefDefCon, RefDefFun, RefDefFunTerm)):
            self.add_decl_ref(node.name, self.unit.tokens[self.unit.node_to_token[id(node)][0]])

    def add_decl_ref(self, name: str, token: Token) -> None:
        if name not in self.unit.decl_refs:
            self.unit.decl_refs[name] = []
        self.unit.decl_refs[name].append(token)

    def add_ctrl_defs_refs(self, def_node: Term, ref_node: Term) -> None:
        self.unit.ctrl_defs[id(ref_node)] = id(def_node)
        if id(def_node) not in self.unit.ctrl_refs:
            self.unit.ctrl_refs[id(def_node)] = []
        self.unit.ctrl_refs[id(def_node)].append(id(ref_node))

    def resolve_unit(self, context: Context) -> None:
        if isinstance(self.parsed_unit.ast, ParsedInclude):
            self.unit.ast = self.resolve_include(self.parsed_unit.ast, context)
        elif isinstance(self.parsed_unit.ast, ParsedDeclaration):
            self.unit.ast = self.resolve_declaration(self.parsed_unit.ast, context)

    def resolve_include(self, node: ParsedInclude, context: Context) -> Include:
        if isinstance(node, ParsedInvalidInclude):
            return InvalidInclude(node.file, node.token)
        else:
            return Include(node.file, node.token)

    def resolve_declaration(self, node: ParsedDeclaration, context: Context) -> Declaration:
        try:
            if isinstance(node, ParsedPrimPred):
                return self.resolve_primpred(node, context)
            elif isinstance(node, ParsedAxiom):
                return self.resolve_axiom(node, context)
            elif isinstance(node, ParsedTheorem):
                return self.resolve_theorem(node, context)
            elif isinstance(node, ParsedDefPred):
                return self.resolve_defpred(node, context)
            elif isinstance(node, ParsedDefCon):
                return self.resolve_defcon(node, context)
            elif isinstance(node, ParsedDefFun):
                return self.resolve_deffun(node, context)
            elif isinstance(node, ParsedDefExist):
                return self.resolve_defexist(node, context)
            elif isinstance(node, ParsedDefUniq):
                return self.resolve_defuniq(node, context)
            elif isinstance(node, ParsedDefFunTerm):
                return self.resolve_deffunterm(node, context)
            elif isinstance(node, ParsedEquality):
                return self.resolve_equality(node, context)
            elif isinstance(node, ParsedInvalidDeclaration):
                return self.resolve_invalid_declaration(node, context)
            else:
                msg = f"Unsupported node {node}"
                raise ResolveError(node, msg)
        except ResolveError as e:
            self.add_lsp_error(self.get_node_token(e.node), e.msg)
            resolved = InvalidDeclaration(node.name)
            self.add_node_to_token(resolved, node)
            return resolved

    def resolve_primpred(self, node: ParsedPrimPred, context: Context) -> PrimPred:
        if node.ref.name in context.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = RefPrimPred(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        tex = self.create_or_check_tex(node.tex, node.name, node.arity, node)
        resolved = PrimPred(node.name, ref, node.arity, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_axiom(self, node: ParsedAxiom, context: Context) -> Axiom:
        if node.ref.name in context.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = RefAxiom(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        conclusion = self.resolve_formula(node.conclusion, context)
        resolved = Axiom(node.name, ref, conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_theorem(self, node: ParsedTheorem, context: Context) -> Theorem:
        if node.ref.name in context.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = RefTheorem(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        conclusion = self.resolve_formula(node.conclusion, context)
        proof = self.resolve_block(node.proof, context.copy_ctrl())
        resolved = Theorem(node.name, ref, conclusion, proof)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_defpred(self, node: ParsedDefPred, context: Context) -> DefPred:
        if node.ref.name in context.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = RefDefPred(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        local_vars, local_pred_tmpls, local_fun_tmpls, args = self.resolve_vars_or_pred_tmpls_or_fun_tmpls(node.args, context.ctrl)
        local_ctx = context.add_ctrl(local_vars, [], local_pred_tmpls, local_fun_tmpls, args)
        formula = self.resolve_formula(node.formula, local_ctx)
        tex = self.create_or_check_tex(node.tex, node.name, len(node.args), node)
        resolved = DefPred(node.name, ref, args, formula, node.autoexpand, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_defcon(self, node: ParsedDefCon, context: Context) -> DefCon:
        if node.ref.name in context.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = RefDefCon(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        if not context.decl.has_theorem(node.ref_theorem.name):
            raise ResolveError(node, f"{node.ref_theorem.name} is unknown")
        ref_theorem = RefTheorem(node.ref_theorem.name)
        self.add_node_to_token(ref_theorem, node.ref_theorem)
        tex = self.create_or_check_tex(node.tex, node.name, 0, node)
        resolved = DefCon(node.name, ref, ref_theorem, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_deffun(self, node: ParsedDefFun, context: Context) -> DefFun:
        if node.ref.name in context.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = RefDefFun(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        if not context.decl.has_theorem(node.ref_theorem.name):
            raise ResolveError(node, f"{node.ref_theorem.name} is unknown")
        ref_theorem = RefTheorem(node.ref_theorem.name)
        self.add_node_to_token(ref_theorem, node.ref_theorem)
        vars_, body = strip_forall_vars(context.decl.get_theorem(node.ref_theorem.name).conclusion)
        if not (isinstance(body, ExistsUniq) or (isinstance(body, Implies) and isinstance(body.right, ExistsUniq))):
            msg = f"conclusion of {node.ref_theorem.name} cannot be used for function definition"
            raise ResolveError(node, msg)
        tex = self.create_or_check_tex(node.tex, node.name, len(vars_), node)
        resolved = DefFun(node.name, ref, vars_, ref_theorem, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_defexist(self, node: ParsedDefExist, context: Context) -> DefConExist | DefFunExist:
        if node.ref.name in context.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        if context.decl.has_defcon(node.ref_term.name):
            ref = RefDefConExist(node.ref.name)
            self.add_node_to_token(ref, node.ref)
            formula = self.resolve_formula(node.formula, context)
            ref_term = RefDefCon(node.ref_term.name)
            self.add_node_to_token(ref_term, node.ref_term)
            resolved = DefConExist(node.name, ref, formula, ref_term)
            self.add_node_to_token(resolved, node)
            return resolved
        elif context.decl.has_deffun(node.ref_term.name):
            ref = RefDefFunExist(node.ref.name)
            self.add_node_to_token(ref, node.ref)
            formula = self.resolve_formula(node.formula, context)
            ref_term = RefDefFun(node.ref_term.name)
            self.add_node_to_token(ref_term, node.ref_term)
            resolved = DefFunExist(node.name, ref, formula, ref_term)
            self.add_node_to_token(resolved, node)
            return resolved
        else:
            msg = f"{node.ref_term.name} is unknown"
            raise ResolveError(node, msg)

    def resolve_defuniq(self, node: ParsedDefUniq, context: Context) -> DefConUniq | DefFunUniq:
        if node.ref.name in context.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        if context.decl.has_defcon(node.ref_term.name):
            ref = RefDefConUniq(node.ref.name)
            self.add_node_to_token(ref, node.ref)
            formula = self.resolve_formula(node.formula, context)
            ref_term = RefDefCon(node.ref_term.name)
            self.add_node_to_token(ref_term, node.ref_term)
            resolved = DefConUniq(node.name, ref, formula, ref_term)
            self.add_node_to_token(resolved, node)
            return resolved
        elif context.decl.has_deffun(node.ref_term.name):
            ref = RefDefFunUniq(node.ref.name)
            self.add_node_to_token(ref, node.ref)
            formula = self.resolve_formula(node.formula, context)
            ref_term = RefDefFun(node.ref_term.name)
            self.add_node_to_token(ref_term, node.ref_term)
            resolved = DefFunUniq(node.name, ref, formula, ref_term)
            self.add_node_to_token(resolved, node)
            return resolved
        else:
            msg = f"{node.ref_term.name} is unknown"
            raise ResolveError(node, msg)

    def resolve_deffunterm(self, node: ParsedDefFunTerm, context: Context) -> DefFunTerm:
        if node.ref.name in context.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = RefDefFunTerm(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        local_vars, local_pred_tmpls, local_fun_tmpls, args = self.resolve_vars_or_pred_tmpls_or_fun_tmpls(node.args, context.ctrl)
        local_ctx = context.add_ctrl(local_vars, [], local_pred_tmpls, local_fun_tmpls, args)
        varterm = self.resolve_term(node.varterm, local_ctx)
        if not isinstance(varterm, VarTerm):
            raise ResolveError(node, "Unexpected type")
        tex = self.create_or_check_tex(node.tex, node.name, len(args), node)
        resolved = DefFunTerm(node.name, ref, args, varterm, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_equality(self, node: ParsedEquality, context: Context) -> Equality:
        if node.ref.name in context.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = RefEquality(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        tex = self.create_or_check_tex(node.tex, node.name, 2, node)
        resolved = Equality(node.name, ref, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_invalid_declaration(self, node: ParsedInvalidDeclaration, context: Context) -> InvalidDeclaration:
        resolved = InvalidDeclaration(node.name)
        self.add_node_to_token(resolved, node)
        return resolved

    def create_or_check_tex(self, tex: list[str], name: str, arity: int, node: ParsedPrimPred | ParsedDefPred | ParsedDefCon | ParsedDefFun | ParsedDefFunTerm | ParsedEquality) -> list[str]:
        if len(tex) == 0:
            return self.create_tex(name, arity)
        elif len(tex) == arity + 1:
            return tex
        else:
            raise ResolveError(node, f"arity of {name} is {arity}, but length of tex is {len(tex)}")

    def create_tex(self, name: str, arity: int) -> list[str]:
        if arity == 0:
            tex = [f"\\mathrm{{{name}}}"]
        else:
            tex = [f"\\mathrm{{{name}}}("]
            tex.extend(["," for _ in range(arity - 1)])
            tex.append(")")
        return tex

    def resolve_block(self, node: list[ParsedControl], context: Context) -> list[Control]:
        return [self.resolve_control(control, context) for control in node]

    def resolve_control(self, node: ParsedControl, context: Context) -> Control:
        try:
            if isinstance(node, ParsedAny):
                return self.resolve_any(node, context)
            elif isinstance(node, ParsedAssume):
                return self.resolve_assume(node, context)
            elif isinstance(node, ParsedDivide):
                return self.resolve_divide(node, context)
            elif isinstance(node, ParsedSome):
                return self.resolve_some(node, context)
            elif isinstance(node, ParsedDeny):
                return self.resolve_deny(node, context)
            elif isinstance(node, ParsedCase):
                return self.resolve_case(node, context)
            elif isinstance(node, ParsedContradict):
                return self.resolve_contradict(node, context)
            elif isinstance(node, ParsedExplode):
                return self.resolve_explode(node, context)
            elif isinstance(node, ParsedApply):
                return self.resolve_apply(node, context)
            elif isinstance(node, ParsedLift):
                return self.resolve_lift(node, context)
            elif isinstance(node, ParsedCharacterize):
                return self.resolve_characterize(node, context)
            elif isinstance(node, ParsedInvoke):
                return self.resolve_invoke(node, context)
            elif isinstance(node, ParsedExpand):
                return self.resolve_expand(node, context)
            elif isinstance(node, ParsedFold):
                return self.resolve_fold(node, context)
            elif isinstance(node, ParsedPad):
                return self.resolve_pad(node, context)
            elif isinstance(node, ParsedSplit):
                return self.resolve_split(node, context)
            elif isinstance(node, ParsedConnect):
                return self.resolve_connect(node, context)
            elif isinstance(node, ParsedSubstitute):
                return self.resolve_substitute(node, context)
            elif isinstance(node, ParsedShow):
                return self.resolve_show(node, context)
            elif isinstance(node, ParsedAssert):
                return self.resolve_assert(node, context)
            elif isinstance(node, ParsedInvalidControl):
                return self.resolve_invalid_control(node, context)
            else:
                msg = f"Unsupported node {node}"
                raise ResolveError(node, msg)
        except ResolveError as e:
            self.add_lsp_error(self.get_node_token(e.node), e.msg)
            invalid = InvalidControl()
            self.add_node_to_token(invalid, node)
            return invalid

    def resolve_any(self, node: ParsedAny, context: Context) -> Any:
        local_vars, local_pred_tmpls, local_fun_tmpls, items = self.resolve_vars_or_pred_tmpls_or_fun_tmpls(node.items, context.ctrl)
        local_ctx = context.add_ctrl(local_vars, [], local_pred_tmpls, local_fun_tmpls, items)
        body = self.resolve_block(node.body, local_ctx)
        resolved = Any(items, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_assume(self, node: ParsedAssume, context: Context) -> Assume:
        premise = self.resolve_formula(node.premise, context)
        body = self.resolve_block(node.body, context.copy_ctrl())
        resolved = Assume(premise, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_divide(self, node: ParsedDivide, context: Context) -> Divide:
        fact = self.resolve_reference_or_formula(node.fact, context)
        if len(node.cases) < 2:
            msg = "At least two cases are required"
            raise ResolveError(node, msg)
        cases = [self.resolve_case(case, context.copy_ctrl()) for case in node.cases]
        resolved = Divide(fact, cases)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_case(self, node: ParsedCase, context: Context) -> Case:
        premise = self.resolve_formula(node.premise, context.copy_ctrl())
        body = self.resolve_block(node.body, context)
        resolved = Case(premise, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_some(self, node: ParsedSome, context: Context) -> Some:
        fact = self.resolve_reference_or_formula(node.fact, context)
        items, local_vars = self.resolve_vars_or_none(node.items, context.ctrl)
        local_ctx = context.add_ctrl(local_vars, [], [], [], list(local_vars))
        body = self.resolve_block(node.body, local_ctx)
        resolved = Some(items, fact, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_deny(self, node: ParsedDeny, context: Context) -> Deny:
        premise = self.resolve_formula(node.premise, context)
        body = self.resolve_block(node.body, context.copy_ctrl())
        resolved = Deny(premise, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_contradict(self, node: ParsedContradict, context: Context) -> Contradict:
        contradiction = self.resolve_formula(node.contradiction, context)
        resolved = Contradict(contradiction)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_explode(self, node: ParsedExplode, context: Context) -> Explode:
        conclusion = self.resolve_formula(node.conclusion, context)
        resolved = Explode(conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_apply(self, node: ParsedApply, context: Context) -> Apply:
        fact = self.resolve_reference_or_formula(node.fact, context)
        terms = [self.resolve_term(term, context) if isinstance(term, ParsedExpr) else None for term in node.terms]
        resolved = Apply(node.invoke, fact, terms)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_lift(self, node: ParsedLift, context: Context) -> Lift:
        varterms: list[VarTerm | None] = []
        for term in node.varterms:
            if isinstance(term, ParsedExpr):
                resolved_term = self.resolve_term(term, context)
                if not isinstance(resolved_term, VarTerm):
                    raise ResolveError(node, "Unexpected type")
                varterms.append(resolved_term)
            elif term is None:
                varterms.append(term)
            else:
                raise ResolveError(node, "Unexpected type")
        conclusion = self.resolve_formula(node.conclusion, context)
        resolved = Lift(varterms, conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_characterize(self, node: ParsedCharacterize, context: Context) -> Characterize:
        if not isinstance(node.varterm, ParsedExpr):
            raise ResolveError(node, "Unexpected type")
        varterm = self.resolve_term(node.varterm, context)
        if not isinstance(varterm, VarTerm):
            raise ResolveError(node, "Unexpected type")
        conclusion = self.resolve_formula(node.conclusion, context)
        if not isinstance(conclusion, ExistsUniq):
            raise ResolveError(node, "Unexpected type")
        resolved = Characterize(varterm, conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_invoke(self, node: ParsedInvoke, context: Context) -> Invoke:
        fact = self.resolve_formula(node.fact, context)
        if node.direction == "none":
            if not isinstance(fact, Implies):
                msg = f"Unexpected type {type(fact)}"
                raise ResolveError(node, msg)
        else:
            if not isinstance(fact, Iff):
                msg = f"Unexpected type {type(fact)}"
                raise ResolveError(node, msg)
        resolved = Invoke(node.direction, fact)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_expand(self, node: ParsedExpand, context: Context) -> Expand:
        fact = self.resolve_reference_or_formula(node.fact, context)
        refs, indexes = self.resolve_refs_indexes(node, context)
        resolved = Expand(fact, refs, indexes)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_fold(self, node: ParsedFold, context: Context) -> Fold:
        refs, indexes = self.resolve_refs_indexes(node, context)
        conclusion = self.resolve_formula(node.conclusion, context)
        resolved = Fold(refs, indexes, conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_refs_indexes(self, node: ParsedExpand | ParsedFold, context: Context) -> tuple[list[RefDefFunTerm | RefDefPred], dict[RefDefFunTerm | RefDefPred, list[int]]]:
        resolved_refs: list[RefDefFunTerm | RefDefPred] = []
        indexes: dict[RefDefFunTerm | RefDefPred, list[int]] = {}
        for ref in node.refs:
            if context.decl.has_deffunterm(ref.name):
                resolved_ref = RefDefFunTerm(ref.name)
                self.add_node_to_token(resolved_ref, ref)
                resolved_refs.append(resolved_ref)
                if ref in node.indexes:
                    indexes[resolved_ref] = node.indexes[ref]
            elif context.decl.has_defpred(ref.name):
                resolved_ref = RefDefPred(ref.name)
                self.add_node_to_token(resolved_ref, ref)
                resolved_refs.append(resolved_ref)
                if ref in node.indexes:
                    indexes[resolved_ref] = node.indexes[ref]
            else:
                msg = f"Unexpected name {ref.name}"
                raise ResolveError(node, msg)
        for k, v in node.indexes.items():
            if context.decl.has_deffunterm(k.name):
                indexes[RefDefFunTerm(k.name)] = v
            elif context.decl.has_defpred(k.name):
                indexes[RefDefPred(k.name)] = v
            else:
                msg = f"Unexpected name {k.name}"
                raise ResolveError(node, msg)
        return resolved_refs, indexes

    def resolve_pad(self, node: ParsedPad, context: Context) -> Pad:
        fact = self.resolve_reference_or_formula(node.fact, context)
        conclusion = self.resolve_formula(node.conclusion, context)
        resolved = Pad(fact, conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_split(self, node: ParsedSplit, context: Context) -> Split:
        fact = self.resolve_reference_or_formula(node.fact, context)
        resolved = Split(node.index, fact)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_connect(self, node: ParsedConnect, context: Context) -> Connect:
        conclusion = self.resolve_formula(node.conclusion, context)
        resolved = Connect(conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_substitute(self, node: ParsedSubstitute, context: Context) -> Substitute:
        fact = self.resolve_reference_or_formula(node.fact, context)
        env: dict[Term, Term] = {}
        indexes: dict[Term, list[int]] = {}
        for k, v in node.env.items():
            new_k = self.resolve_term(k, context)
            self.add_node_to_token(new_k, k)
            new_v = self.resolve_term(v, context)
            self.add_node_to_token(new_v, v)
            env[new_k] = new_v
            if k in node.indexes:
                indexes[new_k] = node.indexes[k]
        resolved = Substitute(fact, env, indexes)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_show(self, node: ParsedShow, context: Context) -> Show:
        conclusion = self.resolve_bot_or_formula(node.conclusion, context)
        body = self.resolve_block(node.body, context.copy_ctrl())
        resolved = Show(conclusion, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_assert(self, node: ParsedAssert, context: Context) -> Assert:
        reference = self.resolve_reference_or_formula(node.reference, context)
        resolved = Assert(reference)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_invalid_control(self, node: ParsedInvalidControl, context: Context) -> InvalidControl:
        resolved = InvalidControl()
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_bot_or_formula(self, node: ParsedBottom | ParsedExpr, context: Context) -> Bottom | Formula:
        if isinstance(node, ParsedBottom):
            return Bottom()
        else:
            return self.resolve_formula(node, context)

    def resolve_reference_or_formula(self, node: ParsedExpr, context: Context) -> RefFact | Formula:
        if isinstance(node, ParsedIdent):
            return self.resolve_reference_or_atomic_zero_arity_formula(node, context)
        else:
            return self.resolve_formula(node, context)

    def resolve_formula(self, node: ParsedExpr, context: Context) -> Formula:
        if isinstance(node, (ParsedIdent, ParsedIdentArgs)):
            return self.resolve_atomic_formula(node, context)
        elif isinstance(node, ParsedNot):
            resolved = Not(self.resolve_formula(node.body, context))
        elif isinstance(node, ParsedAnd):
            resolved = And(self.resolve_formula(node.left, context), self.resolve_formula(node.right, context))
        elif isinstance(node, ParsedOr):
            resolved = Or(self.resolve_formula(node.left, context), self.resolve_formula(node.right, context))
        elif isinstance(node, ParsedImplies):
            resolved = Implies(self.resolve_formula(node.left, context), self.resolve_formula(node.right, context))
        elif isinstance(node, ParsedIff):
            resolved = Iff(self.resolve_formula(node.left, context), self.resolve_formula(node.right, context))
        elif isinstance(node, ParsedForall):
            local_vars, local_pred_tmpls, local_fun_tmpls, item = self.resolve_var_or_pred_tmpl_or_fun_tmpl(node.var, context.form)
            local_ctx = context.add_form(local_vars, local_pred_tmpls, local_fun_tmpls)
            formula = self.resolve_formula(node.body, local_ctx)
            resolved = Forall(item, formula)
        elif isinstance(node, ParsedExists):
            var = self.resolve_var(node.var, context.form)
            local_ctx = context.add_form([var], [], [])
            formula = self.resolve_formula(node.body, local_ctx)
            resolved = Exists(var, formula)
        elif isinstance(node, ParsedExistsUniq):
            var = self.resolve_var(node.var, context.form)
            local_ctx = context.add_form([var], [], [])
            formula = self.resolve_formula(node.body, local_ctx)
            resolved = ExistsUniq(var, formula)
        else:
            msg = f"Unexpected node type: {type(node)}"
            raise ResolveError(node, msg)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_reference_or_atomic_zero_arity_formula(self, node: ParsedIdent, context: Context) -> RefFact | AtomicFormula:
        name = node.name
        if any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
            def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
            pred = PredTemplate(name, def_pred_tmpl.arity)
            self.add_node_to_token(pred, node)
            self.add_ctrl_defs_refs(def_pred_tmpl, pred)
            formula = AtomicFormula(pred, ())
            self.add_node_to_token(formula, node)
            return formula
        elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
            def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name)
            pred = PredTemplate(name, def_pred_tmpl.arity)
            self.add_node_to_token(pred, node)
            self.add_ctrl_defs_refs(def_pred_tmpl, pred)
            formula = AtomicFormula(pred, ())
            self.add_node_to_token(formula, node)
            return formula
        elif context.decl.has_axiom(name):
            ref = RefAxiom(name)
            self.add_node_to_token(ref, node)
            return ref
        elif context.decl.has_theorem(name):
            ref = RefTheorem(name)
            self.add_node_to_token(ref, node)
            return ref
        elif context.decl.has_defconexist(name):
            ref = RefDefConExist(name)
            self.add_node_to_token(ref, node)
            return ref
        elif context.decl.has_defconuniq(name):
            ref = RefDefConUniq(name)
            self.add_node_to_token(ref, node)
            return ref
        elif context.decl.has_deffunexist(name):
            ref = RefDefFunExist(name)
            self.add_node_to_token(ref, node)
            return ref
        elif context.decl.has_deffununiq(name):
            ref = RefDefFunUniq(name)
            self.add_node_to_token(ref, node)
            return ref
        else:
            msg = f"Unexpected name: {name}"
            raise ResolveError(node, msg)

    def resolve_atomic_formula(self, node: ParsedIdent | ParsedIdentArgs, context: Context) -> AtomicFormula:
        if isinstance(node, ParsedIdent):
            name = node.name
            if any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
                pred = PredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(pred, node)
                self.add_ctrl_defs_refs(def_pred_tmpl, pred)
            elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name)
                pred = PredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(pred, node)
                self.add_ctrl_defs_refs(def_pred_tmpl, pred)
            else:
                msg = f"Unexpected name: {name}"
                raise ResolveError(node, msg)
            formula = AtomicFormula(pred, ())
            self.add_node_to_token(formula, node)
            return formula
        else:
            name = node.name.name
            equality = context.decl.get_equality()
            if any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
                pred = PredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(pred, node.name)
                self.add_ctrl_defs_refs(def_pred_tmpl, pred)
                defargs: list[Var | PredTemplate | FunTemplate] = [Var(f"x_{i}") for i in range(pred.arity)]
            elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name)
                pred = PredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(pred, node.name)
                self.add_ctrl_defs_refs(def_pred_tmpl, pred)
                defargs: list[Var | PredTemplate | FunTemplate] = [Var(f"x_{i}") for i in range(pred.arity)]
            elif equality is not None and name == equality.ref.name:
                pred = RefEquality(name)
                self.add_node_to_token(pred, node.name)
                defargs: list[Var | PredTemplate | FunTemplate] = [Var(f"x_{i}") for i in range(2)]
            elif context.decl.has_primpred(name):
                pred = RefPrimPred(name)
                self.add_node_to_token(pred, node.name)
                defargs: list[Var | PredTemplate | FunTemplate] = [Var(f"x_{i}") for i in range(context.decl.get_primpred(name).arity)]
            elif context.decl.has_defpred(name):
                pred = RefDefPred(name)
                self.add_node_to_token(pred, node.name)
                defargs = context.decl.get_defpred(name).args
            else:
                msg = f"Unexpected name: {name}"
                raise ResolveError(node.name, msg)
            subargs = [self.resolve_term(arg, context) for arg in node.args]
            resolved_args = self.match_args(defargs, subargs, node)
            formula = AtomicFormula(pred, tuple(resolved_args))
            self.add_node_to_token(formula, node)
            return formula

    def resolve_term(self, node: ParsedExpr, context: Context) -> Term:
        if isinstance(node, ParsedIdent):
            name = node.name
            if any(var.name == name for var in context.form.vars):
                def_var = next(var for var in context.form.vars if var.name == name)
                ref_var = Var(name)
                self.add_node_to_token(ref_var, node)
                self.add_ctrl_defs_refs(def_var, ref_var)
                return ref_var
            elif any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
                ref_pred_tmpl = PredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(ref_pred_tmpl, node)
                self.add_ctrl_defs_refs(def_pred_tmpl, ref_pred_tmpl)
                return ref_pred_tmpl
            elif any(var.name == name for var in context.ctrl.vars):
                def_var = next((var for var in context.ctrl.vars if var.name == name))
                ref_var = Var(name)
                self.add_node_to_token(ref_var, node)
                self.add_ctrl_defs_refs(def_var, ref_var)
                return ref_var
            elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
                def_pred_tmpl = next((pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name))
                ref_pred_tmpl = PredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(ref_pred_tmpl, node)
                self.add_ctrl_defs_refs(def_pred_tmpl, ref_pred_tmpl)
                return ref_pred_tmpl
            elif context.decl.has_defcon(name):
                ref = RefDefCon(name)
                self.add_node_to_token(ref, node)
                return ref
            elif context.decl.has_primpred(name):
                ref = RefPrimPred(name)
                self.add_node_to_token(ref, node)
                return ref
            elif context.decl.has_defpred(name):
                ref = RefDefPred(name)
                self.add_node_to_token(ref, node)
                return ref
            else:
                raise ResolveError(node, f"{name} is unknown")
        elif isinstance(node, ParsedIdentArgs):
            name = node.name.name
            if context.decl.has_deffun(name) or context.decl.has_deffunterm(name) or any(fun_tmpl.name == name for fun_tmpl in context.form.fun_tmpls) or any(fun_tmpl.name == name for fun_tmpl in context.ctrl.fun_tmpls):
                if context.decl.has_deffun(name):
                    fun = RefDefFun(name)
                    self.add_node_to_token(fun, node.name)
                    defargs = context.decl.get_deffun(name).args
                elif context.decl.has_deffunterm(name):
                    fun = RefDefFunTerm(name)
                    self.add_node_to_token(fun, node.name)
                    defargs = context.decl.get_deffunterm(name).args
                elif any(fun_tmpl.name == name for fun_tmpl in context.form.fun_tmpls):
                    def_fun_tmpl = next(fun_tmpl for fun_tmpl in context.form.fun_tmpls if fun_tmpl.name == name)
                    fun = FunTemplate(name, def_fun_tmpl.arity)
                    self.add_node_to_token(fun, node.name)
                    self.add_ctrl_defs_refs(def_fun_tmpl, fun)
                    defargs = [Var(f"x_{i}") for i in range(fun.arity)]
                else:
                    def_fun_tmpl = next(fun_tmpl for fun_tmpl in context.ctrl.fun_tmpls if fun_tmpl.name == name)
                    fun = FunTemplate(name, def_fun_tmpl.arity)
                    self.add_node_to_token(fun, node.name)
                    self.add_ctrl_defs_refs(def_fun_tmpl, fun)
                    defargs = [Var(f"x_{i}") for i in range(fun.arity)]
                subargs = [self.resolve_term(arg, context) for arg in node.args]
                if len(subargs) == 0:
                    return fun
                else:
                    resolved_args = self.match_args(defargs, subargs, node)
                    term = Compound(fun, tuple(resolved_args))
                    self.add_node_to_token(term, node.name)
                    return term
            elif context.decl.has_primpred(name):
                ref = RefPrimPred(name)
                self.add_node_to_token(ref, node.name)
                return ref
            elif context.decl.has_defpred(name):
                ref = RefDefPred(name)
                self.add_node_to_token(ref, node.name)
                return ref
            else:
                msg = f"Term object is required, but {name} is unknown"
                raise ResolveError(node, msg)
        elif isinstance(node, ParsedPredLambda):
            args = self.resolve_vars(node.args, context.form)
            body = self.resolve_formula(node.body, context.add_form(args, [], []))
            resolved = PredLambda(tuple(args), body)
            self.add_node_to_token(resolved, node)
            return resolved
        elif isinstance(node, ParsedFunLambda):
            args = self.resolve_vars(node.args, context.form)
            body = self.resolve_term(node.body, context.add_form(args, [], []))
            if not isinstance(body, VarTerm):
                raise ResolveError(node, "Unexpected type")
            resolved = FunLambda(tuple(args), body)
            self.add_node_to_token(resolved, node)
            return resolved
        else:
            raise ResolveError(node, "Unexpected type")

    def resolve_vars_or_pred_tmpls_or_fun_tmpls(self, node: list[ParsedIdent | ParsedPredTemplate | ParsedFunTemplate], context: ControlContext | FormulaContext) -> tuple[list[Var], list[PredTemplate], list[FunTemplate], list[Var | PredTemplate | FunTemplate]]:
        vars: list[Var] = []
        pred_tmpls: list[PredTemplate] = []
        fun_tmpls: list[FunTemplate] = []
        items: list[Var | PredTemplate | FunTemplate] = []
        for item in node:
            if item.name in [used.name for used in items]:
                raise ResolveError(item, f"{item.name} is duplicated")
            if isinstance(item, ParsedIdent):
                var = self.resolve_var(item, context)
                vars.append(var)
                items.append(var)
            elif isinstance(item, ParsedPredTemplate):
                pred_tmpl = self.resolve_pred_tmpl(item, context)
                pred_tmpls.append(pred_tmpl)
                items.append(pred_tmpl)
            elif isinstance(item, ParsedFunTemplate):
                fun_tmpl = self.resolve_fun_tmpl(item, context)
                fun_tmpls.append(fun_tmpl)
                items.append(fun_tmpl)
            else:
                raise ResolveError(item, f"Unexpected type {type(item)}")
        return vars, pred_tmpls, fun_tmpls, items

    def resolve_var_or_pred_tmpl_or_fun_tmpl(self, node: ParsedIdent | ParsedPredTemplate | ParsedFunTemplate, context: ControlContext | FormulaContext) -> tuple[list[Var], list[PredTemplate], list[FunTemplate], Var | PredTemplate | FunTemplate]:
        vars: list[Var] = []
        pred_tmpls: list[PredTemplate] = []
        fun_tmpls: list[FunTemplate] = []
        if isinstance(node, ParsedIdent):
            var = self.resolve_var(node, context)
            vars.append(var)
            item = var
        elif isinstance(node, ParsedPredTemplate):
            pred_tmpl = self.resolve_pred_tmpl(node, context)
            pred_tmpls.append(pred_tmpl)
            item = pred_tmpl
        elif isinstance(node, ParsedFunTemplate):
            fun_tmpl = self.resolve_fun_tmpl(node, context)
            fun_tmpls.append(fun_tmpl)
            item = fun_tmpl
        else:
            raise ResolveError(node, f"Unexpected type {type(node)}")
        return vars, pred_tmpls, fun_tmpls, item

    def resolve_vars_or_none(self, node: list[ParsedIdent | None], context: ControlContext | FormulaContext) -> tuple[list[Var | None], list[Var]]:
        vars_or_none: list[Var | None] = []
        vars: list[Var] = []
        for item in node:
            if isinstance(item, ParsedIdent):
                if item.name in [used.name for used in vars]:
                    raise ResolveError(item, f"{item.name} is duplicated")
                var = self.resolve_var(item, context)
                vars_or_none.append(var)
                vars.append(var)
            else:
                vars_or_none.append(None)
        return vars_or_none, vars

    def resolve_vars(self, node: tuple[ParsedIdent, ...], context: ControlContext | FormulaContext) -> list[Var]:
        vars: list[Var] = []
        for item in node:
            if item.name in [used.name for used in vars]:
                raise ResolveError(item, f"{item.name} is duplicated")
            vars.append(self.resolve_var(item, context))
        return vars

    def resolve_var(self, node: ParsedIdent, context: ControlContext | FormulaContext) -> Var:
        if node.name in context.used_names:
            raise ResolveError(node, f"{node.name} is already used")
        var = Var(node.name)
        self.add_node_to_token(var, node)
        self.add_ctrl_defs_refs(var, var)
        return var

    def resolve_pred_tmpl(self, node: ParsedPredTemplate, context: ControlContext | FormulaContext) -> PredTemplate:
        if node.name in context.used_names:
            raise ResolveError(node, f"{node.name} is already used")
        pred_tmpl = PredTemplate(node.name, node.arity)
        self.add_node_to_token(pred_tmpl, node)
        self.add_ctrl_defs_refs(pred_tmpl, pred_tmpl)
        return pred_tmpl

    def resolve_fun_tmpl(self, node: ParsedFunTemplate, context: ControlContext | FormulaContext) -> FunTemplate:
        if node.name in context.used_names:
            raise ResolveError(node, f"{node.name} is already used")
        fun_tmpl = FunTemplate(node.name, node.arity)
        self.add_node_to_token(fun_tmpl, node)
        self.add_ctrl_defs_refs(fun_tmpl, fun_tmpl)
        return fun_tmpl

    def match_args(self, defargs: Sequence[Var | PredTemplate | FunTemplate], subargs: Sequence[Term], node: ParsedIdentArgs) -> list[Term]:
        if len(defargs) != len(subargs):
            msg = f"len(defargs): {len(defargs)}, len(subargs): {len(subargs)}"
            raise ResolveError(node, msg)
        resolved_args: list[Term] = []
        for defarg, subarg in zip(defargs, subargs):
            if isinstance(defarg, Var):
                if isinstance(subarg, VarTerm):
                    resolved_args.append(subarg)
                else:
                    msg = f"VarTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted"
                    raise ResolveError(node, msg)
            elif isinstance(defarg, PredTemplate):
                if isinstance(subarg, PredTerm):
                    resolved_args.append(subarg)
                else:
                    msg = f"PredTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted"
                    raise ResolveError(node, msg)
            else:
                if isinstance(subarg, FunTerm):
                    resolved_args.append(subarg)
                else:
                    msg = f"FunTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted"
                    raise ResolveError(node, msg)
        return resolved_args
