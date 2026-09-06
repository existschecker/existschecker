from lsprotocol import types as lsp
from pygls import uris
from typing import Sequence
from ast_types import DeclarationUnit, DeclarationContextNameSpace, LexedUnit
from ast_types import Var, PredTemplate, FunTemplate
from resolved_ast_types import ResolvedTerm, ResolvedFormula, ResolvedVarTerm, ResolvedVar, ResolvedRefDefCon, ResolvedFunTerm, ResolvedRefDefFun, ResolvedRefDefFunTerm, ResolvedFunTemplate, ResolvedFunLambda, ResolvedCompound, ResolvedPredTerm, ResolvedRefEquality, ResolvedRefPrimPred, ResolvedRefDefPred, ResolvedPredTemplate, ResolvedPredLambda, ResolvedAtomicFormula, ResolvedNot, ResolvedAnd, ResolvedOr, ResolvedImplies, ResolvedIff, ResolvedForall, ResolvedExists, ResolvedExistsUniq, ResolvedBottom, ResolvedRefFact, ResolvedRefAxiom, ResolvedRefTheorem, ResolvedRefDefConExist, ResolvedRefDefConUniq, ResolvedRefDefFunExist, ResolvedRefDefFunUniq, ResolvedControl, ResolvedInvalidControl, ResolvedAssume, ResolvedAny, ResolvedCase, ResolvedDivide, ResolvedSome, ResolvedDeny, ResolvedContradict, ResolvedExplode, ResolvedApply, ResolvedLift, ResolvedCharacterize, ResolvedInvoke, ResolvedExpand, ResolvedFold, ResolvedPad, ResolvedSplit, ResolvedConnect, ResolvedSubstitute, ResolvedShow, ResolvedAssert, ResolvedDeclaration, ResolvedInvalidDeclaration, ResolvedPrimPred, ResolvedAxiom, ResolvedTheorem, ResolvedDefPred, ResolvedDefConExist, ResolvedDefConUniq, ResolvedDefCon, ResolvedDefFunExist, ResolvedDefFunUniq, ResolvedDefFun, ResolvedDefFunTerm, ResolvedEquality, ResolvedInclude, ResolvedInvalidInclude, ResolvedRefStruct, ResolvedStructVar, ResolvedRefStructField, ResolvedStructMemberField, ResolvedRefStructCondition, ResolvedRefStructMemberCondition, ResolvedStruct, ResolvedFormulaContext, ResolvedControlContext, ResolvedContext, ResolvedStructPred, ResolvedRefStructPred, ResolvedStructMemberPred, ResolvedUnit
from parsed_ast_types import ParsedExpr, ParsedIdent, ParsedIdentArgs, ParsedFunTemplate, ParsedFunLambda, ParsedPredTemplate, ParsedPredLambda, ParsedNot, ParsedAnd, ParsedOr, ParsedImplies, ParsedIff, ParsedForall, ParsedExists, ParsedExistsUniq, ParsedBottom, ParsedControl, ParsedInvalidControl, ParsedAny, ParsedAssume, ParsedDivide, ParsedSome, ParsedDeny, ParsedContradict, ParsedCase, ParsedExplode, ParsedApply, ParsedLift, ParsedCharacterize, ParsedInvoke, ParsedExpand, ParsedFold, ParsedPad, ParsedSplit, ParsedConnect, ParsedSubstitute, ParsedShow, ParsedAssert, ParsedDeclaration, ParsedInvalidDeclaration, ParsedPrimPred, ParsedAxiom, ParsedTheorem, ParsedDefPred, ParsedDefCon, ParsedDefFun, ParsedDefFunTerm, ParsedDefExist, ParsedDefUniq, ParsedEquality, ParsedInclude, ParsedInvalidInclude, ParsedUnit, ParsedStruct, ParsedTypedIdent, ParsedAccess, ParsedStructPred, ParsedCall
from lexer import Token
from logic_utils import strip_forall_vars
from dependency import DependencyResolver

class ResolveError(Exception):
    def __init__(self, node: ParsedDeclaration | ParsedControl | ParsedExpr, msg: str) -> None:
        self.node = node
        self.msg = msg

class NameResolver:
    def __init__(self, lexed_unit: LexedUnit, parsed_unit: ParsedUnit, decl: DeclarationContextNameSpace, dependency_resolver: DependencyResolver, file_units: dict[str, list[DeclarationUnit]]) -> None:
        self.lexed_unit = lexed_unit
        self.parsed_unit = parsed_unit
        self.decl = decl
        self.dependency_resolver = dependency_resolver
        self.file_units = file_units

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
        self.diagnostics.append(diag)

    def get_node_token(self, node: ParsedDeclaration | ParsedControl | ParsedExpr) -> Token:
        return self.lexed_unit.tokens[self.parsed_unit.node_to_token[id(node)][0]]

    def add_node_to_token(self, node: ResolvedInclude | ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedStructVar | ResolvedRefStructPred, parsed: ParsedDeclaration | ParsedControl | ParsedExpr) -> None:
        self.resolved_node_to_token[id(node)] = self.parsed_unit.node_to_token[id(parsed)]
        self.resolved_nodes.append(node)
        if isinstance(node, (ResolvedRefFact, ResolvedRefEquality, ResolvedRefPrimPred, ResolvedRefDefPred, ResolvedRefDefCon, ResolvedRefDefFun, ResolvedRefDefFunTerm, ResolvedRefStruct, ResolvedRefStructField, ResolvedRefStructCondition)):
            self.add_decl_ref(node.name, self.lexed_unit.tokens[self.resolved_node_to_token[id(node)][0]])

    def add_decl_ref(self, name: str, token: Token) -> None:
        if name not in self.resolved_decl_refs:
            self.resolved_decl_refs[name] = []
        self.resolved_decl_refs[name].append(token)

    def add_ctrl_defs_refs(self, def_node: ResolvedTerm | ResolvedStructVar | ResolvedRefStructCondition | ResolvedStructPred | ResolvedRefStructPred, ref_node: ResolvedTerm | ResolvedStructVar | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedRefStructPred, unit_name: str | None = None) -> None:
        if unit_name is None:
            if isinstance(self.parsed_unit.ast, ParsedDeclaration):
                unit_name = self.parsed_unit.ast.name
            else:
                unit_name = ""
        self.resolved_ctrl_defs[id(ref_node)] = (unit_name, id(def_node))
        if id(def_node) not in self.resolved_ctrl_refs:
            self.resolved_ctrl_refs[id(def_node)] = []
        self.resolved_ctrl_refs[id(def_node)].append(id(ref_node))

    def build_token_to_node(self) -> tuple[dict[int, ResolvedInclude | ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedStructVar | ResolvedRefStructPred], dict[int, ResolvedControl]]:
        resolved_token_to_node: dict[int, ResolvedInclude | ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedStructVar | ResolvedRefStructPred] = {}
        resolved_token_to_control: dict[int, ResolvedControl] = {}
        for node in reversed(self.resolved_nodes):
            start, end = self.resolved_node_to_token[id(node)]
            for index in range(start, end + 1):
                resolved_token_to_node[index] = node
        for node in reversed(self.resolved_nodes):
            if isinstance(node, ResolvedControl):
                start, end = self.resolved_node_to_token[id(node)]
                for index in range(start, end + 1):
                    resolved_token_to_control[index] = node
        return resolved_token_to_node, resolved_token_to_control

    def resolve_unit(self) -> ResolvedUnit:
        self.resolved_node_to_token: dict[int, tuple[int, int]] = {}
        self.resolved_nodes: list[ResolvedInclude | ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructField | ResolvedRefStructCondition | ResolvedStructVar | ResolvedRefStructPred] = []
        self.resolved_decl_refs: dict[str, list[Token]] = {}
        self.resolved_ctrl_defs: dict[int, tuple[str, int]] = {}
        self.resolved_ctrl_refs: dict[int, list[int]] = {}
        self.diagnostics: list[lsp.Diagnostic] = []
        if isinstance(self.parsed_unit.ast, ParsedInclude):
            resolved_ast = self.resolve_include(self.parsed_unit.ast)
        else:
            resolved_ast = self.resolve_declaration(self.parsed_unit.ast)
        resolved_token_to_node, resolved_token_to_control = self.build_token_to_node()
        return ResolvedUnit(resolved_ast, self.resolved_node_to_token, self.resolved_nodes, resolved_token_to_node, resolved_token_to_control, self.resolved_decl_refs, self.resolved_ctrl_defs, self.resolved_ctrl_refs, self.diagnostics)

    def resolve_include(self, node: ParsedInclude) -> ResolvedInclude:
        if isinstance(node, ParsedInvalidInclude):
            return ResolvedInvalidInclude(node.file, node.token)
        else:
            return ResolvedInclude(node.file, node.token)

    def resolve_declaration(self, node: ParsedDeclaration) -> ResolvedDeclaration:
        try:
            if isinstance(node, ParsedPrimPred):
                return self.resolve_primpred(node)
            elif isinstance(node, ParsedAxiom):
                return self.resolve_axiom(node)
            elif isinstance(node, ParsedTheorem):
                return self.resolve_theorem(node)
            elif isinstance(node, ParsedDefPred):
                return self.resolve_defpred(node)
            elif isinstance(node, ParsedDefCon):
                return self.resolve_defcon(node)
            elif isinstance(node, ParsedDefFun):
                return self.resolve_deffun(node)
            elif isinstance(node, ParsedDefExist):
                return self.resolve_defexist(node)
            elif isinstance(node, ParsedDefUniq):
                return self.resolve_defuniq(node)
            elif isinstance(node, ParsedDefFunTerm):
                return self.resolve_deffunterm(node)
            elif isinstance(node, ParsedEquality):
                return self.resolve_equality(node)
            elif isinstance(node, ParsedStruct):
                return self.resolve_struct(node)
            elif isinstance(node, ParsedStructPred):
                return self.resolve_struct_predicate(node)
            elif isinstance(node, ParsedInvalidDeclaration):
                return self.resolve_invalid_declaration(node)
            else:
                msg = f"Unsupported node {node}"
                raise ResolveError(node, msg)
        except ResolveError as e:
            self.add_lsp_error(self.get_node_token(e.node), e.msg)
            resolved = ResolvedInvalidDeclaration(node.name)
            self.add_node_to_token(resolved, node)
            return resolved

    def resolve_primpred(self, node: ParsedPrimPred) -> ResolvedPrimPred:
        if node.ref.name in self.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = ResolvedRefPrimPred(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        tex = self.create_or_check_tex(node.tex, node.name, node.arity, node)
        resolved = ResolvedPrimPred(node.name, ref, node.arity, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_axiom(self, node: ParsedAxiom) -> ResolvedAxiom:
        if node.ref.name in self.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = ResolvedRefAxiom(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        conclusion = self.resolve_formula(node.conclusion, ResolvedContext.init())
        resolved = ResolvedAxiom(node.name, ref, conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_theorem(self, node: ParsedTheorem) -> ResolvedTheorem:
        if node.ref.name in self.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = ResolvedRefTheorem(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        conclusion = self.resolve_formula(node.conclusion, ResolvedContext.init())
        proof = self.resolve_block(node.proof, ResolvedContext.init())
        resolved = ResolvedTheorem(node.name, ref, conclusion, proof)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_defpred(self, node: ParsedDefPred) -> ResolvedDefPred:
        if node.ref.name in self.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = ResolvedRefDefPred(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        context = ResolvedContext.init()
        local_vars, local_pred_tmpls, local_fun_tmpls, args = self.resolve_vars_or_pred_tmpls_or_fun_tmpls(node.args, context.ctrl)
        local_ctx = context.add_ctrl(local_vars, [], local_pred_tmpls, local_fun_tmpls)
        formula = self.resolve_formula(node.formula, local_ctx)
        tex = self.create_or_check_tex(node.tex, node.name, len(node.args), node)
        resolved = ResolvedDefPred(node.name, ref, args, formula, node.autoexpand, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_defcon(self, node: ParsedDefCon) -> ResolvedDefCon:
        if node.ref.name in self.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = ResolvedRefDefCon(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        if not self.decl.has_theorem(node.ref_theorem.name):
            raise ResolveError(node, f"{node.ref_theorem.name} is unknown")
        ref_theorem = ResolvedRefTheorem(node.ref_theorem.name)
        self.add_node_to_token(ref_theorem, node.ref_theorem)
        tex = self.create_or_check_tex(node.tex, node.name, 0, node)
        resolved = ResolvedDefCon(node.name, ref, ref_theorem, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_deffun(self, node: ParsedDefFun) -> ResolvedDefFun:
        if node.ref.name in self.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = ResolvedRefDefFun(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        if not self.decl.has_theorem(node.ref_theorem.name):
            raise ResolveError(node, f"{node.ref_theorem.name} is unknown")
        ref_theorem = ResolvedRefTheorem(node.ref_theorem.name)
        self.add_node_to_token(ref_theorem, node.ref_theorem)
        vars_, _ = strip_forall_vars(self.decl.get_theorem(node.ref_theorem.name).conclusion)
        tex = self.create_or_check_tex(node.tex, node.name, len(vars_), node)
        resolved = ResolvedDefFun(node.name, ref, ref_theorem, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_defexist(self, node: ParsedDefExist) -> ResolvedDefConExist | ResolvedDefFunExist:
        if node.ref.name in self.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        if self.decl.has_defcon(node.ref_term.name):
            ref = ResolvedRefDefConExist(node.ref.name)
            self.add_node_to_token(ref, node.ref)
            formula = self.resolve_formula(node.formula, ResolvedContext.init())
            ref_term = ResolvedRefDefCon(node.ref_term.name)
            self.add_node_to_token(ref_term, node.ref_term)
            resolved = ResolvedDefConExist(node.name, ref, formula, ref_term)
            self.add_node_to_token(resolved, node)
            return resolved
        elif self.decl.has_deffun(node.ref_term.name):
            ref = ResolvedRefDefFunExist(node.ref.name)
            self.add_node_to_token(ref, node.ref)
            formula = self.resolve_formula(node.formula, ResolvedContext.init())
            ref_term = ResolvedRefDefFun(node.ref_term.name)
            self.add_node_to_token(ref_term, node.ref_term)
            resolved = ResolvedDefFunExist(node.name, ref, formula, ref_term)
            self.add_node_to_token(resolved, node)
            return resolved
        else:
            msg = f"{node.ref_term.name} is unknown"
            raise ResolveError(node, msg)

    def resolve_defuniq(self, node: ParsedDefUniq) -> ResolvedDefConUniq | ResolvedDefFunUniq:
        if node.ref.name in self.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        if self.decl.has_defcon(node.ref_term.name):
            ref = ResolvedRefDefConUniq(node.ref.name)
            self.add_node_to_token(ref, node.ref)
            formula = self.resolve_formula(node.formula, ResolvedContext.init())
            ref_term = ResolvedRefDefCon(node.ref_term.name)
            self.add_node_to_token(ref_term, node.ref_term)
            resolved = ResolvedDefConUniq(node.name, ref, formula, ref_term)
            self.add_node_to_token(resolved, node)
            return resolved
        elif self.decl.has_deffun(node.ref_term.name):
            ref = ResolvedRefDefFunUniq(node.ref.name)
            self.add_node_to_token(ref, node.ref)
            formula = self.resolve_formula(node.formula, ResolvedContext.init())
            ref_term = ResolvedRefDefFun(node.ref_term.name)
            self.add_node_to_token(ref_term, node.ref_term)
            resolved = ResolvedDefFunUniq(node.name, ref, formula, ref_term)
            self.add_node_to_token(resolved, node)
            return resolved
        else:
            msg = f"{node.ref_term.name} is unknown"
            raise ResolveError(node, msg)

    def resolve_deffunterm(self, node: ParsedDefFunTerm) -> ResolvedDefFunTerm:
        if node.ref.name in self.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = ResolvedRefDefFunTerm(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        context = ResolvedContext.init()
        local_vars, local_pred_tmpls, local_fun_tmpls, args = self.resolve_vars_or_pred_tmpls_or_fun_tmpls(node.args, context.ctrl)
        local_ctx = context.add_ctrl(local_vars, [], local_pred_tmpls, local_fun_tmpls)
        varterm = self.resolve_term(node.varterm, local_ctx)
        if not isinstance(varterm, ResolvedVarTerm):
            raise ResolveError(node, "Unexpected type")
        tex = self.create_or_check_tex(node.tex, node.name, len(args), node)
        resolved = ResolvedDefFunTerm(node.name, ref, args, varterm, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_equality(self, node: ParsedEquality) -> ResolvedEquality:
        if node.ref.name in self.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = ResolvedRefEquality(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        tex = self.create_or_check_tex(node.tex, node.name, 2, node)
        resolved = ResolvedEquality(node.name, ref, tex)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_struct(self, node: ParsedStruct) -> ResolvedStruct:
        if node.ref.name in self.decl.get_used_names():
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = ResolvedRefStruct(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        vars: list[ResolvedVar] = []
        struct_vars: list[ResolvedStructVar] = []
        symbols: list[ResolvedVar | ResolvedStructVar] = []
        context = ResolvedContext.init()
        for v in node.vars:
            if isinstance(v, ParsedIdent):
                var = self.resolve_var(v, context.ctrl)
                vars.append(var)
                symbols.append(var)
            else:
                struct_var = self.resolve_struct_var(v, context.ctrl)
                struct_vars.append(struct_var)
                symbols.append(struct_var)
        local_ctx = context.add_ctrl(vars, struct_vars, [], [])
        formulas: dict[ResolvedRefStructCondition, ResolvedFormula] = {}
        for k, v in node.formulas.items():
            ref_formula = ResolvedRefStructCondition(k.name)
            self.add_node_to_token(ref_formula, k)
            self.add_ctrl_defs_refs(ref_formula, ref_formula)
            formulas[ref_formula] = self.resolve_formula(v, local_ctx)
        resolved = ResolvedStruct(node.name, ref, tuple(symbols), formulas)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_struct_predicate(self, node: ParsedStructPred) -> ResolvedStructPred:
        if not self.decl.has_struct(node.ref_struct.name):
            raise ResolveError(node.ref_struct, f"{node.ref_struct.name} is unknown")
        ref_struct = ResolvedRefStruct(node.ref_struct.name)
        self.add_node_to_token(ref_struct, node.ref_struct)
        struct = self.decl.get_struct(node.ref_struct.name)
        field_names = [field.name for field in struct.fields]
        condition_names = [condition.name for condition in struct.conditions]
        predicate_names = [name[len(node.ref_struct.name) + 1:] for name in self.decl.get_used_names() if name.startswith(node.ref_struct.name + ".")]
        if node.ref.name in field_names + condition_names + predicate_names:
            raise ResolveError(node.ref, f"{node.ref.name} is already used")
        ref = ResolvedRefStructPred(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        self.add_ctrl_defs_refs(ref, ref)
        context = ResolvedContext.init()
        context = context.add_ref_struct(ref_struct)
        args = self.resolve_vars(node.args, context.ctrl)
        local_ctx = context.add_ctrl(args, [], [], [])
        formula = self.resolve_formula(node.formula, local_ctx)
        resolved = ResolvedStructPred(node.name, ref_struct, ref, tuple(args), formula)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_invalid_declaration(self, node: ParsedInvalidDeclaration) -> ResolvedInvalidDeclaration:
        resolved = ResolvedInvalidDeclaration(node.name)
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

    def resolve_block(self, node: list[ParsedControl], context: ResolvedContext) -> list[ResolvedControl]:
        return [self.resolve_control(control, context) for control in node]

    def resolve_control(self, node: ParsedControl, context: ResolvedContext) -> ResolvedControl:
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
            invalid = ResolvedInvalidControl()
            self.add_node_to_token(invalid, node)
            return invalid

    def resolve_any(self, node: ParsedAny, context: ResolvedContext) -> ResolvedAny:
        local_vars, local_struct_vars, local_pred_tmpls, local_fun_tmpls, items = self.resolve_vars_or_struct_vars_or_pred_tmpls_or_fun_tmpls(node.items, context)
        local_ctx = context.add_ctrl(local_vars, local_struct_vars, local_pred_tmpls, local_fun_tmpls)
        body = self.resolve_block(node.body, local_ctx)
        resolved = ResolvedAny(items, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_assume(self, node: ParsedAssume, context: ResolvedContext) -> ResolvedAssume:
        premise = self.resolve_formula(node.premise, context)
        body = self.resolve_block(node.body, context)
        resolved = ResolvedAssume(premise, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_divide(self, node: ParsedDivide, context: ResolvedContext) -> ResolvedDivide:
        fact = self.resolve_reference_or_formula(node.fact, context)
        if len(node.cases) < 2:
            msg = "At least two cases are required"
            raise ResolveError(node, msg)
        cases = [self.resolve_case(case, context) for case in node.cases]
        resolved = ResolvedDivide(fact, cases)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_case(self, node: ParsedCase, context: ResolvedContext) -> ResolvedCase:
        premise = self.resolve_formula(node.premise, context)
        body = self.resolve_block(node.body, context)
        resolved = ResolvedCase(premise, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_some(self, node: ParsedSome, context: ResolvedContext) -> ResolvedSome:
        fact = self.resolve_reference_or_formula(node.fact, context)
        items, local_vars = self.resolve_vars_or_none(node.items, context.ctrl)
        local_ctx = context.add_ctrl(local_vars, [], [], [])
        body = self.resolve_block(node.body, local_ctx)
        resolved = ResolvedSome(items, fact, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_deny(self, node: ParsedDeny, context: ResolvedContext) -> ResolvedDeny:
        premise = self.resolve_formula(node.premise, context)
        body = self.resolve_block(node.body, context)
        resolved = ResolvedDeny(premise, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_contradict(self, node: ParsedContradict, context: ResolvedContext) -> ResolvedContradict:
        contradiction = self.resolve_formula(node.contradiction, context)
        resolved = ResolvedContradict(contradiction)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_explode(self, node: ParsedExplode, context: ResolvedContext) -> ResolvedExplode:
        conclusion = self.resolve_formula(node.conclusion, context)
        resolved = ResolvedExplode(conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_apply(self, node: ParsedApply, context: ResolvedContext) -> ResolvedApply:
        fact = self.resolve_reference_or_formula(node.fact, context)
        terms = [self.resolve_term(term, context) if isinstance(term, ParsedExpr) else None for term in node.terms]
        resolved = ResolvedApply(node.invoke, fact, terms)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_lift(self, node: ParsedLift, context: ResolvedContext) -> ResolvedLift:
        varterms: list[ResolvedVarTerm | None] = []
        for term in node.varterms:
            if isinstance(term, ParsedExpr):
                resolved_term = self.resolve_term(term, context)
                if not isinstance(resolved_term, ResolvedVarTerm):
                    raise ResolveError(node, "Unexpected type")
                varterms.append(resolved_term)
            elif term is None:
                varterms.append(term)
            else:
                raise ResolveError(node, "Unexpected type")
        conclusion = self.resolve_formula(node.conclusion, context)
        resolved = ResolvedLift(varterms, conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_characterize(self, node: ParsedCharacterize, context: ResolvedContext) -> ResolvedCharacterize:
        if not isinstance(node.varterm, ParsedExpr):
            raise ResolveError(node, "Unexpected type")
        varterm = self.resolve_term(node.varterm, context)
        if not isinstance(varterm, ResolvedVarTerm):
            raise ResolveError(node, "Unexpected type")
        conclusion = self.resolve_formula(node.conclusion, context)
        if not isinstance(conclusion, ResolvedExistsUniq):
            raise ResolveError(node, "Unexpected type")
        resolved = ResolvedCharacterize(varterm, conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_invoke(self, node: ParsedInvoke, context: ResolvedContext) -> ResolvedInvoke:
        fact = self.resolve_formula(node.fact, context)
        if node.direction == "none":
            if not isinstance(fact, ResolvedImplies):
                msg = f"Unexpected type {type(fact)}"
                raise ResolveError(node, msg)
        else:
            if not isinstance(fact, ResolvedIff):
                msg = f"Unexpected type {type(fact)}"
                raise ResolveError(node, msg)
        resolved = ResolvedInvoke(node.direction, fact)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_expand(self, node: ParsedExpand, context: ResolvedContext) -> ResolvedExpand:
        fact = self.resolve_reference_or_formula(node.fact, context)
        refs, indexes = self.resolve_refs_indexes(node, context)
        resolved = ResolvedExpand(fact, refs, indexes)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_fold(self, node: ParsedFold, context: ResolvedContext) -> ResolvedFold:
        refs, indexes = self.resolve_refs_indexes(node, context)
        conclusion = self.resolve_formula(node.conclusion, context)
        resolved = ResolvedFold(refs, indexes, conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_refs_indexes(self, node: ParsedExpand | ParsedFold, context: ResolvedContext) -> tuple[list[ResolvedRefDefFunTerm | ResolvedRefDefPred], dict[ResolvedRefDefFunTerm | ResolvedRefDefPred, list[int]]]:
        resolved_refs: list[ResolvedRefDefFunTerm | ResolvedRefDefPred] = []
        indexes: dict[ResolvedRefDefFunTerm | ResolvedRefDefPred, list[int]] = {}
        for ref in node.refs:
            if self.decl.has_deffunterm(ref.name):
                resolved_ref = ResolvedRefDefFunTerm(ref.name)
                self.add_node_to_token(resolved_ref, ref)
                resolved_refs.append(resolved_ref)
                if ref in node.indexes:
                    indexes[resolved_ref] = node.indexes[ref]
            elif self.decl.has_defpred(ref.name):
                resolved_ref = ResolvedRefDefPred(ref.name)
                self.add_node_to_token(resolved_ref, ref)
                resolved_refs.append(resolved_ref)
                if ref in node.indexes:
                    indexes[resolved_ref] = node.indexes[ref]
            else:
                msg = f"Unexpected name {ref.name}"
                raise ResolveError(node, msg)
        for k, v in node.indexes.items():
            if self.decl.has_deffunterm(k.name):
                indexes[ResolvedRefDefFunTerm(k.name)] = v
            elif self.decl.has_defpred(k.name):
                indexes[ResolvedRefDefPred(k.name)] = v
            else:
                msg = f"Unexpected name {k.name}"
                raise ResolveError(node, msg)
        return resolved_refs, indexes

    def resolve_pad(self, node: ParsedPad, context: ResolvedContext) -> ResolvedPad:
        fact = self.resolve_reference_or_formula(node.fact, context)
        conclusion = self.resolve_formula(node.conclusion, context)
        resolved = ResolvedPad(fact, conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_split(self, node: ParsedSplit, context: ResolvedContext) -> ResolvedSplit:
        fact = self.resolve_reference_or_formula(node.fact, context)
        resolved = ResolvedSplit(node.index, fact)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_connect(self, node: ParsedConnect, context: ResolvedContext) -> ResolvedConnect:
        conclusion = self.resolve_formula(node.conclusion, context)
        resolved = ResolvedConnect(conclusion)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_substitute(self, node: ParsedSubstitute, context: ResolvedContext) -> ResolvedSubstitute:
        fact = self.resolve_reference_or_formula(node.fact, context)
        env: dict[ResolvedTerm, ResolvedTerm] = {}
        indexes: dict[ResolvedTerm, list[int]] = {}
        for k, v in node.env.items():
            new_k = self.resolve_term(k, context)
            self.add_node_to_token(new_k, k)
            new_v = self.resolve_term(v, context)
            self.add_node_to_token(new_v, v)
            env[new_k] = new_v
            if k in node.indexes:
                indexes[new_k] = node.indexes[k]
        resolved = ResolvedSubstitute(fact, env, indexes)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_show(self, node: ParsedShow, context: ResolvedContext) -> ResolvedShow:
        conclusion = self.resolve_bot_or_formula(node.conclusion, context)
        body = self.resolve_block(node.body, context)
        resolved = ResolvedShow(conclusion, body)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_assert(self, node: ParsedAssert, context: ResolvedContext) -> ResolvedAssert:
        reference = self.resolve_reference_or_formula(node.reference, context)
        resolved = ResolvedAssert(reference)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_invalid_control(self, node: ParsedInvalidControl, context: ResolvedContext) -> ResolvedInvalidControl:
        resolved = ResolvedInvalidControl()
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_bot_or_formula(self, node: ParsedBottom | ParsedExpr, context: ResolvedContext) -> ResolvedBottom | ResolvedFormula:
        if isinstance(node, ParsedBottom):
            return ResolvedBottom()
        else:
            return self.resolve_formula(node, context)

    def resolve_reference_or_formula(self, node: ParsedExpr, context: ResolvedContext) -> ResolvedRefFact | ResolvedFormula:
        if isinstance(node, (ParsedIdent, ParsedAccess)):
            return self.resolve_reference_or_atomic_zero_arity_formula(node, context)
        else:
            return self.resolve_formula(node, context)

    def resolve_formula(self, node: ParsedExpr, context: ResolvedContext) -> ResolvedFormula:
        if isinstance(node, (ParsedIdent, ParsedIdentArgs, ParsedCall)):
            return self.resolve_atomic_formula(node, context)
        elif isinstance(node, ParsedNot):
            resolved = ResolvedNot(self.resolve_formula(node.body, context))
        elif isinstance(node, ParsedAnd):
            resolved = ResolvedAnd(self.resolve_formula(node.left, context), self.resolve_formula(node.right, context))
        elif isinstance(node, ParsedOr):
            resolved = ResolvedOr(self.resolve_formula(node.left, context), self.resolve_formula(node.right, context))
        elif isinstance(node, ParsedImplies):
            resolved = ResolvedImplies(self.resolve_formula(node.left, context), self.resolve_formula(node.right, context))
        elif isinstance(node, ParsedIff):
            resolved = ResolvedIff(self.resolve_formula(node.left, context), self.resolve_formula(node.right, context))
        elif isinstance(node, ParsedForall):
            local_vars, local_struct_vars, local_pred_tmpls, local_fun_tmpls, item = self.resolve_var_or_struct_var_or_pred_tmpl_or_fun_tmpl(node.var, context)
            local_ctx = context.add_form(local_vars, local_struct_vars, local_pred_tmpls, local_fun_tmpls)
            formula = self.resolve_formula(node.body, local_ctx)
            resolved = ResolvedForall(item, formula)
        elif isinstance(node, ParsedExists):
            var = self.resolve_var(node.var, context.form)
            local_ctx = context.add_form([var], [], [], [])
            formula = self.resolve_formula(node.body, local_ctx)
            resolved = ResolvedExists(var, formula)
        elif isinstance(node, ParsedExistsUniq):
            var = self.resolve_var(node.var, context.form)
            local_ctx = context.add_form([var], [], [], [])
            formula = self.resolve_formula(node.body, local_ctx)
            resolved = ResolvedExistsUniq(var, formula)
        else:
            msg = f"Unexpected node type: {type(node)}"
            raise ResolveError(node, msg)
        self.add_node_to_token(resolved, node)
        return resolved

    def resolve_reference_or_atomic_zero_arity_formula(self, node: ParsedIdent | ParsedAccess, context: ResolvedContext) -> ResolvedRefFact | ResolvedAtomicFormula:
        if isinstance(node, ParsedIdent):
            name = node.name
            if any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
                pred = ResolvedPredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(pred, node)
                self.add_ctrl_defs_refs(def_pred_tmpl, pred)
                formula = ResolvedAtomicFormula(pred, ())
                self.add_node_to_token(formula, node)
                return formula
            elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name)
                pred = ResolvedPredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(pred, node)
                self.add_ctrl_defs_refs(def_pred_tmpl, pred)
                formula = ResolvedAtomicFormula(pred, ())
                self.add_node_to_token(formula, node)
                return formula
            elif self.decl.has_axiom(name):
                ref = ResolvedRefAxiom(name)
                self.add_node_to_token(ref, node)
                return ref
            elif self.decl.has_theorem(name):
                ref = ResolvedRefTheorem(name)
                self.add_node_to_token(ref, node)
                return ref
            elif self.decl.has_defconexist(name):
                ref = ResolvedRefDefConExist(name)
                self.add_node_to_token(ref, node)
                return ref
            elif self.decl.has_defconuniq(name):
                ref = ResolvedRefDefConUniq(name)
                self.add_node_to_token(ref, node)
                return ref
            elif self.decl.has_deffunexist(name):
                ref = ResolvedRefDefFunExist(name)
                self.add_node_to_token(ref, node)
                return ref
            elif self.decl.has_deffununiq(name):
                ref = ResolvedRefDefFunUniq(name)
                self.add_node_to_token(ref, node)
                return ref
            else:
                msg = f"Unexpected name: {name}"
                raise ResolveError(node, msg)
        else:
            parent = self.resolve_term(node.parent, context)
            if isinstance(parent, ResolvedStructVar):
                ref_struct = parent.ref_struct
            elif isinstance(parent, ResolvedStructMemberField):
                ref_struct = parent.ref_struct
                if ref_struct is None:
                    raise ResolveError(node.parent, f"ref_struct of parent is unknown")
            else:
                raise ResolveError(node.parent, f"Unexpected type {type(node.parent)}")
            order = self.dependency_resolver.get_dependent_order(self.lexed_unit.file)
            def_unit = None
            def_struct = None
            for path in order:
                for unit in self.file_units[path]:
                    if isinstance(unit.resolved_unit.resolved_ast, ResolvedStruct) and unit.resolved_unit.resolved_ast.name == ref_struct.name:
                        def_unit = unit
                        def_struct = unit.resolved_unit.resolved_ast
            if def_unit is None or def_struct is None:
                raise ResolveError(node, "unit is not found")
            def_condition = None
            for condition in def_struct.conditions:
                if condition.name == node.child.name:
                    def_condition = condition
            if def_condition is None:
                raise ResolveError(node.child, f"{node.child.name} is not found")
            ref_condition = ResolvedRefStructCondition(node.child.name)
            self.add_node_to_token(ref_condition, node.child)
            self.add_ctrl_defs_refs(def_condition, ref_condition, ref_struct.name)
            access = ResolvedRefStructMemberCondition("", parent, ref_condition)
            self.add_node_to_token(access, node)
            return access

    def resolve_atomic_formula(self, node: ParsedIdent | ParsedIdentArgs | ParsedCall, context: ResolvedContext) -> ResolvedAtomicFormula:
        if isinstance(node, ParsedIdent):
            name = node.name
            if any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
                pred = ResolvedPredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(pred, node)
                self.add_ctrl_defs_refs(def_pred_tmpl, pred)
            elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name)
                pred = ResolvedPredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(pred, node)
                self.add_ctrl_defs_refs(def_pred_tmpl, pred)
            else:
                msg = f"Unexpected name: {name}"
                raise ResolveError(node, msg)
            formula = ResolvedAtomicFormula(pred, ())
            self.add_node_to_token(formula, node)
            return formula
        elif isinstance(node, ParsedIdentArgs):
            name = node.name.name
            equality = self.decl.get_equality()
            if any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
                pred = ResolvedPredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(pred, node.name)
                self.add_ctrl_defs_refs(def_pred_tmpl, pred)
                defargs = [Var(f"x_{i}") for i in range(pred.arity)]
            elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name)
                pred = ResolvedPredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(pred, node.name)
                self.add_ctrl_defs_refs(def_pred_tmpl, pred)
                defargs = [Var(f"x_{i}") for i in range(pred.arity)]
            elif equality is not None and name == equality.ref.name:
                pred = ResolvedRefEquality(name)
                self.add_node_to_token(pred, node.name)
                defargs = [Var(f"x_{i}") for i in range(2)]
            elif self.decl.has_primpred(name):
                pred = ResolvedRefPrimPred(name)
                self.add_node_to_token(pred, node.name)
                defargs = [Var(f"x_{i}") for i in range(self.decl.get_primpred(name).arity)]
            elif self.decl.has_defpred(name):
                pred = ResolvedRefDefPred(name)
                self.add_node_to_token(pred, node.name)
                defargs = self.decl.get_defpred(name).args
            else:
                msg = f"Unexpected name: {name}"
                raise ResolveError(node.name, msg)
            subargs = [self.resolve_term(arg, context) for arg in node.args]
            self.match_args(defargs, subargs, node)
            formula = ResolvedAtomicFormula(pred, tuple(subargs))
            self.add_node_to_token(formula, node)
            return formula
        else:
            callee = self.resolve_term(node.callee, context)
            if not isinstance(callee, ResolvedStructMemberPred):
                raise ResolveError(node.callee, f"Unexpected type {type(callee)}")
            if isinstance(callee.parent, ResolvedStructVar):
                ref_struct = callee.parent.ref_struct
            elif isinstance(callee.parent, ResolvedStructMemberField):
                ref_struct = callee.parent.ref_struct
                if ref_struct is None:
                    raise ResolveError(node.callee, f"ref_struct of parent is unknown")
            else:
                raise ResolveError(node.callee, f"Unexpected type {type(callee.parent)}")
            def_args = self.decl.get_structpred(f"{ref_struct.name}.{callee.struct_pred.name}").args
            subargs = tuple(self.resolve_term(arg, context) for arg in node.args)
            self.match_args(def_args, subargs, node)
            formula = ResolvedAtomicFormula(callee, subargs)
            self.add_node_to_token(formula, node)
            return formula

    def resolve_term(self, node: ParsedExpr, context: ResolvedContext) -> ResolvedTerm:
        if isinstance(node, ParsedIdent):
            name = node.name
            struct = None if context.ref_struct is None else self.get_struct(context.ref_struct.name)
            if any(var.name == name for var in context.form.vars):
                def_var = next(var for var in context.form.vars if var.name == name)
                ref_var = ResolvedVar(name)
                self.add_node_to_token(ref_var, node)
                self.add_ctrl_defs_refs(def_var, ref_var)
                return ref_var
            elif any(struct_var.name == name for struct_var in context.form.struct_vars):
                def_var = next(struct_var for struct_var in context.form.struct_vars if struct_var.name == name)
                ref_var = ResolvedStructVar(name, def_var.ref_struct)
                self.add_node_to_token(ref_var, node)
                self.add_ctrl_defs_refs(def_var, ref_var)
                return ref_var
            elif any(pred_tmpl.name == name for pred_tmpl in context.form.pred_tmpls):
                def_pred_tmpl = next(pred_tmpl for pred_tmpl in context.form.pred_tmpls if pred_tmpl.name == name)
                ref_pred_tmpl = ResolvedPredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(ref_pred_tmpl, node)
                self.add_ctrl_defs_refs(def_pred_tmpl, ref_pred_tmpl)
                return ref_pred_tmpl
            elif any(var.name == name for var in context.ctrl.vars):
                def_var = next((var for var in context.ctrl.vars if var.name == name))
                ref_var = ResolvedVar(name)
                self.add_node_to_token(ref_var, node)
                self.add_ctrl_defs_refs(def_var, ref_var)
                return ref_var
            elif any(struct_var.name == name for struct_var in context.ctrl.struct_vars):
                def_var = next(struct_var for struct_var in context.ctrl.struct_vars if struct_var.name == name)
                ref_var = ResolvedStructVar(name, def_var.ref_struct)
                self.add_node_to_token(ref_var, node)
                self.add_ctrl_defs_refs(def_var, ref_var)
                return ref_var
            elif any(pred_tmpl.name == name for pred_tmpl in context.ctrl.pred_tmpls):
                def_pred_tmpl = next((pred_tmpl for pred_tmpl in context.ctrl.pred_tmpls if pred_tmpl.name == name))
                ref_pred_tmpl = ResolvedPredTemplate(name, def_pred_tmpl.arity)
                self.add_node_to_token(ref_pred_tmpl, node)
                self.add_ctrl_defs_refs(def_pred_tmpl, ref_pred_tmpl)
                return ref_pred_tmpl
            elif struct is not None and any(field.name == name for field in struct.fields):
                def_field = next(field for field in struct.fields if field.name == name)
                if isinstance(def_field, ResolvedVar):
                    ref_field = ResolvedVar(name)
                else:
                    ref_field = ResolvedStructVar(name, def_field.ref_struct)
                self.add_node_to_token(ref_field, node)
                self.add_ctrl_defs_refs(def_field, ref_field, struct.name)
                return ref_field
            elif self.decl.has_defcon(name):
                ref = ResolvedRefDefCon(name)
                self.add_node_to_token(ref, node)
                return ref
            elif self.decl.has_primpred(name):
                ref = ResolvedRefPrimPred(name)
                self.add_node_to_token(ref, node)
                return ref
            elif self.decl.has_defpred(name):
                ref = ResolvedRefDefPred(name)
                self.add_node_to_token(ref, node)
                return ref
            else:
                raise ResolveError(node, f"{name} is unknown")
        elif isinstance(node, ParsedIdentArgs):
            name = node.name.name
            if self.decl.has_deffun(name) or self.decl.has_deffunterm(name) or any(fun_tmpl.name == name for fun_tmpl in context.form.fun_tmpls) or any(fun_tmpl.name == name for fun_tmpl in context.ctrl.fun_tmpls):
                if self.decl.has_deffun(name):
                    fun = ResolvedRefDefFun(name)
                    self.add_node_to_token(fun, node.name)
                    defargs, _ = strip_forall_vars(self.decl.get_theorem(self.decl.get_deffun(name).ref_theorem).conclusion)
                elif self.decl.has_deffunterm(name):
                    fun = ResolvedRefDefFunTerm(name)
                    self.add_node_to_token(fun, node.name)
                    defargs = self.decl.get_deffunterm(name).args
                elif any(fun_tmpl.name == name for fun_tmpl in context.form.fun_tmpls):
                    def_fun_tmpl = next(fun_tmpl for fun_tmpl in context.form.fun_tmpls if fun_tmpl.name == name)
                    fun = ResolvedFunTemplate(name, def_fun_tmpl.arity)
                    self.add_node_to_token(fun, node.name)
                    self.add_ctrl_defs_refs(def_fun_tmpl, fun)
                    defargs = [Var(f"x_{i}") for i in range(fun.arity)]
                else:
                    def_fun_tmpl = next(fun_tmpl for fun_tmpl in context.ctrl.fun_tmpls if fun_tmpl.name == name)
                    fun = ResolvedFunTemplate(name, def_fun_tmpl.arity)
                    self.add_node_to_token(fun, node.name)
                    self.add_ctrl_defs_refs(def_fun_tmpl, fun)
                    defargs = [Var(f"x_{i}") for i in range(fun.arity)]
                subargs = [self.resolve_term(arg, context) for arg in node.args]
                if len(subargs) == 0:
                    return fun
                else:
                    self.match_args(defargs, subargs, node)
                    term = ResolvedCompound(fun, tuple(subargs))
                    self.add_node_to_token(term, node.name)
                    return term
            elif self.decl.has_primpred(name):
                ref = ResolvedRefPrimPred(name)
                self.add_node_to_token(ref, node.name)
                return ref
            elif self.decl.has_defpred(name):
                ref = ResolvedRefDefPred(name)
                self.add_node_to_token(ref, node.name)
                return ref
            else:
                msg = f"Term object is required, but {name} is unknown"
                raise ResolveError(node, msg)
        elif isinstance(node, ParsedPredLambda):
            args = self.resolve_vars(node.args, context.form)
            body = self.resolve_formula(node.body, context.add_form(args, [], [], []))
            resolved = ResolvedPredLambda(tuple(args), body)
            self.add_node_to_token(resolved, node)
            return resolved
        elif isinstance(node, ParsedFunLambda):
            args = self.resolve_vars(node.args, context.form)
            body = self.resolve_term(node.body, context.add_form(args, [], [], []))
            if not isinstance(body, ResolvedVarTerm):
                raise ResolveError(node, "Unexpected type")
            resolved = ResolvedFunLambda(tuple(args), body)
            self.add_node_to_token(resolved, node)
            return resolved
        elif isinstance(node, ParsedAccess):
            parent = self.resolve_term(node.parent, context)
            if isinstance(parent, ResolvedStructVar):
                ref_struct = parent.ref_struct
            elif isinstance(parent, ResolvedStructMemberField):
                ref_struct = parent.ref_struct
                if ref_struct is None:
                    raise ResolveError(node.parent, f"ref_struct of parent is unknown")
            else:
                raise ResolveError(node.parent, f"Unexpected type {type(node.parent)}")
            order = self.dependency_resolver.get_dependent_order(self.lexed_unit.file)
            def_unit = None
            def_struct = None
            for path in order:
                for unit in self.file_units[path]:
                    if isinstance(unit.resolved_unit.resolved_ast, ResolvedStruct) and unit.resolved_unit.resolved_ast.name == ref_struct.name:
                        def_unit = unit
                        def_struct = unit.resolved_unit.resolved_ast
            if def_unit is None or def_struct is None:
                raise ResolveError(node, "unit is not found")
            def_field = None
            for field in def_struct.fields:
                if field.name == node.child.name:
                    def_field = field
            if def_field is not None:
                next_ref_struct = None if isinstance(def_field, ResolvedVar) else def_field.ref_struct
                ref_field = ResolvedRefStructField(node.child.name)
                self.add_node_to_token(ref_field, node.child)
                self.add_ctrl_defs_refs(def_field, ref_field, ref_struct.name)
                access = ResolvedStructMemberField(parent, ref_field, next_ref_struct)
                self.add_node_to_token(access, node)
                return access
            struct_predicate_name = f"{ref_struct.name}.{node.child.name}"
            def_predicate = self.get_struct_predicate(struct_predicate_name)
            if def_predicate is None:
                raise ResolveError(node, f"{struct_predicate_name} is not found")
            ref_predicate = ResolvedRefStructPred(node.child.name)
            self.add_node_to_token(ref_predicate, node.child)
            self.add_ctrl_defs_refs(def_predicate.ref, ref_predicate, def_predicate.name)
            access = ResolvedStructMemberPred(parent, ref_predicate)
            self.add_node_to_token(access, node)
            return access
        else:
            raise ResolveError(node, "Unexpected type")

    def resolve_vars_or_struct_vars_or_pred_tmpls_or_fun_tmpls(self, node: list[ParsedIdent | ParsedTypedIdent | ParsedPredTemplate | ParsedFunTemplate], context: ResolvedContext) -> tuple[list[ResolvedVar], list[ResolvedStructVar], list[ResolvedPredTemplate], list[ResolvedFunTemplate], list[ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate]]:
        vars: list[ResolvedVar] = []
        struct_vars: list[ResolvedStructVar] = []
        pred_tmpls: list[ResolvedPredTemplate] = []
        fun_tmpls: list[ResolvedFunTemplate] = []
        items: list[ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate] = []
        for item in node:
            if item.name in [used.name for used in items]:
                raise ResolveError(item, f"{item.name} is duplicated")
            if isinstance(item, ParsedIdent):
                var = self.resolve_var(item, context.ctrl)
                vars.append(var)
                items.append(var)
            elif isinstance(item, ParsedTypedIdent):
                struct_var = self.resolve_struct_var(item, context.ctrl)
                struct_vars.append(struct_var)
                items.append(struct_var)
            elif isinstance(item, ParsedPredTemplate):
                pred_tmpl = self.resolve_pred_tmpl(item, context.ctrl)
                pred_tmpls.append(pred_tmpl)
                items.append(pred_tmpl)
            elif isinstance(item, ParsedFunTemplate):
                fun_tmpl = self.resolve_fun_tmpl(item, context.ctrl)
                fun_tmpls.append(fun_tmpl)
                items.append(fun_tmpl)
            else:
                raise ResolveError(item, f"Unexpected type {type(item)}")
        return vars, struct_vars, pred_tmpls, fun_tmpls, items

    def resolve_vars_or_pred_tmpls_or_fun_tmpls(self, node: list[ParsedIdent | ParsedPredTemplate | ParsedFunTemplate], context: ResolvedControlContext | ResolvedFormulaContext) -> tuple[list[ResolvedVar], list[ResolvedPredTemplate], list[ResolvedFunTemplate], list[ResolvedVar | ResolvedPredTemplate | ResolvedFunTemplate]]:
        vars: list[ResolvedVar] = []
        pred_tmpls: list[ResolvedPredTemplate] = []
        fun_tmpls: list[ResolvedFunTemplate] = []
        items: list[ResolvedVar | ResolvedPredTemplate | ResolvedFunTemplate] = []
        for item in node:
            if item.name in [used.name for used in items]:
                raise ResolveError(item, f"{item.name} is duplicated")
            if isinstance(item, (ParsedIdent, ParsedTypedIdent)):
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

    def resolve_var_or_struct_var_or_pred_tmpl_or_fun_tmpl(self, node: ParsedIdent | ParsedTypedIdent | ParsedPredTemplate | ParsedFunTemplate, context: ResolvedContext) -> tuple[list[ResolvedVar], list[ResolvedStructVar], list[ResolvedPredTemplate], list[ResolvedFunTemplate], ResolvedVar | ResolvedStructVar | ResolvedPredTemplate | ResolvedFunTemplate]:
        vars: list[ResolvedVar] = []
        struct_vars: list[ResolvedStructVar] = []
        pred_tmpls: list[ResolvedPredTemplate] = []
        fun_tmpls: list[ResolvedFunTemplate] = []
        if isinstance(node, ParsedIdent):
            var = self.resolve_var(node, context.form)
            vars.append(var)
            item = var
        elif isinstance(node, ParsedTypedIdent):
            struct_var = self.resolve_struct_var(node, context.form)
            struct_vars.append(struct_var)
            item = struct_var
        elif isinstance(node, ParsedPredTemplate):
            pred_tmpl = self.resolve_pred_tmpl(node, context.form)
            pred_tmpls.append(pred_tmpl)
            item = pred_tmpl
        elif isinstance(node, ParsedFunTemplate):
            fun_tmpl = self.resolve_fun_tmpl(node, context.form)
            fun_tmpls.append(fun_tmpl)
            item = fun_tmpl
        else:
            raise ResolveError(node, f"Unexpected type {type(node)}")
        return vars, struct_vars, pred_tmpls, fun_tmpls, item

    def resolve_vars_or_none(self, node: list[ParsedIdent | None], context: ResolvedControlContext | ResolvedFormulaContext) -> tuple[list[ResolvedVar | None], list[ResolvedVar]]:
        vars_or_none: list[ResolvedVar | None] = []
        vars: list[ResolvedVar] = []
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

    def resolve_vars(self, node: tuple[ParsedIdent, ...], context: ResolvedControlContext | ResolvedFormulaContext) -> list[ResolvedVar]:
        vars: list[ResolvedVar] = []
        for item in node:
            if item.name in [used.name for used in vars]:
                raise ResolveError(item, f"{item.name} is duplicated")
            vars.append(self.resolve_var(item, context))
        return vars

    def resolve_var_or_struct_var(self, node: ParsedIdent | ParsedTypedIdent, context: ResolvedContext) -> ResolvedVar | ResolvedStructVar:
        if isinstance(node, ParsedIdent):
            return self.resolve_var(node, context.form)
        else:
            return self.resolve_struct_var(node, context.form)

    def resolve_struct_var(self, node: ParsedTypedIdent, context: ResolvedControlContext | ResolvedFormulaContext) -> ResolvedStructVar:
        if node.name.name in context.used_names:
            raise ResolveError(node.name, f"{node.name.name} is already used")
        if not self.decl.has_struct(node.type.name):
            raise ResolveError(node.type, f"{node.type.name} is unknown")
        ref = ResolvedRefStruct(node.type.name)
        self.add_node_to_token(ref, node.type)
        resolved = ResolvedStructVar(node.name.name, ref)
        self.add_node_to_token(resolved, node)
        self.add_ctrl_defs_refs(resolved, resolved)
        return resolved

    def resolve_var(self, node: ParsedIdent, context: ResolvedControlContext | ResolvedFormulaContext) -> ResolvedVar:
        if node.name in context.used_names:
            raise ResolveError(node, f"{node.name} is already used")
        var = ResolvedVar(node.name)
        self.add_node_to_token(var, node)
        self.add_ctrl_defs_refs(var, var)
        return var

    def resolve_pred_tmpl(self, node: ParsedPredTemplate, context: ResolvedControlContext | ResolvedFormulaContext) -> ResolvedPredTemplate:
        if node.name in context.used_names:
            raise ResolveError(node, f"{node.name} is already used")
        pred_tmpl = ResolvedPredTemplate(node.name, node.arity)
        self.add_node_to_token(pred_tmpl, node)
        self.add_ctrl_defs_refs(pred_tmpl, pred_tmpl)
        return pred_tmpl

    def resolve_fun_tmpl(self, node: ParsedFunTemplate, context: ResolvedControlContext | ResolvedFormulaContext) -> ResolvedFunTemplate:
        if node.name in context.used_names:
            raise ResolveError(node, f"{node.name} is already used")
        fun_tmpl = ResolvedFunTemplate(node.name, node.arity)
        self.add_node_to_token(fun_tmpl, node)
        self.add_ctrl_defs_refs(fun_tmpl, fun_tmpl)
        return fun_tmpl

    def match_args(self, defargs: Sequence[Var | PredTemplate | FunTemplate], subargs: Sequence[ResolvedTerm], node: ParsedIdentArgs | ParsedCall) -> None:
        if len(defargs) != len(subargs):
            msg = f"len(defargs): {len(defargs)}, len(subargs): {len(subargs)}"
            raise ResolveError(node, msg)
        for defarg, subarg in zip(defargs, subargs):
            if isinstance(defarg, Var):
                if not isinstance(subarg, ResolvedVarTerm):
                    msg = f"ResolvedVarTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted"
                    raise ResolveError(node, msg)
            elif isinstance(defarg, PredTemplate):
                if not isinstance(subarg, ResolvedPredTerm):
                    msg = f"ResolvedPredTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted"
                    raise ResolveError(node, msg)
            else:
                if not isinstance(subarg, ResolvedFunTerm):
                    msg = f"ResolvedFunTerm must be substituted into {defarg.name}, but {type(subarg)} is substituted"
                    raise ResolveError(node, msg)

    def get_struct(self, name: str) -> ResolvedStruct | None:
        order = self.dependency_resolver.get_dependent_order(self.lexed_unit.file)
        for path in order:
            for unit in self.file_units[path]:
                resolved_ast = unit.resolved_unit.resolved_ast
                if (isinstance(resolved_ast, ResolvedStruct) and resolved_ast.name == name):
                    return resolved_ast
        return None

    def get_struct_predicate(self, struct_predicate_name: str) -> ResolvedStructPred | None:
        order = self.dependency_resolver.get_dependent_order(self.lexed_unit.file)
        for path in order:
            for unit in self.file_units[path]:
                resolved_ast = unit.resolved_unit.resolved_ast
                if isinstance(resolved_ast, ResolvedStructPred) and resolved_ast.name == struct_predicate_name:
                    return resolved_ast
        return None
