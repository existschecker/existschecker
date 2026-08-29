from lsprotocol import types as lsp
from pygls import uris
from ast_types import DeclarationUnit, Term, Declaration, PrimPred, Axiom, Theorem, DefPred, DefCon, DefConExist, DefConUniq, DefFun, DefFunExist, DefFunUniq, DefFunTerm, Equality, InvalidDeclaration, Formula, AtomicFormula, Not, And, Or, Implies, Iff, Forall, Exists, ExistsUniq, PredTemplate, Var, FunTemplate, RefEquality, Compound, RefPrimPred, RefDefPred, RefDefCon, RefDefFun, RefDefFunTerm, VarTerm, PredTerm, FunTerm, Control, Any, Assume, Divide, Some, Deny, Case, Contradict, Explode, Apply, Lift, Characterize, Invoke, Expand, Fold, Pad, Split, Connect, Substitute, Show, Assert, InvalidControl, RefAxiom, RefTheorem, RefDefConExist, RefDefConUniq, RefDefFunExist, RefDefFunUniq, RefFact, PredLambda, FunLambda, Bottom, Include, InvalidInclude, DeclarationContextNameSpace, RefStruct, Struct, RefStructCondition, StructVar, RefStructPred, StructPred
from resolved_ast_types import ResolvedTerm, ResolvedFormula, ResolvedVarTerm, ResolvedVar, ResolvedRefDefCon, ResolvedFunTerm, ResolvedRefDefFun, ResolvedRefDefFunTerm, ResolvedFunTemplate, ResolvedFunLambda, ResolvedCompound, ResolvedPredTerm, ResolvedRefEquality, ResolvedRefPrimPred, ResolvedRefDefPred, ResolvedPredTemplate, ResolvedPredLambda, ResolvedAtomicFormula, ResolvedNot, ResolvedAnd, ResolvedOr, ResolvedImplies, ResolvedIff, ResolvedForall, ResolvedExists, ResolvedExistsUniq, ResolvedBottom, ResolvedRefFact, ResolvedRefAxiom, ResolvedRefTheorem, ResolvedRefDefConExist, ResolvedRefDefConUniq, ResolvedRefDefFunExist, ResolvedRefDefFunUniq, ResolvedControl, ResolvedInvalidControl, ResolvedAssume, ResolvedAny, ResolvedCase, ResolvedDivide, ResolvedSome, ResolvedDeny, ResolvedContradict, ResolvedExplode, ResolvedApply, ResolvedLift, ResolvedCharacterize, ResolvedInvoke, ResolvedExpand, ResolvedFold, ResolvedPad, ResolvedSplit, ResolvedConnect, ResolvedSubstitute, ResolvedShow, ResolvedAssert, ResolvedDeclaration, ResolvedInvalidDeclaration, ResolvedPrimPred, ResolvedAxiom, ResolvedTheorem, ResolvedDefPred, ResolvedDefConExist, ResolvedDefConUniq, ResolvedDefCon, ResolvedDefFunExist, ResolvedDefFunUniq, ResolvedDefFun, ResolvedDefFunTerm, ResolvedEquality, ResolvedInclude, ResolvedInvalidInclude, ResolvedRefStruct, ResolvedStructVar, ResolvedStructMemberField, ResolvedRefStructCondition, ResolvedRefStructMemberCondition, ResolvedStruct, ResolvedStructPred, ResolvedStructMemberPred, ResolvedRefStructPred
from lexer import Token
from logic_utils import Substitutor, DefExpander, strip_forall_vars, alpha_safe_formula

class ElaborateError(Exception):
    def __init__(self, node: ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact, msg: str) -> None:
        self.node = node
        self.msg = msg

class Elaborator:
    def __init__(self, unit: DeclarationUnit, decl: DeclarationContextNameSpace) -> None:
        self.unit = unit
        self.decl = decl

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
            source="Elaborator",
            severity=lsp.DiagnosticSeverity.Error
        )
        self.unit.diagnostics.append(diag)

    def get_node_token(self, node: ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact) -> Token:
        return self.unit.tokens[self.unit.resolved_node_to_token[id(node)][0]]

    def add_node_to_token(self, node: Declaration | Control | Formula | Term | RefFact | RefStruct | RefStructCondition | StructVar | RefStructPred, resolved: ResolvedDeclaration | ResolvedControl | ResolvedFormula | ResolvedTerm | ResolvedRefFact | ResolvedRefStruct | ResolvedRefStructCondition | ResolvedRefStructPred) -> None:
        self.unit.node_to_token[id(node)] = self.unit.resolved_node_to_token[id(resolved)]
        self.unit.nodes.append(node)

    def elaborate_unit(self) -> None:
        if isinstance(self.unit.resolved_ast, ResolvedInclude):
            self.unit.ast = self.elaborate_include(self.unit.resolved_ast)
        elif isinstance(self.unit.resolved_ast, ResolvedDeclaration):
            self.unit.ast = self.elaborate_declaration(self.unit.resolved_ast)

    def elaborate_include(self, node: ResolvedInclude) -> Include:
        if isinstance(node, ResolvedInvalidInclude):
            return InvalidInclude(node.file, node.token)
        else:
            return Include(node.file, node.token)

    def elaborate_declaration(self, node: ResolvedDeclaration) -> Declaration:
        try:
            if isinstance(node, ResolvedPrimPred):
                return self.elaborate_primpred(node)
            elif isinstance(node, ResolvedAxiom):
                return self.elaborate_axiom(node)
            elif isinstance(node, ResolvedTheorem):
                return self.elaborate_theorem(node)
            elif isinstance(node, ResolvedDefPred):
                return self.elaborate_defpred(node)
            elif isinstance(node, ResolvedDefCon):
                return self.elaborate_defcon(node)
            elif isinstance(node, ResolvedDefFun):
                return self.elaborate_deffun(node)
            elif isinstance(node, ResolvedDefConExist):
                return self.elaborate_defconexist(node)
            elif isinstance(node, ResolvedDefConUniq):
                return self.elaborate_defconuniq(node)
            elif isinstance(node, ResolvedDefFunExist):
                return self.elaborate_deffunexist(node)
            elif isinstance(node, ResolvedDefFunUniq):
                return self.elaborate_deffununiq(node)
            elif isinstance(node, ResolvedDefFunTerm):
                return self.elaborate_deffunterm(node)
            elif isinstance(node, ResolvedEquality):
                return self.elaborate_equality(node)
            elif isinstance(node, ResolvedStruct):
                return self.elaborate_struct(node)
            elif isinstance(node, ResolvedStructPred):
                return self.elaborate_struct_predicate(node)
            elif isinstance(node, ResolvedInvalidDeclaration):
                return self.elaborate_invalid_declaration(node)
            else:
                msg = f"Unsupported node {node}"
                raise ElaborateError(node, msg)
        except ElaborateError as e:
            self.add_lsp_error(self.get_node_token(e.node), e.msg)
            elaborated = InvalidDeclaration(node.name)
            self.add_node_to_token(elaborated, node)
            return elaborated

    def elaborate_primpred(self, node: ResolvedPrimPred) -> PrimPred:
        ref = RefPrimPred(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        elaborated = PrimPred(node.name, ref, node.arity, node.tex)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_axiom(self, node: ResolvedAxiom) -> Axiom:
        ref = RefAxiom(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        conclusion = self.elaborate_formula(node.conclusion)
        elaborated = Axiom(node.name, ref, conclusion)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_theorem(self, node: ResolvedTheorem) -> Theorem:
        ref = RefTheorem(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        conclusion = self.elaborate_formula(node.conclusion)
        proof = self.elaborate_block(node.proof)
        elaborated = Theorem(node.name, ref, conclusion, proof)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_defpred(self, node: ResolvedDefPred) -> DefPred:
        ref = RefDefPred(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        _, _, _, args = self.elaborate_vars_or_pred_tmpls_or_fun_tmpls(node.args)
        formula = self.elaborate_formula(node.formula)
        elaborated = DefPred(node.name, ref, args, formula, node.autoexpand, node.tex)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_defcon(self, node: ResolvedDefCon) -> DefCon:
        ref = RefDefCon(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        ref_theorem = RefTheorem(node.ref_theorem.name)
        self.add_node_to_token(ref_theorem, node.ref_theorem)
        elaborated = DefCon(node.name, ref, ref_theorem, node.tex)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_deffun(self, node: ResolvedDefFun) -> DefFun:
        ref = RefDefFun(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        ref_theorem = RefTheorem(node.ref_theorem.name)
        self.add_node_to_token(ref_theorem, node.ref_theorem)
        elaborated = DefFun(node.name, ref, ref_theorem, node.tex)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_defconexist(self, node: ResolvedDefConExist) -> DefConExist:
        ref = RefDefConExist(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        formula = self.elaborate_formula(node.formula)
        ref_con = RefDefCon(node.ref_con.name)
        self.add_node_to_token(ref_con, node.ref_con)
        elaborated = DefConExist(node.name, ref, formula, ref_con)
        self.add_node_to_token(elaborated, node)
        return elaborated
    
    def elaborate_defconuniq(self, node: ResolvedDefConUniq) -> DefConUniq:
        ref = RefDefConUniq(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        formula = self.elaborate_formula(node.formula)
        ref_con = RefDefCon(node.ref_con.name)
        self.add_node_to_token(ref_con, node.ref_con)
        elaborated = DefConUniq(node.name, ref, formula, ref_con)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_deffunexist(self, node: ResolvedDefFunExist) -> DefFunExist:
        ref = RefDefFunExist(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        formula = self.elaborate_formula(node.formula)
        ref_fun = RefDefFun(node.ref_fun.name)
        self.add_node_to_token(ref_fun, node.ref_fun)
        elaborated = DefFunExist(node.name, ref, formula, ref_fun)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_deffununiq(self, node: ResolvedDefFunUniq) -> DefFunUniq:
        ref = RefDefFunUniq(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        formula = self.elaborate_formula(node.formula)
        ref_fun = RefDefFun(node.ref_fun.name)
        self.add_node_to_token(ref_fun, node.ref_fun)
        elaborated = DefFunUniq(node.name, ref, formula, ref_fun)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_deffunterm(self, node: ResolvedDefFunTerm) -> DefFunTerm:
        ref = RefDefFunTerm(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        _, _, _, args = self.elaborate_vars_or_pred_tmpls_or_fun_tmpls(node.args)
        varterm = self.elaborate_var_term(node.varterm)
        elaborated = DefFunTerm(node.name, ref, args, varterm, node.tex)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_equality(self, node: ResolvedEquality) -> Equality:
        ref = RefEquality(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        elaborated = Equality(node.name, ref, node.tex)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_struct(self, node: ResolvedStruct) -> Declaration:
        ref = RefStruct(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        fields = self.elaborate_vars_or_struct_vars(node.fields)
        conditions: dict[RefStructCondition, Formula] = {}
        for k, v in node.conditions.items():
            ref_condition = RefStructCondition(k.name)
            self.add_node_to_token(ref_condition, k)
            conditions[ref_condition] = self.elaborate_formula(v)
        elaboated = Struct(node.name, ref, fields, conditions)
        self.add_node_to_token(elaboated, node)
        return elaboated

    def elaborate_struct_predicate(self, node: ResolvedStructPred) -> StructPred:
        ref_struct = RefStruct(node.ref_struct.name)
        self.add_node_to_token(ref_struct, node.ref_struct)
        ref = RefStructPred(node.ref.name)
        self.add_node_to_token(ref, node.ref)
        args = self.elaborate_vars(node.args)
        formula = self.elaborate_formula(node.formula)
        elaborated = StructPred(node.name, ref_struct, ref, args, formula)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_vars_or_struct_vars(self, nodes: tuple[ResolvedVar | ResolvedStructVar, ...]) -> list[Var | StructVar]:
        fields: list[Var | StructVar] = []
        for node in nodes:
            if isinstance(node, ResolvedVar):
                field = Var(node.name)
            else:
                ref_struct = RefStruct(node.ref_struct.name)
                self.add_node_to_token(ref_struct, node.ref_struct)
                field = StructVar(node.name, ref_struct)
            self.add_node_to_token(field, node)
            fields.append(field)
        return fields

    def elaborate_invalid_declaration(self, node: ResolvedInvalidDeclaration) -> InvalidDeclaration:
        elaborated = InvalidDeclaration(node.name)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_block(self, node: list[ResolvedControl]) -> list[Control]:
        controls: list[Control] = []
        for control in node:
            controls.extend(self.elaborate_control(control))
        return controls

    def elaborate_control(self, node: ResolvedControl) -> list[Control]:
        try:
            if isinstance(node, ResolvedAny):
                return self.elaborate_any(node)
            elif isinstance(node, ResolvedAssume):
                return self.elaborate_assume(node)
            elif isinstance(node, ResolvedDivide):
                return self.elaborate_divide(node)
            elif isinstance(node, ResolvedSome):
                return self.elaborate_some(node)
            elif isinstance(node, ResolvedDeny):
                return self.elaborate_deny(node)
            elif isinstance(node, ResolvedContradict):
                return self.elaborate_contradict(node)
            elif isinstance(node, ResolvedExplode):
                return self.elaborate_explode(node)
            elif isinstance(node, ResolvedApply):
                return self.elaborate_apply(node)
            elif isinstance(node, ResolvedLift):
                return self.elaborate_lift(node)
            elif isinstance(node, ResolvedCharacterize):
                return self.elaborate_characterize(node)
            elif isinstance(node, ResolvedInvoke):
                return self.elaborate_invoke(node)
            elif isinstance(node, ResolvedExpand):
                return self.elaborate_expand(node)
            elif isinstance(node, ResolvedFold):
                return self.elaborate_fold(node)
            elif isinstance(node, ResolvedPad):
                return self.elaborate_pad(node)
            elif isinstance(node, ResolvedSplit):
                return self.elaborate_split(node)
            elif isinstance(node, ResolvedConnect):
                return self.elaborate_connect(node)
            elif isinstance(node, ResolvedSubstitute):
                return self.elaborate_substitute(node)
            elif isinstance(node, ResolvedShow):
                return self.elaborate_show(node)
            elif isinstance(node, ResolvedAssert):
                return self.elaborate_assert(node)
            elif isinstance(node, ResolvedInvalidControl):
                return self.elaborate_invalid_control(node)
            else:
                msg = f"Unsupported node {node}"
                raise ElaborateError(node, msg)
        except ElaborateError as e:
            self.add_lsp_error(self.get_node_token(e.node), e.msg)
            invalid = InvalidControl()
            self.add_node_to_token(invalid, node)
            return [invalid]

    def elaborate_any(self, node: ResolvedAny) -> list[Control]:
        body: list[Control] = self.elaborate_block(node.body)
        for item in reversed(node.items):
            if isinstance(item, ResolvedVar):
                var = self.elaborate_var(item)
                control = Any([var], body)
                self.add_node_to_token(control, node)
                body = [control]
            elif isinstance(item, ResolvedStructVar):
                fields, conditions = self.collect_struct_members(item)
                for condition in reversed(conditions.values()):
                    control = Assume(condition, body)
                    self.add_node_to_token(control, node)
                    body = [control]
                control = Any(list(fields), body)
                self.add_node_to_token(control, node)
                body = [control]
            elif isinstance(item, ResolvedPredTemplate):
                var = self.elaborate_pred_tmpl(item)
                control = Any([var], body)
                self.add_node_to_token(control, node)
                body = [control]
            elif isinstance(item, ResolvedFunTemplate):
                var = self.elaborate_fun_tmpl(item)
                control = Any([var], body)
                self.add_node_to_token(control, node)
                body = [control]
            else:
                raise ElaborateError(node, f"Unexpected type {type(item)}")
        result = body[0]
        if not isinstance(result, Any):
            raise ElaborateError(node, f"Unexpected type {type(result)}")
        return [result]

    def elaborate_assume(self, node: ResolvedAssume) -> list[Control]:
        premise = self.elaborate_formula(node.premise)
        body = self.elaborate_block(node.body)
        elaborated = Assume(premise, body)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_divide(self, node: ResolvedDivide) -> list[Control]:
        fact = self.elaborate_reference_or_formula(node.fact)
        if len(node.cases) < 2:
            msg = "At least two cases are required"
            raise ElaborateError(node, msg)
        cases = [self.elaborate_case(case) for case in node.cases]
        elaborated = Divide(fact, cases)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_case(self, node: ResolvedCase) -> Case:
        premise = self.elaborate_formula(node.premise)
        body = self.elaborate_block(node.body)
        elaborated = Case(premise, body)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_some(self, node: ResolvedSome) -> list[Control]:
        fact = self.elaborate_reference_or_formula(node.fact)
        items, _ = self.elaborate_vars_or_none(node.items)
        body = self.elaborate_block(node.body)
        elaborated = Some(items, fact, body)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_deny(self, node: ResolvedDeny) -> list[Control]:
        premise = self.elaborate_formula(node.premise)
        body = self.elaborate_block(node.body)
        elaborated = Deny(premise, body)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_contradict(self, node: ResolvedContradict) -> list[Control]:
        contradiction = self.elaborate_formula(node.contradiction)
        elaborated = Contradict(contradiction)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_explode(self, node: ResolvedExplode) -> list[Control]:
        conclusion = self.elaborate_formula(node.conclusion)
        elaborated = Explode(conclusion)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_apply(self, node: ResolvedApply) -> list[Control]:
        reference_or_formula = self.elaborate_reference_or_formula(node.fact)
        struct_used = False
        for term in node.terms:
            if isinstance(term, ResolvedStructVar):
                struct_used = True
                break
            elif isinstance(term, ResolvedStructMemberField) and term.ref_struct is not None:
                struct_used = True
                break
        if not struct_used:
            terms_or_none = [None if term is None else self.elaborate_term(term) for term in node.terms]
            apply = Apply(node.invoke, reference_or_formula, terms_or_none)
            self.add_node_to_token(apply, node)
            return [apply]
        first = True
        fact = reference_or_formula
        controls: list[Control] = []
        for term in node.terms:
            if term is None:
                raise ElaborateError(node, "Struct and None cannot be used together")
            if isinstance(term, ResolvedStructVar):
                terms, conditions = self.collect_struct_members(term)
            elif isinstance(term, ResolvedStructMemberField):
                if term.ref_struct is None:
                    raise ElaborateError(term, "ref_struct is unknown")
                terms, conditions = self.collect_struct_members(ResolvedStructVar(self.get_struct_access_name(term), term.ref_struct))
            else:
                terms = [self.elaborate_term(term)]
                conditions = {}
            if isinstance(fact, RefFact):
                fact = self.decl.get_fact(fact)
            if isinstance(fact, AtomicFormula) and isinstance(fact.pred, RefDefPred):
                fact = DefExpander([fact.pred], self.decl, {fact.pred: [1]}).expand_defs_formula(fact)
            vars_, _ = strip_forall_vars(fact)
            if len(vars_) < len(terms):
                raise ElaborateError(node, f"{len(terms)} terms are given to {len(vars_)} forall vars")
            apply = Apply("none", reference_or_formula if first else fact, list(terms + [None] * (len(vars_) - len(terms))))
            first = False
            self.add_node_to_token(apply, node)
            controls.append(apply)
            mapping: dict[Term, Term] = {}
            for term in terms:
                if not isinstance(fact, Forall):
                    raise ElaborateError(node, f"Expected Forall, got {type(fact)}")
                mapping[fact.var] = term
                fact = fact.body
            fact, renamed_mapping = alpha_safe_formula(fact, mapping)
            fact = Substitutor(renamed_mapping).substitute_formula(fact)
            for _ in range(len(conditions)):
                if not isinstance(fact, Implies):
                    raise ElaborateError(node, f"Expected Implies, got {type(fact)}")
                invoke = Invoke("none", fact)
                self.add_node_to_token(invoke, node)
                controls.append(invoke)
                fact = fact.right
        if node.invoke != "none":
            if not isinstance(fact, (Implies, Iff)):
                raise ElaborateError(node, f"Expected Implies of Iff, got {type(fact)}")
            if node.invoke == "invoke":
                invoke = Invoke("none", fact)
            elif node.invoke == "invoke-rightward":
                invoke = Invoke("rightward", fact)
            else:
                invoke = Invoke("leftward", fact)
            self.add_node_to_token(invoke, node)
            controls.append(invoke)
        return controls

    def elaborate_lift(self, node: ResolvedLift) -> list[Control]:
        varterms: list[VarTerm | None] = []
        for term in node.varterms:
            if isinstance(term, ResolvedVarTerm):
                elaborated_term = self.elaborate_var_term(term)
                varterms.append(elaborated_term)
            elif term is None:
                varterms.append(term)
            else:
                raise ElaborateError(node, "Unexpected type")
        conclusion = self.elaborate_formula(node.conclusion)
        elaborated = Lift(varterms, conclusion)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_characterize(self, node: ResolvedCharacterize) -> list[Control]:
        varterm = self.elaborate_var_term(node.varterm)
        conclusion = self.elaborate_formula(node.conclusion)
        if not isinstance(conclusion, ExistsUniq):
            raise ElaborateError(node, "Unexpected type")
        elaborated = Characterize(varterm, conclusion)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_invoke(self, node: ResolvedInvoke) -> list[Control]:
        fact = self.elaborate_formula(node.fact)
        if node.direction == "none":
            if not isinstance(fact, Implies):
                msg = f"Unexpected type {type(fact)}"
                raise ElaborateError(node, msg)
        else:
            if not isinstance(fact, Iff):
                msg = f"Unexpected type {type(fact)}"
                raise ElaborateError(node, msg)
        elaborated = Invoke(node.direction, fact)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_expand(self, node: ResolvedExpand) -> list[Control]:
        fact = self.elaborate_reference_or_formula(node.fact)
        refs, indexes = self.elaborate_refs_indexes(node)
        elaborated = Expand(fact, refs, indexes)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_fold(self, node: ResolvedFold) -> list[Control]:
        refs, indexes = self.elaborate_refs_indexes(node)
        conclusion = self.elaborate_formula(node.conclusion)
        elaborated = Fold(refs, indexes, conclusion)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_refs_indexes(self, node: ResolvedExpand | ResolvedFold) -> tuple[list[RefDefFunTerm | RefDefPred], dict[RefDefFunTerm | RefDefPred, list[int]]]:
        elaborated_refs: list[RefDefFunTerm | RefDefPred] = []
        indexes: dict[RefDefFunTerm | RefDefPred, list[int]] = {}
        for ref in node.refs:
            if self.decl.has_deffunterm(ref.name):
                elaborated_ref = RefDefFunTerm(ref.name)
                self.add_node_to_token(elaborated_ref, ref)
                elaborated_refs.append(elaborated_ref)
                if ref in node.indexes:
                    indexes[elaborated_ref] = node.indexes[ref]
            elif self.decl.has_defpred(ref.name):
                elaborated_ref = RefDefPred(ref.name)
                self.add_node_to_token(elaborated_ref, ref)
                elaborated_refs.append(elaborated_ref)
                if ref in node.indexes:
                    indexes[elaborated_ref] = node.indexes[ref]
            else:
                msg = f"Unexpected name {ref.name}"
                raise ElaborateError(node, msg)
        for k, v in node.indexes.items():
            if self.decl.has_deffunterm(k.name):
                indexes[RefDefFunTerm(k.name)] = v
            elif self.decl.has_defpred(k.name):
                indexes[RefDefPred(k.name)] = v
            else:
                msg = f"Unexpected name {k.name}"
                raise ElaborateError(node, msg)
        return elaborated_refs, indexes

    def elaborate_pad(self, node: ResolvedPad) -> list[Control]:
        fact = self.elaborate_reference_or_formula(node.fact)
        conclusion = self.elaborate_formula(node.conclusion)
        elaborated = Pad(fact, conclusion)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_split(self, node: ResolvedSplit) -> list[Control]:
        fact = self.elaborate_reference_or_formula(node.fact)
        elaborated = Split(node.index, fact)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_connect(self, node: ResolvedConnect) -> list[Control]:
        conclusion = self.elaborate_formula(node.conclusion)
        elaborated = Connect(conclusion)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_substitute(self, node: ResolvedSubstitute) -> list[Control]:
        fact = self.elaborate_reference_or_formula(node.fact)
        env: dict[Term, Term] = {}
        indexes: dict[Term, list[int]] = {}
        for k, v in node.env.items():
            new_k = self.elaborate_term(k)
            self.add_node_to_token(new_k, k)
            new_v = self.elaborate_term(v)
            self.add_node_to_token(new_v, v)
            env[new_k] = new_v
            if k in node.indexes:
                indexes[new_k] = node.indexes[k]
        elaborated = Substitute(fact, env, indexes)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_show(self, node: ResolvedShow) -> list[Control]:
        conclusion = self.elaborate_bot_or_formula(node.conclusion)
        body = self.elaborate_block(node.body)
        elaborated = Show(conclusion, body)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_assert(self, node: ResolvedAssert) -> list[Control]:
        reference = self.elaborate_reference_or_formula(node.reference)
        elaborated = Assert(reference)
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_invalid_control(self, node: ResolvedInvalidControl) -> list[Control]:
        elaborated = InvalidControl()
        self.add_node_to_token(elaborated, node)
        return [elaborated]

    def elaborate_bot_or_formula(self, node: ResolvedBottom | ResolvedFormula) -> Bottom | Formula:
        if isinstance(node, ResolvedBottom):
            return Bottom()
        else:
            return self.elaborate_formula(node)

    def elaborate_reference_or_formula(self, node: ResolvedRefFact | ResolvedFormula) -> RefFact | Formula:
        if isinstance(node, ResolvedRefFact):
            if isinstance(node, ResolvedRefAxiom):
                elaborated = RefAxiom(node.name)
            elif isinstance(node, ResolvedRefTheorem):
                elaborated = RefTheorem(node.name)
            elif isinstance(node, ResolvedRefDefConExist):
                elaborated = RefDefConExist(node.name)
            elif isinstance(node, ResolvedRefDefConUniq):
                elaborated = RefDefConUniq(node.name)
            elif isinstance(node, ResolvedRefDefFunExist):
                elaborated = RefDefFunExist(node.name)
            elif isinstance(node, ResolvedRefDefFunUniq):
                elaborated = RefDefFunUniq(node.name)
            elif isinstance(node, ResolvedRefStructMemberCondition):
                parent_name = self.get_struct_access_name(node.parent)
                full_name = f"{parent_name}.{node.struct_condition.name}"
                _, conditions = self.collect_struct_members(node.parent)
                elaborated = conditions[RefStructCondition(full_name)]
            else:
                raise ElaborateError(node, f"Unexpected type {type(node)}")
            self.add_node_to_token(elaborated, node)
            return elaborated
        else:
            return self.elaborate_formula(node)

    def elaborate_formula(self, node: ResolvedFormula) -> Formula:
        if isinstance(node, ResolvedAtomicFormula):
            return self.elaborate_atomic_formula(node)
        elif isinstance(node, ResolvedNot):
            elaborated = Not(self.elaborate_formula(node.body))
        elif isinstance(node, ResolvedAnd):
            elaborated = And(self.elaborate_formula(node.left), self.elaborate_formula(node.right))
        elif isinstance(node, ResolvedOr):
            elaborated = Or(self.elaborate_formula(node.left), self.elaborate_formula(node.right))
        elif isinstance(node, ResolvedImplies):
            elaborated = Implies(self.elaborate_formula(node.left), self.elaborate_formula(node.right))
        elif isinstance(node, ResolvedIff):
            elaborated = Iff(self.elaborate_formula(node.left), self.elaborate_formula(node.right))
        elif isinstance(node, ResolvedForall):
            body = self.elaborate_formula(node.body)
            if isinstance(node.var, ResolvedVar):
                var = self.elaborate_var(node.var)
                elaborated = Forall(var, body)
            elif isinstance(node.var, ResolvedStructVar):
                fields, conditions = self.collect_struct_members(node.var)
                elaborated = body
                for condition in reversed(conditions.values()):
                    elaborated = Implies(condition, elaborated)
                for field in reversed(fields):
                    elaborated = Forall(field, elaborated)
            elif isinstance(node.var, ResolvedPredTemplate):
                var = self.elaborate_pred_tmpl(node.var)
                elaborated = Forall(var, body)
            elif isinstance(node.var, ResolvedFunTemplate):
                var = self.elaborate_fun_tmpl(node.var)
                elaborated = Forall(var, body)
            else:
                msg = f"Unexpected var type: {type(node.var)}"
                raise ElaborateError(node.var, msg)
        elif isinstance(node, ResolvedExists):
            var = self.elaborate_var(node.var)
            body = self.elaborate_formula(node.body)
            elaborated = Exists(var, body)
        elif isinstance(node, ResolvedExistsUniq):
            var = self.elaborate_var(node.var)
            body = self.elaborate_formula(node.body)
            elaborated = ExistsUniq(var, body)
        else:
            msg = f"Unexpected node type: {type(node)}"
            raise ElaborateError(node, msg)
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_atomic_formula(self, node: ResolvedAtomicFormula) -> Formula:
        if isinstance(node.pred, ResolvedStructMemberPred):
            if isinstance(node.pred.parent, ResolvedStructVar):
                ref_struct = node.pred.parent.ref_struct
            elif isinstance(node.pred.parent, ResolvedStructMemberField):
                if node.pred.parent.ref_struct is None:
                    raise ElaborateError(node.pred.parent, "Parent is not a struct")
                ref_struct = node.pred.parent.ref_struct
            else:
                raise ElaborateError(node.pred.parent, f"Unexpected type {type(node.pred.parent)}")
            fields, _ = self.collect_struct_members(node.pred.parent)
            prefix = self.get_struct_access_name(node.pred.parent)
            mapping_field: dict[VarTerm, VarTerm] = {}
            for field in fields:
                if not field.name.startswith(prefix + "."):
                    continue
                mapping_field[Var(field.name[len(prefix) + 1:])] = field
            structpred = self.decl.get_structpred(f"{ref_struct.name}.{node.pred.struct_pred.name}")
            ref_args: list[VarTerm] = []
            for arg in node.args:
                if not isinstance(arg, ResolvedVarTerm):
                    raise ElaborateError(arg, f"Unexpected type {type(arg)}")
                ref_args.append(self.elaborate_var_term(arg))
            mapping_args: dict[VarTerm, VarTerm] = {def_arg: ref_arg for def_arg, ref_arg in zip(structpred.args, ref_args)}
            elaborated = Substitutor((mapping_field | mapping_args, {}, {})).substitute_formula(structpred.formula)
            self.add_node_to_token(elaborated, node)
            return elaborated
        else:
            pred = self.elaborate_pred_term(node.pred)
            args = [self.elaborate_term(arg) for arg in node.args]
            elaborated = AtomicFormula(pred, tuple(args))
            self.add_node_to_token(elaborated, node)
            return elaborated

    def elaborate_term(self, node: ResolvedTerm) -> Term:
        if isinstance(node, ResolvedVarTerm):
            return self.elaborate_var_term(node)
        elif isinstance(node, ResolvedPredTerm):
            return self.elaborate_pred_term(node)
        elif isinstance(node, ResolvedFunTerm):
            return self.elaborate_fun_term(node)
        else:
            raise ElaborateError(node, f"Unexpected type {type(node)}")

    def elaborate_var_term(self, node: ResolvedVarTerm) -> VarTerm:
        if isinstance(node, ResolvedVar):
            elaborated = Var(node.name)
        elif isinstance(node, ResolvedRefDefCon):
            elaborated = RefDefCon(node.name)
        elif isinstance(node, ResolvedCompound):
            fun = self.elaborate_fun_term(node.fun)
            args = [self.elaborate_term(arg) for arg in node.args]
            elaborated = Compound(fun, tuple(args))
        elif isinstance(node, ResolvedStructVar):
            raise ElaborateError(node, f"Unexpected type {type(node)}")
        elif isinstance(node, ResolvedStructMemberField):
            name = self.get_struct_access_name(node)
            elaborated = Var(name)
        else:
            raise ElaborateError(node, f"Unexpected type {type(node)}")
        self.add_node_to_token(elaborated, node)
        return elaborated

    def get_struct_access_name(self, node: ResolvedStructVar | ResolvedStructMemberField) -> str:
        if isinstance(node, ResolvedStructVar):
            return node.name
        elif isinstance(node, ResolvedStructMemberField):
            parent_name = self.get_struct_access_name(node.parent)
            return f"{parent_name}.{node.struct_field.name}"
        else:
            raise ElaborateError(node, f"Unexpected type {type(node)}")

    def elaborate_pred_term(self, node: ResolvedPredTerm) -> PredTerm:
        if isinstance(node, ResolvedRefEquality):
            elaborated = RefEquality(node.name)
        elif isinstance(node, ResolvedRefPrimPred):
            elaborated = RefPrimPred(node.name)
        elif isinstance(node, ResolvedRefDefPred):
            elaborated = RefDefPred(node.name)
        elif isinstance(node, ResolvedPredTemplate):
            elaborated = PredTemplate(node.name, node.arity)
        elif isinstance(node, ResolvedPredLambda):
            args = self.elaborate_vars(node.args)
            body = self.elaborate_formula(node.body)
            elaborated = PredLambda(tuple(args), body)
        elif isinstance(node, ResolvedStructMemberPred):
            if isinstance(node.parent, ResolvedStructVar):
                ref_struct = node.parent.ref_struct
            elif isinstance(node.parent, ResolvedStructMemberField):
                if node.parent.ref_struct is None:
                    raise ElaborateError(node.parent, "Parent is not a struct")
                ref_struct = node.parent.ref_struct
            else:
                raise ElaborateError(node.parent, f"Unexpected type {type(node.parent)}")
            fields, _ = self.collect_struct_members(node.parent)
            prefix = self.get_struct_access_name(node.parent)
            mapping_field: dict[VarTerm, VarTerm] = {}
            for field in fields:
                if not field.name.startswith(prefix + "."):
                    continue
                mapping_field[Var(field.name[len(prefix) + 1:])] = field
            structpred = self.decl.get_structpred(f"{ref_struct.name}.{node.struct_pred.name}")
            formula = Substitutor((mapping_field, {}, {})).substitute_formula(structpred.formula)
            elaborated = PredLambda(tuple(structpred.args), formula)
            self.add_node_to_token(elaborated, node)
            return elaborated
        else:
            raise ElaborateError(node, f"Unexpected node type {type(node)}")
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_fun_term(self, node: ResolvedFunTerm) -> FunTerm:
        if isinstance(node, ResolvedRefDefFun):
            elaborated = RefDefFun(node.name)
        elif isinstance(node, ResolvedRefDefFunTerm):
            elaborated = RefDefFunTerm(node.name)
        elif isinstance(node, ResolvedFunTemplate):
            elaborated = FunTemplate(node.name, node.arity)
        elif isinstance(node, ResolvedFunLambda):
            args = self.elaborate_vars(node.args)
            body = self.elaborate_var_term(node.body)
            elaborated = FunLambda(tuple(args), body)
        else:
            raise ElaborateError(node, f"Unexpected node type {type(node)}")
        self.add_node_to_token(elaborated, node)
        return elaborated

    def elaborate_vars_or_pred_tmpls_or_fun_tmpls(self, node: list[ResolvedVar | ResolvedPredTemplate | ResolvedFunTemplate]) -> tuple[list[Var], list[PredTemplate], list[FunTemplate], list[Var | PredTemplate | FunTemplate]]:
        vars: list[Var] = []
        pred_tmpls: list[PredTemplate] = []
        fun_tmpls: list[FunTemplate] = []
        items: list[Var | PredTemplate | FunTemplate] = []
        for item in node:
            if isinstance(item, ResolvedVar):
                var = self.elaborate_var(item)
                vars.append(var)
                items.append(var)
            elif isinstance(item, ResolvedPredTemplate):
                pred_tmpl = self.elaborate_pred_tmpl(item)
                pred_tmpls.append(pred_tmpl)
                items.append(pred_tmpl)
            elif isinstance(item, ResolvedFunTemplate):
                fun_tmpl = self.elaborate_fun_tmpl(item)
                fun_tmpls.append(fun_tmpl)
                items.append(fun_tmpl)
            else:
                raise ElaborateError(item, f"Unexpected type {type(item)}")
        return vars, pred_tmpls, fun_tmpls, items

    def elaborate_vars_or_none(self, node: list[ResolvedVar | None]) -> tuple[list[Var | None], list[Var]]:
        vars_or_none: list[Var | None] = []
        vars: list[Var] = []
        for item in node:
            if isinstance(item, ResolvedVar):
                var = self.elaborate_var(item)
                vars_or_none.append(var)
                vars.append(var)
            else:
                vars_or_none.append(None)
        return vars_or_none, vars

    def elaborate_vars(self, node: tuple[ResolvedVar, ...]) -> list[Var]:
        return [self.elaborate_var(item) for item in node]

    def elaborate_var(self, node: ResolvedVar) -> Var:
        var = Var(node.name)
        self.add_node_to_token(var, node)
        return var

    def elaborate_pred_tmpl(self, node: ResolvedPredTemplate) -> PredTemplate:
        pred_tmpl = PredTemplate(node.name, node.arity)
        self.add_node_to_token(pred_tmpl, node)
        return pred_tmpl

    def elaborate_fun_tmpl(self, node: ResolvedFunTemplate) -> FunTemplate:
        fun_tmpl = FunTemplate(node.name, node.arity)
        self.add_node_to_token(fun_tmpl, node)
        return fun_tmpl

    def collect_struct_members(self, var: ResolvedStructVar | ResolvedStructMemberField) -> tuple[list[Var], dict[RefStructCondition, Formula]]:
        if isinstance(var, ResolvedStructVar):
            struct = self.decl.get_struct(var.ref_struct.name)
            fields: list[Var] = []
            conditions = dict(struct.conditions)
            for field in struct.fields:
                if isinstance(field, Var):
                    fields.append(field)
                else:
                    child_fields, child_conditions = self.collect_struct_members(ResolvedStructVar(field.name, ResolvedRefStruct(field.ref_struct.name)))
                    fields.extend(child_fields)
                    conditions.update(child_conditions)
            full_fields = [Var(f"{var.name}.{field.name}") for field in fields]
            full_conditions: dict[RefStructCondition, Formula] = {}
            for ref, condition in conditions.items():
                full_ref = RefStructCondition(f"{var.name}.{ref.name}")
                mapping: dict[VarTerm, VarTerm] = {field: Var(f"{var.name}.{field.name}") for field in fields}
                full_conditions[full_ref] = Substitutor((mapping, {}, {})).substitute_formula(condition)
            return full_fields, full_conditions
        else:
            return self.collect_struct_members(var.parent)
