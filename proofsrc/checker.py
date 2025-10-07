from ast_types import Context, Theorem, Any, Assume, Check, Divide, Case, Some, Deny, Contradict, Explode, Apply, Lift, Symbol, And, Or, Implies, Forall, Exists, Not, Bottom, Iff, Axiom, Invoke, Expand, ExistsUniq, Characterize, Atom, Definition, DefCon, Identify, Pad, Split, Connect, pretty, pretty_expr
from logic_utils import normalize_neg, expr_in_context, logic_equiv, collect_quantifier_vars, substitute, collect_vars, flatten_op

import logging
logger = logging.getLogger("proof")

def goal_in_context(goal, context, indent):
    sp = '  ' * indent
    logger.debug(f"{sp}[derivable] goal: {pretty_expr(goal)}")
    logger.debug(f"{sp}[derivable] context.formulas: {",".join([pretty_expr(c) for c in context.formulas])}")
    if isinstance(goal, Bottom):
        return context.bot_derived
    elif isinstance(goal, Axiom):
        return goal.name in context.axioms
    elif isinstance(goal, Theorem):
        return goal.name in context.theorems
    else:
        return expr_in_context(goal, context)

def add_conclusion(context, conclusion):
    if isinstance(conclusion, Bottom):
        context.bot_derived = True
    else:
        context.formulas.append(conclusion)

def check_ast(ast):
    context = Context.init()
    return all(check_proof(node, context) for node in ast)

# === 証明チェッカー ===
def check_proof(node, context: Context, indent=0):
    sp = "  " * indent

    if isinstance(node, Atom):
        logger.debug(f"{sp}[Atom] type: {node.type}, name: {node.name}, arity: {node.arity}")
        context.atoms[node.name] = node
        return True

    if isinstance(node, Axiom):
        logger.debug(f"{sp}[Axiom] name: {node.name}, conclusion: {pretty_expr(node.conclusion)}")
        context.axioms[node.name] = node
        return True

    # --- Theorem ---
    if isinstance(node, Theorem):
        logger.debug(f"{sp}[Theorem] {node.name}: {pretty_expr(node.conclusion)}")
        local_ctx = context.copy([], False)
        for stmt in node.proof:
            if not check_proof(stmt, local_ctx, indent+1):
                logger.error(f"{sp}❌ [Theorem] {node.name} not proved: {pretty_expr(node.conclusion)}")
                return False
        if goal_in_context(node.conclusion, local_ctx, indent+1):
            logger.debug(f"{sp}[Theorem] {node.name} proved: {pretty_expr(node.conclusion)}")
            context.theorems[node.name] = node
            return True
        else:
            logger.error(f"{sp}❌ [Theorem] {node.name} not proved: {pretty_expr(node.conclusion)}")
            return False

    # --- Check ---
    if isinstance(node, Check):
        logger.debug(f"{sp}[Check] Checking {pretty_expr(node.conclusion)}")
        if goal_in_context(node.conclusion, context, indent+1):
            logger.debug(f"{sp}[Check] goal {pretty_expr(node.conclusion)} derived")
            return True
        else:
            logger.error(f"{sp}❌ [Check] goal {pretty_expr(node.conclusion)} not derivable")
            return False

    # --- Assume ---
    if isinstance(node, Assume):
        logger.debug(f"{sp}[Assume] premise={pretty_expr(node.premise)}, conclusion={pretty_expr(node.conclusion)}")
        local_ctx = context.copy(list(context.formulas + [node.premise]), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if goal_in_context(node.conclusion, local_ctx, indent+1):
            logger.debug(f"{sp}[Assume] Derived conclusion {pretty_expr(node.conclusion)}")
        else:
            logger.error(f"{sp}❌ [Assume] Cannot derive {pretty_expr(node.conclusion)}")
            return False
        implication = Implies(node.premise, node.conclusion)
        add_conclusion(context, implication)
        logger.debug(f"{sp}[Assume] Added implication {pretty_expr(implication)}")
        return True

    # --- Any ---
    if isinstance(node, Any):
        logger.debug(f"{sp}[Any] Taking {node.vars}")
        local_ctx = context.copy(list(context.formulas), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if goal_in_context(node.conclusion, local_ctx, indent+1):
            logger.debug(f"{sp}[Any] Derived conclusion {pretty_expr(node.conclusion)}")
        else:
            logger.error(f"{sp}❌ [Any] Cannot derive {pretty_expr(node.conclusion)}")
            return False
        goal = node.conclusion
        for v in reversed(node.vars):
            goal = Forall(v, goal)
        add_conclusion(context, goal)
        logger.debug(f"{sp}[Any] Generalized to {pretty_expr(goal)}")
        return True

    if isinstance(node, Divide):
        if not goal_in_context(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Divide] Not fact: {pretty_expr(node.fact)}")
            return False
        connected_premise = Or(node.cases[0].premise, node.cases[1].premise)
        i = 2
        while i < len(node.cases):
            connected_premise = Or(connected_premise, node.cases[i].premise)
            i += 1
        if logic_equiv(connected_premise, node.fact, context):
            logger.debug(f"{sp}[Divide] mathched: fact={pretty_expr(node.fact)}, connected_premise={pretty_expr(connected_premise)}")
        else:
            logger.error(f"{sp}❌ [Divide] not matched: fact={pretty_expr(node.fact)}, conected_premise={pretty_expr(connected_premise)}")
            return False
        logger.debug(f"{sp}[Divide] fact={pretty_expr(node.fact)}, goal={pretty_expr(node.conclusion)}")
        local_ctx = context.copy(list(context.formulas), False)
        for stmt in node.cases:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Divide] derived in all cases: {pretty_expr(node.conclusion)}")
        return True

    if isinstance(node, Case):
        logger.debug(f"{sp}[Case] premise={pretty_expr(node.premise)}")
        local_ctx = context.copy(list(context.formulas + [node.premise]), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if goal_in_context(node.conclusion, local_ctx, indent+1):
            logger.debug(f"{sp}[Case] derived conclusion {pretty_expr(node.conclusion)}")
            return True
        else:
            logger.error(f"{sp}❌ [Case] Cannot derive {pretty_expr(node.conclusion)}")
            return False

    if isinstance(node, Some):
        if not goal_in_context(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Some] not derivable: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Some] derivable: {pretty_expr(node.fact)}")
        if isinstance(node.fact, Axiom):
            fact = node.fact.conclusion
        elif isinstance(node.fact, Theorem):
            fact = node.fact.conclusion
        else:
            fact = node.fact
        if not isinstance(fact, Exists):
            logger.error(f"{sp}❌ Not Exists object: {pretty_expr(node.fact)}")
            return False
        vars, body = collect_quantifier_vars(fact, Exists)
        if not set(node.env.keys()).issubset(set(vars)):
            logger.error(f"{sp}❌ invalid vars: node.env.keys()={node.env.keys()}, vars={vars}")
            return False
        premise = substitute(body, node.env)
        logger.debug(f"{sp}[Some] Taking {node.env.values()}, premise={pretty_expr(premise)}")
        local_ctx = context.copy(list(context.formulas + [premise]), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if not goal_in_context(node.conclusion, local_ctx, indent+1):
            logger.error(f"{sp}❌ [Some] Cannot derive {pretty_expr(node.conclusion)}")
            return False
        logger.debug(f"{sp}[Some] derived conclusion {pretty_expr(node.conclusion)}")
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Some] Added {pretty_expr(node.conclusion)}")
        return True
    
    if isinstance(node, Deny):
        logger.debug(f"{sp}[Deny] premise={pretty_expr(node.premise)}")
        local_ctx = context.copy(list(context.formulas + [node.premise]), False)
        for stmt in node.body:
            if not check_proof(stmt, local_ctx, indent+1):
                return False
        if local_ctx.bot_derived:
            add_conclusion(context, Not(node.premise))
            logger.debug(f"{sp}[Deny] contradiction is derived; added {pretty_expr(Not(node.premise))}")
            return True
        else:
            logger.error(f"{sp}❌ [Deny] conradiction has not been deried")
            return False
    
    if isinstance(node, Contradict):
        if not goal_in_context(node.contradiction, context, indent+1):
            logger.error(f"{sp}❌ [Contradict] Cannot derive {pretty_expr(node.contradiction)}")
            return False
        if not goal_in_context(Not(node.contradiction), context, indent+1):
            logger.error(f"{sp}❌ [Contradict] Cannot derive {pretty_expr(Not(node.contradiction))}")
            return False
        logger.debug(f"{sp}[Contradict] Derived contradiction: {pretty_expr(node.contradiction)}, {pretty_expr(Not(node.contradiction))}")
        context.bot_derived = True
        return True
    
    if isinstance(node, Explode):
        if context.bot_derived:
            add_conclusion(context, node.conclusion)
            logger.debug(f"{sp}[Explode] added {pretty_expr(node.conclusion)}")
            return True
        else:
            logger.error(f"{sp}❌ [Explode] contradiction has not been derived")
            return False
        
    if isinstance(node, Apply):
        if not goal_in_context(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Apply] Cannot derive fact: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Apply] Drivable fact: {pretty_expr(node.fact)}")
        if isinstance(node.fact, Axiom):
            fact = node.fact.conclusion
        elif isinstance(node.fact, Theorem):
            fact = node.fact.conclusion
        elif isinstance(node.fact, Symbol):
            if node.fact.name not in context.definitions:
                logger.error(f"{sp}❌ [Apply] Undefined name: {node.fact.name}")
                return False
            vars, body = collect_quantifier_vars(context.definitions[node.fact.name].formula, Forall)
            if len(vars) != len(node.fact.args):
                logger.error(f"{sp}❌ [Apply] not matched: len(vars)={len(vars)}, len(node.fact.args)={len(node.fact.args)}")
                return False
            fact = substitute(body, dict(zip(vars, node.fact.args))).right
            logger.debug(f"{sp}[Apply] replace {pretty_expr(node.fact)} to {pretty_expr(fact)}")
        else:
            fact = node.fact
        if node.env is not None:
            vars, body = collect_quantifier_vars(fact, Forall)
            if set(vars) != set(node.env.keys()):
                logger.error(f"{sp}❌ [Apply] matched: vars={vars}, env={node.env}")
                return False
            logger.debug(f"{sp}[Apply] Instantiable: vars={vars}, env={node.env}")
            instantiation = substitute(body, node.env)
            logger.debug(f"{sp}[Apply] \\forall-elimination is done: instantiation={pretty_expr(instantiation)}")
            if node.premise is None:
                if not logic_equiv(node.conclusion, instantiation, context):
                    logger.error(f"{sp}❌ [Apply] Not matched: node.conclusion={pretty_expr(node.conclusion)}, instantiation={pretty_expr(instantiation)}")
                    return False
                logger.debug(f"{sp}[Apply] Matched: node.conclusion={pretty_expr(node.conclusion)}, instantiation={pretty_expr(instantiation)}")
                logger.debug(f"{sp}[Apply] Added node.conclusion={pretty_expr(node.conclusion)}")
                add_conclusion(context, node.conclusion)
                return True
            else:
                implication = instantiation
        else:
            implication = fact
        if not isinstance(implication, Implies):
            logger.error(f"{sp}❌ [Apply] Not Implies object: {pretty_expr(implication)}")
            return False
        logger.debug(f"{sp}[Apply] Implies object: {pretty_expr(implication)}")
        if not goal_in_context(node.premise, context, indent+1):
            logger.error(f"{sp}❌ [Apply] Cannot derive premise: {pretty_expr(node.premise)}")
            return False
        logger.debug(f"{sp}[Apply] Derivable premise: {pretty_expr(node.premise)}")
        if not logic_equiv(implication.left, node.premise, context):
            logger.error(f"{sp}❌ [Apply] Not matched: implication.left={pretty_expr(implication.left)}, node.premise={pretty_expr(node.premise)}")
            return False
        logger.debug(f"{sp}[Apply] Matched: implication.left={pretty_expr(implication.left)}, node.premise={pretty_expr(node.premise)}")
        logger.debug(f"{sp}[Apply] \\to-elimination is done: {pretty_expr(implication.right)}")
        if not logic_equiv(node.conclusion, implication.right, context):
            logger.error(f"{sp}❌ [Apply] Not matched: node.conclusion={pretty_expr(node.conclusion)}, implication.right={pretty_expr(implication.right)}")
            return False
        logger.debug(f"{sp}[Apply] Matched: node.conclusion={pretty_expr(node.conclusion)}, implication.right={pretty_expr(implication.right)}")
        logger.debug(f"{sp}[Apply] Added node.conclusion={pretty_expr(node.conclusion)}")
        add_conclusion(context, node.conclusion)
        return True
    
    if isinstance(node, Lift):
        if not goal_in_context(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Lift] Not fact: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Lift] fact: {pretty_expr(node.fact)}")
        free_vars, _ = collect_vars(node.fact)
        if not set(node.env.values()).issubset(free_vars):
            logger.error(f"{sp}❌ [Lift] Cannot be lifted: vars={sorted(free_vars)}, env={node.env}")
            return False
        logger.debug(f"{sp}[Lift] Can be lifted: vars={sorted(free_vars)}, env={node.env}")
        lifted = substitute(node.fact, {v: k for k, v in node.env.items()})
        for k in reversed(list(node.env.keys())):
            lifted = Exists(k, lifted)
        logger.debug(f"{sp}[Lift] lifted formula: {pretty_expr(lifted)}")
        if not logic_equiv(node.conclusion, lifted, context):
            logger.error(f"{sp}❌ [Lift] Not matched: node.conclusion={pretty_expr(node.conclusion)}, lifted={pretty_expr(lifted)}")
            return False
        logger.debug(f"{sp}[Lift] Matched: node.conclusion={pretty_expr(node.conclusion)}, lifted={pretty_expr(lifted)}")        
        add_conclusion(context, node.conclusion)
        return True

    if isinstance(node, Invoke):
        if not goal_in_context(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Invoke] Not fact: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Invoke] fact: {pretty_expr(node.fact)}")
        if not isinstance(node.fact, Implies):
            logger.error(f"{sp}❌ [Invoke] Not Implies object: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Invoke] Implies object: {pretty_expr(node.fact)}")
        if not goal_in_context(node.fact.left, context, indent+1):
            logger.error(f"{sp}❌ [Invoke] Left of Implies object not derived: {pretty_expr(node.fact.left)}")
            return False
        logger.debug(f"{sp}[Invoke] Left of Implies object derived: {pretty_expr(node.fact.left)}")
        if not logic_equiv(node.conclusion, node.fact.right, context):
            logger.error(f"{sp}❌ [Invoke] Not matched: node.conclusion={pretty_expr(node.conclusion)}, node.fact.right={pretty_expr(node.fact.right)}")
            return False
        logger.debug(f"{sp}[Invoke] Matched: node.conclusion={pretty_expr(node.conclusion)}, node.fact.right={pretty_expr(node.fact.right)}")
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Invoke] conclusion added: {pretty_expr(node.conclusion)}")
        return True

    if isinstance(node, Expand):
        if not goal_in_context(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Expand] Not fact: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Expand] fact: {pretty_expr(node.fact)}")
        if not isinstance(node.fact, Symbol):
            logger.error(f"{sp}❌ [Expand] Not Symbol object: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Expand] Symbol object: {pretty_expr(node.fact)}")
        if node.fact.name not in context.definitions:
            logger.error(f"{sp}❌ [Expand] Not defined: {node.fact.name}")
            return False
        logger.debug(f"{sp}[Expand] Defined: {node.fact.name}")
        vars, body = collect_quantifier_vars(context.definitions[node.fact.name].formula, Forall)
        if len(vars) != len(node.fact.args):
            logger.error(f"{sp}❌ [Expand] Length not matched: vars={vars}, node.fact.args={node.fact.args}")
            return False
        logger.debug(f"{sp}[Expand] Length matched: vars={vars}, node.fact.args={node.fact.args}")
        expanded = substitute(body, dict(zip(vars, node.fact.args))).right
        logger.debug(f"{sp}[Expand] Expanded: {pretty_expr(expanded)}")
        if not logic_equiv(node.conclusion, expanded, context):
            logger.error(f"{sp}❌ [Expand] Not matched: node.conclusion={pretty_expr(node.conclusion)}, expanded={pretty_expr(expanded)}")
            return False
        logger.debug(f"{sp}[Expand] Matched: node.conclusion={pretty_expr(node.conclusion)}, expanded={pretty_expr(expanded)}")
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Expand] Added: {pretty_expr(node.conclusion)}")
        return True

    if isinstance(node, Characterize):
        if not goal_in_context(node.fact.left, context, indent+1):
            logger.error(f"{sp}❌ [Characterize] Not derived: {pretty_expr(node.fact.left)}")
            return False
        logger.debug(f"{sp}[Characterize] Derived: {pretty_expr(node.fact.left)}")
        free_vars, _ = collect_vars(node.fact.left)
        if not set(node.env.values()).issubset(free_vars):
            logger.error(f"{sp}❌ [Characterize] Invalid env: vars={sorted(free_vars)}, env={node.env}")
            return False
        logger.debug(f"{sp}[Characterize] Valid env: vars={sorted(free_vars)}, env={node.env}")
        if not logic_equiv(substitute(node.fact.left, {list(node.env.values())[0]: node.fact.right.var}), node.fact.right.body.left, context):
            logger.error(f"{sp}❌ [Characterize] Not matched: node.fact.left={pretty_expr(node.fact.left)}, node.fact.right.body.left={pretty_expr(node.fact.right.body.left)}")
            return False
        logger.debug(f"{sp}[Characterize] Matched: node.fact.left={pretty_expr(node.fact.left)}, node.fact.right.body.left={pretty_expr(node.fact.right.body.left)}")
        if not (node.fact.right.body.right.name == "equal" and set(node.fact.right.body.right.args) == set([list(node.env.values())[0], node.fact.right.var])):
            logger.error(f"{sp}❌ [Characterized] Unexpected: node.fact.right.body.right={pretty_expr(node.fact.right.body.right)}")
            return False
        logger.debug(f"{sp}[Characterized] Expected: node.fact.right.body.right={pretty_expr(node.fact.right.body.right)}")
        characterized = ExistsUniq(list(node.env.keys())[0], substitute(node.fact.left, {v: k for k, v in node.env.items()}))
        logger.debug(f"{sp}[Characterize] derived formula: {pretty_expr(characterized)}")
        if not logic_equiv(node.conclusion, characterized, context):
            logger.error(f"{sp}❌ [Characterize] Not matched: node.conclusion={pretty_expr(node.conclusion)}, derived={pretty_expr(characterized)}")
            return False
        logger.debug(f"{sp}[Characterize] Matched: node.conclusion={pretty_expr(node.conclusion)}, derived={pretty_expr(characterized)}")
        add_conclusion(context, node.conclusion)
        return True

    if isinstance(node, Identify):
        if not goal_in_context(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Identify] Not derivable: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Identify] Derivable: {pretty_expr(node.fact)}")
        logger.debug(f"{sp}[Identify] Add conclusion: {pretty_expr(node.conclusion)}")
        add_conclusion(context, node.conclusion)
        return True

    if isinstance(node, Pad):
        if not goal_in_context(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Pad] Not derivable: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Pad] Derivable: {pretty_expr(node.fact)}")
        if not isinstance(node.conclusion, Or):
            logger.error(f"{sp}❌ [Pad] Not Or object: {pretty_expr(node.conclusion)}")
            return False
        logger.debug(f"{sp}[Pad] Or object: {pretty_expr(node.conclusion)}")
        fact_parts = flatten_op(node.fact, Or)
        conclusion_parts = flatten_op(node.conclusion, Or)
        if not all(any(logic_equiv(c, f, context) for c in conclusion_parts) for f in fact_parts):
            logger.error(f"{sp}❌ [Pad] neither left or right not derivable: {pretty_expr(node.conclusion)}")
            return False
        add_conclusion(context, node.conclusion)
        logger.debug(f"{sp}[Pad] Derivable, added {pretty_expr(node.conclusion)}")
        return True

    if isinstance(node, Split):
        if not goal_in_context(node.fact, context, indent+1):
            logger.error(f"{sp}❌ [Split] Not derivable: {pretty_expr(node.fact)}")
            return False
        logger.debug(f"{sp}[Split] Derivable: {pretty_expr(node.fact)}")
        if isinstance(node.fact, And):
            logger.debug(f"{sp}[Split] And object: {pretty_expr(node.fact)}")
            fact_parts = flatten_op(node.fact, And)
            for f in fact_parts:
                add_conclusion(context, f)
                logger.debug(f"{sp}[Split] added {pretty_expr(f)}")
            return True
        elif isinstance(node.fact, Iff):
            logger.debug(f"{sp}[Split] Iff object: {pretty_expr(node.fact)}")
            implication = Implies(node.fact.left, node.fact.right)
            add_conclusion(context, implication)
            logger.debug(f"{sp}[Split] added {pretty_expr(implication)}")
            implication = Implies(node.fact.right, node.fact.left)
            add_conclusion(context, implication)
            logger.debug(f"{sp}[Split] added {pretty_expr(implication)}")
            return True
        else:
            logger.error(f"{sp}❌ [Split] Not And or Iff object: {pretty_expr(node.fact)}")
            return False

    if isinstance(node, Connect):
        if isinstance(node.conclusion, And):
            logger.debug(f"{sp}[Connect] And object: {pretty_expr(node.conclusion)}")
            conclusion_parts = flatten_op(node.conclusion, And)
            for c in conclusion_parts:
                if not goal_in_context(c, context, indent+1):
                    logger.error(f"{sp}❌ [Connect] Not derivable: {pretty_expr(c)}")
                    return False
            add_conclusion(context, node.conclusion)
            logger.debug(f"{sp}[Connect] Derivable, added {pretty_expr(node.conclusion)}")
            return True
        elif isinstance(node.conclusion, Iff):
            logger.debug(f"{sp}[Connect] Iff object: {pretty_expr(node.conclusion)}")
            implication = Implies(node.conclusion.left, node.conclusion.right)
            if not goal_in_context(implication, context, indent+1):
                logger.error(f"{sp}❌ [Connect] Not derivable: {pretty_expr(implication)}")
                return False
            implication = Implies(node.conclusion.right, node.conclusion.left)
            if not goal_in_context(implication, context, indent+1):
                logger.error(f"{sp}❌ [Connect] Not derivable: {pretty_expr(implication)}")
                return False
            add_conclusion(context, node.conclusion)
            logger.debug(f"{sp}[Connect] derivable, added {pretty_expr(node.conclusion)}")
            return True
        else:
            logger.error(f"{sp}❌ [Connect] Not And or Iff object: {pretty_expr(node.conclusion)}")
            return False

    if isinstance(node, Definition):
        logger.debug(f"{sp}[Definition] type: {node.type}, name: {node.name}, arity: {node.arity}, formula: {pretty_expr(node.formula)}")
        context.definitions[node.name] = node
        return True

    if isinstance(node, DefCon):
        logger.debug(f"{sp}[DefCon] name: {node.name}, theorem: {node.theorem}, formula: {node.formula}")
        context.defcons[node.name] = node
        return True

    logger.error(f"{sp}❌ Unsupported node {node}")
    return False

if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    f = open(path)
    src = f.read()
    f.close()

    import os
    import logging

    logger = logging.getLogger("proof")
    logger.setLevel(logging.DEBUG)

    # 標準出力用ハンドラ
    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.DEBUG)

    # ファイル出力用ハンドラ
    file_handler = logging.FileHandler(os.path.join("logs", os.path.basename(path).replace(".proof", ".log")), mode='w', encoding='utf-8')
    file_handler.setLevel(logging.DEBUG)

    # 共通フォーマット
    formatter = logging.Formatter("[%(filename)s] %(message)s")
    console_handler.setFormatter(formatter)
    file_handler.setFormatter(formatter)

    # ハンドラ登録
    logger.addHandler(console_handler)
    logger.addHandler(file_handler)

    from lexer import lex
    tokens = lex(src)
    from parser import Parser
    parser = Parser(tokens)
    ast = parser.parse_file()
    if check_ast(ast):
        print("All theorems proved")
    else:
        print("❌ Not all theorems proved")
