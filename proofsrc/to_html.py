from datetime import datetime
from html import escape
from ast_types import PrimPred, Axiom, Theorem, DefPred, DefCon, DefFun, DefFunTerm, Equality, Any, Assume, Connect, Expand, Split, Apply, Invoke, Deny, Some, Contradict, Lift, Pad, Divide, Case, Explode, Characterize, Substitute, Show, Context, DefConExist, DefConUniq, DefFunExist, DefFunUniq, EqualityReflection, EqualityReplacement, Symbol, Pred, Compound, Fun, Control, pretty_expr
from svg import output_svg

HTML_TEMPLATE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<title>{title}</title>
{extra_head}
</head>
<body>
<header>
  Rendered at {now_str}
</header>
<div class="proof">
  <div class="controls">
    <button id="expandAll">Expand all</button>
    <button id="collapseAll">Collapse all</button>
  </div>
{body}
</div>
<div class="info-panel" id="infoPanel">
  <h3>Information</h3>
  <div id="infoContent">Please click a line to show its information.</div>
</div>
{footer}
<script src="script.js"></script>
</body>
</html>
"""

MATHJAX_HEAD = """
<script id="MathJax-script" async
  src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
<link rel="stylesheet" href="style_mathjax.css">
"""

MATHJAX_FOOTER = """
<footer style="font-size:0.8em; color:#666; margin-top:2rem;">
  MathJax is used for rendering LaTeX math. Licensed under 
  <a href="https://www.apache.org/licenses/LICENSE-2.0" target="_blank">Apache License 2.0</a>.
</footer>
"""

SVG_HEAD = """
<link rel="stylesheet" href="style_svg.css">
"""

def render_keyword(keyword: str) -> str:
    return f"<span class='keyword'>{keyword}</span>"

def render_identifier(name: str) -> str:
    return f"<span class='identifier'>{escape(name)}</span>"

def render_expr_mathjax(node, context: Context) -> str:
    if isinstance(node, (Axiom, Theorem, DefConExist, DefConUniq, DefFunExist, DefFunUniq)):
        return render_identifier(node.name)
    else:
        return escape(f"\\({pretty_expr(node, context)}\\)")

def render_expr_list_mathjax(expr_list: list, context: Context) -> str:
    return escape(f"\\({",".join(pretty_expr(expr, context) for expr in expr_list)}\\)")

def render_expr_dict_mathjax(expr_dict: dict, context: Context) -> str:
    parts = [f"{pretty_expr(k, context)}:{pretty_expr(v, context)}" for k, v in expr_dict.items()]
    return escape(f"\\({",".join(parts)}\\)")

def render_tex_mathjax(tex: list[str]):
    return escape(f"\\({"".join(tex)}\\)")

def img_tag(svg_path: str, latex_code: str) -> str:
    return f"<img src='{escape(svg_path)}' alt='{escape(latex_code)}'>"

def render_expr_svg(node, context: Context) -> str:
    if isinstance(node, (Axiom, Theorem, DefConExist, DefConUniq, DefFunExist, DefFunUniq)):
        return render_identifier(node.name)
    else:
        latex_code = pretty_expr(node, context)
        svg_path = output_svg(latex_code)
        return img_tag(svg_path, latex_code)

def render_expr_list_svg(expr_list: list, context: Context) -> str:
    return ",".join((render_expr_svg(expr, context) for expr in expr_list))

def render_expr_dict_svg(expr_dict: dict, context: Context) -> str:
    parts = [f"{render_expr_svg(k, context)}:{render_expr_svg(v, context)}" for k, v in expr_dict.items()]
    return f"{",".join(parts)}"

def render_tex_svg(tex: list[str]):
    latex_code = "".join(tex)
    svg_path = output_svg(latex_code)
    return img_tag(svg_path, latex_code)

def render_node(node, context: Context, mode: bool) -> str:
    if mode == "mathjax":
        render_expr = render_expr_mathjax
        render_expr_list = render_expr_list_mathjax
        render_expr_dict = render_expr_dict_mathjax
        render_tex = render_tex_mathjax
    elif mode == "svg":
        render_expr = render_expr_svg
        render_expr_list = render_expr_list_svg
        render_expr_dict = render_expr_dict_svg
        render_tex = render_tex_svg
    else:
        raise Exception(f"Unexpected mode: {mode}")

    header_parts = []
    body_html = ""
    bullet = "<button class='bullet'>•</button>"
    toggle = "<button class='toggle'>▼</button>"

    if isinstance(node, PrimPred):
        header_parts = [bullet,
                        render_keyword("primitive predicate"),
                        render_identifier(node.name),
                        render_tex(node.tex),
                        render_keyword("arity"),
                        f"{str(node.arity)}"]
    elif isinstance(node, Axiom):
        header_parts = [bullet,
                        render_keyword("axiom"),
                        render_identifier(node.name),
                        render_expr(node.conclusion, context)]
    elif isinstance(node, Theorem):
        header_parts = [toggle,
                        render_keyword("theorem"),
                        render_identifier(node.name),
                        render_expr(node.conclusion, context)]
        body_html = "".join(render_node(s, context, mode) for s in node.proof)
    elif isinstance(node, DefPred):
        header_parts = [bullet,
                        render_keyword("definition predicate"),
                        render_keyword("autoexpand") if node.autoexpand else "",
                        render_identifier(node.name),
                        render_expr(Symbol(Pred(node.name), node.args), context),
                        render_keyword("as"),
                        render_expr(node.formula, context)]
    elif isinstance(node, DefCon):
        header_parts = [toggle,
                        render_keyword("definition constant"),
                        render_identifier(node.name),
                        render_tex(node.tex),
                        render_keyword("by"),
                        render_identifier(node.theorem)]
        body_html = render_node(node.existence, context, mode) + render_node(node.uniqueness, context, mode)
    elif isinstance(node, DefConExist):
        header_parts = [bullet,
                        render_keyword("existence"),
                        render_identifier(node.name),
                        render_expr(node.formula, context)]
    elif isinstance(node, DefConUniq):
        header_parts = [bullet,
                        render_keyword("uniqueness"),
                        render_identifier(node.name),
                        render_expr(node.formula, context)]
    elif isinstance(node, DefFun):
        header_parts = [toggle,
                        render_keyword("definition function"),
                        render_identifier(node.name),
                        render_tex(node.tex),
                        render_keyword("by"),
                        render_identifier(node.theorem)]
        body_html = render_node(node.existence, context, mode) + render_node(node.uniqueness, context, mode)
    elif isinstance(node, DefFunExist):
        header_parts = [bullet,
                        render_keyword("existence"),
                        render_identifier(node.name),
                        render_expr(node.formula, context)]
    elif isinstance(node, DefFunUniq):
        header_parts = [bullet,
                        render_keyword("uniqueness"),
                        render_identifier(node.name),
                        render_expr(node.formula, context)]
    elif isinstance(node, DefFunTerm):
        header_parts = [bullet,
                        render_keyword("definition function"),
                        render_identifier(node.name),
                        render_expr(Compound(Fun(node.name), node.args), context),
                        render_keyword("as"),
                        render_expr(node.term, context)]
    elif isinstance(node, Equality):
        header_parts = [toggle,
                        render_keyword("equality"),
                        render_identifier(node.equal.name)]
        body_html = render_node(node.reflection, context, mode) + render_node(node.replacement, context, mode)
    elif isinstance(node, EqualityReflection):
        header_parts = [bullet,
                        render_keyword("reflection"),
                        render_identifier(node.evidence.name)]
    elif isinstance(node, EqualityReplacement):
        header_parts = [bullet,
                        render_keyword("replacement"),
                        ",".join([render_identifier(k) + ":" + render_identifier(v.name) for k, v in node.evidence.items()])]
    elif isinstance(node, Any):
        header_parts = [toggle,
                        render_keyword("any"),
                        render_expr_list(node.vars, context)]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    elif isinstance(node, Assume):
        header_parts = [toggle,
                        render_keyword("assume"),
                        render_expr(node.premise, context)]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    elif isinstance(node, Connect):
        header_parts = [bullet,
                        render_keyword("connect"),
                        render_expr(node.conclusion, context)]
    elif isinstance(node, Expand):
        header_parts = [bullet,
                        render_keyword("expand"),
                        render_expr(node.fact, context),
                        render_keyword("conclude"),
                        render_expr(node.conclusion, context)]
    elif isinstance(node, Split):
        header_parts = [bullet,
                        render_keyword("split"),
                        render_expr(node.fact, context)]
    elif isinstance(node, Apply):
        fact = render_expr(node.fact, context)
        header_parts = [bullet,
                        render_keyword("apply"),
                        fact,
                        render_keyword("for"),
                        render_expr_dict(node.env, context)]
        if node.conclusion is not None:
            header_parts.append(f"<span class='keyword'>conclude</span> {render_expr(node.conclusion, context)}")
    elif isinstance(node, Invoke):
        header_parts = [bullet,
                        render_keyword("invoke"),
                        render_expr(node.fact, context)]
        if node.conclusion is not None:
            header_parts.append(f"<span class='keyword'>conclude</span> {render_expr(node.conclusion, context)}")
    elif isinstance(node, Deny):
        header_parts = [toggle,
                        render_keyword("deny"),
                        render_expr(node.premise, context)]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    elif isinstance(node, Some):
        header_parts = [toggle,
                        render_keyword("some"),
                        render_expr_dict(node.env, context),
                        render_keyword("such"),
                        render_expr(node.fact, context)]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    elif isinstance(node, Contradict):
        header_parts = [bullet,
                        render_keyword("contradict"),
                        render_expr(node.contradiction, context)]
    elif isinstance(node, Lift):
        header_parts = [bullet,
                        render_keyword("lift")]
        if node.fact is not None:
            header_parts.append(render_expr(node.fact, context))
        header_parts.extend([render_keyword("for"),
                             render_expr_dict(node.env, context),
                             render_keyword("conclude"),
                             render_expr(node.conclusion, context)])
    elif isinstance(node, Pad):
        header_parts = [bullet,
                        render_keyword("pad"),
                        render_expr(node.fact, context),
                        render_keyword("conclude"),
                        render_expr(node.conclusion, context)]
    elif isinstance(node, Divide):
        header_parts = [toggle,
                        render_keyword("divide"),
                        render_expr(node.fact, context)]
        body_html = "".join(render_node(s, context, mode) for s in node.cases)
    elif isinstance(node, Case):
        header_parts = [toggle,
                        render_keyword("case"),
                        render_expr(node.premise, context)]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    elif isinstance(node, Explode):
        header_parts = [bullet,
                        render_keyword("explode"),
                        render_expr(node.conclusion, context)]
    elif isinstance(node, Characterize):
        header_parts = [bullet,
                        render_keyword("characterize")]
        if node.fact is not None:
            header_parts.append(render_expr(node.fact, context))
        header_parts.extend([render_keyword("for"),
                             render_expr_dict(node.env, context),
                             render_keyword("conclude"),
                             render_expr(node.conclusion, context)])
    elif isinstance(node, Substitute):
        header_parts = [bullet,
                        render_keyword("substitute"),
                        render_expr(node.fact, context),
                        render_keyword("for"),
                        render_expr_dict(node.env, context),
                        render_keyword("conclude"),
                        render_expr(node.conclusion, context)]
    elif isinstance(node, Show):
        header_parts = [toggle,
                        render_keyword("show"),
                        render_expr(node.conclusion, context)]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    else:
        raise Exception(f"Unexpected node: {type(node)}")

    header_html = f"<div class='block-header'>" + " ".join(header_parts) + "</div>"
    context_vars = f"context_vars: {render_expr_list(node.proofinfo.context_vars, context)}" if isinstance(node, Control) else ""
    context_vars_html = f"<div class='context-vars' hidden>{context_vars}</div>"
    context_formulas = f"context_formulas: {render_expr_list(node.proofinfo.context_formulas, context)}" if isinstance(node, Control) else ""
    context_formulas_html = f"<div class='context-formulas' hidden>{context_formulas}</div>"
    premises = f"premises: {render_expr_list(node.proofinfo.premises, context)}" if isinstance(node, Control) else ""
    premises_html = f"<div class='premises' hidden>{premises}</div>"
    conclusions = f"conclusions: {render_expr_list(node.proofinfo.conclusions, context)}" if isinstance(node, Control) else ""
    conclusions_html = f"<div class='conclusions' hidden>{conclusions}</div>"
    content_html = f"<div class='block-content'>{body_html}</div>"
    local_vars = f"local_vars: {render_expr_list(node.proofinfo.local_vars, context)}" if isinstance(node, (Any, Assume, Divide, Case, Some, Deny, Show)) else ""
    local_vars_html = f"<div class='local_vars' hidden>{local_vars}</div>"
    local_premise = f"local_premise: {render_expr_list(node.proofinfo.local_premise, context)}" if isinstance(node, (Any, Assume, Divide, Case, Some, Deny, Show)) else ""
    local_premise_html = f"<div class='local_premise' hidden>{local_premise}</div>"
    local_conclusion = f"local_conclusion: {render_expr_list(node.proofinfo.local_conclusion, context)}" if isinstance(node, (Any, Assume, Divide, Case, Some, Deny, Show)) else ""
    local_conclusion_html = f"<div class='local_conclusion' hidden>{local_conclusion}</div>"
    return f"  <div class='block'>{header_html}{context_vars_html}{context_formulas_html}{premises_html}{conclusions_html}{local_vars_html}{local_premise_html}{local_conclusion_html}{content_html}</div>"

def to_html(ast: list, context: Context, title: str, mode: str):
    now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    parts = []
    for i, node in enumerate(ast):
        print(f"Rendering node {i + 1} / {len(ast)} finished")
        parts.append(render_node(node, context, mode))
    body_html = "\n".join(parts)
    if mode == "mathjax":
        extra_head = MATHJAX_HEAD.format()
        footer = MATHJAX_FOOTER
    elif mode == "svg":
        extra_head = SVG_HEAD.format()
        footer = ""
    else:
        raise Exception(f"Unexpected mode: {mode}")
    return HTML_TEMPLATE.format(title=escape(title), now_str=now_str, extra_head=extra_head, body=body_html, footer=footer)

if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    mode = sys.argv[2]
    f = open(path)
    src = f.read()
    f.close()
    from lexer import lex
    tokens = lex(src)
    from parser import Parser
    parser = Parser(tokens)
    ast, _ = parser.parse_file()
    from checker import check_ast
    result, ast, context = check_ast(ast)
    if result:
        print("All theorems proved")
    else:
        print("❌ Not all theorems proved")
    import os
    title = os.path.splitext(os.path.basename(path))[0]
    html = to_html(ast, context, title, mode)
    f = open(os.path.join("html", f"{title}_{mode}.html"), 'w', encoding='utf-8')
    f.write(html)
    f.close()
