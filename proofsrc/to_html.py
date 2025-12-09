from datetime import datetime
from html import escape
from ast_types import PrimPred, Axiom, Theorem, DefPred, DefCon, DefFun, DefFunTerm, Equality, Any, Assume, Connect, Expand, Split, Apply, Invoke, Deny, Some, Contradict, Lift, Pad, Divide, Case, Explode, Characterize, Substitute, Show, Context, DefConExist, DefConUniq, DefFunExist, DefFunUniq, EqualityReflection, EqualityReplacement, Symbol, Pred, Compound, Fun, Control, Declaration, Bottom, Formula, Term, DeclarationSupport, Var, Include, Assert
from svg import output_svg
from typing import Sequence, Mapping, TypeVar
from logic_utils import pretty_expr

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
  {header_right}
</header>
<div class="controls">
  <button id="expandAll">Expand all</button>
  <button id="collapseAll">Collapse all</button>
  <button id="toggleInfoPanel">Hide info (i)</button>
  <button id="toggleView">日本語 (Japanese)</button>
</div>
<div class="proof">
{body}
</div>
<div class="info-panel" id="infoPanel">
  <h3>Information</h3>
  <div id="infoContent">Please click a line to show its information.</div>
</div>
<script src="script.js"></script>
</body>
</html>
"""

MATHJAX_HEAD = """
<script id="MathJax-script" async
  src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
<link rel="stylesheet" href="style_mathjax.css">
"""

MATHJAX_HEADER_RIGHT = """
<div class="header-right">
  MathJax is used for rendering LaTeX math. Licensed under 
  <a href="https://www.apache.org/licenses/LICENSE-2.0" target="_blank">Apache License 2.0</a>.
</div>
"""

SVG_HEAD = """
<link rel="stylesheet" href="style_svg.css">
"""

def render_keyword(keyword: str) -> str:
    return f"<span class='keyword'>{keyword}</span>"

def render_identifier(name: str) -> str:
    return f"<span class='identifier'>{escape(name)}</span>"

def render_expr_mathjax(node: str | Bottom | Formula | Term, context: Context) -> str:
    if isinstance(node, str):
        return render_identifier(node)
    else:
        return escape(f"\\({pretty_expr(node, context)}\\)")

def render_expr_list_mathjax(expr_list: Sequence[str | Bottom | Formula | Term], context: Context) -> str:
    return ",".join(render_expr_mathjax(expr, context) for expr in expr_list)

T_Key = TypeVar("T_Key", str, Var)

def render_expr_dict_mathjax(expr_dict: Mapping[T_Key, Term], context: Context) -> str:
    parts = [f"{escape(f"\\({pretty_expr(k, context)}\\)")}:{escape(f"\\({pretty_expr(v, context)}\\)")}" for k, v in expr_dict.items()]
    return ",".join(parts)

def render_tex_mathjax(tex: list[str]):
    return escape(f"\\({"".join(tex)}\\)")

def img_tag(svg_path: str, latex_code: str) -> str:
    return f"<img src='{escape(svg_path)}' alt='{escape(latex_code)}'>"

def render_expr_svg(node: str | Bottom | Formula | Term, context: Context) -> str:
    if isinstance(node, str):
        return render_identifier(node)
    else:
        latex_code = pretty_expr(node, context)
        svg_path = output_svg(latex_code)
        return img_tag(svg_path, latex_code)

def render_expr_list_svg(expr_list: Sequence[str | Bottom | Formula | Term], context: Context) -> str:
    return ",".join((render_expr_svg(expr, context) for expr in expr_list))

def render_expr_dict_svg(expr_dict: Mapping[T_Key, Term], context: Context) -> str:
    parts = [f"{render_expr_svg(k, context)}:{render_expr_svg(v, context)}" for k, v in expr_dict.items()]
    return f"{",".join(parts)}"

def render_tex_svg(tex: list[str]):
    latex_code = "".join(tex)
    svg_path = output_svg(latex_code)
    return img_tag(svg_path, latex_code)

def render_node(node: Include | Declaration | DeclarationSupport | Control, context: Context, mode: str) -> str:
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
    header_parts_jp = []
    body_html = ""
    bullet = "<button class='bullet'>•</button>"
    toggle = "<button class='toggle'>▼</button>"

    if isinstance(node, Include):
        header_parts = [bullet,
                        render_keyword("include"),
                        node.file]
        header_parts_jp = [bullet,
                           render_keyword("読み込み"),
                           node.file]
        header_syntax_html = f"<div class='syntax-view'>{' '.join(header_parts)}</div>"
        header_jp_html = f"<div class='jp-view'>{' '.join(header_parts_jp)}</div>"
        header_html = f"<div class='block-header'>{header_syntax_html}{header_jp_html}</div>"
        return f"  <div class='block'>{header_html}</div>"

    if isinstance(node, PrimPred):
        header_parts = [bullet,
                        render_keyword("primitive predicate"),
                        render_identifier(node.name),
                        render_tex(node.tex),
                        render_keyword("arity"),
                        f"{str(node.arity)}"]
        header_parts_jp = [bullet,
                           render_keyword("原始述語記号"),
                           render_identifier(node.name),
                           render_tex(node.tex),
                           render_keyword("arity"),
                           str(node.arity)]
    elif isinstance(node, Axiom):
        header_parts = [bullet,
                        render_keyword("axiom"),
                        render_identifier(node.name),
                        render_expr(node.conclusion, context)]
        header_parts_jp = [bullet,
                           render_keyword("公理"),
                           render_identifier(node.name),
                           render_expr(node.conclusion, context)]
    elif isinstance(node, Theorem):
        header_parts = [toggle,
                        render_keyword("theorem"),
                        render_identifier(node.name),
                        render_expr(node.conclusion, context)]
        header_parts_jp = [toggle,
                           render_keyword("定理"),
                           render_identifier(node.name),
                           render_expr(node.conclusion, context)]
        body_html = "".join(render_node(s, context, mode) for s in node.proof)
    elif isinstance(node, DefPred):
        header_parts = [bullet,
                        render_keyword("definition predicate"),
                        render_keyword("autoexpand") if node.autoexpand else "",
                        render_identifier(node.name),
                        render_expr(Symbol(Pred(node.name), tuple(node.args)), context),
                        render_keyword("as"),
                        render_expr(node.formula, context)]
        header_parts_jp = [bullet,
                        render_keyword("述語記号定義"),
                        render_keyword("autoexpand") if node.autoexpand else "",
                        render_identifier(node.name),
                        render_expr(Symbol(Pred(node.name), tuple(node.args)), context),
                        "を",
                        render_expr(node.formula, context),
                        "により定める。"]
    elif isinstance(node, DefCon):
        header_parts = [bullet,
                        render_keyword("definition constant"),
                        render_identifier(node.name),
                        render_tex(node.tex),
                        render_keyword("by"),
                        render_identifier(node.theorem)]
        header_parts_jp = [bullet,
                           render_keyword("定数記号定義"),
                           render_identifier(node.name),
                           render_tex(node.tex),
                           "存在と一意性は",
                           render_identifier(node.theorem),
                           "により示された。"]
    elif isinstance(node, DefConExist):
        header_parts = [bullet,
                        render_keyword("existence"),
                        render_identifier(node.name),
                        render_expr(node.formula, context),
                        render_keyword("by"),
                        render_identifier(node.con_name)]
        header_parts_jp = [bullet,
                           render_keyword("存在"),
                           render_identifier(node.name),
                           render_expr(node.formula, context),
                           render_identifier(node.con_name),
                           "の定義による。"]
    elif isinstance(node, DefConUniq):
        header_parts = [bullet,
                        render_keyword("uniqueness"),
                        render_identifier(node.name),
                        render_expr(node.formula, context),
                        render_keyword("by"),
                        render_identifier(node.con_name)]
        header_parts_jp = [bullet,
                           render_keyword("一意性"),
                           render_identifier(node.name),
                           render_expr(node.formula, context),
                           render_identifier(node.con_name),
                           "の定義による。"]
    elif isinstance(node, DefFun):
        header_parts = [bullet,
                        render_keyword("definition function"),
                        render_identifier(node.name),
                        render_tex(node.tex),
                        render_keyword("by"),
                        render_identifier(node.theorem)]
        header_parts_jp = [bullet,
                           render_keyword("関数記号定義"),
                           render_identifier(node.name),
                           render_tex(node.tex),
                           "存在と一意性は",
                           render_identifier(node.theorem),
                           "により示された。"]
    elif isinstance(node, DefFunExist):
        header_parts = [bullet,
                        render_keyword("existence"),
                        render_identifier(node.name),
                        render_expr(node.formula, context),
                        render_keyword("by"),
                        render_identifier(node.fun_name)]
        header_parts_jp = [bullet,
                           render_keyword("存在"),
                           render_identifier(node.name),
                           render_expr(node.formula, context),
                           render_identifier(node.fun_name),
                           "の定義による。"]
    elif isinstance(node, DefFunUniq):
        header_parts = [bullet,
                        render_keyword("uniqueness"),
                        render_identifier(node.name),
                        render_expr(node.formula, context),
                        render_keyword("by"),
                        render_identifier(node.fun_name)]
        header_parts_jp = [bullet,
                           render_keyword("一意性"),
                           render_identifier(node.name),
                           render_expr(node.formula, context),
                           render_identifier(node.fun_name),
                           "の定義による。"]
    elif isinstance(node, DefFunTerm):
        header_parts = [bullet,
                        render_keyword("definition function"),
                        render_identifier(node.name),
                        render_expr(Compound(Fun(node.name), tuple(node.args)), context),
                        render_keyword("as"),
                        render_expr(node.term, context)]
        header_parts_jp = [bullet,
                           render_keyword("関数記号定義"),
                           render_identifier(node.name),
                           render_expr(Compound(Fun(node.name), tuple(node.args)), context),
                           "を",
                           render_expr(node.term, context),
                           "により定める。"]
    elif isinstance(node, Equality):
        header_parts = [toggle,
                        render_keyword("equality"),
                        render_identifier(node.equal.name)]
        header_parts_jp = [toggle,
                           render_keyword("等号宣言"),
                           render_identifier(node.equal.name),
                           "は等号である。"]
        body_html = render_node(node.reflection, context, mode) + render_node(node.replacement, context, mode)
    elif isinstance(node, EqualityReflection):
        header_parts = [bullet,
                        render_keyword("reflection"),
                        render_identifier(node.evidence.name)]
        header_parts_jp = [bullet,
                           "反射律は",
                           render_identifier(node.evidence.name),
                           "で示された。"]
    elif isinstance(node, EqualityReplacement):
        header_parts = [bullet,
                        render_keyword("replacement"),
                        ",".join([render_identifier(k) + ":" + render_identifier(v.name) for k, v in node.evidence.items()])]
        header_parts_jp = [bullet,
                           "、".join([render_identifier(k) + "の置換律は" + render_identifier(v.name) + "で" for k, v in node.evidence.items()]),
                           "示された。"]
    elif isinstance(node, Any):
        header_parts = [toggle,
                        render_keyword("any"),
                        render_expr_list(node.items, context)]
        header_parts_jp = [toggle,
                           "任意の",
                           render_expr_list(node.items, context),
                           "をとる。"]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    elif isinstance(node, Assume):
        header_parts = [toggle,
                        render_keyword("assume"),
                        render_expr(node.premise, context)]
        header_parts_jp = [toggle,
                           render_expr(node.premise, context),
                           "を仮定する。"]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    elif isinstance(node, Connect):
        header_parts = [bullet,
                        render_keyword("connect"),
                        render_expr(node.conclusion, context)]
        header_parts_jp = [bullet,
                           "結合により",
                           render_expr(node.conclusion, context),
                           "を得る。"]
    elif isinstance(node, Expand):
        defs = ",".join([render_identifier(definition) for definition in node.defs])
        header_parts = [bullet,
                        render_keyword("expand"),
                        render_expr(node.fact, context),
                        render_keyword("for"),
                        defs,
                        render_keyword("conclude"),
                        render_expr(node.conclusion, context)]
        header_parts_jp = [bullet,
                           render_expr(node.fact, context),
                           f"を{defs}の定義により言い換えて",
                           render_expr(node.conclusion, context),
                           "を得る。"]
    elif isinstance(node, Split):
        header_parts = [bullet,
                        render_keyword("split")]
        if node.index is not None:
            header_parts.append(str(node.index))
        header_parts.append(render_expr(node.fact, context))
        header_parts_jp = [bullet,
                           render_expr(node.fact, context),
                           "を分解する。" if node.index is None else f"を分解して{node.index}番目を得る。"]
    elif isinstance(node, Apply):
        fact = render_expr(node.fact, context)
        if node.invoke == "none":
            invoke = []
            invoke_jp = "適用する。"
        elif node.invoke == "invoke":
            invoke = [render_keyword("invoke")]
            invoke_jp = "適用し、左側が成り立つので右側を得る。"
        elif node.invoke == "invoke-rightward":
            invoke = [render_keyword("invoke"), render_keyword("rightward")]
            invoke_jp = "適用し、左側が成り立つので右側を得る。"
        elif node.invoke == "invoke-leftward":
            invoke = [render_keyword("invoke"), render_keyword("leftward")]
            invoke_jp = "適用し、右側が成り立つので左側を得る。"
        else:
            raise Exception(f"Unexpected invoke option {node.invoke}")
        header_parts = [bullet,
                        render_keyword("apply")]
        header_parts.extend(invoke)
        header_parts.extend([fact,
                             render_keyword("for"),
                             render_expr_dict(node.env, context)])
        header_parts_jp = [bullet,
                           fact,
                           "の",
                           "、".join([render_expr(k, context) + "を" + render_expr(v, context) + "に" for k, v in node.env.items()]),
                           invoke_jp]
    elif isinstance(node, Invoke):
        if node.direction == "none" or node.direction == "rightward":
            premise = "左側"
            conclusion = "右側"
        else:
            premise = "右側"
            conclusion = "左側"
        header_parts = [bullet,
                        render_keyword("invoke"),
                        "" if node.direction == "none" else render_keyword(node.direction),
                        render_expr(node.fact, context)]
        header_parts_jp = [bullet,
                           render_expr(node.fact, context),
                           f"の{premise}が成り立つので{conclusion}を得る。"]
    elif isinstance(node, Deny):
        header_parts = [toggle,
                        render_keyword("deny"),
                        render_expr(node.premise, context)]
        header_parts_jp = [toggle,
                           "背理法を用いる。",
                           render_expr(node.premise, context),
                           "を仮定する。"]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    elif isinstance(node, Some):
        header_parts = [toggle,
                        render_keyword("some"),
                        render_expr_dict(node.env, context),
                        render_keyword("such"),
                        render_expr(node.fact, context)]
        header_parts_jp = [toggle,
                           render_expr(node.fact, context),
                           "の",
                           "、".join([render_expr(k, context) + "を" + render_expr(v, context) + "として" for k, v in node.env.items()]),
                           "とる。"]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    elif isinstance(node, Contradict):
        header_parts = [bullet,
                        render_keyword("contradict"),
                        render_expr(node.contradiction, context)]
        header_parts_jp = [bullet,
                          render_expr(node.contradiction, context),
                          "とその否定が成り立つので矛盾する。"]
    elif isinstance(node, Lift):
        header_parts = [bullet,
                        render_keyword("lift"),
                        render_keyword("for"),
                        render_expr_dict(node.env, context),
                        render_keyword("conclude"),
                        render_expr(node.conclusion, context)]
        header_parts_jp = [bullet,
                           "、".join([render_expr(v, context) + "を" + render_expr(k, context) + "に" for k, v in node.env.items()]),
                           "置き換えて",
                           render_expr(node.conclusion, context),
                           "を得る。"]
    elif isinstance(node, Pad):
        header_parts = [bullet,
                        render_keyword("pad"),
                        render_expr(node.fact, context),
                        render_keyword("conclude"),
                        render_expr(node.conclusion, context)]
        header_parts_jp = [bullet,
                           render_expr(node.fact, context),
                           "を水増しして",
                           render_expr(node.conclusion, context),
                           "を得る。"]
    elif isinstance(node, Divide):
        header_parts = [toggle,
                        render_keyword("divide"),
                        render_expr(node.fact, context)]
        header_parts_jp = [toggle,
                           render_expr(node.fact, context),
                           "を場合分けする。"]
        body_html = "".join(render_node(s, context, mode) for s in node.cases)
    elif isinstance(node, Case):
        header_parts = [toggle,
                        render_keyword("case"),
                        render_expr(node.premise, context)]
        header_parts_jp = [toggle,
                           render_expr(node.premise, context),
                           "のとき"]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    elif isinstance(node, Explode):
        header_parts = [bullet,
                        render_keyword("explode"),
                        render_expr(node.conclusion, context)]
        header_parts_jp = [bullet,
                           "矛盾から任意に結論を導けるので",
                           render_expr(node.conclusion, context),
                           "を得る。"]
    elif isinstance(node, Characterize):
        header_parts = [bullet,
                        render_keyword("characterize"),
                        render_keyword("for"),
                        render_expr_dict(node.env, context),
                        render_keyword("conclude"),
                        render_expr(node.conclusion, context)]
        header_parts_jp = [bullet,
                           "、".join([render_expr(v, context) + "を" + render_expr(k, context) + "に" for k, v in node.env.items()]),
                           "置き換えて",
                           render_expr(node.conclusion, context),
                           "を得る。"]
    elif isinstance(node, Substitute):
        env_parts = ""
        for k, v in node.env.items():
            env_parts += render_expr(k, context)
            if k in node.indexes:
                env_parts += "@" + ",".join(f"{i}" for i in node.indexes[k])
            env_parts +=  ":" + render_expr(v, context)
            if k in node.evidence:
                env_parts += render_keyword("by") + render_identifier(node.evidence[k])
        header_parts = [bullet,
                        render_keyword("substitute"),
                        render_expr(node.fact, context),
                        render_keyword("for"),
                        env_parts,
                        render_keyword("conclude"),
                        render_expr(node.conclusion, context)]
        if context.decl.equality is None:
            raise Exception("context.equality is None")
        header_parts_jp = [bullet,
                           render_expr(node.fact, context),
                           "に",
                           ",".join([render_expr(Symbol(Pred(context.decl.equality.equal.name), (k, v)), context) for k, v in node.env.items()]),
                           "を代入して",
                           render_expr(node.conclusion, context),
                           "を得る。"]
    elif isinstance(node, Show):
        header_parts = [toggle,
                        render_keyword("show"),
                        render_expr(node.conclusion, context)]
        header_parts_jp = [toggle,
                           render_expr(node.conclusion, context),
                           "を示す。"]
        body_html = "".join(render_node(s, context, mode) for s in node.body)
    elif isinstance(node, Assert):
        header_parts = [bullet,
                        render_keyword("assert"),
                        render_identifier(node.reference)]
        header_parts_jp = [bullet,
                           render_identifier(node.reference),
                           "を呼び出す。"]
    else:
        raise Exception(f"Unexpected node: {type(node)}")

    header_syntax_html = f"<div class='syntax-view'>{' '.join(header_parts)}</div>"
    header_jp_html = f"<div class='jp-view'>{' '.join(header_parts_jp)}</div>"
    header_html = f"<div class='block-header'>{header_syntax_html}{header_jp_html}</div>"
    status = node.proofinfo.status
    status_html = f"<div class='status' hidden>{status}</div>"
    context_vars = render_expr_list(node.proofinfo.ctrl_ctx.vars, context)
    context_vars_html = f"<div class='context-vars' hidden>{context_vars}</div>"
    context_formulas = render_expr_list(node.proofinfo.ctrl_ctx.formulas, context)
    context_formulas_html = f"<div class='context-formulas' hidden>{context_formulas}</div>"
    context_templates = render_expr_list(node.proofinfo.ctrl_ctx.templates, context)
    context_templates_html = f"<div class='context-templates' hidden>{context_templates}</div>"
    premises = render_expr_list(node.proofinfo.premises, context)
    premises_html = f"<div class='premises' hidden>{premises}</div>"
    conclusions = render_expr_list(node.proofinfo.conclusions, context)
    conclusions_html = f"<div class='conclusions' hidden>{conclusions}</div>"
    content_html = f"<div class='block-content'>{body_html}</div>"
    local_vars = render_expr_list(node.proofinfo.local_vars, context)
    local_vars_html = f"<div class='local_vars' hidden>{local_vars}</div>"
    local_premise = render_expr_list(node.proofinfo.local_premise, context)
    local_premise_html = f"<div class='local_premise' hidden>{local_premise}</div>"
    local_conclusion = render_expr_list(node.proofinfo.local_conclusion, context)
    local_conclusion_html = f"<div class='local_conclusion' hidden>{local_conclusion}</div>"
    return f"  <div class='block'>{header_html}{status_html}{context_vars_html}{context_formulas_html}{context_templates_html}{premises_html}{conclusions_html}{local_vars_html}{local_premise_html}{local_conclusion_html}{content_html}</div>"

def to_html(ast: list[Include | Declaration], context: Context, title: str, mode: str):
    now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    parts: list[str] = []
    for i, node in enumerate(ast):
        print(f"\rRendering node {i + 1} / {len(ast)} finished", end="")
        parts.append(render_node(node, context, mode))
    print()
    body_html = "\n".join(parts)
    if mode == "mathjax":
        extra_head = MATHJAX_HEAD.format()
        header_right = MATHJAX_HEADER_RIGHT
    elif mode == "svg":
        extra_head = SVG_HEAD.format()
        header_right = ""
    else:
        raise Exception(f"Unexpected mode: {mode}")
    return HTML_TEMPLATE.format(title=escape(title), now_str=now_str, extra_head=extra_head, body=body_html, header_right=header_right)

if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    mode = sys.argv[2]
    from dependency import DependencyResolver
    resolver = DependencyResolver()
    resolver.resolve(path)
    resolved_files, tokens_cache = resolver.get_result()
    parser_context = Context.init()
    checker_context = Context.init()
    for file in resolved_files:
        import os
        name = os.path.splitext(os.path.basename(file))[0]
        from parser import Parser
        parser = Parser(tokens_cache[file])
        ast, parser_context = parser.parse_file(parser_context)
        title = f"{name}_parser_{mode}"
        parser_html = to_html(ast, parser_context, title, mode)
        f = open(os.path.join("html", f"{title}.html"), 'w', encoding='utf-8')
        f.write(parser_html)
        f.close()
        from checker import check_ast
        result, ast, checker_context = check_ast(ast, checker_context)
        if result:
            print("All theorems proved")
        else:
            print("❌ Not all theorems proved")
        title = f"{name}_checker_{mode}"
        checker_html = to_html(ast, checker_context, title, mode)
        f = open(os.path.join("html", f"{title}.html"), 'w', encoding='utf-8')
        f.write(checker_html)
        f.close()
