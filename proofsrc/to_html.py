from html import escape
from ast_types import PrimPred, Axiom, Theorem, DefPred, DefCon, DefFun, DefFunTerm, Equality, Any, Assume, Connect, Expand, Split, Apply, Invoke, Deny, Some, Contradict, Lift, Pad, Divide, Case, Explode, Characterize, Substitute, Show, Check, Context, DefConExist, DefConUniq, DefFunExist, DefFunUniq, pretty_expr

HTML_TEMPLATE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8" />
<title>{title}</title>
<script id="MathJax-script" async
  src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
<style>
  body {{ font-family: "Noto Sans JP", sans-serif; background:#fff; color:#111; padding:1rem; }}
  .proof {{ max-width: 1000px; margin: 0 auto; }}
  .controls {{ margin-bottom:0.5rem; }}
  .block {{ margin-left: 1rem; padding-left: 0.8rem; margin-top:0.4rem; }}
  .block-header {{ display:flex; align-items:center; gap:0.5rem; }}
  .block-content {{ margin-top:0.25rem; }}
  .toggle {{ all: unset; width:1.2em; display:inline-block; background:none; border:none; cursor:pointer; color:#446; font-size:0.9em; text-align:center; }}
  .bullet {{ all: unset; display:inline-block; width:1.2em; text-align:center; color:#888; }}
  .keyword {{ font-weight:600; color:#064; margin-right:0.3rem; }}
  .identifier {{ color:#094; font-weight:600; margin-right:0.4rem; }}
  .collapsed {{ display:none; }}
</style>
</head>
<body>
<div class="proof">
  <div class="controls">
    <button id="expandAll">Expand all</button>
    <button id="collapseAll">Collapse all</button>
  </div>
{body}
</div>
<footer style="font-size:0.8em; color:#666; margin-top:2rem;">
  MathJax is used for rendering LaTeX math. Licensed under 
  <a href="https://www.apache.org/licenses/LICENSE-2.0" target="_blank">Apache License 2.0</a>.
</footer>
<script>
document.addEventListener('click', (e) => {{
  if (!e.target.matches('.toggle')) return;
  const btn = e.target;
  const header = btn.closest('.block-header');
  if (!header) return;
  const content = header.nextElementSibling;
  if (!content || !content.classList.contains('block-content')) return;
  content.classList.toggle('collapsed');
  btn.textContent = content.classList.contains('collapsed') ? '▶' : '▼';
  MathJax.typesetPromise();
}});
document.getElementById('expandAll').addEventListener('click', () => {{
  document.querySelectorAll('.block-content').forEach(c => c.classList.remove('collapsed'));
  document.querySelectorAll('.toggle').forEach(b => b.textContent='▼');
  MathJax.typesetPromise();
}});
document.getElementById('collapseAll').addEventListener('click', () => {{
  document.querySelectorAll('.block-content').forEach(c => c.classList.add('collapsed'));
  document.querySelectorAll('.toggle').forEach(b => b.textContent='▶');
}});
</script>
</body>
</html>
"""

def render_keyword(keyword: str) -> str:
    return f"<span class='keyword'>{keyword}</span>"

def render_identifier(name: str) -> str:
    return f"<span class='identifier'>{escape(name)}</span>"

def render_expr(node, context: Context) -> str:
    if isinstance(node, (Axiom, Theorem, DefConExist, DefConUniq, DefFunExist, DefFunUniq)):
        return render_identifier(node.name)
    else:
        return f"\\({pretty_expr(node, context)}\\)"

def render_expr_list(expr_list: list, context: Context) -> str:
    return f"\\({",".join(pretty_expr(expr, context) for expr in expr_list)}\\)"

def render_expr_dict(expr_dict: dict, context: Context) -> str:
    parts = [f"{pretty_expr(k, context)}:{pretty_expr(v, context)}" for k, v in expr_dict.items()]
    return f"\\({",".join(parts)}\\)"

def render_node(node, context: Context) -> str:
    header_parts = []
    body_html = ""
    bullet = "<button class='bullet'>•</button>"
    toggle = "<button class='toggle'>▼</button>"

    if isinstance(node, PrimPred):
        header_parts = [bullet,
                        render_keyword("primitive predicate"),
                        render_identifier(node.name)]
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
        body_html = "".join(render_node(s, context) for s in node.proof)
    elif isinstance(node, DefPred):
        header_parts = [bullet,
                        render_keyword("definition predicate"),
                        render_keyword("autoexpand") if node.autoexpand else "",
                        render_identifier(node.name),
                        render_expr(node.formula, context)]
    elif isinstance(node, DefCon):
        header_parts = [bullet,
                        render_keyword("definition constant"),
                        render_identifier(node.name)]
        body_html = render_node(node.existence, context) + render_node(node.uniqueness, context)
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
        header_parts = [bullet,
                        render_keyword("definition function"),
                        render_identifier(node.name)]
        body_html = render_node(node.existence, context) + render_node(node.uniqueness, context)
    elif isinstance(node, DefFunExist):
        header_parts = [bullet,
                        render_keyword("existence"),
                        render_identifier(node.name),
                        render_expr(node.formula, context)]
    elif isinstance(node, DefFunUniq):
        header_parts = [bullet,
                        render_identifier(node.name),
                        render_expr(node.formula, context)]
    elif isinstance(node, DefFunTerm):
        header_parts = [bullet,
                        render_keyword("definition function"),
                        render_identifier(node.name) + "(" + ",".join(arg.name for arg in node.args) + ")",
                        render_expr(node.term, context)]
    elif isinstance(node, Equality):
        header_parts = [bullet,
                        render_keyword("equality"),
                        render_identifier(node.equal.name),
                        render_keyword("reflection"),
                        render_identifier(node.reflection.name),
                        render_keyword("replacement")]
    elif isinstance(node, Any):
        header_parts = [toggle,
                        render_keyword("any"),
                        render_expr_list(node.vars, context)]
        if node.conclusion is not None:
            header_parts.extend([render_keyword("show"),
                                 render_expr(node.conclusion, context)])
        body_html = "".join(render_node(s, context) for s in node.body)
    elif isinstance(node, Assume):
        header_parts = [toggle,
                        render_keyword("assume"),
                        render_expr(node.premise, context)]
        if node.conclusion is not None:
            header_parts.extend([render_keyword("show"),
                                 render_expr(node.conclusion, context)])
        body_html = "".join(render_node(s, context) for s in node.body)
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
        body_html = "".join(render_node(s, context) for s in node.body)
    elif isinstance(node, Some):
        header_parts = [toggle,
                        render_keyword("some"),
                        render_expr_dict(node.env, context),
                        render_keyword("such"),
                        render_expr(node.fact, context)]
        if node.conclusion is not None:
            header_parts.append(f"<span class='keyword'>show</span> {render_expr(node.conclusion, context)}")
        body_html = "".join(render_node(s, context) for s in node.body)
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
        if node.conclusion is not None:
            header_parts.extend([render_keyword("show"),
                                 render_expr(node.conclusion, context)])
        body_html = "".join(render_node(s, context) for s in node.cases)
    elif isinstance(node, Case):
        header_parts = [toggle,
                        render_keyword("case"),
                        render_expr(node.premise, context)]
        body_html = "".join(render_node(s, context) for s in node.body)
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
        body_html = "".join(render_node(s, context) for s in node.body)
    elif isinstance(node, Check):
        header_parts = [bullet,
                        render_keyword("check"),
                        render_expr(node.conclusion, context)]
    else:
        raise Exception(f"Unexpected node: {type(node)}")

    header_html = "<div class='block-header'>" + " ".join(header_parts) + "</div>"
    content_html = f"<div class='block-content'>{body_html}</div>"
    return f"  <div class='block'>{header_html}{content_html}</div>"

def to_html(ast: list, context: Context, title: str):
    body_html = "\n".join(render_node(node, context) for node in ast)
    return HTML_TEMPLATE.format(title=escape(title), body=body_html)

if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    f = open(path)
    src = f.read()
    f.close()
    from lexer import lex
    tokens = lex(src)
    from parser import Parser
    parser = Parser(tokens)
    ast, context = parser.parse_file()
    import os
    title = os.path.splitext(os.path.basename(path))[0]
    html = to_html(ast, context, title)
    f = open(os.path.join("html", title + ".html"), 'w', encoding='utf-8')
    f.write(html)
    f.close()
