from datetime import datetime
from html import escape
from ast_types import PrimPred, Axiom, Theorem, DefPred, DefCon, DefFun, DefFunTerm, Equality, Any, Assume, Connect, Expand, Split, Apply, Invoke, Deny, Some, Contradict, Lift, Pad, Divide, Case, Explode, Characterize, Substitute, Show, Context, DefConExist, DefConUniq, DefFunExist, DefFunUniq, EqualityReflection, EqualityReplacement, Symbol, Pred, Compound, Fun, Control, Declaration, Bottom, Formula, Term, DeclarationSupport, Var, Include, Assert, Fold, Template, Membership, DefFunTemplateTerm, CompoundTemplate
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

class Renderer:
    def __init__(self, context: Context, mode: str):
        self.context = context
        self.mode = mode
        if mode == "mathjax":
            self.render_expr = self.render_expr_mathjax
            self.render_expr_list = self.render_expr_list_mathjax
            self.render_expr_dict = self.render_expr_dict_mathjax
            self.render_tex = self.render_tex_mathjax
        elif mode == "svg":
            self.render_expr = self.render_expr_svg
            self.render_expr_list = self.render_expr_list_svg
            self.render_expr_dict = self.render_expr_dict_svg
            self.render_tex = self.render_tex_svg
        else:
            raise Exception(f"Unexpected mode: {mode}")
        self.bullet = "<button class='bullet'>•</button>"
        self.toggle = "<button class='toggle'>▼</button>"

    def render_keyword(self, keyword: str) -> str:
        return f"<span class='keyword'>{keyword}</span>"

    def render_identifier(self, name: str) -> str:
        return f"<span class='identifier'>{escape(name)}</span>"

    def render_expr_mathjax(self, node: str | Bottom | Formula | Term) -> str:
        if isinstance(node, str):
            return self.render_identifier(node)
        else:
            return escape(f"\\({pretty_expr(node, self.context)}\\)")

    def render_expr_list_mathjax(self, expr_list: Sequence[str | Bottom | Formula | Term]) -> str:
        return ",".join(self.render_expr_mathjax(expr) for expr in expr_list)

    T_Key = TypeVar("T_Key", str, Var)

    def render_expr_dict_mathjax(self, expr_dict: Mapping[T_Key, Term]) -> str:
        parts = [f"{escape(f"\\({pretty_expr(k, self.context)}\\)")}:{escape(f"\\({pretty_expr(v, self.context)}\\)")}" for k, v in expr_dict.items()]
        return ",".join(parts)

    def render_tex_mathjax(self, tex: list[str]):
        return escape(f"\\({"".join(tex)}\\)")

    def img_tag(self, svg_path: str, latex_code: str) -> str:
        return f"<img src='{escape(svg_path)}' alt='{escape(latex_code)}'>"

    def render_expr_svg(self, node: str | Bottom | Formula | Term) -> str:
        if isinstance(node, str):
            return self.render_identifier(node)
        else:
            latex_code = pretty_expr(node, self.context)
            svg_path = output_svg(latex_code)
            return self.img_tag(svg_path, latex_code)

    def render_expr_list_svg(self, expr_list: Sequence[str | Bottom | Formula | Term]) -> str:
        return ",".join((self.render_expr_svg(expr) for expr in expr_list))

    def render_expr_dict_svg(self, expr_dict: Mapping[T_Key, Term]) -> str:
        parts = [f"{self.render_expr_svg(k)}:{self.render_expr_svg(v)}" for k, v in expr_dict.items()]
        return f"{",".join(parts)}"

    def render_tex_svg(self, tex: list[str]):
        latex_code = "".join(tex)
        svg_path = output_svg(latex_code)
        return self.img_tag(svg_path, latex_code)

    def render_include(self, node: Include):
        header_parts = [self.bullet,
                        self.render_keyword("include"),
                        node.file]
        header_parts_jp = [self.bullet,
                            self.render_keyword("読み込み"),
                            node.file]
        return header_parts, header_parts_jp, ""

    def render_primpred(self, node: PrimPred):
        header_parts = [self.bullet,
                        self.render_keyword("primitive predicate"),
                        self.render_identifier(node.name),
                        self.render_tex(node.tex),
                        self.render_keyword("arity"),
                        f"{str(node.arity)}"]
        header_parts_jp = [self.bullet,
                           self.render_keyword("原始述語記号"),
                           self.render_identifier(node.name),
                           self.render_tex(node.tex),
                           self.render_keyword("arity"),
                           str(node.arity)]
        return header_parts, header_parts_jp, ""

    def render_axiom(self, node: Axiom):
        header_parts = [self.bullet,
                        self.render_keyword("axiom"),
                        self.render_identifier(node.name),
                        self.render_expr(node.conclusion)]
        header_parts_jp = [self.bullet,
                           self.render_keyword("公理"),
                           self.render_identifier(node.name),
                           self.render_expr(node.conclusion)]
        return header_parts, header_parts_jp, ""

    def render_theorem(self, node: Theorem):
        header_parts = [self.toggle,
                        self.render_keyword("theorem"),
                        self.render_identifier(node.name),
                        self.render_expr(node.conclusion)]
        header_parts_jp = [self.toggle,
                           self.render_keyword("定理"),
                           self.render_identifier(node.name),
                           self.render_expr(node.conclusion)]
        body_html = "".join(self.render_node(s) for s in node.proof)
        return header_parts, header_parts_jp, body_html

    def render_defpred(self, node: DefPred):
        header_parts = [self.bullet,
                        self.render_keyword("definition predicate"),
                        self.render_keyword("autoexpand") if node.autoexpand else "",
                        self.render_identifier(node.name),
                        self.render_expr(Symbol(Pred(node.name), tuple(node.args))),
                        self.render_keyword("as"),
                        self.render_expr(node.formula)]
        header_parts_jp = [self.bullet,
                           self.render_keyword("述語記号定義"),
                           self.render_keyword("autoexpand") if node.autoexpand else "",
                           self.render_identifier(node.name),
                           self.render_expr(Symbol(Pred(node.name), tuple(node.args))),
                           "を",
                           self.render_expr(node.formula),
                           "により定める。"]
        return header_parts, header_parts_jp, ""

    def render_defcon(self, node: DefCon):
        header_parts = [self.bullet,
                        self.render_keyword("definition constant"),
                        self.render_identifier(node.name),
                        self.render_tex(node.tex),
                        self.render_keyword("by"),
                        self.render_identifier(node.theorem)]
        header_parts_jp = [self.bullet,
                           self.render_keyword("定数記号定義"),
                           self.render_identifier(node.name),
                           self.render_tex(node.tex),
                           "存在と一意性は",
                           self.render_identifier(node.theorem),
                           "により示された。"]
        return header_parts, header_parts_jp, ""

    def render_defconexist(self, node: DefConExist):
        header_parts = [self.bullet,
                        self.render_keyword("existence"),
                        self.render_identifier(node.name),
                        self.render_expr(node.formula),
                        self.render_keyword("by"),
                        self.render_identifier(node.con_name)]
        header_parts_jp = [self.bullet,
                           self.render_keyword("存在"),
                           self.render_identifier(node.name),
                           self.render_expr(node.formula),
                           self.render_identifier(node.con_name),
                           "の定義による。"]
        return header_parts, header_parts_jp, ""
    
    def render_defconuniq(self, node: DefConUniq):
        header_parts = [self.bullet,
                        self.render_keyword("uniqueness"),
                        self.render_identifier(node.name),
                        self.render_expr(node.formula),
                        self.render_keyword("by"),
                        self.render_identifier(node.con_name)]
        header_parts_jp = [self.bullet,
                           self.render_keyword("一意性"),
                           self.render_identifier(node.name),
                           self.render_expr(node.formula),
                           self.render_identifier(node.con_name),
                           "の定義による。"]
        return header_parts, header_parts_jp, ""

    def render_deffun(self, node: DefFun):
        header_parts = [self.bullet,
                        self.render_keyword("definition function"),
                        self.render_identifier(node.name),
                        self.render_tex(node.tex),
                        self.render_keyword("by"),
                        self.render_identifier(node.theorem)]
        header_parts_jp = [self.bullet,
                           self.render_keyword("関数記号定義"),
                           self.render_identifier(node.name),
                           self.render_tex(node.tex),
                           "存在と一意性は",
                           self.render_identifier(node.theorem),
                           "により示された。"]
        return header_parts, header_parts_jp, ""

    def render_deffunexist(self, node: DefFunExist):
        header_parts = [self.bullet,
                        self.render_keyword("existence"),
                        self.render_identifier(node.name),
                        self.render_expr(node.formula),
                        self.render_keyword("by"),
                        self.render_identifier(node.fun_name)]
        header_parts_jp = [self.bullet,
                           self.render_keyword("存在"),
                           self.render_identifier(node.name),
                           self.render_expr(node.formula),
                           self.render_identifier(node.fun_name),
                           "の定義による。"]
        return header_parts, header_parts_jp, ""

    def render_deffununiq(self, node: DefFunUniq):
        header_parts = [self.bullet,
                        self.render_keyword("uniqueness"),
                        self.render_identifier(node.name),
                        self.render_expr(node.formula),
                        self.render_keyword("by"),
                        self.render_identifier(node.fun_name)]
        header_parts_jp = [self.bullet,
                           self.render_keyword("一意性"),
                           self.render_identifier(node.name),
                           self.render_expr(node.formula),
                           self.render_identifier(node.fun_name),
                           "の定義による。"]
        return header_parts, header_parts_jp, ""

    def render_deffunterm(self, node: DefFunTerm):
        header_parts = [self.bullet,
                        self.render_keyword("definition function"),
                        self.render_identifier(node.name),
                        self.render_expr(Compound(Fun(node.name), tuple(node.args))),
                        self.render_keyword("as"),
                        self.render_expr(node.term)]
        header_parts_jp = [self.bullet,
                           self.render_keyword("関数記号定義"),
                           self.render_identifier(node.name),
                           self.render_expr(Compound(Fun(node.name), tuple(node.args))),
                           "を",
                           self.render_expr(node.term),
                           "により定める。"]
        return header_parts, header_parts_jp, ""

    def render_deffuntemplateterm(self, node: DefFunTemplateTerm):
        header_parts = [self.bullet,
                        self.render_keyword("definition function template"),
                        f"[{node.arity}]",
                        self.render_identifier(node.name),
                        self.render_expr(CompoundTemplate(Fun(node.name), tuple(node.args))),
                        self.render_keyword("as"),
                        self.render_expr(node.term)]
        header_parts_jp = [self.bullet,
                           self.render_keyword("関数記号定義(テンプレート)"),
                           f"[{node.arity}]",
                           self.render_identifier(node.name),
                           self.render_expr(CompoundTemplate(Fun(node.name), tuple(node.args))),
                           "を",
                           self.render_expr(node.term),
                           "により定める。"]
        return header_parts, header_parts_jp, ""

    def render_equality(self, node: Equality):
        header_parts = [self.toggle,
                        self.render_keyword("equality"),
                        self.render_identifier(node.equal.name)]
        header_parts_jp = [self.toggle,
                        self.render_keyword("等号宣言"),
                        self.render_identifier(node.equal.name),
                        "は等号である。"]
        body_html = self.render_node(node.reflection) + self.render_node(node.replacement)
        return header_parts, header_parts_jp, body_html

    def render_membership(self, node: Membership):
        header_parts = [self.bullet,
                        self.render_keyword("membership"),
                        self.render_identifier(node.membership.name)]
        header_parts_jp = [self.bullet,
                           self.render_keyword("帰属関係宣言"),
                           self.render_identifier(node.membership.name),
                           "は帰属関係である。"]
        return header_parts, header_parts_jp, ""

    def render_declaration(self, node: Declaration):
        if isinstance(node, PrimPred):
            return self.render_primpred(node)
        elif isinstance(node, Axiom):
            return self.render_axiom(node)
        elif isinstance(node, Theorem):
            return self.render_theorem(node)
        elif isinstance(node, DefPred):
            return self.render_defpred(node)
        elif isinstance(node, DefCon):
            return self.render_defcon(node)
        elif isinstance(node, DefConExist):
            return self.render_defconexist(node)
        elif isinstance(node, DefConUniq):
            return self.render_defconuniq(node)
        elif isinstance(node, DefFun):
            return self.render_deffun(node)
        elif isinstance(node, DefFunExist):
            return self.render_deffunexist(node)
        elif isinstance(node, DefFunUniq):
            return self.render_deffununiq(node)
        elif isinstance(node, DefFunTerm):
            return self.render_deffunterm(node)
        elif isinstance(node, DefFunTemplateTerm):
            return self.render_deffuntemplateterm(node)
        elif isinstance(node, Equality):
            return self.render_equality(node)
        elif isinstance(node, Membership):
            return self.render_membership(node)
        else:
            raise Exception(f"Unexpected type: {type(node)}")

    def render_equality_reflection(self, node: EqualityReflection):
        header_parts = [self.bullet,
                        self.render_keyword("reflection"),
                        self.render_identifier(node.evidence.name)]
        header_parts_jp = [self.bullet,
                           "反射律は",
                           self.render_identifier(node.evidence.name),
                           "で示された。"]
        return header_parts, header_parts_jp, ""

    def render_equality_replacement(self, node: EqualityReplacement):
        header_parts = [self.bullet,
                        self.render_keyword("replacement"),
                        ",".join([self.render_identifier(k) + ":" + self.render_identifier(v.name) for k, v in node.evidence.items()])]
        header_parts_jp = [self.bullet,
                           "、".join([self.render_identifier(k) + "の置換律は" + self.render_identifier(v.name) + "で" for k, v in node.evidence.items()]),
                           "示された。"]
        return header_parts, header_parts_jp, ""

    def render_declaration_support(self, node: DeclarationSupport):
        if isinstance(node, EqualityReflection):
            return self.render_equality_reflection(node)
        elif isinstance(node, EqualityReplacement):
            return self.render_equality_replacement(node)
        else:
            raise Exception(f"Unexpected type: {type(node)}")

    def render_any(self, node: Any):
        header_parts = [self.toggle,
                        self.render_keyword("any"),
                        self.render_expr_list(node.items)]
        header_parts_jp = [self.toggle,
                           "任意の",
                           self.render_expr_list(node.items),
                           "をとる。"]
        body_html = "".join(self.render_node(s) for s in node.body)
        return header_parts, header_parts_jp, body_html

    def render_assume(self, node: Assume):
        header_parts = [self.toggle,
                        self.render_keyword("assume"),
                        self.render_expr(node.premise)]
        header_parts_jp = [self.toggle,
                           self.render_expr(node.premise),
                           "を仮定する。"]
        body_html = "".join(self.render_node(s) for s in node.body)
        return header_parts, header_parts_jp, body_html

    def render_connect(self, node: Connect):
        header_parts = [self.bullet,
                        self.render_keyword("connect"),
                        self.render_expr(node.conclusion)]
        header_parts_jp = [self.bullet,
                           "結合により",
                           self.render_expr(node.conclusion),
                           "を得る。"]
        return header_parts, header_parts_jp, ""

    def render_expand(self, node: Expand):
        defs = ",".join([self.render_identifier(definition) for definition in node.defs])
        header_parts = [self.bullet,
                        self.render_keyword("expand"),
                        self.render_expr(node.fact),
                        self.render_keyword("for"),
                        defs]
        header_parts_jp = [self.bullet,
                           self.render_expr(node.fact),
                           f"を{defs}の定義により言い換える。"]
        return header_parts, header_parts_jp, ""

    def render_fold(self, node: Fold):
        defs = ",".join([self.render_identifier(definition) for definition in node.defs])
        header_parts = [self.bullet,
                        self.render_keyword("fold"),
                        self.render_keyword("for"),
                        defs,
                        self.render_keyword("conclude"),
                        self.render_expr(node.conclusion)]
        header_parts_jp = [self.bullet,
                           f"{defs}の定義により言い換えて",
                           self.render_expr(node.conclusion),
                        "を得る。"]
        return header_parts, header_parts_jp, ""

    def render_split(self, node: Split):
        header_parts = [self.bullet,
                        self.render_keyword("split")]
        if node.index is not None:
            header_parts.append(str(node.index))
        header_parts.append(self.render_expr(node.fact))
        header_parts_jp = [self.bullet,
                           self.render_expr(node.fact),
                           "を分解する。" if node.index is None else f"を分解して{node.index}番目を得る。"]
        return header_parts, header_parts_jp, ""

    def render_apply(self, node: Apply):
        fact = self.render_expr(node.fact)
        if node.invoke == "none":
            invoke = []
            invoke_jp = "に適用する。"
        elif node.invoke == "invoke":
            invoke = [self.render_keyword("invoke")]
            invoke_jp = "に適用し、左側が成り立つので右側を得る。"
        elif node.invoke == "invoke-rightward":
            invoke = [self.render_keyword("invoke"), self.render_keyword("rightward")]
            invoke_jp = "に適用し、左側が成り立つので右側を得る。"
        elif node.invoke == "invoke-leftward":
            invoke = [self.render_keyword("invoke"), self.render_keyword("leftward")]
            invoke_jp = "に適用し、右側が成り立つので左側を得る。"
        else:
            raise Exception(f"Unexpected invoke option {node.invoke}")
        terms_str: list[str] = []
        for term in node.terms:
            if isinstance(term, Term):
                terms_str.append(self.render_expr(term))
            elif term is None:
                terms_str.append("_")
            else:
                raise Exception(f"Unexpected term: {term}")
        header_parts = [self.bullet,
                        self.render_keyword("apply")]
        header_parts.extend(invoke)
        header_parts.extend([fact,
                             self.render_keyword("for"),
                             ",".join(terms_str)])
        header_parts_jp = [self.bullet,
                           fact,
                           "を",
                           ",".join(terms_str),
                           invoke_jp]
        return header_parts, header_parts_jp, ""

    def render_invoke(self, node: Invoke):
        if node.direction == "none" or node.direction == "rightward":
            premise = "左側"
            conclusion = "右側"
        else:
            premise = "右側"
            conclusion = "左側"
        header_parts = [self.bullet,
                        self.render_keyword("invoke"),
                        "" if node.direction == "none" else self.render_keyword(node.direction),
                        self.render_expr(node.fact)]
        header_parts_jp = [self.bullet,
                           self.render_expr(node.fact),
                           f"の{premise}が成り立つので{conclusion}を得る。"]
        return header_parts, header_parts_jp, ""

    def render_deny(self, node: Deny):
        header_parts = [self.toggle,
                        self.render_keyword("deny"),
                        self.render_expr(node.premise)]
        header_parts_jp = [self.toggle,
                           "背理法を用いる。",
                           self.render_expr(node.premise),
                        "を仮定する。"]
        body_html = "".join(self.render_node(s) for s in node.body)
        return header_parts, header_parts_jp, body_html

    def render_some(self, node: Some):
        items_str: list[str] = []
        for item in node.items:
            if isinstance(item, (Var, Template)):
                items_str.append(self.render_expr(item))
            elif item is None:
                items_str.append("_")
            else:
                raise Exception(f"Unexpected item: {item}")
        header_parts = [self.toggle,
                        self.render_keyword("some"),
                        ",".join(items_str),
                        self.render_keyword("such"),
                        self.render_expr(node.fact)]
        header_parts_jp = [self.toggle,
                           self.render_expr(node.fact),
                           "において",
                           ",".join(items_str),
                           "としてとる。"]
        body_html = "".join(self.render_node(s) for s in node.body)
        return header_parts, header_parts_jp, body_html

    def render_contradict(self, node: Contradict):
        header_parts = [self.bullet,
                        self.render_keyword("contradict"),
                        self.render_expr(node.contradiction)]
        header_parts_jp = [self.bullet,
                           self.render_expr(node.contradiction),
                           "とその否定が成り立つので矛盾する。"]
        return header_parts, header_parts_jp, ""

    def render_lift(self, node: Lift):
        terms_str: list[str] = []
        for term in node.terms:
            if isinstance(term, Term):
                terms_str.append(self.render_expr(term))
            elif term is None:
                terms_str.append("_")
            else:
                raise Exception(f"Unexpected term: {term}")
        header_parts = [self.bullet,
                        self.render_keyword("lift"),
                        self.render_keyword("for"),
                        ",".join(terms_str),
                        self.render_keyword("conclude"),
                        self.render_expr(node.conclusion)]
        header_parts_jp = [self.bullet,
                           ",".join(terms_str),
                           "を置き換えて",
                           self.render_expr(node.conclusion),
                           "を得る。"]
        return header_parts, header_parts_jp, ""

    def render_pad(self, node: Pad):
        header_parts = [self.bullet,
                        self.render_keyword("pad"),
                        self.render_expr(node.fact),
                        self.render_keyword("conclude"),
                        self.render_expr(node.conclusion)]
        header_parts_jp = [self.bullet,
                           self.render_expr(node.fact),
                           "を水増しして",
                           self.render_expr(node.conclusion),
                           "を得る。"]
        return header_parts, header_parts_jp, ""

    def render_divide(self, node: Divide):
        header_parts = [self.toggle,
                        self.render_keyword("divide"),
                        self.render_expr(node.fact)]
        header_parts_jp = [self.toggle,
                           self.render_expr(node.fact),
                           "を場合分けする。"]
        body_html = "".join(self.render_node(s) for s in node.cases)
        return header_parts, header_parts_jp, body_html

    def render_case(self, node: Case):
        header_parts = [self.toggle,
                        self.render_keyword("case"),
                        self.render_expr(node.premise)]
        header_parts_jp = [self.toggle,
                           self.render_expr(node.premise),
                           "のとき"]
        body_html = "".join(self.render_node(s) for s in node.body)
        return header_parts, header_parts_jp, body_html

    def render_explode(self, node: Explode):
        header_parts = [self.bullet,
                        self.render_keyword("explode"),
                        self.render_expr(node.conclusion)]
        header_parts_jp = [self.bullet,
                           "矛盾から任意に結論を導けるので",
                           self.render_expr(node.conclusion),
                           "を得る。"]
        return header_parts, header_parts_jp, ""

    def render_characterize(self, node: Characterize):
        header_parts = [self.bullet,
                        self.render_keyword("characterize"),
                        self.render_keyword("for"),
                        self.render_expr(node.term),
                        self.render_keyword("conclude"),
                        self.render_expr(node.conclusion)]
        header_parts_jp = [self.bullet,
                           self.render_expr(node.term),
                           "を置き換えて",
                           self.render_expr(node.conclusion),
                           "を得る。"]
        return header_parts, header_parts_jp, ""

    def render_substitute(self, node: Substitute):
        env_parts = ""
        for k, v in node.env.items():
            env_parts += self.render_expr(k)
            if k in node.indexes:
                env_parts += "[" + ",".join(f"{i}" for i in node.indexes[k]) + "]"
            env_parts +=  ":" + self.render_expr(v)
        header_parts = [self.bullet,
                        self.render_keyword("substitute"),
                        self.render_expr(node.fact),
                        self.render_keyword("for"),
                        env_parts]
        if self.context.decl.equality is None:
            raise Exception("context.equality is None")
        header_parts_jp = [self.bullet,
                        self.render_expr(node.fact),
                        "に",
                        ",".join([self.render_expr(Symbol(Pred(self.context.decl.equality.equal.name), (k, v))) for k, v in node.env.items()]),
                        "を代入する。"]
        return header_parts, header_parts_jp, ""

    def render_show(self, node: Show):
        header_parts = [self.toggle,
                        self.render_keyword("show"),
                        self.render_expr(node.conclusion)]
        header_parts_jp = [self.toggle,
                           self.render_expr(node.conclusion),
                           "を示す。"]
        body_html = "".join(self.render_node(s) for s in node.body)
        return header_parts, header_parts_jp, body_html

    def render_assert(self, node: Assert):
        header_parts = [self.bullet,
                        self.render_keyword("assert"),
                        self.render_expr(node.reference)]
        header_parts_jp = [self.bullet,
                           self.render_expr(node.reference),
                           "を呼び出す。"]
        return header_parts, header_parts_jp, ""

    def render_control(self, node: Control) -> tuple[list[str], list[str], str]:
        if isinstance(node, Any):
            return self.render_any(node)
        elif isinstance(node, Assume):
            return self.render_assume(node)
        elif isinstance(node, Connect):
            return self.render_connect(node)
        elif isinstance(node, Expand):
            return self.render_expand(node)
        elif isinstance(node, Fold):
            return self.render_fold(node)
        elif isinstance(node, Split):
            return self.render_split(node)
        elif isinstance(node, Apply):
            return self.render_apply(node)
        elif isinstance(node, Invoke):
            return self.render_invoke(node)
        elif isinstance(node, Deny):
            return self.render_deny(node)
        elif isinstance(node, Some):
            return self.render_some(node)
        elif isinstance(node, Contradict):
            return self.render_contradict(node)
        elif isinstance(node, Lift):
            return self.render_lift(node)
        elif isinstance(node, Pad):
            return self.render_pad(node)
        elif isinstance(node, Divide):
            return self.render_divide(node)
        elif isinstance(node, Case):
            return self.render_case(node)
        elif isinstance(node, Explode):
            return self.render_explode(node)
        elif isinstance(node, Characterize):
            return self.render_characterize(node)
        elif isinstance(node, Substitute):
            return self.render_substitute(node)
        elif isinstance(node, Show):
            return self.render_show(node)
        elif isinstance(node, Assert):
            return self.render_assert(node)
        else:
            raise Exception(f"Unexpected type: {type(node)}")

    def render_proofinfo(self, node: Declaration | DeclarationSupport | Control):
        status = node.proofinfo.status
        status_html = f"<div class='status' hidden>{status}</div>"
        context_vars = self.render_expr_list(node.proofinfo.ctrl_ctx.vars)
        context_vars_html = f"<div class='context-vars' hidden>{context_vars}</div>"
        context_formulas = self.render_expr_list(node.proofinfo.ctrl_ctx.formulas)
        context_formulas_html = f"<div class='context-formulas' hidden>{context_formulas}</div>"
        context_templates = self.render_expr_list(node.proofinfo.ctrl_ctx.templates)
        context_templates_html = f"<div class='context-templates' hidden>{context_templates}</div>"
        premises = self.render_expr_list(node.proofinfo.premises)
        premises_html = f"<div class='premises' hidden>{premises}</div>"
        conclusions = self.render_expr_list(node.proofinfo.conclusions)
        conclusions_html = f"<div class='conclusions' hidden>{conclusions}</div>"
        local_vars = self.render_expr_list(node.proofinfo.local_vars)
        local_vars_html = f"<div class='local_vars' hidden>{local_vars}</div>"
        local_premise = self.render_expr_list(node.proofinfo.local_premise)
        local_premise_html = f"<div class='local_premise' hidden>{local_premise}</div>"
        local_conclusion = self.render_expr_list(node.proofinfo.local_conclusion)
        local_conclusion_html = f"<div class='local_conclusion' hidden>{local_conclusion}</div>"
        return f"{status_html}{context_vars_html}{context_formulas_html}{context_templates_html}{premises_html}{conclusions_html}{local_vars_html}{local_premise_html}{local_conclusion_html}"

    def render_node(self, node: Include | Declaration | DeclarationSupport | Control) -> str:
        if isinstance(node, Include):
            header_parts, header_parts_jp, body_html = self.render_include(node)
            header_syntax_html = f"<div class='syntax-view'>{' '.join(header_parts)}</div>"
            header_jp_html = f"<div class='jp-view'>{' '.join(header_parts_jp)}</div>"
            header_html = f"<div class='block-header'>{header_syntax_html}{header_jp_html}</div>"
            return f"  <div class='block'>{header_html}</div>"
        if isinstance(node, Declaration):
            header_parts, header_parts_jp, body_html = self.render_declaration(node)
        elif isinstance(node, DeclarationSupport):
            header_parts, header_parts_jp, body_html = self.render_declaration_support(node)
        elif isinstance(node, Control):
            header_parts, header_parts_jp, body_html = self.render_control(node)
        else:
            raise Exception(f"Unexpected type: {type(node)}")

        header_syntax_html = f"<div class='syntax-view'>{' '.join(header_parts)}</div>"
        header_jp_html = f"<div class='jp-view'>{' '.join(header_parts_jp)}</div>"
        header_html = f"<div class='block-header'>{header_syntax_html}{header_jp_html}</div>"
        proofinfo_html = self.render_proofinfo(node)
        content_html = f"<div class='block-content'>{body_html}</div>"
        return f"  <div class='block'>{header_html}{proofinfo_html}{content_html}</div>"

def to_html(ast: list[Include | Declaration], context: Context, title: str, mode: str) -> tuple[str, bool]:
    error_found = False
    now_str = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    parts: list[str] = []
    for i, node in enumerate(ast):
        print(f"\rRendering node {i + 1} / {len(ast)} finished", end="")
        parts.append(Renderer(context, mode).render_node(node))
        if isinstance(node, Declaration) and node.proofinfo.status == "ERROR":
            error_found = True
            print(f"\n❌ Rendering stopped", end="")
            break
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
    return HTML_TEMPLATE.format(title=escape(title), now_str=now_str, extra_head=extra_head, body=body_html, header_right=header_right), error_found

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
        parser_html, _ = to_html(ast, parser_context, title, mode)
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
        checker_html, error_found = to_html(ast, checker_context, title, mode)
        f = open(os.path.join("html", f"{title}.html"), 'w', encoding='utf-8')
        f.write(checker_html)
        f.close()
        if error_found:
            break
