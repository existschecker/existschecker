import re
from dataclasses import dataclass

@dataclass
class Token:
    type: str
    value: str
    pos: int
    line: int

KEYWORDS = {"theorem", "definition", "any", "assume", "conclude", "divide", "case", "some", "such", "deny", "contradict", "explode", "apply", "for", "lift", "primitive", "predicate", "arity", "axiom", "invoke", "expand", "constant", "by", "pad", "split", "connect", "existence", "uniqueness", "autoexpand", "function", "equality", "reflection", "replacement", "substitute", "characterize", "show", "tex", "as", "template"}

SYMBOLS = {
    "{": "LBRACE",
    "}": "RBRACE",
    ":": "COLON",
    ",": "COMMA",
    "(": "LPAREN",
    ")": "RPAREN"
}

def lex(src: str) -> list[Token]:
    tokens = []
    i = 0
    line = 1
    while i < len(src):
        c = src[i]
        if c == "\n":
            line += 1
            i += 1
            continue
        if c.isspace():
            i += 1
            continue
        if src[i:i+2] == "/*":
            i += 2
            while i < len(src) and src[i:i+2] != "*/":
                if src[i] == "\n":
                    line += 1
                i += 1
            if i >= len(src):
                raise SyntaxError("Unterminated comment")
            i += 2
            continue
        if c in SYMBOLS:
            tokens.append(Token(SYMBOLS[c], c, i, line))
            i += 1
        elif src[i:].startswith("\\forall^T"):
            tokens.append(Token("FORALL_TEMPLATE", "\\forall^T", i, line))
            i += len("\\forall^T")
        elif src[i:].startswith("\\forall"):
            tokens.append(Token("FORALL", "\\forall", i, line))
            i += len("\\forall")
        elif src[i:].startswith("\\exists!"):
            tokens.append(Token("EXISTS_UNIQ", "\\exists!", i, line))
            i += len("\\exists!")
        elif src[i:].startswith("\\exists"):
            tokens.append(Token("EXISTS", "\\exists", i, line))
            i += len("\\exists")
        elif src[i:].startswith("\\wedge"):
            tokens.append(Token("AND", "\\wedge", i, line))
            i += len("\\wedge")
        elif src[i:].startswith("\\vee"):
            tokens.append(Token("OR", "\\vee", i, line))
            i += len("\\vee")
        elif src[i:].startswith("\\neg"):
            tokens.append(Token("NOT", "\\neg", i, line))
            i += len("\\neg")
        elif src[i:].startswith("\\to"):
            tokens.append(Token("IMPLIES", "\\to", i, line))
            i += len("\\to")
        elif src[i:].startswith("\\leftrightarrow"):
            tokens.append(Token("IFF", "\\leftrightarrow", i, line))
            i += len("\\leftrightarrow")
        elif src[i:].startswith("\\bot"):
            tokens.append(Token("BOT", "\\bot", i, line))
            i += len("\\bot")
        elif src[i] == '"':
            i += 1
            start = i
            while i < len(src) and src[i] != '"':
                i += 1
            if i >= len(src):
                raise SyntaxError(f"Unterminated string starting at pos {start}")
            text = src[start:i]
            tokens.append(Token("STRING", text, start, line))
            i += 1
        else:
            m = re.match(r"(\\[A-Za-z][A-Za-z0-9_]*)|([A-Za-z_][A-Za-z0-9_]*'*)", src[i:])
            if m:
                text = m.group(0)
                if text in KEYWORDS:
                    tokens.append(Token(text.upper(), text, i, line))
                else:
                    tokens.append(Token("IDENT", text, i, line))
                i += len(text)
            elif re.match(r"\d+", src[i:]):
                m = re.match(r"\d+", src[i:])
                text = m.group(0)
                tokens.append(Token("NUMBER", text, i, line))
                i += len(text)
            else:
                raise SyntaxError(f"Unexpected character {c} at pos {i}, line {line}")
    tokens.append(Token("EOF", "", i, line))
    return tokens

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
    file_handler = logging.FileHandler(os.path.join("logs", os.path.basename(path).replace(".proof", "_lexer.log")), mode='w', encoding='utf-8')
    file_handler.setLevel(logging.DEBUG)

    # 共通フォーマット
    formatter = logging.Formatter("[%(filename)s] %(message)s")
    console_handler.setFormatter(formatter)
    file_handler.setFormatter(formatter)

    # ハンドラ登録
    logger.addHandler(console_handler)
    logger.addHandler(file_handler)

    tokens = lex(src)
    for t in tokens:
        logger.debug(t)
