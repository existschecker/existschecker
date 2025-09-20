import re
from dataclasses import dataclass

@dataclass
class Token:
    type: str
    value: str
    pos: int

KEYWORDS = {"theorem", "definition", "any", "assume", "conclude", "by"}

SYMBOLS = {
    "{": "LBRACE",
    "}": "RBRACE",
    ";": "SEMI",
    ",": "COMMA",
    "(": "LPAREN",
    ")": "RPAREN"
}

def lex(src: str) -> list[Token]:
    tokens = []
    i = 0
    while i < len(src):
        c = src[i]
        if c.isspace():
            i += 1
            continue
        if c in SYMBOLS:
            tokens.append(Token(SYMBOLS[c], c, i))
            i += 1
        elif src[i:].startswith("\\forall"):
            tokens.append(Token("FORALL", "\\forall", i))
            i += len("\\forall")
        elif src[i:].startswith("\\exists"):
            tokens.append(Token("EXISTS", "\\exists", i))
            i += len("\\exists")
        elif src[i:].startswith("\\wedge"):
            tokens.append(Token("AND", "\\wedge", i))
            i += len("\\wedge")
        elif src[i:].startswith("\\vee"):
            tokens.append(Token("OR", "\\vee", i))
            i += len("\\vee")
        elif src[i:].startswith("\\to"):
            tokens.append(Token("IMPLIES", "\\to", i))
            i += len("\\to")
        elif src[i:].startswith("\\leftrightarrow"):
            tokens.append(Token("IFF", "\\leftrightarrow", i))
            i += len("\\leftrightarrow")
        else:
            m = re.match(r"(\\[A-Za-z][A-Za-z0-9_]*)|([A-Za-z_][A-Za-z0-9_]*)", src[i:])
            if m:
                text = m.group(0)
                if text in KEYWORDS:
                    tokens.append(Token(text.upper(), text, i))
                else:
                    tokens.append(Token("IDENT", text, i))
                i += len(text)
            else:
                raise SyntaxError(f"Unexpected character {c} at {i}")
    return tokens

if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    f = open(path)
    src = f.read()
    f.close()
    tokens = lex(src)
    for t in tokens:
        print(t)
