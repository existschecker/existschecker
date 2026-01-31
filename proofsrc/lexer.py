import re
from dataclasses import dataclass, field

@dataclass
class Token:
    type: str
    value: str
    file: str
    pos: int
    line: int
    column: int
    end_line: int
    end_column: int
    index: int = field(init=False)

    def info(self):
        return f"[{self.file}:{self.line}:{self.column}]"

KEYWORDS = {"theorem", "definition", "any", "assume", "conclude", "divide", "case", "some", "such", "deny", "contradict", "explode", "apply", "for", "lift", "primitive", "predicate", "arity", "axiom", "invoke", "expand", "constant", "by", "pad", "split", "connect", "existence", "uniqueness", "autoexpand", "function", "equality", "reflection", "replacement", "substitute", "characterize", "show", "tex", "as", "template", "leftward", "rightward", "include", "assert", "fold", "membership"}

SYMBOLS = {
    "{": "LBRACE",
    "}": "RBRACE",
    ":": "COLON",
    ",": "COMMA",
    "(": "LPAREN",
    ")": "RPAREN",
    "[": "LBRACKET",
    "]": "RBRACKET",
    "|": "SLASH",
    ".": "DOT",
    "_": "UNDERSCORE",
}

STRINGS = {
    "\\lambda^P": "LAMBDA_PRED",
    "\\lambda^F": "LAMBDA_FUN",
    "\\forall^P": "FORALL_PRED_TMPL",
    "\\forall^F": "FORALL_FUN_TMPL",
    "\\forall":   "FORALL",
    "\\exists!":  "EXISTS_UNIQ",
    "\\exists":   "EXISTS",
    "\\wedge":    "AND",
    "\\vee":      "OR",
    "\\neg":      "NOT",
    "\\to":       "IMPLIES",
    "\\leftrightarrow": "IFF",
    "\\bot":      "BOT",
}

def lex(path: str, src: str | None = None) -> tuple[list[Token], str]:
    if src is None:
        f = open(path)
        src = f.read()
        f.close()
    tokens: list[Token] = []
    i = 0
    line = 1
    line_start_pos = 0
    while i < len(src):
        column = i - line_start_pos + 1
        c = src[i]
        if c == "\n":
            line += 1
            i += 1
            line_start_pos = i
            continue
        if c.isspace():
            i += 1
            continue
        if src[i:i+2] == "/*":
            start_i = i
            start_line = line
            start_column = column
            i += 2
            while i < len(src) and src[i:i+2] != "*/":
                if src[i] == "\n":
                    line += 1
                    line_start_pos = i + 1
                i += 1
            if i >= len(src):
                tokens.append(Token("UNTERMINATED_COMMENT", src[start_i:], path, start_i, start_line, start_column, line, i - line_start_pos + 1))
                break
            i += 2
            continue
        if c in SYMBOLS:
            tokens.append(Token(SYMBOLS[c], c, path, i, line, column, line, column + 1))
            i += 1
            continue
        if src[i] == '"':
            start_i = i
            i += 1
            content_start_i = i
            while i < len(src) and src[i] != "\n" and src[i] != '"':
                i += 1
            content_end_i = i
            if i >= len(src) or src[i] == "\n":
                tokens.append(Token("UNTERMINATED_STRING", src[content_start_i:content_end_i], path, start_i, line, column, line, column + (i - start_i)))
            else:
                i += 1
                tokens.append(Token("STRING", src[content_start_i:content_end_i], path, start_i, line, column, line, column + (i - start_i)))
            continue
        if c == "\\":
            sorted_patterns = sorted(STRINGS.keys(), key=len, reverse=True)
            found = False
            for pattern in sorted_patterns:
                if src[i:].startswith(pattern):
                    length = len(pattern)
                    tokens.append(Token(STRINGS[pattern], pattern, path, i, line, column, line, column + length))
                    i += length
                    found = True
                    break
            if found:
                continue
        m = re.match(r"(\\[A-Za-z][A-Za-z0-9_]*)|([A-Za-z_][A-Za-z0-9_]*'*)", src[i:])
        if m:
            text = m.group(0)
            if text in KEYWORDS:
                tokens.append(Token(text.upper(), text, path, i, line, column, line, column + len(text)))
            else:
                tokens.append(Token("IDENT", text, path, i, line, column, line, column + len(text)))
            i += len(text)
            continue
        m = re.match(r"\d+", src[i:])
        if m:
            text = m.group(0)
            tokens.append(Token("NUMBER", text, path, i, line, column, line, column + len(text)))
            i += len(text)
            continue
        tokens.append(Token("INVALID_CHARACTER", src[i], path, i, line, column, line, column + 1))
        i += 1
    column = len(src) - line_start_pos + 1
    tokens.append(Token("EOF", "", path, i, line, column, line, column))
    return tokens, src

if __name__ == "__main__":
    import sys
    path = sys.argv[1]

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

    tokens, _ = lex(path)
    for t in tokens:
        logger.debug(t)
