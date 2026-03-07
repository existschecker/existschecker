from lexer import Token
from token_stream import TokenStream
from ast_types import DeclarationUnit

import hashlib

def split(file: str, file_tokens: list[Token], source: str) -> list[DeclarationUnit]:
    stream = TokenStream(file_tokens)
    units: list[DeclarationUnit] = []
    while True:
        start_token = stream.peek()
        if start_token.type == "EOF":
            break
        stream.consume(start_token.type)
        unit_tokens = [start_token] + get_tokens_until_next(stream)
        last_token = unit_tokens[-1]
        unit_tokens.append(Token("EOF", "", last_token.file, last_token.pos + len(last_token.value), last_token.line, last_token.column + len(last_token.value), last_token.line, last_token.column + len(last_token.value)))
        for index, token in enumerate(unit_tokens):
            token.index = index
        start = unit_tokens[0].pos
        end = unit_tokens[-1].pos
        raw_text = source[start:end]
        normalized_text = raw_text.replace("\r\n", "\n")
        hash = hashlib.md5(normalized_text.encode()).hexdigest()
        unit = DeclarationUnit(file=file, tokens=unit_tokens, hash=hash)
        units.append(unit)
    return units

def get_tokens_until_next(stream: TokenStream) -> list[Token]:
    tokens: list[Token] = []
    while True:
        tok = stream.peek()
        if tok.type in ("INCLUDE", "PRIMITIVE", "AXIOM", "THEOREM", "DEFINITION", "EXISTENCE", "UNIQUENESS", "EQUALITY", "MEMBERSHIP", "EOF"):
            return tokens
        else:
            tokens.append(stream.consume(tok.type))
