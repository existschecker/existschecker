from lexer import Token
from token_stream import TokenStream
from ast_types import DeclarationUnit, Workspace

import hashlib

def split(resolved_files: list[str], tokens_cache: dict[str, list[Token]], source_cache: dict[str, str]) -> Workspace:
    file_units: dict[str, list[DeclarationUnit]] = {}
    for file in resolved_files:
        stream = TokenStream(tokens_cache[file])
        units: list[DeclarationUnit] = []
        while True:
            start_token = stream.peek()
            if start_token.type == "EOF":
                break
            stream.consume(start_token.type)
            tokens = [start_token] + get_tokens_until_next(stream)
            last_token = tokens[-1]
            tokens.append(Token("EOF", "", last_token.file, last_token.pos + len(last_token.value), last_token.line, last_token.column + len(last_token.value), last_token.line, last_token.column + len(last_token.value), tokens[-1].index + 1))
            start = tokens[0].pos
            end = tokens[-1].pos
            raw_text = source_cache[file][start:end]
            normalized_text = raw_text.replace("\r\n", "\n")
            hash = hashlib.md5(normalized_text.encode()).hexdigest()
            unit = DeclarationUnit(file=file, tokens=tokens, hash=hash)
            units.append(unit)
        file_units[file] = units
    return Workspace(resolved_files, file_units)

def get_tokens_until_next(stream: TokenStream) -> list[Token]:
    tokens: list[Token] = []
    while True:
        tok = stream.peek()
        if tok.type in ("INCLUDE", "PRIMITIVE", "AXIOM", "THEOREM", "DEFINITION", "EXISTENCE", "UNIQUENESS", "EQUALITY", "MEMBERSHIP", "EOF"):
            return tokens
        else:
            tokens.append(stream.consume(tok.type))
