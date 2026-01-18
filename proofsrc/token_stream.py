from lexer import Token

class TokenStreamError(Exception):
    def __init__(self, token: Token, msg: str) -> None:
        self.token = token
        self.msg = msg

class TokenStream:
    def __init__(self, tokens: list[Token]):
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> Token:
        if self.pos >= len(self.tokens):
            msg = "Unexpected end of input"
            raise TokenStreamError(self.tokens[-1], msg)
        return self.tokens[self.pos]

    def consume(self, expected_type: str) -> Token:
        tok = self.peek()
        if tok.type != expected_type:
            msg = f"Expected {expected_type}, got {tok.type}"
            raise TokenStreamError(tok, msg)
        self.pos += 1
        return tok
