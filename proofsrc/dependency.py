from lexer import Token, lex
from token_stream import TokenStream
import os

class DependencyResolver:
    def __init__(self):
        self.resolved_files: list[str] = []
        self.tokens_cache: dict[str, list[Token]] = {}
        self.visiting_files: set[str] = set()

    def resolve(self, path: str):
        if path in self.resolved_files:
            print(f"Skipping {path}")
            return
        if path in self.visiting_files:
            raise Exception(f"Cyclic dependency detected: {path}")
        self.visiting_files.add(path)
        print(f"Visiting {path}")
        tokens = lex(path)
        self.tokens_cache[path] = tokens
        stream = TokenStream(tokens)
        while True:
            token = stream.peek()
            if token.type == "INCLUDE":
                stream.consume("INCLUDE")
                token = stream.peek()
                if token.type == "STRING":
                    token = stream.consume("STRING")
                    new_path = os.path.join(os.path.dirname(path), token.value)
                    if not os.path.exists(new_path):
                        raise Exception(f"File not found at {new_path}")
                    self.resolve(new_path)
                else:
                    raise Exception("STRING is required after INCLUDE")
            elif token.type == "EOF":
                break
            else:
                stream.consume(token.type)
        self.visiting_files.remove(path)
        self.resolved_files.append(path)
        print(f"Resolved {path}")

    def get_result(self) -> tuple[list[str], dict[str, list[Token]]]:
        return self.resolved_files, self.tokens_cache

if __name__ == "__main__":
    import sys
    path = sys.argv[1]
    resolver = DependencyResolver()
    resolver.resolve(path)
    resolved_files, tokens_cache = resolver.get_result()
    for file in resolved_files:
        print(f"file: {file}, length of tokens: {len(tokens_cache[file])}")
