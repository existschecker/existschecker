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
console_handler.setLevel(logging.INFO)

# ファイル出力用ハンドラ
file_handler = logging.FileHandler(os.path.join("logs", os.path.basename(path).replace(".proof", ".log")), mode='w', encoding='utf-8')
file_handler.setLevel(logging.DEBUG)

# 共通フォーマット
formatter = logging.Formatter("[%(filename)s] %(message)s")
console_handler.setFormatter(formatter)
file_handler.setFormatter(formatter)

# ハンドラ登録
logger.addHandler(console_handler)
logger.addHandler(file_handler)

from dependency import DependencyResolver
resolver = DependencyResolver()
resolver.resolve(path)
resolved_files, tokens_cache = resolver.get_result()
from ast_types import Context
parser_context = Context.init()
checker_context = Context.init()
for file in resolved_files:
    from parser import Parser
    parser = Parser(tokens_cache[file])
    ast, parser_context = parser.parse_file(parser_context)
    from checker import check_ast
    result, _, checker_context = check_ast(ast, checker_context)
    if result:
        print(f"All theorems proved: {file}")
    else:
        print(f"❌ Not all theorems proved: {file}")
        break
