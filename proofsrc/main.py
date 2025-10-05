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

from lexer import lex
tokens = lex(src)
from parser import Parser
parser = Parser(tokens)
ast = parser.parse_file()
from checker import check_ast
if check_ast(ast):
    print("All theorems proved")
else:
    print("❌ Not all theorems proved")
