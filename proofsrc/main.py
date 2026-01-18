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
from splitter import split
workspace = split(resolved_files, tokens_cache, resolver.source_cache)
from ast_types import Context
context = Context.init()
from parser import Parser
from checker import Checker
for file in workspace.resolved_files:
    for unit in workspace.file_units[file]:
        working_context = context.copy()
        Parser(unit).parse_unit(working_context)
        if Checker(unit).check_unit(working_context):
            context = working_context
        unit.context = context.copy()
total_errors = sum(len(unit.diagnostics) for file in workspace.file_units.values() for unit in file)
print(f"tota_errors: {total_errors}")
