import sys
path = sys.argv[1]

import os
import logging

logger = logging.getLogger("proof")
logger.setLevel(logging.DEBUG)

console_handler = logging.StreamHandler()
console_handler.setLevel(logging.INFO)

file_handler = logging.FileHandler(os.path.join("logs", os.path.basename(path).replace(".proof", ".log")), mode='w', encoding='utf-8')
file_handler.setLevel(logging.DEBUG)

formatter = logging.Formatter("[%(filename)s] %(message)s")
console_handler.setFormatter(formatter)
file_handler.setFormatter(formatter)

logger.addHandler(console_handler)
logger.addHandler(file_handler)

from dependency import DependencyResolver, prepare_context
resolver = DependencyResolver()
resolver.resolve(path)
order = resolver.get_dependent_order(path)
from splitter import split
from ast_types import Context, DeclarationUnit
context = Context.init()
from parser import Parser
from checker import Checker
file_units: dict[str, list[DeclarationUnit]] = {}
file_final_contexts: dict[str, Context] = {}
for file in order:
    all_units = split(file, resolver.tokens_cache[file], resolver.source_cache[file])
    file_units[file] = all_units
    context = prepare_context(file, resolver, file_final_contexts)
    for unit in all_units:
        working_context = context.copy()
        Parser(unit).parse_unit(working_context)
        if Checker(unit).check_unit(working_context):
            context = working_context
        unit.context = context.copy()
    file_final_contexts[file] = context.copy()
total_errors = sum(len(unit.diagnostics) for file in file_units.values() for unit in file)
print(f"total_errors: {total_errors}")
