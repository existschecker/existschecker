import sys
path = sys.argv[1]
f = open(path)
src = f.read()
from parser import parse_file_from_source
parse_file_from_source(src)
