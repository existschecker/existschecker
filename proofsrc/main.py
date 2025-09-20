import sys
from parser import parse_file_from_source, pretty
from checker import check_proof

def main():
    if len(sys.argv) != 2:
        print("Usage: python proofsrc/main.py <file.proof>")
        return
    path = sys.argv[1]
    f = open(path)
    src = f.read()
    f.close()
    ast = parse_file_from_source(src)
    for node in ast:
        pretty(node)
        if hasattr(node, "proof"):
            result = check_proof(node, [])
            print("✔ OK" if result else "❌ Failed")

if __name__ == "__main__":
    main()
