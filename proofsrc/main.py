import sys
from parser import parse_file, pretty
from checker import check_proof

def main():
    if len(sys.argv) != 2:
        print("Usage: python proofsrc/main.py <file.proof>")
        return
    path = sys.argv[1]
    ast = parse_file(path)
    for node in ast:
        pretty(node)
        if hasattr(node, "proof"):
            result = check_proof(node, [])
            print("✔ OK" if result else "❌ Failed")

if __name__ == "__main__":
    main()
