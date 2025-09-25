from parser import parse_file_from_source, pretty
from checker import check_proof

def main(args):
    import logging
    numeric_level = getattr(logging, args.log.upper(), None)
    logging.basicConfig(level=numeric_level)
    f = open(args.input_file)
    src = f.read()
    f.close()
    ast = parse_file_from_source(src)
    for node in ast:
        pretty(node)
        if hasattr(node, "proof"):
            result = check_proof(node)
            if result:
                print(f"✔ theorem {node.name}: OK")
            else:
                print(f"❌ theorem {node.name}: Failed")

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("input_file", help="Proof file to process")
    parser.add_argument("--log", default="info",
                        choices=["debug", "info", "warning", "error", "critical"],
                        help="Set the logging level")
    args = parser.parse_args()
    main(args)
