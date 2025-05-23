import os
import argparse
import sys
from trs_parser import parse_trs_file

def main():
    parser = argparse.ArgumentParser(description='Parse TRS files')
    parser.add_argument('--debug', action='store_true', help='Enable debug output')
    args = parser.parse_args()

    trs_dir = "mkbTT"
    for filename in os.listdir(trs_dir):
        if filename.endswith(".trs"):
            filepath = os.path.join(trs_dir, filename)
            try:
                print(f"\nParsing {filename}:")
                sys.stdout.flush()
                vars, rules = parse_trs_file(filepath, debug=args.debug)
                print(f"Variables: {vars}")
                print("Rules:")
                for rule in rules:
                    print(f"  {rule}")
            except Exception as e:
                print(f"Error parsing {filename}: {e}")

if __name__ == "__main__":
    main()
