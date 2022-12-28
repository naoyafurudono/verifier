from parse import AppTerm, ConstTerm, LambdaTerm, PiTerm, SortTerm, StarTerm, Term, VarTerm, parse_term
import argparse
from parse import alpha_eqv


if __name__ == "__main__":
    apaser = argparse.ArgumentParser(prog='alpha')
    apaser.add_argument('filename')
    args = apaser.parse_args()
    filename = args.filename
    with open(filename, 'r') as f:
        code1 = f.readline()
        code2 = f.readline()
    try:
        term1 = parse_term(code1)
        term2 = parse_term(code2)
        if alpha_eqv(term1, term2):
            print("yes")
        else:
            print("no")
    except (SyntaxError) as e:
        print('syntax error')
        print(e)
