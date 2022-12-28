from parse import AppTerm, ConstTerm, LambdaTerm, PiTerm, SortTerm, StarTerm, Term, VarTerm, parse_term
import argparse


def alpha_eqv(t1: Term, t2: Term) -> bool:
    return alpha_with_env_depth(t1, t2, {}, {}, 0)


class AlphaEqvException(Exception):
    pass


def alpha_with_env_depth(t1: Term, t2: Term, env1: dict[str, int], env2: dict[str, int], depth: int) -> bool:
    # 代入をしないで、環境をもつことにした。
    # 代入後の部分は、それ以降代入されることのない変数なのでこの手法でうまくいく。
    # 環境は辞書で表現する。Shadowingは単に環境を上書きすれば良い。
    # レキシカルスコープのために環境を書き換えるときにコピーが必要。
    # [x:=depth]を環境でもつ。ASTの構造が同じならば、変数を束縛した「深さ」がどこかだけを問題にすればよい。
    if t1.tag() != t2.tag():
        return False

    name = t1.__class__
    if isinstance(t1, VarTerm) and isinstance(t2, VarTerm):
        name1 = env1.get(t1.name)
        name2 = env2.get(t2.name)
        if (not name1 is None) and (not name2 is None):
            return name1 == name2
        if (not name1 is None) or (not name2 is None):
            return False
        # 両方自由
        return t1.name == t2.name
    elif isinstance(t1, LambdaTerm) and isinstance(t2, LambdaTerm) or (
            isinstance(t1, PiTerm) and isinstance(t2, PiTerm)):
        # $x:(M).(N)のMを検査
        if not alpha_eqv(t1.t1, t2.t1):
            return False
        envc1 = env1.copy()
        envc2 = env2.copy()
        envc1[t1.name] = depth
        envc2[t2.name] = depth
        return alpha_with_env_depth(t1.t2, t2.t2, envc1, envc2, depth+1)
    elif isinstance(t1, StarTerm) and isinstance(t2, StarTerm) or (
            isinstance(t1, SortTerm) and isinstance(t2, SortTerm)):
        return True
    elif isinstance(t1, AppTerm) and isinstance(t2, AppTerm):
        return alpha_with_env_depth(t1.t1, t2.t1, env1, env2, depth) and alpha_with_env_depth(t1.t2, t2.t2, env1, env2, depth)

    elif isinstance(t1, ConstTerm) and isinstance(t2, ConstTerm):
        if t1.op != t2.op:
            return False
        for (tt1, tt2) in zip(t1.children, t2.children):
            if not alpha_with_env_depth(tt1, tt2, env1, env2, depth):
                return False
        return True

    raise AlphaEqvException(
        f"Error at alpha_with_eqv: unexpected term: {t1,t2}")


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
