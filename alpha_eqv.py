# python3.10以上が必要。match-caseを使っている(switch相当の使い方)

from parse import parse_term
import argparse

def run():
    apaser = argparse.ArgumentParser(prog = 'alpha')
    apaser.add_argument('filename')
    args = apaser.parse_args()
    filename = args.filename
    with open(filename,'r') as f:
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

def alpha_eqv(t1, t2):
    # return alpha_with_env(t1, t2, {}, {})
    return alpha_with_env_depth(t1, t2, {}, {}, 0)

def alpha_with_env_depth(t1, t2, env1, env2, depth):
    # 代入をしないで、環境をもつことにした。
    # 代入後の部分は、それ以降代入されることのない変数なのでこの手法でうまくいく。
    # 環境は辞書で表現する。Shadowingは単に環境を上書きすれば良い。
    # レキシカルスコープのために環境を書き換えるときにコピーが必要。
    # [x:=depth]を環境でもつ。ASTの構造が同じならば、変数を束縛した「深さ」がどこかだけを問題にすればよい。
    if t1['tag'] != t2['tag']:
        return False

    match t1["tag"]:
        case "var":
            name1 = env1.get(t1["name"])
            name2 = env2.get(t2["name"])
            if (not name1 is None) and (not name2 is None):
                # 両方束縛されている
                return name1 == name2
            if (not name1 is None) or (not name2 is None):
                # 片方は束縛されていて、もう片方は自由
                return False
            # 両方自由
            return t1["name"] == t2["name"]

        case x if x in ["lambda", "type"]:
            # $x:(M).(N)のMを検査
            if not alpha_eqv(t1["children"][0], t2["children"][0]):
                return False
            envc1 = env1.copy()
            envc2 = env2.copy()
            envc1[t1["var"]] = depth
            envc2[t2["var"]] = depth
            return alpha_with_env_depth(t1["children"][1], t2["children"][1], envc1, envc2, depth+1)

        case x if x in ["star", "sort"]:
            return True

        case "app":
            for (tt1, tt2) in zip(t1["children"], t2["children"]):
                if not alpha_with_env_depth(tt1, tt2, env1, env2, depth):
                    return False
            return True

        case "const":
            if t1["op"] != t2["op"]:
                return False
            for (tt1, tt2) in zip(t1["children"], t2["children"]):
                if not alpha_eqv(tt1, tt2):
                    return False
            return True

        case x:
            raise f"Error at alpha_with_eqv: unexpected term: {x}"

if __name__ == "__main__":
    run()
