from parse import parse_term
from fresh_name import Fresh
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
    return alpha_with_env(t1, t2, {}, {})

def alpha_with_env(t1, t2, env1, env2):
    # print(t1)
    # print(t2)
    # print()
    # 代入をしないで、環境をもつことにした。
    # 代入後の部分は、それ以降代入されることのない変数なのでこの手法でうまくいく。
    # 環境は辞書で表現する。Shadowingは単に環境を上書きすれば良い。
    # レキシカルスコープのために環境を書き換えるときにコピーが必要。
    if t1['tag'] != t2['tag']:
        return False
    match t1["tag"]:
        case "var":
            name1 = env1.get(t1["name"], t1["name"])
            name2 = env2.get(t2["name"], t2["name"])
            return name1 == name2
        case x if x in ["star", "sort"]:
            return True
        case "app":
            for (tt1, tt2) in zip(t1["children"], t2["children"]):
                if not alpha_with_env(tt1, tt2, env1, env2):
                    return False
            return True
        case "const":
            if t1["op"] != t2["op"]:
                return False
            for (tt1, tt2) in zip(t1["children"], t2["children"]):
                if not alpha_eqv(tt1, tt2):
                    return False
            return True
        case x if x in ["lambda", "type"]:
            # $x:(M).(N)のMを検査
            if not alpha_eqv(t1["children"][0], t2["children"][0]):
                return False
            # 代入を
            envc1 = env1.copy()
            envc2 = env2.copy()
            new_name = Fresh.fresh()
            envc1[t1["var"]] = new_name
            envc2[t2["var"]] = new_name
            return alpha_with_env(t1["children"][1], t2["children"][1], envc1, envc2)
        case x:
            raise f"Error at alpha_with_eqv: unexpected term: {x}"

if __name__ == "__main__":
    run()

# t1とt2がアルファ同値か判定する
# def alpha_eqv(t1, t2):
#     if t1['tag'] != t2['tag']:
#         return False
#     match t1["tag"]:
#         case "var":
#             return t1["name"] == t2["name"]
#         case x if x in ["star", "sort"]:
#             return True
#         case "app":
#             for (tt1, tt2) in zip(t1["children"], t2["children"]):
#                 if not alpha_eqv(tt1, tt2):
#                     return False
#                 return True
#         case "const":
#             if t1["op"] != t2["op"]:
#                 return False
#             for (tt1, tt2) in zip(t1["children"], t2["children"]):
#                 if not alpha_eqv(tt1, tt2):
#                     return False
#                 return True

#         case "lambda":
#             # $x:(M).(N)のMを検査
#             if not alpha_eqv(t1["children"][0], t2["children"][0]):
#                 return False
#             pass
#         case "type":
#             pass

# termに自由出現する変数frmをtoで置き換える
# def subst_var(term, frm, to):
#     tag = term["tag"]
#     match tag:
#         case "var":
#             if term["name"] == frm:
#                 return { "tag": "var", "name": to }
#             else:
#                 return term
#         case x if x in ["star", "sort"]:
#             return term
#         case "app":
#             return {
#                 "tag": "app",
#                 "children": list(map(lambda t: subst_var(t, frm, to), term["children"]))
#             }
#         case "const":
#             return {
#                 "tag": "const",
#                 "op": term["op"],
#                 "children": list(map(lambda t: subst_var(t, frm, to), term["children"]))
#             }
#         case x if x in ["lambda", "type"]:
#             if term["var"] == frm:
#                 children = term["children"]
#                 return {
#                     "tag": term["tag"],
#                     "var": term["var"],
#                     "children": [subst_var(children[0], frm, to),children[1]]
#                 }
#             else:
#                 return {
#                     "tag": term["tag"],
#                     "var": term["var"],
#                     "children": list(map(lambda t: subst_var(t, frm, to), term["children"]))
#                 }
#         case x:
#             raise f"Error at subst_var: unexpected term: {x}"

