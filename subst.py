from fresh_name import Fresh
import argparse


def run():
    from parse import parse_term
    import re
    from to_string import to_string
    apaser = argparse.ArgumentParser(prog='subst')
    apaser.add_argument('filename')
    args = apaser.parse_args()
    filename = args.filename
    with open(filename, 'r') as f:
        code1 = f.readline()
        name = re.match("[a-zA-Z]", f.readline()).group(0)
        code2 = f.readline()
    try:
        term1 = parse_term(code1)
        term2 = parse_term(code2)
    except (SyntaxError) as e:
        print('syntax error')
        print(e)

    print(to_string(subst(term1, term2, name)))

# t1[name:=t2]


def subst(t1, t2, name):
    match t1["tag"]:
        case "var":
            if t1["name"] == name:
                return t2
            else:
                return t1
        case x if x in ["lambda", "type"]:
            t10 = subst(t1["children"][0], t2, name)
            if t1["var"] == name:
                return {
                    "tag": t1["tag"],
                    "var": t1["var"],
                    "children": [
                        t10, t1["children"][1]
                    ]
                }
            else:
                fresh_name = Fresh.fresh()
                t11 = subst(subst_fresh(
                    t1["children"][1], t1["var"], fresh_name), t2, name)
                return {
                    "tag": t1["tag"],
                    "var": fresh_name,
                    "children": [
                        t10, t11
                    ]
                }
        case "app":
            return {
                "tag": "app",
                "children": list(map(lambda t: subst(t, t2, name), t1["children"]))
            }
        case "const":
            return {
                "tag": "const",
                "op": t1["op"],
                "children": list(map(lambda t: subst(t, t2, name), t1["children"]))
            }
        case x if x in ["sort", "star"]:
            return t1

# toがフレッシュな変数名であることを仮定する。
# t[frm:=to]


def subst_fresh(t, frm, to):
    match t["tag"]:
        case "var":
            if t["name"] == frm:
                return {
                    "tag": "var",
                    "name": to
                }
            else:
                return t
        case x if x in ["lambda", "type"]:
            if t["var"] == frm:
                return {
                    "tag": t["tag"],
                    "var": t["var"],
                    "children": [
                        subst_fresh(t["children"][0], frm, to),
                        t["children"][1]
                    ]
                }
            else:
                return {
                    "tag": t["tag"],
                    "var": t["var"],
                    "children": list(map(lambda t1: subst_fresh(t1, frm, to), t["children"]))
                }
        case "app":
            return {
                "tag": "app",
                "children": list(map(lambda t: subst_fresh(t, frm, to), t["children"]))
            }
        case "const":
            return {
                "tag": "const",
                "op": t["op"],
                "children": list(map(lambda t: subst_fresh(t, frm, to), t["children"]))
            }

        case x if x in ["sort", "star"]:
            return t


def subst_in_one_sweep(t, env):
    # env : {var_name !--> term}
    # tにenvを同時代入した結果を返す
    match t["tag"]:
        case "var":
            if t["name"] in env:
                return {
                    "tag": "var",
                    "name": env[t["name"]]
                }
            else:
                return t
        case x if x in ["lambda", "type"]:
            env2 = env.copy()
            if t["var"] in env2:
                del env2[t["var"]]
            fresh_name = Fresh.fresh()
            return {
                "tag": t["tag"],
                "var": fresh_name,
                "children": [
                    subst_in_one_sweep(t["children"][0], env2),
                    subst_in_one_sweep(subst_fresh(t["children"][1], t["var"], fresh_name), env2)
                ]
            }
        case "app":
            return {
                "tag": "app",
                "children": list(map(lambda t: subst_in_one_sweep(t, env), t["children"]))
            }
        case "const":
            return {
                "tag": "const",
                "op": t["op"],
                "children": list(map(lambda t: subst_in_one_sweep(t, env), t["children"]))
            }

        case x if x in ["sort", "star"]:
            return t


if __name__ == "__main__":
    run()
