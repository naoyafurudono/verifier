# 2022-12-19

# deriv_treesが既存の導出木の列だとしたとき、
# instで構成される新しい導出木をderiv_treeにappendした列を返す
from parse import parse_term
from to_string import to_string


def run():
    import argparse
    from pprint import pprint
    apaser = argparse.ArgumentParser(prog='verify')
    apaser.add_argument('filename')
    args = apaser.parse_args()
    filename = args.filename
    with open(filename, 'r') as f:
        trees = []
        for line in f.readlines():
            inst = scan_inst(line.replace("\n", ""))
            trees = verif(inst, trees)
    for i, tree in enumerate(trees):
        print(show_conseq(i,tree))


def show_conseq(lnum, tree):
    return f"{lnum} : {show_env(tree['environment'])} ; {show_ctx(tree['context'])} |- {show_proof(tree['proof'])} : {show_prop(tree['prop'])}"


def show_env(env):
    return "todo"


def show_ctx(ctx):
    return ", ".join(map(lambda binding: f"{to_string(binding[0])}:{to_string(binding[1])}", ctx))


def show_proof(proof):
    return to_string(proof)


def show_prop(prop):
    return to_string(prop)


def verif(inst, conseqs):
    # 今回処理する命令（適用する推論規則とパラメータ）をすでに得られている
    # 結論のリストconseqsのもとで処理する。得られた結論をappendしたリストを返す。
    match inst["tag"]:
        case "sort":
            conseq = {
                "environment": [],
                "context": [],
                "proof": parse_term("*"),
                "prop": parse_term("@"),
            }
        case "var":
            premise_id = inst["pre"]
            premise = conseqs[premise_id]
            var = inst["var"]
            ctx = premise["context"].copy()
            ctx.append((var, premise["proof"]))
            conseq = {
                "environment": premise["environment"],
                "context": ctx,
                "proof": var,
                "prop": premise["proof"],
            }
        case "weak":
            premise1 = conseqs[inst["pre1"]]
            premise2 = conseqs[inst["pre2"]]
            var = inst["var"]
            # TODO check x \not \in \Gamma
            if not (premise1["environment"] == premise2["environment"] and premise1["context"] == premise2["context"]):
                print("error: env and context must match")
                exit(1)
            ctx = premise1["context"].copy()
            ctx.append((var, premise2["proof"]))
            conseq = {
                "environment": premise1["environment"],
                "context": ctx,
                "proof": premise1["proof"],
                "prop": premise1["prop"],
            }
        case "form":
            premise1 = conseqs[inst["pre1"]]
            premise2 = conseqs[inst["pre2"]]
            if not (premise1["environment"] == premise2["environment"] and
                    premise1["context"] == premise2["context"][:-1] and
                    premise1["proof"] == premise2["context"][-1][1]):  # 型Aが一致する
                print("error: env and context must match")
                exit(1)
            conseq = {
                "environment": premise1["environment"],
                "context": premise1["context"],
                "proof": {
                    "tag": "type",
                    "children": [
                        premise1["proof"],
                        premise2["proof"]
                    ],
                    "var": to_string(premise2["context"][-1][0])
                },
                "prop": premise2["prop"],

            }
        case "appl":

            pass
        case "abst":
            pass
        case "def":
            pass
        case "inst":
            pass
        case x if x in ["conv", "def-prim", "inst-prim"]:
            print(f"not implemented yet: {x}")
            exit(1)
        case "end":
            return conseqs
    res = conseqs.copy()
    res.append(conseq)
    return res


def scan_inst(inst_code: str):
    # https://www.kurims.kyoto-u.ac.jp/~tshun/ex20221208A
    # 上の例の一行が入力のinst_codeに対応する。
    # inst_codeをverifが処理する形式に変換する
    tokens = inst_code.split(" ")
    if len(tokens) == 0:
        exit(1)
    lnum = int(tokens[0])
    if lnum == -1:
        return {
            "tag": "end"
        }
    if len(tokens) == 1:
        exit(1)
    tag = tokens[1]
    res = {
        "tag": tag,
        "lnum": lnum
    }
    match tag:
        case "sort":
            # l "sort"
            pass
        case "var":
            # l "var" m var-name
            res["pre"] = int(tokens[2])
            res["var"] = parse_term(tokens[3])
        case "weak":
            # l weak m n var-name
            res["pre1"] = int(tokens[2])
            res["pre2"] = int(tokens[3])
            res["var"] = parse_term(tokens[4])
        case "form":
            # l form m n
            res["pre1"] = int(tokens[2])
            res["pre2"] = int(tokens[3])
        case "appl":
            res["pre1"] = int(tokens[2])
            res["pre2"] = int(tokens[3])
        case "abst":
            res["pre1"] = int(tokens[2])
            res["pre2"] = int(tokens[3])
        case "def":
            res["pre1"] = int(tokens[2])
            res["pre2"] = int(tokens[3])
            res["const-name"] = tokens[4]
        case "inst":
            res["pre"] = int(tokens[2])
            length = int(tokens[3])
            res["pres"] = list(map(int, tokens[4:4+length]))
            res["def"] = int(tokens[-1])
    return res


if __name__ == "__main__":
    run()
