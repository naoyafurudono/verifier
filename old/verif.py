# 2022-12-19

# deriv_treesが既存の導出木の列だとしたとき、
# instで構成される新しい導出木をderiv_treeにappendした列を返す
import pprint

from alpha_eqv import alpha_eqv
from parse import parse_term
from subst import subst, subst_in_one_sweep
from to_string import to_string


def run():
    import argparse
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
        print(show_conseq(i, tree))


class TypeError(Exception):
    pass


def show_conseq(lnum, tree):
    return f"{lnum} : {show_env(tree['environment'])} ; {show_ctx(tree['context'])} |- {show_proof(tree['proof'])} : {show_prop(tree['prop'])}"


def show_env(env):
    return ", ".join(map(show_definition, env))


def show_ctx(ctx):
    return ", ".join(map(lambda binding: f"{to_string(binding[0])}:{to_string(binding[1])}", ctx))


def show_proof(proof):
    return to_string(proof)


def show_prop(prop):
    return to_string(prop)


def verif(inst, conseqs):
    # INST * CONSEQ --> CONSEQ[]
    # DATATYPE: CONSEQ
    # 今回処理する命令（適用する推論規則とパラメータ）をすでに得られている
    # 結論のリストconseqsのもとで処理する。得られた結論をappendしたリストを返す。
    print(inst["lnum"])
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
            if not (premise1["environment"] == premise2["environment"] and
                    premise1["context"] == premise2["context"]):
                raise TypeError("error: env and context must match")
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
                raise TypeError("error: env and context must match")
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
            premise1 = conseqs[inst["pre1"]]
            if premise1["prop"]["tag"] != "type":
                raise TypeError(
                    f"error at {inst['lnum']}: the proposition of first premise of (appl) must be Pai.\nfound: {premise1['prop']}")
            premise2 = conseqs[inst["pre2"]]
            param_type = premise1["prop"]["children"][0]
            if param_type != premise2["prop"]:
                raise TypeError(f"parameter type and argument type must agree")
            if not (premise1["environment"] == premise2["environment"] and
                    premise1["context"] == premise2["context"]):
                raise TypeError("error: env and context must match")
            conseq = {
                "environment": premise1["environment"],
                "context": premise1["context"],
                "proof": {
                    "tag": "app",
                    "children": [premise1["proof"], premise2["proof"]]
                },
                "prop": subst(premise1["prop"]["children"][1], premise2["prop"], premise1["prop"]["var"])
            }
        case "abst":
            premise1 = conseqs[inst["pre1"]]
            premise2 = conseqs[inst["pre2"]]
            if premise2["proof"]["tag"] != "type":
                raise TypeError(
                    f"error at {inst['lnum']}: the proposition of second premise of (abst) must be Pai.\nfound: {premise2['prop']}in\n{pprint.pformat( premise2)}")
            var_name = premise2["proof"]["var"]
            param_type = premise2["proof"]["children"][0]
            last_binding = premise1["context"][-1]
            if not (last_binding[0] == parse_term(var_name) and last_binding[1] == param_type):
                raise TypeError(
                    f"invalid extension of the context of the first premise")
            if premise1["prop"] != premise2["proof"]["children"][1]:
                raise TypeError(f"body type mismatch")
            if not (premise1["environment"] == premise2["environment"] and
                    premise1["context"][:-1] == premise2["context"]):
                raise TypeError("env and context must match")
            conseq = {
                "environment": premise2["environment"],
                "context": premise2["context"],
                "proof": {
                    "tag": "lambda",
                    "children": [param_type, premise1["proof"]],
                    "var": var_name

                },
                "prop": {
                    "tag": "type",
                    "children": [param_type, premise2["proof"]],
                    "var": var_name
                }
            }
        case "def":
            premise1 = conseqs[inst["pre1"]]
            premise2 = conseqs[inst["pre2"]]
            if premise1["environment"] != premise2["environment"]:
                raise TypeError("env must match")
            # TODO check a \not\in \Gamma
            env = premise1["environment"].copy()
            env.append(to_definition(inst["const-name"], premise2))
            conseq = premise1.copy()
            conseq["environment"] = env
        case "inst":
            premise = conseqs[inst["pre"]]
            if not (premise["proof"] == parse_term("*") and premise["prop"] == parse_term("@")):
                raise TypeError("inst first premise is not good")
            premises = list(map(lambda i: conseqs[i], inst["pres"]))
            if not all(map(lambda p: premise["environment"] == p["environment"] and premise["context"] == p["context"],
                           premises)):
                raise TypeError("env and ctx must agree")
            # TODO 引数の検査
            defs = premise["environment"]
            definition = defs[inst["const-name"]]
            params = list(
                map(lambda binding: binding[0], definition["context"]))
            args = list(map(lambda p: p["proof"], premises))
            env = dict(zip(map(to_string, params), args))
            conseq = {
                "environment": premise["environment"],
                "context": premise["context"],
                "proof": {
                    "tag": "const",
                    "op": definition["op"],
                    "children": args
                },
                "prop": subst_in_one_sweep(definition["prop"], env)
            }
        case "conv":
            premise1 = conseqs[inst["pre1"]]
            premise2 = conseqs[inst["pre2"]]
            if not (premise1["environment"] == premise2["environment"] and
                    premise1["context"] == premise2["context"]):
                raise TypeError("env and context must match")
            if not beta_eqv(premise1["prop"],  premise1["environment"], premise1["context"],
                            premise2["proof"], premise2["environment"], premise2["context"]):
                raise TypeError("non-beta equivalent term cannot be converted")
            conseq = {
                "environment": premise1["environment"],
                "context": premise1["context"],
                "proof": premise1["proof"],
                "prop": premise2["proof"]
            }
        case "cp":
            conseq = conseqs[inst["target"]]
            print(f"cp:\n{conseq}")
        case "sp":
            target = conseqs[inst["target"]]
            binding = target["context"][inst["bind"]]
            x = binding[0]
            t = binding[1]
            conseq = {
                "environment": target["environment"],
                "context": target["context"],
                "proof": x,
                "prop": t
            }
        case x if x in ["conv", "def-prim", "inst-prim"]:
            print(f"not implemented yet: {x}")
            exit(1)
        case "end":
            return conseqs
        case _:
            print(inst)
            raise FormatError("not defined yet")
    res = conseqs.copy()
    if not all(map(lambda d: is_definition(d), conseq["environment"])):
        print(conseq["environment"])
        raise "ouch"
    res.append(conseq)
    return res

def beta_eqv(t1, env1, ctx1, t2, env2, ctx2):
    # TODO beta等価かを判定する
    nf1 = normalize(t1, env1, ctx1)
    nf2 = normalize(t2, env2, ctx2)
    print("goo")
    pprint.pprint(t2)
    return alpha_eqv(nf1, nf2)

def normalize(t, env, ctx):
    # TODO beta-正規形に変換する
    match t["tag"]:
        case x if x in ["var", "star", "sort"]:
            return t
        case "app":
            t0 = t["children"][0]
            t1 = t["children"][1]
            nt0 = normalize(t0, env, ctx)
            nt1 = normalize(t1, env, ctx)
            if nt0["tag"] in  ["lambda"]:
                # 簡約して結果を正規化する
                pass
                return normalize() # 簡約した何か
            return {
                "tag": "app",
                "children": [nt0, nt1]
            }
        case tag if tag in ["lambda", "type"]:
            t0 = t["children"][0]
            t1 = t["children"][1]
            nt0 = normalize(t0, env, ctx)
            # TODO 変数名の付け替えが必要？
            nt1 = normalize(t1, env, ctx)
            return {
                "tag": tag,
                "children": [nt0, nt1],
                "var": t["var"]
            }
        case "const":
            nts = list(map(lambda t: normalize(t, env, ctx), t["children"]))
            df = env[list(map(lambda df: df["op"], env)).index(t["op"])]
            body = df["body"]
            print(f"body: {body}")
            return normalize(subst_in_one_sweep(body, dict(zip(map(lambda pair: to_string(pair[0]),  df["context"]), nts))), env, ctx)




def show_definition(df):
    return f"{show_ctx(df['context'])} |> {df['op']} := {to_string(df['body'])} : {to_string(df['prop'])}"

def to_definition(name, conseq):
    # DATATYPE: definition, D
    return {
        "op": name,
        "context": conseq["context"],
        "body": conseq["proof"],
        "prop": conseq["prop"]
    }

def is_definition(x):
    if not type(x) is dict:
        return False
    if not ("op" in x and "context" in x and "body" in x and "prop" in x):
        return False
    if not type(x["op"]) is str:
        return False
    if not is_context(x["context"]):
        return False
    if not is_term(x["body"]):
        return False
    if not is_term(x["prop"]):
        return False
    return True

def is_context(x):
    if not type(x) is list:
        print("bad ctx")
        return False
    return all(map(lambda binding: len(binding) == 2 and is_term(binding[0]) and is_term(binding[1]), x))

class FormatError(Exception):
    pass


def scan_inst(inst_code: str):
    # TODO dictリテラルを毎回書く。データ構造を一目で理解できないので
    # そもそもクラスで表現するかTypeScriptに乗り換えるのが素直かもしれない
    # DATATYPE: INST
    # https://www.kurims.kyoto-u.ac.jp/~tshun/ex20221208A
    # 上の例の一行が入力のinst_codeに対応する。
    # inst_codeをverifが処理する形式に変換する
    tokens = inst_code.split(" ")
    if len(tokens) == 0:
        raise FormatError("サイズ0の命令行")
    lnum = int(tokens[0])
    if lnum == -1:
        return {
            "tag": "end"
        }
    if len(tokens) == 1:
        raise FormatError(f"無効な命令 {inst_code}")
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
            res["const-name"] = int(tokens[-1])
            print(tokens)
        case "conv":
            # lnum "conv" m n
            res["pre1"] = int(tokens[2])
            res["pre2"] = int(tokens[3])
        case "cp":
            res["target"] = int(tokens[2])
        case "sp":
            res["target"] = int(tokens[2])
            res["bind"] = int(tokens[3])
        case _:
            raise FormatError(f"not defined yet {tokens[1]}")
    return res

def is_inst(inst_like):
    if not type(inst_like) is dict:
        return False
    if not "tag" in inst_like:
        return False
    match inst_like["tag"]:
        case x if x in ["sort", "star"]:
            return True
        case "var":
            return ("pre" in inst_like and "var" in inst_like and
                    inst_like["pre"] is int and is_term(inst_like["var"]))

    print("TODO verify.py: is_inst")
    return True

def is_term(term):
    print("TODO verify.py is_term")
    return True

if __name__ == "__main__":
    run()
