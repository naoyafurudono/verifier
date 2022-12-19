#!/usr/local/bin/python3

# NOTE 構文チェックが緩い

import re
import pprint as pp
import argparse

# ファイルを読んで、1行目が項であるかを判定する
def run():
    apaser = argparse.ArgumentParser(prog = '20221212')
    apaser.add_argument('filename')
    args = apaser.parse_args()
    filename = args.filename
    with open(filename,'r') as f:
        code = f.readline()
    # code = "%($x:(@).(*))(@)"
    # code = "$x:(@).(*)"
    # code = "x"
    # code = "*"
    # code = "%(*)(@)"
    # code = "$x:(*).(@)"
    # code1 = "co[($x:(@).(*))]"
    # code2 = f"co[($x:({code1}).(*))]"
    # code3 = f"co[($x:({code2}).({code2}))]"
    # code = code2
    try:
        term = parse_term(code)
        print("succeed")
        pp.pprint(term)
    except (SyntaxError) as e:
        print('fail')
        print(e)


class SyntaxError(Exception):
    pass

# 項を構文解析する。失敗したら例外を投げる
def parse_term(code):
    if is_var(code):
        return {"tag": "var", "name": code}
    if is_star(code):
        return {"tag": "star"}
    if is_sort(code):
        return {"tag": "sort"}
    if is_app(code):
        code1, end = find_first_term(code)
        code2, _ = find_first_term(code[end:])
        t1 = parse_term(code1)
        t2 = parse_term(code2)
        return {"tag": "app", "children": [t1, t2]}
    if is_lambda(code):
        var = code[1]
        code1, end = find_first_term(code)
        if not code[end] == ".":
            raise SyntaxError(f"parsing lambda in {code}\nexpect: '.', found: {code[end]}\n")
        code2, _ = find_first_term(code[end:])
        t1 = parse_term(code1)
        t2 = parse_term(code2)
        return {"tag": "lambda", "children": [t1, t2], "var": var}
    if is_type(code):
        var = code[1]
        code1, end = find_first_term(code)
        if not code[end] == ".":
            raise SyntaxError(f"parsing type in {code}\nexpect: '.', found: {code[end]}\n")
        code2, _ = find_first_term(code[end:])
        return {
            "tag": "type",
            "children": [code1, code2],
            "var": var
        }
    if is_const(code):
        op_name = get_op_name(code)
        start = 0
        code_list = []
        while True:
            code1, next_start = find_first_term(code[start:])
            if next_start == 0:
                break
            code_list.append(code1)
            start = next_start
        term_list = list(map(lambda code: parse_term(code), code_list))
        return {"tag": "const", "children": term_list, "op": op_name}

op_name_re = re.compile("([a-zA-Z0-9][a-zA-Z0-9_]+)\[")
def get_op_name(code):
  return code.split("[")[0]

def find_first_term(code):
    # 初めのかっこで正しく囲まれたコードを返す。
    # かっこの終わった次のインデックスも同時に返す
    # 該当する式がない場合、第二返り値を0とする
    # e.g. %((M))(N)  --> (M)
    count = 0
    start = -1
    end = -1
    for i in range(len(code)):
        if code[i] == "(":
            count += 1
            if start == -1:
                start = i

        if code[i] == ")":
            count -= 1
            if count == 0:
                end = i
                break
    return code[start+1:end], end+1

var_re = re.compile("^[a-zA-Z]$")
def is_var(code):
    return var_re.match(code)
def is_star(code):
  return code == "*"
def is_sort(code):
    return code == "@"
def is_app(code):
    return code[0] == "%"
def is_lambda(code):
    return code[0] == "$"
def is_type(code):
    return code[0] == "?"
op_name_re = re.compile("^[a-zA-Z][a-zA-Z0-9_]*$")
def is_const(code):
    op_name = code.split("[")[0]
    return op_name_re.match(op_name)

if __name__ == "__main__":
    run()
