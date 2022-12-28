# parse.py
# Termとその生成関数（parse_term）を定義する

from typing import Tuple
import re
import argparse
from dataclasses import dataclass

from alpha_eqv import alpha_eqv


@dataclass
class Term:
    def __eq__(self, that):
        return alpha_eqv(self, that)

    def __str__(self) -> str:
        return f"TODO {self.__class__.__name__}"


@dataclass
class VarTerm(Term):
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass
class StarTerm(Term):
    def __str__(self) -> str:
        return "*"


@dataclass
class SortTerm(Term):
    def __str__(self) -> str:
        return "@"


@dataclass
class AppTerm(Term):
    t1: Term
    t2: Term

    def __str__(self) -> str:
        s1 = self.t1.__str__()
        s2 = self.t2.__str__()
        return f"%({s1})({s2})"


@dataclass
class LambdaTerm(Term):
    t1: Term
    t2: Term
    name: str

    def __str__(self) -> str:
        s1 = self.t1.__str__()
        s2 = self.t2.__str__()
        return f"${self.name}:({s1}).({s2})"


@dataclass
class PiTerm(Term):
    t1: Term
    t2: Term
    name: str

    def __str__(self) -> str:
        s1 = self.t1.__str__()
        s2 = self.t2.__str__()
        return f"?{self.name}:({s1}).({s2})"


@dataclass
class ConstTerm(Term):
    op: str
    children: list[Term]


class SyntaxError(Exception):
    pass


class UnExpectedTermError(Exception):
    pass


def parse_term(code: str) -> Term:
    # 失敗したらSyntaxErrorを投げる
    if is_var(code):
        return VarTerm(name=code)
    if is_star(code):
        return StarTerm()
    if is_sort(code):
        return SortTerm()
    if is_app(code):
        code1, end = find_first_term(code)
        code2, _ = find_first_term(code[end:])
        t1 = parse_term(code1)
        t2 = parse_term(code2)
        return AppTerm(t1, t2)
    if is_lambda(code):
        var = code[1]
        code1, end = find_first_term(code)
        if not code[end] == ".":
            raise SyntaxError(
                f"parsing lambda in {code}\nexpect: '.', found: {code[end]}\n")
        code2, _ = find_first_term(code[end:])
        t1 = parse_term(code1)
        t2 = parse_term(code2)
        return LambdaTerm(t1, t2, var)
    if is_type(code):
        var = code[1]
        code1, end = find_first_term(code)
        if not code[end] == ".":
            raise SyntaxError(
                f"parsing type in {code}\nexpect: '.', found: {code[end]}\n")
        code2, _ = find_first_term(code[end:])
        t1 = parse_term(code1)
        t2 = parse_term(code2)
        return PiTerm(t1, t2, var)
    if is_const(code):
        op_name = get_op_name(code)
        fresh_code = code
        code_list = []
        while True:
            code1, next_start = find_first_term(fresh_code)
            if next_start == 0:
                if fresh_code[next_start] != "]":
                    raise SyntaxError(
                        f"`{fresh_code}` {next_start} {fresh_code[next_start]}")
                break
            if not fresh_code[next_start] in [",", "]"]:
                raise SyntaxError(f"`{fresh_code}` {next_start}")
            code_list.append(code1)
            fresh_code = fresh_code[next_start:]
        term_list = list(map(lambda code: parse_term(code), code_list))
        return ConstTerm(op_name, term_list)
    raise SyntaxError(f"マッチする式がない: {code}")


op_name_re = re.compile("([a-zA-Z0-9][a-zA-Z0-9_]+)\\[")


def get_op_name(code: str):
    return code.split("[")[0]


def find_first_term(code: str) -> Tuple[str, int]:
    # 初めのかっこで正しく囲まれたコードを返す。
    # かっこの終わった次のインデックスも同時に返す
    # 該当する式がない場合、第二返り値を0とする
    # e.g. %((M))(N)  --> (M), 5
    # idx: 012345
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


def is_var(code: str):
    return var_re.match(code)


def is_star(code: str):
    return code == "*"


def is_sort(code: str):
    return code == "@"


def is_app(code: str):
    return code[0] == "%"


def is_lambda(code: str):
    return code[0] == "$"


def is_type(code: str):
    return code[0] == "?"


op_name_re = re.compile("^[a-zA-Z][a-zA-Z0-9_]*$")


def is_const(code: str):
    op_name = code.split("[")[0]
    return op_name_re.match(op_name)


if __name__ == "__main__":
    apaser = argparse.ArgumentParser(prog='20221212')
    apaser.add_argument('filename')
    args = apaser.parse_args()
    filename = args.filename
    with open(filename, 'r') as f:
        code = f.readline()
    try:
        term = parse_term(code)
        print("succeed")
        print(term)
    except (SyntaxError) as e:
        print('fail')
        print(e)
