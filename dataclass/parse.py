# parse.py
# Termとその生成関数（parse_term）を定義する

from typing import Tuple
import re
import argparse
from dataclasses import dataclass


@dataclass(frozen=True)
class Term:
    def __eq__(self, that):
        return alpha_eqv(self, that)

    def __str__(self) -> str:
        return f"TODO {self.__class__.__name__}"


@dataclass(frozen=True)
class VarTerm(Term):
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class StarTerm(Term):
    def __str__(self) -> str:
        return "*"


@dataclass(frozen=True)
class SortTerm(Term):
    def __str__(self) -> str:
        return "@"


@dataclass(frozen=True)
class AppTerm(Term):
    t1: Term
    t2: Term

    def __str__(self) -> str:
        s1 = self.t1.__str__()
        s2 = self.t2.__str__()
        return f"%({s1})({s2})"


@dataclass(frozen=True)
class LambdaTerm(Term):
    t1: Term
    t2: Term
    name: str

    def __str__(self) -> str:
        s1 = self.t1.__str__()
        s2 = self.t2.__str__()
        return f"${self.name}:({s1}).({s2})"


@dataclass(frozen=True)
class PiTerm(Term):
    t1: Term
    t2: Term
    name: str

    def __str__(self) -> str:
        s1 = self.t1.__str__()
        s2 = self.t2.__str__()
        return f"?{self.name}:({s1}).({s2})"


@dataclass(frozen=True)
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
    if type(t1) != type(t2):
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
