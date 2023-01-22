# automakeに対応
# 定義の列は依存関係でトポロジカルソートされていると仮定する

"""
上から定義を見ていって、
def, def-primに従ってデルタを拡張していく。
それぞれの導出規則は、deltaを順次増やす以外は環境を空、K, Lが*,sortとする。
そうすると、最終的なデルタを得たときにそこまでの導出木を生成しやすい。
"""

from typing import Tuple
from check import Context, Definition, bd_eqv
from inst import AbstInst, ApplInst, DefInst, EndInst, Instruction, VarInst, WeakInst
from parse import (
    AppTerm,
    ConstTerm,
    LambdaTerm,
    PiTerm,
    SortTerm,
    StarTerm,
    Term,
    VarTerm,
    parse_term,
)
from subst import subst


class DeriveError(Exception):
    pass


def fmtDeriveError(msg: str, term: Term) -> DeriveError:
    return DeriveError(f"{msg}\nterm: {term}")


def prove_def(dfn: Definition, env: list[Definition], index: int) -> list[Instruction]:
    # 単一の定義と、環境を受け取って定義本体の導出木を生成するinstの列を返す
    # 返すinstの行番号はindexからつけ始める
    if dfn.is_prim:
        insts, prop, next_index = prove_term(env, dfn.context, dfn.prop, index, index - 1)
        if not is_s(prop): raise fmtDeriveError("must be sort for prim def", dfn.prop)
        insts.append(DefInst(next_index, index-1, next_index-1,dfn.op))
        return insts
    else:
        insts, prop, next_index = prove_term(env, dfn.context, dfn.body, index, index - 1)
        if not check_abd_eqv(prop, dfn.prop, env):
            raise fmtDeriveError("fail to derive expected property", dfn.prop)
        insts.append(DefInst(next_index, index-1, next_index-1,dfn.op))
        return insts


def check_abd_eqv(t1: Term, t2: Term, env: list[Definition]) -> bool:
    return t1 == t2 or bd_eqv(t1, t2, env)


def prove_term(
    env: list[Definition],
    ctx: Context,
    t: Term,
    current_index: int,
    index_for_sort: int,
) -> Tuple[list[Instruction], Term, int]:
    # 返すのは
    #   証明列、示した命題、次に使えるインデックス
    if isinstance(t, SortTerm):
        raise fmtDeriveError("sort cannot be typed", t)
    if isinstance(t, StarTerm):
        # 1. weak を無限に呼んで環境を空にする。
        # 2. このdefinitionの直前のinstとつなげる。
        # 以上を下から順番に行うと、ほしいinstの列を構成できる
        if len(ctx.container) == 0:
            raise fmtDeriveError("internal", t)
        if len(ctx.container) == 1:
            mb_tuple = ctx.get_last()
            if not mb_tuple:
                raise fmtDeriveError("internal", t)
            name, tp = mb_tuple
            head = ctx.get_ahead()
            if not head:
                raise fmtDeriveError("internal", t)
            else:
                # use (weak)
                insts, prop, next_index = prove_term(
                    env, head, tp, current_index, index_for_sort
                )
                insts.append(
                    WeakInst(current_index, index_for_sort, next_index - 1, name)
                )
                return insts, prop, next_index + 1
    if isinstance(t, VarTerm):
        mb_tuple = ctx.get_last()
        if not mb_tuple:
            raise fmtDeriveError("no binding found", t)
        name, tp = mb_tuple
        if name != t.name:
            # use (weak)
            head = ctx.get_ahead()
            if not head:
                raise fmtDeriveError("ctx too short", t)
            insts, prop, next_index = prove_term(
                env, head, t, current_index, index_for_sort
            )
            insts.append(WeakInst(current_index, index_for_sort, next_index - 1, name))
            return insts, prop, next_index + 1
        else:
            mb_ctx = ctx.get_ahead()
            if not mb_ctx:
                raise fmtDeriveError("empty ctx", t)
            else:
                insts, prop, next_index = prove_term(
                    env, mb_ctx, tp, current_index, index_for_sort
                )
                insts.append(VarInst(next_index, next_index - 1, t))
                return insts, prop, next_index + 1
    if isinstance(t, AppTerm):
        insts1, prop1, next_index1 = prove_term(
            env, ctx, t.t1, current_index, index_for_sort
        )
        insts2, prop2, next_index2 = prove_term(
            env, ctx, t.t2, next_index1, index_for_sort
        )
        if not isinstance(prop1, PiTerm):
            raise fmtDeriveError("must have Pi term", t.t1)
        else:
            # TODO: bd/同値を使った場合にconvを追加する
            if not check_abd_eqv(prop1.t1, prop2, env):
                raise fmtDeriveError("fail to check eqv", t)
            insts1.extend(insts2)
            insts1.append(ApplInst(next_index2, next_index1 - 1, next_index2 - 1))
            return insts1, subst(prop1.t2, t.t2, prop1.name), next_index2 + 1
    if isinstance(t, LambdaTerm):
        insts1, prop1, next_index1 = prove_term(
            env, ctx.extend(t.name, t.t1), t.t2, current_index, index_for_sort
        )
        prop = PiTerm(t.t1, prop1, t.name)
        insts2, prop2, next_index2 = prove_term(
            env, ctx, prop, next_index1, index_for_sort
        )
        if not is_s(prop2):
            raise fmtDeriveError("must be a sort", prop2)
        insts1.extend(insts2)
        insts1.append(AbstInst(next_index2, next_index1 - 1, next_index2 - 1))
        return insts1, prop, next_index2 + 1
    if isinstance(t, ConstTerm):
        raise Exception(f"TODO {t}\n not defined yet")
    if isinstance(t, PiTerm):
        raise Exception(f"TODO {t}\n not defined yet")
    raise Exception(f"forget to implement {t}\n not defined yet")


def is_s(t: Term) -> bool:
    return isinstance(t, SortTerm) or isinstance(t, StarTerm)


class ParseDefinitionError(Exception):
    pass


def fmtErr(msg: str) -> ParseDefinitionError:
    return ParseDefinitionError(msg)


def parse_script(lines: list[str]) -> Definition:
    """
    lines はdef2から始まって、edef2で終わる各行の文字列のリスト。
    各文字列は改行を__含まない__
    ```
    def2
    n
    x1
    A1
    ...
    xn
    An
    c
    M
    N
    edef2
    ```
    これをDefinitionに変換する
    名前がcで、環境がx1:A1,...,xn:An、定義の本体がMでその型がNであるようなDefinition
    """
    l = 0
    if lines[l] != "def2" or lines[-1] != "edef2":
        raise fmtErr("def2 or edf2 key words not found")
    l += 1
    arity = int(lines[l])
    l += 1
    binds: list[tuple[str, Term]] = []
    for _ in range(arity):
        binds.append((lines[l], parse_term(lines[l + 1])))
        l += 2
    op = lines[l]
    l += 1
    if lines[l] == "#":
        M: Term = VarTerm(
            "# MESSAGE: this is not regular term, but a place holder for axiom"
        )
        prim_flag = True
    else:
        M = parse_term(lines[l])
        prim_flag = False
    l += 1
    N = parse_term(lines[l])
    l += 1
    if lines[l] != "edef2" or l + 1 != len(lines):
        raise fmtErr(f"internal error: bad end of definition {lines=} {l=} {lines[l]=}")

    return Definition(op, Context(binds), M, N, is_prim=prim_flag)


if __name__ == "__main__":
    import argparse

    apaser = argparse.ArgumentParser(prog="20221212")
    apaser.add_argument("filename")
    args = apaser.parse_args()
    filename = args.filename

    with open(filename, "r") as f:
        lines = f.readlines()
    dfn_scripts: list[list[str]] = []
    dfn_script: list[str] = []
    for line in lines:
        line = line[:-1]
        if line == "":
            dfn_scripts.append(dfn_script)
            dfn_script = []
        else:
            dfn_script.append(line)
    dfns = []
    for ds in filter(lambda x: len(x) > 1, dfn_scripts):
        try:
            dfns.append(parse_script(ds))
        except Exception as e:
            import traceback

            traceback.print_exc()
            print(f"at: {ds=}")
            exit(1)
    instructions: list[list[Instruction]] = []
    instruction_index = 0
    for i, dfn in enumerate(dfns):
        print(dfn)
        insts = prove_def(dfn, dfns[:i], instruction_index)
        instructions.append(insts)
        instruction_index += len(insts)
    instructions.append([EndInst(-1)])
    for insts in instructions:
        for inst in insts:
            print(inst)
