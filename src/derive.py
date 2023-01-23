# automakeに対応
# 定義の列は依存関係でトポロジカルソートされていると仮定する

"""
上から定義を見ていって、
def, def-primに従ってデルタを拡張していく。
それぞれの導出規則は、deltaを順次増やす以外は環境を空、K, Lが*,sortとする。
そうすると、最終的なデルタを得たときにそこまでの導出木を生成しやすい。
"""

from typing import Tuple
from check import Context, Definition, bd_eqv, normalize
from inst import (
    AbstInst,
    ApplInst,
    DefInst,
    EndInst,
    FormInst,
    InstInst,
    Instruction,
    SortInst,
    VarInst,
    WeakInst,
)
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
from subst import subst, subst_all


class DeriveError(Exception):
    pass


def fmtDeriveError(msg: str, term: Term) -> DeriveError:
    return DeriveError(f"{msg}\nterm: {term}")


def prove_def(
    dfn: Definition, env: list[Definition], insts: list[Instruction]
) -> list[Instruction]:
    # 単一の定義と、環境を受け取って定義本体の導出木を生成するinstの列を返す
    # 返すinstの行番号はindexからつけ始める
    initial = len(insts) - 1
    if dfn.is_prim:
        insts, prop, pr_index = prove_term(env, dfn.context, dfn.prop, insts, initial)
        if not is_s(prop):
            raise fmtDeriveError("must be sort for prim def", dfn.prop)
        insts.append(DefInst(len(insts), initial, pr_index, dfn.op))
        return insts
    else:
        insts, prop, pr_index = prove_term(env, dfn.context, dfn.body, insts, initial)
        if not check_abd_eqv(prop, dfn.prop, env):
            # print(f"{prop=}\n{dfn=}")
            raise fmtDeriveError("fail to derive expected property", dfn.prop)
        insts.append(DefInst(len(insts), initial, pr_index, dfn.op))
        return insts


def check_abd_eqv(t1: Term, t2: Term, env: list[Definition]) -> bool:
    return t1 == t2 or bd_eqv(t1, t2, env)


def assert_index(insts: list[Instruction], base: int, actual: int):
    if not base + len(insts) == actual:
        raise Exception(f"insts len: {len(insts)}\n{base=}\n{actual=}")


def prove_term(
    env: list[Definition],
    ctx: Context,
    t: Term,
    insts: list[Instruction],
    index_for_sort: int,
) -> Tuple[list[Instruction], Term, int]:
    # 返すのは
    #   証明列、示した命題、命題を示したインデックス
    if isinstance(t, SortTerm):
        raise fmtDeriveError("sort cannot be typed", t)
    if isinstance(t, StarTerm):
        if ctx.is_empty:
            return insts, SortTerm(), index_for_sort
        else:
            mb_tuple = ctx.get_last()
            if not mb_tuple:
                raise fmtDeriveError("internal", t)
            name, tp = mb_tuple
            head = ctx.get_ahead()
            if not head:
                raise fmtDeriveError("internal", t)
            insts, prop1, pr_index1 = prove_term(env, head, t, insts, index_for_sort)
            insts, prop2, pr_index2 = prove_term(env, head, tp, insts, index_for_sort)
            insts.append(WeakInst(len(insts), pr_index1, pr_index2, name))
            return insts, prop1, len(insts) - 1
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
            insts, prop1, pr_index1 = prove_term(env, head, t, insts, index_for_sort)
            insts, prop2, pr_index2 = prove_term(env, head, tp, insts, index_for_sort)
            insts.append(WeakInst(len(insts), pr_index1, pr_index2, name))
            return insts, prop1, len(insts) - 1
        else:
            mb_ctx = ctx.get_ahead()
            if not mb_ctx:
                raise fmtDeriveError("empty ctx", t)
            else:
                insts, prop, pr_index = prove_term(
                    env, mb_ctx, tp, insts, index_for_sort
                )
                insts.append(VarInst(len(insts), pr_index, t))
                return insts, tp, len(insts) - 1
    if isinstance(t, AppTerm):
        insts, prop1, pr_index1 = prove_term(env, ctx, t.t1, insts, index_for_sort)
        insts, prop2, pr_index2 = prove_term(env, ctx, t.t2, insts, index_for_sort)
        n1 = normalize(prop1, env)
        print("TODO use conv rule")
        if not isinstance(n1, PiTerm):
            raise fmtDeriveError("must have Pi term", t.t1)
        else:
            if not check_abd_eqv(n1.t1, prop2, env):
                raise fmtDeriveError("fail to check eqv", t)
            print("TODO use conv rule")
            insts.append(ApplInst(len(insts), pr_index1, pr_index2))
            return (insts, subst(n1.t2, t.t2, n1.name), len(insts) - 1)
    if isinstance(t, LambdaTerm):
        insts, prop1, pr_index1 = prove_term(
            env, ctx.extend(t.name, t.t1), t.t2, insts, index_for_sort
        )
        prop = PiTerm(t.t1, prop1, t.name)
        insts, prop2, pr_index2 = prove_term(env, ctx, prop, insts, index_for_sort)
        if not is_s(prop2):
            raise fmtDeriveError("must be a sort", prop2)
        insts.append(AbstInst(len(insts), pr_index1, pr_index2))
        return insts, prop, len(insts) - 1
    if isinstance(t, ConstTerm):
        insts, prop1, pr_index1 = prove_term(
            env, ctx, StarTerm(), insts, index_for_sort
        )
        if not isinstance(prop1, SortTerm):
            raise fmtDeriveError("must be sort", prop1)
        dfn_i, dfn = next((i, dfn) for (i, dfn) in enumerate(env) if dfn.op == t.op)
        pres: list[int] = []
        names, tps = dfn.context.names_tps()
        for i, u in enumerate(t.children):
            insts, prop_u, pr_index_u = prove_term(env, ctx, u, insts, index_for_sort)
            pres.append(pr_index_u)
            if not check_abd_eqv(
                prop_u, subst_all(tps[i], names[:i], t.children[:i]), env
            ):
                raise fmtDeriveError("type not matched", t)
        insts.append(
            InstInst(len(insts), pr_index1, len(dfn.context.container), pres, dfn_i)
        )
        return insts, subst_all(dfn.prop, names, tps), len(insts) - 1
    if isinstance(t, PiTerm):
        insts, prop1, pr_index1 = prove_term(env, ctx, t.t1, insts, index_for_sort)
        if not is_s(prop1):
            raise fmtDeriveError("must be a sort", t.t1)
        insts, prop2, pr_index2 = prove_term(
            env, ctx.extend(t.name, t.t1), t.t2, insts, index_for_sort
        )
        if not is_s(prop2):
            raise fmtDeriveError("must be a sort", t.t2)
        insts.append(FormInst(len(insts), pr_index1, pr_index2))
        return insts, prop2, len(insts) - 1
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
        m: Term = VarTerm(
            "# MESSAGE: this is not regular term, but a place holder for axiom"
        )
        prim_flag = True
    else:
        m = parse_term(lines[l])
        prim_flag = False
    l += 1
    n = parse_term(lines[l])
    l += 1
    if lines[l] != "edef2" or l + 1 != len(lines):
        raise fmtErr(f"internal error: bad end of definition {lines=} {l=} {lines[l]=}")

    return Definition(op, Context(binds), m, n, is_prim=prim_flag)


if __name__ == "__main__":
    import argparse

    apaser = argparse.ArgumentParser(prog="automake")
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
    dfns: list[Definition] = []
    for ds in filter(lambda x: len(x) > 1, dfn_scripts):
        try:
            dfns.append(parse_script(ds))
        except Exception as e:
            import traceback

            traceback.print_exc()
            print(f"at: {ds=}")
            exit(1)
    instructions: list[Instruction] = [SortInst(0)]
    for i, dfn in enumerate(dfns):
        print()
        try:
            tpsss = set()
            instructions = prove_def(dfn, dfns[:i], instructions)
            print(tpsss)
        except Exception as e:
            print(tpsss)
            for iss in instructions:
                print(iss)

            raise e
    instructions.append(EndInst(-1))
    for inst in instructions:
        print(inst)
