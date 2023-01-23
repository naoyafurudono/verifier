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


def prove_def(dfn: Definition, env: list[Definition], index: int) -> list[Instruction]:
    # 単一の定義と、環境を受け取って定義本体の導出木を生成するinstの列を返す
    # 返すinstの行番号はindexからつけ始める
    if dfn.is_prim:
        insts, prop, pr_index, next_index = prove_term(
            env, dfn.context, dfn.prop, index, index - 1
        )
        if not is_s(prop):
            raise fmtDeriveError("must be sort for prim def", dfn.prop)
        insts.append(DefInst(next_index, index - 1, pr_index, dfn.op))
        return insts
    else:
        insts, prop, pr_index, next_index = prove_term(
            env, dfn.context, dfn.body, index, index - 1
        )
        if not check_abd_eqv(prop, dfn.prop, env):
            # print(f"{prop=}\n{dfn=}")
            print(f"dfn: {dfn}\nprop: {prop}")
            raise fmtDeriveError("fail to derive expected property", dfn.prop)
        insts.append(DefInst(next_index, index - 1, pr_index, dfn.op))
        return insts


def check_abd_eqv(t1: Term, t2: Term, env: list[Definition]) -> bool:
    return t1 == t2 or bd_eqv(t1, t2, env)


def prove_term(
    env: list[Definition],
    ctx: Context,
    t: Term,
    current_index: int,
    index_for_sort: int,
) -> Tuple[list[Instruction], Term, int, int]:
    if 24 <= current_index <= 26:
        print(f"{current_index=} {t}")
    global tpsss
    tpsss.add(type(t))
    # 返すのは
    #   証明列、示した命題、命題を示したインデックス、次に使えるインデックス
    if isinstance(t, SortTerm):
        raise fmtDeriveError("sort cannot be typed", t)
    if isinstance(t, StarTerm):
        if ctx.is_empty:
            return [], SortTerm(), index_for_sort, current_index
        else:
            mb_tuple = ctx.get_last()
            if not mb_tuple:
                raise fmtDeriveError("internal", t)
            name, tp = mb_tuple
            head = ctx.get_ahead()
            if not head:
                raise fmtDeriveError("internal", t)
            insts1, prop1, pr_index1, next_index1 = prove_term(
                env, head, t, current_index, index_for_sort
            )
            insts2, prop2, pr_index2, next_index2 = prove_term(
                env, head, tp, next_index1, index_for_sort
            )
            insts1.extend(insts2)
            insts1.append(WeakInst(next_index2, pr_index1, pr_index2, name))
            return insts1, prop1, next_index2, next_index2 + 1
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
            insts1, prop1, pr_index1, next_index1 = prove_term(
                env, head, t, current_index, index_for_sort
            )
            insts2, prop2, pr_index2, next_index2 = prove_term(
                env, head, tp, next_index1, index_for_sort
            )
            insts1.extend(insts2)
            insts1.append(WeakInst(next_index2, pr_index1, pr_index2, name))
            return insts1, prop1, next_index2, next_index2 + 1
        else:
            mb_ctx = ctx.get_ahead()
            if not mb_ctx:
                raise fmtDeriveError("empty ctx", t)
            else:
                insts, prop, pr_index, next_index = prove_term(
                    env, mb_ctx, tp, current_index, index_for_sort
                )
                insts.append(VarInst(next_index, pr_index, t))
                return insts, tp, next_index, next_index + 1
    if isinstance(t, AppTerm):
        insts1, prop1, pr_index1, next_index1 = prove_term(
            env, ctx, t.t1, current_index, index_for_sort
        )
        insts2, prop2, pr_index2, next_index2 = prove_term(
            env, ctx, t.t2, next_index1, index_for_sort
        )
        n1 = normalize(prop1, env)
        if not isinstance(n1, PiTerm):
            raise fmtDeriveError("must have Pi term", t.t1)
        else:
            if not check_abd_eqv(n1.t1, prop2, env):
                raise fmtDeriveError("fail to check eqv", t)
            # raise fmtDeriveError("# TODO: bd/同値を使った場合にconvを追加する", t)
            insts1.extend(insts2)
            insts1.append(ApplInst(next_index2, pr_index1, pr_index2))
            print(f"DEBUG {next_index1=} {next_index2=}")
            return (
                insts1,
                subst(n1.t2, t.t2, n1.name),
                next_index2,
                next_index2 + 1,
            )
    if isinstance(t, LambdaTerm):
        insts1, prop1, pr_index1, next_index1 = prove_term(
            env, ctx.extend(t.name, t.t1), t.t2, current_index, index_for_sort
        )
        prop = PiTerm(t.t1, prop1, t.name)
        print(f"prop Pi: {prop}")
        insts2, prop2, pr_index2, next_index2 = prove_term(
            env, ctx, prop, next_index1, index_for_sort
        )
        if not is_s(prop2):
            raise fmtDeriveError("must be a sort", prop2)
        insts1.extend(insts2)
        insts1.append(AbstInst(next_index2, pr_index1, pr_index2))
        return insts1, prop, next_index2, next_index2 + 1
    if isinstance(t, ConstTerm):
        insts1, prop1, pr_index1, next_index1 = prove_term(
            env, ctx, StarTerm(), current_index, index_for_sort
        )
        if not isinstance(prop1, SortTerm):
            raise fmtDeriveError("must be sort", prop1)
        dfn_i, dfn = next((i, dfn) for (i, dfn) in enumerate(env) if dfn.op == t.op)
        next_index_u = next_index1
        pres: list[int] = []
        insts: list[Instruction] = []
        names, tps = dfn.context.names_tps()
        for i, u in enumerate(t.children):
            insts_u, prop_u, pr_index_u, next_index_u = prove_term(
                env, ctx, u, next_index_u, index_for_sort
            )
            pres.append(pr_index_u)
            insts.extend(insts_u)
            if not check_abd_eqv(
                prop_u, subst_all(tps[i], names[:i], t.children[:i]), env
            ):
                raise fmtDeriveError("type not matched", t)
        insts.append(
            InstInst(next_index_u, pr_index1, len(dfn.context.container), pres, dfn_i)
        )
        return insts, subst_all(dfn.prop, names, tps), next_index_u, next_index_u + 1
    if isinstance(t, PiTerm):
        insts1, prop1, pr_index1, next_index1 = prove_term(
            env, ctx, t.t1, current_index, index_for_sort
        )
        if not is_s(prop1):
            raise fmtDeriveError("must be a sort", t.t1)
        insts2, prop2, pr_index2, next_index2 = prove_term(
            env, ctx.extend(t.name, t.t1), t.t2, next_index1, index_for_sort
        )
        if not is_s(prop2):
            raise fmtDeriveError("must be a sort", t.t2)
        insts1.extend(insts2)
        insts1.append(FormInst(next_index2, pr_index1, pr_index2))
        return insts1, prop2, next_index2, next_index2 + 1
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
        dfns.append(parse_script(ds))
    instructions: list[list[Instruction]] = [[SortInst(0)]]
    instruction_index = 1
    try: # for debug
        for i, dfn in enumerate(dfns):
            print()
            try: # for debug
                tpsss = set()
                insts = prove_def(dfn, dfns[:i], instruction_index)
                print(tpsss)
            except Exception as e:
                print(tpsss)
                print("FAIL")
                raise e
            instructions.append(insts)
            instruction_index += len(insts)
    except:
        pass
    instructions.append([EndInst(-1)])
    for insts in instructions:
        for inst in insts:
            print(inst)
