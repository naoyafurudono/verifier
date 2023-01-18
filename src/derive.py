# automakeに対応
# 定義の列は依存関係でトポロジカルソートされていると仮定する

"""
上から定義を見ていって、
def, def-primに従ってデルタを拡張していく。
それぞれの導出規則は、deltaを順次増やす以外は環境を空、K, Lが*,sortとする。
そうすると、最終的なデルタを得たときにそこまでの導出木を生成しやすい。
"""

from check import Context, Definition
from inst import EndInst, Instruction
from parse import SortTerm, StarTerm, Term, VarTerm, parse_term
import parse


def prove_def(dfn: Definition, env: list[Definition]) -> list[Instruction]:
    # 単一の定義と、環境を受け取って定義本体の導出木を生成するinstの列を返す
    res: list[Instruction] = []
    return res


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
    for i, dfn in enumerate(dfns):
        print(dfn)
        insts = prove_def(dfn, dfns[:i])
        instructions.append(insts)
    instructions.append([EndInst(-1)])
    for insts in instructions:
        for inst in insts:
            print(inst)
