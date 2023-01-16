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
from parse import SortTerm, StarTerm


def prove_def(dfn: Definition, env: list[Definition]) -> list[Instruction]:
    # 単一の定義と、環境を受け取って定義本体の導出木を生成するinstの列を返す
    res: list[Instruction] = []
    return res


def parse_script(lines: list[str]) -> Definition:
    """
    lines はdef2から始まって、end2で終わる定義の列:
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
    """
    return Definition("dummy", Context([]), StarTerm(), SortTerm())


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
        if line == "":
            dfn_scripts.append(dfn_script)
            dfn_script = []
        else:
            dfn_script.append(line)
    dfns = list((parse_script(ds) for ds in dfn_scripts))
    instructions: list[list[Instruction]] = []
    for i, dfn in enumerate(dfns):
        insts = prove_def(dfn, dfns[:i])
        instructions.append(insts)
    instructions.append([EndInst(-1)])
    for insts in instructions:
        for inst in insts:
            print(inst)
