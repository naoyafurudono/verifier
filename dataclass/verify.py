from dataclasses import dataclass
from typing import Tuple
from inst import Instruction, SortInst, VarInst, WeakInst, scan_inst

from parse import Term, parse_term


@dataclass
class Context:
    __container: list[Tuple[str, Term]]

    def extend(self, var, t):
        lst = self.__container.copy()
        lst.append((var, t))
        return Context(lst)

    def __eq__(self, that):
        if super().__eq__(that):
            return True
        if len(self.__container) != len(that.__container):
            return False

        def fst(b): return b[0]
        if map(fst, self.__container) != map(fst, that.__container):
            return False

        def snd(b): return b[1]
        if any(map(lambda p: p[0] != p[1],
                   zip(map(snd, self.__container),  map(snd, that.__container)))):
            return False
        return True


@dataclass
class Definition:
    op: str
    context: Context
    body: Term
    prop: Term

    def __eq__(self, that):
        if super().__eq__(that):
            return True
        return isinstance(that, Definition) and all([
            self.op == that.op,
            self.context == that.context,
            self.body == that.body,
            self.prop == that.prop
        ])


@ dataclass
class Judgement:
    environment: list[Definition]
    context: Context
    proof: Term
    prop: Term


def verify(inst: Instruction, book: list[Judgement]) -> list[Judgement]:
    if isinstance(inst, SortInst):
        _book=book.copy()
        _book.append(Judgement(
            environment=[],
            context=Context([]),
            proof=parse_term("*"),
            prop=parse_term("@")
        ))
        return _book
    elif isinstance(inst, VarInst):
        print(inst)
        premise=book[inst.pre]
        var_name: str=inst.var.__str__()
        ctx=premise.context.extend(var_name, premise.proof)
        _book=book.copy()
        _book.append(Judgement(
            environment=premise.environment,
            context=ctx,
            proof=inst.var,
            prop=premise.proof
        ))
        return _book
    elif isinstance(inst, WeakInst):
        premise1=book[inst.pre1]
        premise2=book[inst.pre2]
        if not (premise1.environment == premise2.environment and premise1.context == premise2.context):
            raise TypeError()
    return book


if __name__ == "__main__":
    import argparse
    apaser=argparse.ArgumentParser(prog = 'verify')
    apaser.add_argument('filename')
    args=apaser.parse_args()
    filename=args.filename
    with open(filename, 'r') as f:
        trees: list[Judgement]=[]
        for line in f.readlines():
            inst=scan_inst(line.replace("\n", ""))
            trees=verify(inst, trees)
    for i, tree in enumerate(trees):
        print(i, tree)
