from dataclasses import dataclass
from typing import Tuple
from inst import FormInst, Instruction, SortInst, VarInst, WeakInst, scan_inst

from parse import PiTerm, Term, parse_term


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

    def cdr(self):
        return Context(self.__container[:-1])

    def car(self):
        return self.__container[-1]


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
        _book = book.copy()
        _book.append(Judgement(
            environment=[],
            context=Context([]),
            proof=parse_term("*"),
            prop=parse_term("@")
        ))
        return _book
    elif isinstance(inst, VarInst):
        print(inst)
        premise = book[inst.pre]
        var_name: str = inst.var.name
        _book = book.copy()
        _book.append(Judgement(
            environment=premise.environment,
            context=premise.context.extend(var_name, premise.proof),
            proof=inst.var,
            prop=premise.proof
        ))
        return _book
    elif isinstance(inst, WeakInst):
        premise1 = book[inst.pre1]
        premise2 = book[inst.pre2]
        if premise1.environment != premise2.environment:
            raise TypeError()
        if premise1.context != premise2.context:
            raise TypeError()
        _book = book.copy()
        _book.append(Judgement(
            environment=premise1.environment,
            context=premise1.context.extend(inst.var.name, premise2.proof),
            proof=premise1.proof,
            prop=premise1.prop
        ))
        return _book
    elif isinstance(inst, FormInst):
        premise1 = book[inst.pre1]
        premise2 = book[inst.pre2]
        if premise1.environment != premise2.environment:
            raise TypeError
        if premise1.context != premise2.context.cdr():
            raise TypeError
        if premise1.proof != premise2.context.car()[1]:
            raise TypeError
        _book = book.copy()
        _book.append(Judgement(
            environment=premise1.environment,
            context=premise1.context,
            proof=PiTerm(premise1.proof, premise2.proof, premise2.context.car()[0]),
            prop=premise2.prop
        ))
        return _book
    # TODO appl, abst, conv, def, def-prim, inst, inst-prim, cp, sp
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
