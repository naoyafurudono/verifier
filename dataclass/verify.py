from dataclasses import dataclass
from typing import Tuple
from inst import AbstInst, ApplInst, CPInst, ConvInst, DefInst, DefPrInst, EndInst, FormInst, InstInst, Instruction, SPInst, SortInst, VarInst, WeakInst, scan_inst
from normalize import bd_eqv

from parse import AppTerm, ConstTerm, LambdaTerm, PiTerm, SortTerm, StarTerm, Term, parse_term
from subst import subst


@dataclass(frozen=True)
class Context:
    container: list[Tuple[str, Term]]

    def extend(self, var, t):
        lst = self.container.copy()
        lst.append((var, t))
        return Context(lst)

    def __eq__(self, that):
        if self is that:
            return True
        if len(self.container) != len(that.container):
            return False

        def fst(b): return b[0]
        if list(map(fst, self.container)) != list(map(fst, that.container)):
            return False

        def snd(b): return b[1]
        if any(map(lambda p: p[0] != p[1],
                   zip(map(snd, self.container),  map(snd, that.container)))):
            return False
        return True

    def cdr(self):
        return Context(self.container[:-1])

    def car(self):
        return self.container[-1]

    def __str__(self) -> str:
        return ", ".join(map(lambda binding: f"{binding[0]}:{binding[1]}", self.container))


@dataclass(frozen=True)
class Definition:
    op: str
    context: Context
    body: Term
    prop: Term
    is_prim: bool = False

    def __eq__(self, that):
        if self is that:
            return True
        return isinstance(that, Definition) and all([
            self.op == that.op,
            self.context == that.context,
            self.body == that.body,
            self.prop == that.prop
        ])

    def __str__(self) -> str:
        return self.op
        # 定義の中身を載せるとうるさすぎる
        # if self.is_prim:
        #     body = "⊥"
        # else:
        #     body = self.body.__str__()
        # return f"{self.context} |> {self.op} := {body} : {self.prop}"


@dataclass(frozen=True)
class Judgement:
    environment: list[Definition]
    context: Context
    proof: Term
    prop: Term

    def __str__(self) -> str:
        return f"{', '.join(map(lambda dfn: dfn.__str__(), self.environment))} ; {self.context} |- {self.proof} : {self.prop}"


class VerificationError(Exception):
    pass


def fmtErr_(inst: Instruction, msg: str) -> VerificationError:
    return VerificationError(f"at {inst.lnum}: {inst}\n{msg}")


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
        new_name = inst.var.name
        if premise1.environment != premise2.environment:
            raise fmtErr_(inst, "environments are not agree")
        if premise1.context != premise2.context:
            print(premise1.context)
            print(premise2.context)
            raise fmtErr_(inst, "contexts are not agree")
        if new_name in premise1.context.container:
            raise fmtErr_(
                inst, f"variable {new_name} is already used in the context")
        _book = book.copy()
        _book.append(Judgement(
            environment=premise1.environment,
            context=premise1.context.extend(new_name, premise2.proof),
            proof=premise1.proof,
            prop=premise1.prop
        ))
        return _book
    elif isinstance(inst, FormInst):
        premise1 = book[inst.pre1]
        premise2 = book[inst.pre2]
        if premise1.environment != premise2.environment:
            raise fmtErr_(inst, "environments are not agree")
        if premise1.context != premise2.context.cdr():
            raise fmtErr_(inst, "contexts are not agree")
        if premise1.proof != premise2.context.car()[1]:
            raise fmtErr_(
                inst, "proof of pre1 does not agree with last type of the pre2 context")
        _book = book.copy()
        _book.append(Judgement(
            environment=premise1.environment,
            context=premise1.context,
            proof=PiTerm(premise1.proof, premise2.proof,
                         premise2.context.car()[0]),
            prop=premise2.prop
        ))
        return _book
    elif isinstance(inst, ApplInst):
        premise1 = book[inst.pre1]
        premise2 = book[inst.pre2]
        if premise1.environment != premise2.environment:
            raise fmtErr_(inst, "environments are not agree")
        if premise1.context != premise2.context:
            raise fmtErr_(inst, "contexts are not agree")
        mb_funtype = premise1.prop
        if not isinstance(mb_funtype, PiTerm):
            raise fmtErr_(inst, "pre1 must prove Pi type")
        else:
            if not mb_funtype.t1 == premise2.prop:
                raise fmtErr_(
                    inst, "pre1 parameter type does not agree with pre2 type")
            _book = book.copy()
            _book.append(Judgement(
                environment=premise1.environment,
                context=premise1.context,
                proof=AppTerm(premise1.proof, premise2.proof),
                prop=subst(mb_funtype.t2, premise2.proof, mb_funtype.name)
            ))
            return _book
    elif isinstance(inst, AbstInst):
        premise1 = book[inst.pre1]
        premise2 = book[inst.pre2]
        if premise1.environment != premise2.environment:
            raise fmtErr_(inst, "environments are not agree")
        if premise1.context.cdr() != premise2.context:
            raise fmtErr_(inst, "contexts are not agree")
        mb_pi_term = premise2.proof
        if not isinstance(mb_pi_term, PiTerm):
            raise fmtErr_(inst, "pre2 must prove Pi term")
        else:
            if premise1.context.car()[0] != mb_pi_term.name or premise1.context.car()[1] != mb_pi_term.t1:
                raise fmtErr_(
                    inst, "pre1.context must end with binding of pre2.proof")
            if premise1.prop != mb_pi_term.t2:
                raise fmtErr_(inst, "pre1 must prove pre2.proof's conclusion")
            _book = book.copy()
            _book.append(Judgement(
                environment=premise2.environment,
                context=premise2.context,
                proof=LambdaTerm(
                    mb_pi_term.t1, premise1.proof, mb_pi_term.name),
                prop=premise2.proof
            ))
            return _book
    elif isinstance(inst, ConvInst):
        premise1 = book[inst.pre1]
        premise2 = book[inst.pre2]
        if premise1.environment != premise2.environment:
            raise fmtErr_(inst, "environments are not agree")
        if premise1.context != premise2.context:
            raise fmtErr_(inst, "contexts are not agree")
        if not bd_eqv(premise1.prop, premise2.proof):
            raise fmtErr_(
                inst, "pre2.proof must be beta-delta eqv to pre1 prop")
        _book = book.copy()
        _book.append(Judgement(
            environment=premise1.environment,
            context=premise1.context,
            proof=premise1.proof,
            prop=premise2.proof
        ))
        return _book
    elif isinstance(inst, DefInst):
        premise1 = book[inst.pre1]
        premise2 = book[inst.pre2]
        op = inst.op
        if premise1.environment != premise2.environment:
            raise fmtErr_(inst, "environments are not agree")
        if op in map(lambda d: d.op, premise1.environment):
            raise fmtErr_(
                inst, f"constant {op} is already defined in the environment")
        dfn = Definition(op=op, context=premise2.context,
                         body=premise2.proof, prop=premise2.prop)
        _env = premise1.environment.copy()
        _env.append(dfn)
        _book = book.copy()
        _book.append(Judgement(
            environment=_env,
            context=premise1.context,
            proof=premise1.proof,
            prop=premise1.prop
        ))
        return _book
    elif isinstance(inst, DefPrInst):
        premise1 = book[inst.pre1]
        premise2 = book[inst.pre2]
        op = inst.op
        if premise1.environment != premise2.environment:
            raise fmtErr_(inst, "environments are not agree")
        if op in map(lambda d: d.op, premise1.environment):
            raise fmtErr_(
                inst, f"constant {op} is already defined in the environment")
        dfn = Definition(op=op, context=premise2.context,
                         body=StarTerm(),  # Dummy
                         prop=premise2.prop, is_prim=True)
        _env = premise1.environment.copy()
        _env.append(dfn)
        _book = book.copy()
        _book.append(Judgement(
            environment=_env,
            context=premise1.context,
            proof=premise1.proof,
            prop=premise1.prop,
        ))
        return _book
    elif isinstance(inst, InstInst):
        # instとinst-primを区別する必要はない
        premise = book[inst.pre]
        premises = list(map(lambda i: book[i], inst.pres))
        if any(map(lambda pre: premise.environment != pre.environment, premises)):
            raise fmtErr_(inst, "environments are not agree")
        if any(map(lambda pre: premise.context != pre.context, premises)):
            raise fmtErr_(inst, "context are not agree")
        if premise.proof != StarTerm() or premise.prop != SortTerm():
            raise fmtErr_(inst, "TODO")
        dfn = premise.environment[inst.op_offset]
        if len(dfn.context.container) != len(premises):
            raise fmtErr_(inst, "arity mismatch")
        if not check_arity_type(dfn, premises):
            raise fmtErr_(inst, "arg type mismatch")
        prop = dfn.prop  # TODO 代入
        _book = book.copy()
        _book.append(Judgement(
            environment=premise.environment,
            context=premise.context,
            proof=ConstTerm(dfn.op, list(map(lambda p: p.proof, premises))),
            prop=prop
        ))
        return _book
    elif isinstance(inst, CPInst):
        _book = book.copy()
        _book.append(book[inst.target])
        return _book
    elif isinstance(inst, SPInst):
        j = book[inst.target]
        binding = j.context.container[inst.bind]
        _book = book.copy()
        _book.append(Judgement(
            environment=j.environment,
            context=j.context,
            proof=parse_term(binding[0]),
            prop=binding[1]
        ))
        return _book
    elif isinstance(inst, EndInst):
        print("checked")
        return book
    else:
        raise fmtErr_(inst, "have not implemented")


def check_arity_type(dfn: Definition, premises: list[Judgement]) -> bool:
    print(f"TODO {__file__}: check_arity_type")
    return True


if __name__ == "__main__":
    import argparse
    apaser = argparse.ArgumentParser(prog='verify')
    apaser.add_argument('filename')
    args = apaser.parse_args()
    filename = args.filename
    with open(filename, 'r') as f:
        trees: list[Judgement] = []
        for line in f.readlines():
            inst = scan_inst(line.replace("\n", ""))
            trees = verify(inst, trees)
    for i, tree in enumerate(trees):
        print(i, tree.__str__())
