import functools
from dataclasses import dataclass
from typing import Tuple

from fresh_name import Fresh
from inst import (
    AbstInst,
    ApplInst,
    ConvInst,
    CPInst,
    DefInst,
    DefPrInst,
    EndInst,
    FormInst,
    InstInst,
    Instruction,
    SortInst,
    SPInst,
    VarInst,
    WeakInst,
    scan_inst,
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
    alpha_eqv,
    parse_term,
)
from subst import rename, subst, subst_all


@dataclass(frozen=True)
class Context:
    container: list[Tuple[str, Term]]

    def extend(self, var: str, t: Term):
        lst = self.container.copy()
        lst.append((var, t))
        return Context(lst)

    def get(self, name: str) -> Term | None:
        return next((b[1] for b in self.container if b[0] == name), None)

    @property
    def size(self):
        return len(self.container)

    @property
    def is_empty(self) -> bool:
        return len(self.container) == 0

    def get_last(self) -> Tuple[str, Term] | None:
        if self.is_empty:
            return None
        return self.container[-1]

    def get_ahead(self):
        if self.is_empty:
            return None
        return Context(self.container[:-1])

    def __eq__(self, that):
        if self is that:
            return True
        if len(self.container) != len(that.container):
            return False

        def fst(b):
            return b[0]

        if list(map(fst, self.container)) != list(map(fst, that.container)):
            return False

        def snd(b):
            return b[1]

        if any(
            map(
                lambda p: p[0] != p[1],
                zip(map(snd, self.container), map(snd, that.container)),
            )
        ):
            return False
        return True

    def cdr(self):
        return Context(self.container[:-1])

    def car(self):
        return self.container[-1]

    def __str__(self) -> str:
        return ", ".join(
            map(lambda binding: f"{binding[0]}:{binding[1]}", self.container)
        )

    def params(self) -> list[str]:
        def fst(d: Tuple[str, Term]) -> str:
            return d[0]

        return list(map(fst, self.container))

    def names_tps(self) -> Tuple[list[str], list[Term]]:
        names: list[str] = []
        tps: list[Term] = []
        for b in self.container:
            names.append(b[0])
            tps.append(b[1])
        return names, tps


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
        return isinstance(that, Definition) and all(
            [
                self.op == that.op,
                self.context == that.context,
                self.body == that.body,
                self.prop == that.prop,
            ]
        )

    def __str__(self) -> str:
        # return self.op

        # 定義の中身を載せるとうるさすぎる
        if self.is_prim:
            body = "⊥"
        else:
            body = self.body.__str__()
        return f"{self.context} |> {self.op} := {body} : {self.prop}"

    @property
    def names(self):
        return list(map(lambda b: b[0], self.context.container))


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
    return VerificationError(f"at: {inst}\n{msg}")


def check(inst: Instruction, book: list[Judgement]) -> list[Judgement]:
    match inst:
        case SortInst(_lnum):
            _book = book.copy()
            _book.append(
                Judgement(
                    environment=[],
                    context=Context([]),
                    proof=parse_term("*"),
                    prop=parse_term("@"),
                )
            )
            return _book
        case VarInst(_lnum, pre, var):
            premise = book[pre]
            var_name: str = inst.var.name
            _book = book.copy()
            _book.append(
                Judgement(
                    environment=premise.environment,
                    context=premise.context.extend(var_name, premise.proof),
                    proof=var,
                    prop=premise.proof,
                )
            )
            return _book
        case WeakInst(_lnum, pre1, pre2, var):
            try:
                premise1 = book[pre1]
                premise2 = book[pre2]
            except IndexError:
                raise fmtErr_(inst, "no book entry found")
            new_name = inst.var
            if premise1.environment != premise2.environment:
                raise fmtErr_(inst, "environments are not agree")
            if premise1.context != premise2.context:
                raise fmtErr_(inst, "contexts are not agree")
            if new_name in premise1.context.params():
                raise fmtErr_(
                    inst, f"variable {new_name} is already used in the context"
                )
            _book = book.copy()
            _book.append(
                Judgement(
                    environment=premise1.environment,
                    context=premise1.context.extend(new_name, premise2.proof),
                    proof=premise1.proof,
                    prop=premise1.prop,
                )
            )
            return _book
        case FormInst(_lnum, pre1, pre2):
            premise1 = book[pre1]
            premise2 = book[pre2]
            if premise1.environment != premise2.environment:
                raise fmtErr_(inst, "environments are not agree")
            if premise1.context != premise2.context.cdr():
                raise fmtErr_(inst, "contexts are not agree")
            if premise1.proof != premise2.context.car()[1]:
                raise fmtErr_(
                    inst,
                    "proof of pre1 does not agree with last type of the pre2 context",
                )
            _book = book.copy()
            _book.append(
                Judgement(
                    environment=premise1.environment,
                    context=premise1.context,
                    proof=PiTerm(
                        premise1.proof, premise2.proof, premise2.context.car()[0]
                    ),
                    prop=premise2.prop,
                )
            )
            return _book
        case ApplInst(_lnum, pre1, pre2):
            premise1 = book[pre1]
            premise2 = book[pre2]
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
                        inst, "pre1 parameter type does not agree with pre2 type"
                    )
                _book = book.copy()
                _book.append(
                    Judgement(
                        environment=premise1.environment,
                        context=premise1.context,
                        proof=AppTerm(premise1.proof, premise2.proof),
                        prop=subst(mb_funtype.t2, premise2.proof, mb_funtype.name),
                    )
                )
                return _book
        case AbstInst(_lnum, pre1, pre2):
            premise1 = book[pre1]
            premise2 = book[pre2]
            if premise1.environment != premise2.environment:
                raise fmtErr_(inst, "environments are not agree")
            if premise1.context.cdr() != premise2.context:
                raise fmtErr_(inst, "contexts are not agree")

            mb_pi_term = premise2.proof
            if not isinstance(mb_pi_term, PiTerm):
                raise fmtErr_(inst, "pre2 must derive Pi term")

            if (
                premise1.context.car()[0] != mb_pi_term.name
                or premise1.context.car()[1] != mb_pi_term.t1
            ):
                raise fmtErr_(inst, "pre1.context must end with binding of pre2.proof")

            if premise1.prop != mb_pi_term.t2:
                raise fmtErr_(
                    inst,
                    f"""pre1 must prove pre2.proof's conclusion\npre1.prop:\t{premise1.prop}\nconcl.   :\t{mb_pi_term.t2}
                        premise1: {premise1}
                        premise2: {premise2}
                    """,
                )

            _book = book.copy()
            _book.append(
                Judgement(
                    environment=premise2.environment,
                    context=premise2.context,
                    proof=LambdaTerm(mb_pi_term.t1, premise1.proof, mb_pi_term.name),
                    prop=premise2.proof,
                )
            )
            return _book
        case ConvInst(_lnum, pre1, pre2):
            premise1 = book[pre1]
            premise2 = book[pre2]
            if premise1.environment != premise2.environment:
                raise fmtErr_(inst, "environments are not agree")
            if premise1.context != premise2.context:
                raise fmtErr_(inst, "contexts are not agree")
            if not bd_eqv(premise1.prop, premise2.proof, premise1.environment):
                raise fmtErr_(
                    inst,
                    f"pre2.proof must be beta-delta eqv to pre1 prop\n{premise1.prop} vs. {premise2.proof}",
                )
            _book = book.copy()
            _book.append(
                Judgement(
                    environment=premise1.environment,
                    context=premise1.context,
                    proof=premise1.proof,
                    prop=premise2.proof,
                )
            )
            return _book
        case DefInst(_lnum, pre1, pre2, op):
            premise1 = book[pre1]
            premise2 = book[pre2]
            if premise1.environment != premise2.environment:
                raise fmtErr_(inst, "environments are not agree")
            if op in map(lambda d: d.op, premise1.environment):
                raise fmtErr_(
                    inst, f"constant {op} is already defined in the environment"
                )
            dfn = Definition(
                op=op, context=premise2.context, body=premise2.proof, prop=premise2.prop
            )
            _env = premise1.environment.copy()
            _env.append(dfn)
            _book = book.copy()
            _book.append(
                Judgement(
                    environment=_env,
                    context=premise1.context,
                    proof=premise1.proof,
                    prop=premise1.prop,
                )
            )
            return _book
        case DefPrInst(_lnum, pre1, pre2, op):
            premise1 = book[pre1]
            premise2 = book[pre2]
            if premise1.environment != premise2.environment:
                raise fmtErr_(inst, "environments are not agree")
            if op in map(lambda d: d.op, premise1.environment):
                raise fmtErr_(
                    inst, f"constant {op} is already defined in the environment"
                )
            dfn = Definition(
                op=op,
                context=premise2.context,
                body=StarTerm(),  # Dummy
                prop=premise2.proof,
                is_prim=True,
            )
            _env = premise1.environment.copy()
            _env.append(dfn)
            _book = book.copy()
            _book.append(
                Judgement(
                    environment=_env,
                    context=premise1.context,
                    proof=premise1.proof,
                    prop=premise1.prop,
                )
            )
            return _book
        case InstInst(_lnum, pre, _length, pres, op_offset):
            # instとinst-primを区別する必要はない
            premise = book[pre]
            premises = list(map(lambda i: book[i], pres))
            if any(map(lambda pre: premise.environment != pre.environment, premises)):
                raise fmtErr_(inst, "environments are not agree")
            if any(map(lambda pre: premise.context != pre.context, premises)):
                raise fmtErr_(inst, "context are not agree")
            if premise.proof != StarTerm() or premise.prop != SortTerm():
                raise fmtErr_(inst, "bad premise {premise}")
            dfn = premise.environment[op_offset]
            if len(dfn.context.container) != len(premises):
                raise fmtErr_(inst, "arity mismatch")
            if not check_arity_type(dfn, premises):
                raise fmtErr_(inst, "arg type mismatch")

            pre_proofs = [p.proof for p in premises]
            prop = subst_all(dfn.prop, dfn.names, pre_proofs)
            _book = book.copy()
            _book.append(
                Judgement(
                    environment=premise.environment,
                    context=premise.context,
                    proof=ConstTerm(dfn.op, pre_proofs),
                    prop=prop,
                )
            )
            return _book
        case CPInst(_lnum, target):
            _book = book.copy()
            _book.append(book[target])
            return _book
        case SPInst(_lnum, target, bind):
            j = book[target]
            binding = j.context.container[bind]
            _book = book.copy()
            _book.append(
                Judgement(
                    environment=j.environment,
                    context=j.context,
                    proof=parse_term(binding[0]),
                    prop=binding[1],
                )
            )
            return _book
        case EndInst(_lnum):
            return book
        case _:
            raise fmtErr_(inst, "have not implemented")


def check_arity_type(dfn: Definition, premises: list[Judgement]) -> bool:
    us = map(lambda pre: pre.proof, premises)
    sbst = list(zip(dfn.names, us))
    for i, pre in enumerate(premises):
        pre_prop = pre.prop
        a = functools.reduce(
            lambda a, b: subst(a, b[1], b[0]),
            sbst[:i],
            dfn.context.container[i][1],  # A
        )
        if pre_prop != a:
            print(f"{pre_prop=}\n{a=}")
            return False
    return True


"""
# 正規化/delta-beta比較

## 高速化のアイデア

### 正規化

- 環境を使う（代入を遅延する）

### beta/delta-eqv

- 環境を使う
- diffだけを正規化してalpha比較する
"""


class NormalizationError(Exception):
    pass


def fmtErrN_(t: Term, env: list[Definition], msg: str):
    return NormalizationError(f"{t}:\n  {msg}")


def bd_eqv(t1: Term, t2: Term, env: list[Definition]) -> bool:
    n1 = normalize(t1, env)
    n2 = normalize(t2, env)
    return alpha_eqv(n1, n2)


def normalize(t: Term, env: list[Definition]) -> Term:
    if type(t) in [VarTerm, StarTerm, SortTerm]:
        return t
    elif isinstance(t, AppTerm):
        t1 = normalize(t.t1, env)
        t2 = normalize(t.t2, env)
        if isinstance(t1, LambdaTerm):
            return normalize(beta_reduction(t1, t2), env)
        else:
            return AppTerm(t1, t2)
    elif isinstance(t, LambdaTerm):
        return LambdaTerm(normalize(t.t1, env), normalize(t.t2, env), t.name)
    elif isinstance(t, PiTerm):
        return PiTerm(normalize(t.t1, env), normalize(t.t2, env), t.name)
    elif isinstance(t, ConstTerm):
        children = list(map(lambda tt: normalize(tt, env), t.children))
        mb_dfn = next(dfn for dfn in env if dfn.op == t.op)
        if not mb_dfn:
            raise fmtErrN_(t, env, "definition not found")
        dfn = mb_dfn
        if len(dfn.context.container) != len(children):
            # 型検査通ってるのでokなはず？
            raise fmtErrN_(t, env, "arity mismatch")
        if dfn.is_prim:
            return ConstTerm(op=t.op, children=children)
        else:
            return normalize(delta_reduction(dfn, children), env)
    else:
        raise fmtErrN_(t, env, "not implemented yet")


def beta_reduction(f: LambdaTerm, t: Term) -> Term:
    fresh_name = Fresh.fresh()
    escaped_t = rename(t, f.name, fresh_name)
    return subst(f.t2, escaped_t, f.name)


def delta_reduction(dfn: Definition, args: list[Term]) -> Term:
    if dfn.is_prim:
        raise NormalizationError("cannot reduce")
    names = dfn.context.params()
    return subst_all(dfn.body, names, args)


if __name__ == "__main__":
    import argparse

    apaser = argparse.ArgumentParser(prog="verify")
    apaser.add_argument("filename")
    args = apaser.parse_args()
    filename = args.filename

    def run():
        with open(filename, "r") as f:
            book: list[Judgement] = []
            for line in f.readlines():
                inst = scan_inst(line.replace("\n", ""))
                book = check(inst, book)
            return book

    # 今はまだ一瞬で終わる
    # import bench
    # print(f"{bench.repeat_sec(run, 10)} sec")
    book = run()
    for i, judgement in enumerate(book):
        print(i, judgement)
