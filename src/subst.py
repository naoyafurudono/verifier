import functools

from fresh_name import Fresh
from parse import (
    AppTerm,
    ConstTerm,
    LambdaTerm,
    PiTerm,
    SortTerm,
    StarTerm,
    Term,
    UnExpectedTermError,
    VarTerm,
)


def subst(t1: Term, t2: Term, name: str) -> Term:
    # t1[name !--> t2]
    if isinstance(t1, VarTerm):
        if t1.name == name:
            return t2
        else:
            return t1
    elif isinstance(t1, LambdaTerm):
        _t11 = subst(t1.t1, t2, name)
        if t1.name == name:
            return LambdaTerm(_t11, t1.t2, name)
        else:
            fresh_name = Fresh.fresh()
            t12 = rename(t1.t2, t1.name, fresh_name)
            _t12 = subst(t12, t2, name)
            return LambdaTerm(_t11, _t12, fresh_name)
    elif isinstance(t1, PiTerm):
        _t11 = subst(t1.t1, t2, name)
        if t1.name == name:
            return PiTerm(_t11, t1.t2, name)
        else:
            fresh_name = Fresh.fresh()
            t12 = rename(t1.t2, t1.name, fresh_name)
            _t12 = subst(t12, t2, name)
            return PiTerm(_t11, _t12, fresh_name)
    elif isinstance(t1, AppTerm):
        return AppTerm(subst(t1.t1, t2, name), subst(t1.t2, t2, name))
    elif isinstance(t1, ConstTerm):
        return ConstTerm(t1.op, list(map(lambda tt: subst(tt, t2, name), t1.children)))
    return t1


def subst_all(t: Term, names: list[str], terms: list[Term]) -> Term:
    tt = t
    freshes: list[str] = []
    for i in range(len(names)):
        fresh = Fresh.fresh()
        freshes.append(fresh)
        tt = rename(tt, names[i], fresh)
    return functools.reduce(lambda t, b: subst(t, b[1], b[0]), zip(freshes, terms), tt)


def rename(t: Term, frm: str, to: str) -> Term:
    if isinstance(t, VarTerm):
        if t.name == frm:
            return VarTerm(to)
        else:
            return t
    elif isinstance(t, LambdaTerm):
        _t1 = rename(t.t1, frm, to)
        if t.name == frm:
            return LambdaTerm(_t1, t.t2, t.name)
        else:
            _t2 = rename(t.t2, frm, to)
            return LambdaTerm(_t1, _t2, t.name)
    elif isinstance(t, PiTerm):
        _t1 = rename(t.t1, frm, to)
        if t.name == frm:
            return PiTerm(_t1, t.t2, t.name)
        else:
            _t2 = rename(t.t2, frm, to)
            return PiTerm(_t1, _t2, t.name)
    elif isinstance(t, AppTerm):
        return AppTerm(rename(t.t1, frm, to), rename(t.t2, frm, to))
    elif isinstance(t, ConstTerm):
        return ConstTerm(t.op, list(map(lambda tt: rename(tt, frm, to), t.children)))
    elif isinstance(t, SortTerm) or isinstance(t, StarTerm):
        return t
    else:
        raise UnExpectedTermError(t)


if __name__ == "__main__":
    import argparse
    import re

    from parse import parse_term

    apaser = argparse.ArgumentParser(prog="subst")
    apaser.add_argument("filename")
    args = apaser.parse_args()
    filename = args.filename
    with open(filename, "r") as f:
        code1 = f.readline()
        mo = re.match("[a-zA-Z]", f.readline())
        if not mo:
            print("bad variable name")
            exit(1)
        else:
            name = mo.group(0)
        code2 = f.readline()
    try:
        term1 = parse_term(code1)
        term2 = parse_term(code2)
        print(subst(term1, term2, name))
    except (SyntaxError) as e:
        print("syntax error")
        print(e)
