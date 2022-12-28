from dataclasses import dataclass
from typing import Tuple

from parse import Term, VarTerm, parse_term


@dataclass
class Instruction:
    lnum: int
    pass


@dataclass
class EndInst(Instruction):
    pass


@dataclass
class SortInst(Instruction):
    pass


@dataclass
class VarInst(Instruction):
    pre: int
    var: VarTerm


@dataclass
class WeakInst(Instruction):
    pre1: int
    pre2: int
    var: VarTerm


@dataclass
class FormInst(Instruction):
    pre1: int
    pre2: int


@dataclass
class ApplInst(Instruction):
    pre1: int
    pre2: int


@dataclass
class AbstInst(Instruction):
    pre1: int
    pre2: int


@dataclass
class DefInst(Instruction):
    pre1: int
    pre2: int
    op: str


@dataclass
class InstInst(Instruction):
    # instantiation instruction
    pre: int
    length: int
    pres: list[int]
    op_offset: int


@dataclass
class ConvInst(Instruction):
    pre1: int
    pre2: int


@dataclass
class CPInst(Instruction):
    target: int


@dataclass
class SPInst(Instruction):
    target: int
    bind: int


class FormatError(Exception):
    pass


def __fmtErr(lnum: int, badcode: str = "", msg: str = "") -> FormatError:
    return FormatError(f"at {lnum}: `{badcode}`\n{msg}")


def scan_inst(inst_code: str) -> Instruction:
    tokens = inst_code.split(" ")
    if len(tokens) == 0:
        raise FormatError("サイズ0の命令行")
    lnum = int(tokens[0])
    if lnum == -1:
        return EndInst(lnum=lnum)
    if len(tokens) == 1:
        raise FormatError(f"無効な命令 {inst_code}")
    tag = tokens[1]
    match tag:
        case "sort":
            return SortInst(lnum=lnum)
        case "var":
            mb_var = parse_term(tokens[3])
            if not isinstance(mb_var, VarTerm):
                raise __fmtErr(lnum, inst_code, "not a variable")
            else:
                return VarInst(lnum=lnum, pre=int(tokens[2]), var=mb_var)
        case "weak":
            mb_var = parse_term(tokens[4])
            if not isinstance(mb_var, VarTerm):
                raise __fmtErr(lnum, inst_code, "not a variable")
            else:
                return WeakInst(lnum=lnum, pre1=int(
                    tokens[2]), pre2=int(tokens[3]), var=mb_var)
        case "form":
            return FormInst(lnum=lnum, pre1=int(
                tokens[2]), pre2=int(tokens[3]))
        case "abst":
            return AbstInst(lnum=lnum, pre1=int(
                tokens[2]), pre2=int(tokens[3]))
        case "def":
            return DefInst(lnum=lnum, pre1=int(
                tokens[2]), pre2=int(tokens[3]), op=tokens[4])
        case "inst":
            return InstInst(lnum=lnum, pre=int(
                tokens[2]), length=int(tokens[3]), pres=list(map(int, tokens[4:-1])), op_offset=int(tokens[-1]))
        case "conv":
            return ConvInst(lnum=lnum, pre1=int(
                tokens[2]), pre2=int(tokens[3]))
        case "cp":
            return CPInst(lnum=lnum, target=int(tokens[2]))
        case "sp":
            return SPInst(lnum=lnum, target=int(tokens[2]), bind=int(tokens[3]))
    raise __fmtErr(lnum, inst_code, "no inst matched")
