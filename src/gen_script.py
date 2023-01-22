from inst import EndInst, Instruction, SortInst
from typing import Generator
from check import Context, Definition
from parse import StarTerm, Term


def run(
    t: Term, env: list[Definition], ctx: Context
) -> Generator[Instruction, None, None]:
    for inst in gen_script(t, env, ctx):
        yield inst
    yield EndInst(-1)


def gen_script(
    t: Term, env: list[Definition], ctx: Context
) -> Generator[Instruction, None, None]:
    if isinstance(t, StarTerm):
        yield SortInst(-2)
    yield Instruction(-2)
