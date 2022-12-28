from time import time


def measure_sec(f) -> float:
    tic = time()
    f()
    tac = time()
    return tac - tic


def repeat_sec(f, n: int) -> float:
    s = 0.0
    for _ in range(n):
        s += measure_sec(f)
    return s / n
