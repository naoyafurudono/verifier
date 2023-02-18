
if __name__ == "__main__":
    import argparse

    from check import Judgement, check
    from derive import derive_lines

    apaser = argparse.ArgumentParser(prog="test derive and check")
    apaser.add_argument("filename")
    args = apaser.parse_args()
    filename = args.filename

    with open(filename, "r") as f:
        lines = f.readlines()
    instructions = derive_lines(lines)
    book: list[Judgement] = []
    for inst in instructions:
        book = check(inst, book)
    for i, judgement in enumerate(book):
        print(i, judgement)
