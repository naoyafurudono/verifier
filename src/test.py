if __name__ == "__main__":
    import argparse

    from check import Judgement, check
    from derive import derive_lines
    import logging
    logging.basicConfig(filename="test.log", encoding="utf-8", level=logging.DEBUG)

    apaser = argparse.ArgumentParser(prog="test derive and check")
    apaser.add_argument("filename")
    args = apaser.parse_args()
    filename = args.filename

    with open(filename, "r") as f:
        lines = f.readlines()
    instructions = derive_lines(lines)
    book: list[Judgement] = []
    try:
        for inst in instructions:
            book = check(inst, book)
    except Exception as e:
        for inst in instructions:
            print(inst)
        for i, judgement in enumerate(book):
            print(i, judgement)
        raise e
