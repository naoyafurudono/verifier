class Fresh:
    __gen = 0
    @staticmethod
    def fresh():
        num = Fresh.__gen
        Fresh.__gen += 1
        return f"#{num}"
