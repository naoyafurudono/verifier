class Fresh:
    # フレッシュな変数名を生成する
    # ユーザからの入力では、イプシロンの定義から#で始まる変数名は生成され得ないため衝突しない
    # 内部処理では、このクラス経由でしか変数名を生成しなければ衝突しない
    __gen = 0
    @staticmethod
    def fresh():
        num = Fresh.__gen
        Fresh.__gen += 1
        return f"^{num}"
