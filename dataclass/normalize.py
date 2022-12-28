# normalize terms (in the sense of beta / delta eqv)

# not substitute, but use environment which is not delta

"""
# 高速化のアイデア

## 正規化

- 環境を使う（代入を遅延する）

## beta/delta-eqv

- 環境を使う
- diffだけを正規化してalpha比較する
"""

from parse import Term


def bd_eqv(t1: Term, t2: Term)->bool:
    return True
