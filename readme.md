# 検証器の作成

## 実行方法

Python3.11以上が必要。

### automake | autobook

```
cd src
python3.11 test.py test/def2 > res
```

### automake

```
cd src
python3.11 derive.py test/def2 > insts
```

### autobook

```
cd src
python3.11 check.py insts > res
```
