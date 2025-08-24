/-
# 問題 18
(中級 🌟🌟) 2つのインデックス `i`, `k` が与えられたとき、リストの`i`番目から`k`番目まで（両端含む）の部分リスト（スライス）を求めよ。要素のカウントは1から始める。
-/
variable {α : Type}

def slice (l : List α) (i k : Nat) : List α :=
  if i <= k then
    l.drop (i - 1) |>.take (k - i + 1)
  else
    l.drop (k - 1) |>.take (i - k + 1)

#guard slice [1, 2, 3, 4, 5, 6, 7, 8, 9] 3 7 == [3, 4, 5, 6, 7]
#guard slice [1, 2, 3, 4, 5] 1 1 == [1]
#guard slice [1, 2, 3, 4, 5] 2 3 == [2, 3]
