/- # 問題 61

二分木の葉の数を数える関数を定義せよ。

ただし、葉とは子を持たないノードのことである。
-/
import LeanBook.Problem55

/-- ２分木の葉を数える -/
def countLeaves {α : Type} (t : BinTree α) : Nat :=
  match t with
  | .empty => 0
  | .node _ left right =>
    if left.isEmpty && right.isEmpty then
      1
    else
      countLeaves left + countLeaves right

#guard countLeaves [tree| 1] = 1
#guard countLeaves [tree| 1 * (2 + 3)] = 2
#guard countLeaves [tree| 1 * (2 * (3 + 4) + 5 * (6 + 7))] = 4
#guard countLeaves [tree| 1 * (2 + ∅)] = 1
