/- # 問題61

与えられた二分木の葉の数を数える関数を定義しなさい。
-/
import LeanBook.Problem55

def countLeaves {α : Type} (t : BinTree α) : Nat :=
  match t with
  | .empty => 0
  | .node _ .empty .empty => 1
  | .node _ left right =>
    countLeaves left + countLeaves right

#guard countLeaves [tree| 1] = 1
#guard countLeaves [tree| 1 * (2 + 3)] = 2
#guard countLeaves [tree| 1 * (2 * (3 + 4) + 5 * (6 + 7))] = 4
