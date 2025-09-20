/- # 問題62B

与えられたレベルのノードの値をリストとして返しなさい。レベルは根が1、次のレベルが2、というように数えます。
-/
import LeanBook.Problem62

def atlevel {α : Type} (t : BinTree α) (l : Nat) : List α :=
  match t, l with
  | _, 0 => []
  | .empty, _ => []
  | .node v _ _, 1 => [v]
  | .node _ left right, .succ l =>
    atlevel left l ++ atlevel right l

#guard atlevel [tree| 1] 1 = [1]
#guard atlevel [tree| 1 * (2 + 3)] 2 = [2, 3]
#guard atlevel [tree| 1 * (2 * (3 + 4) + 5 * (6 + 7))] 2 = [2, 5]
#guard atlevel [tree| 1 * (2 * (3 + 4) + 5 * (6 + 7))] 3 = [3, 4, 6, 7]
#guard atlevel [tree| 1] 0 = []
