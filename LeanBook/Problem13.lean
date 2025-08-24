/-
# 問題 13
(中級 🌟🌟) ランレングス符号化を直接実装せよ。問題9のように重複部分のサブリストを明示的に作らず、カウントだけを行うこと。問題11のように (1 X) は X に簡約せよ。
-/
import LeanBook.Problem11

variable {α : Type} [BEq α] [Inhabited α]

open Data

def encodeDirect (l : List α) : List (Data α) :=
  counting l |>.map fun (n, a) =>
    if n == 1 then
      single a
    else
      multiple n a
where
  counting : List α → List (Nat × α)
    | [] => []
    | [a] => [(1, a)]
    | a :: b :: t =>
      if a != b then
        (1, a) :: counting (b :: t)
      else
        let (n, a) := counting (b :: t) |>.head!
        (n + 1, a) :: (counting (b :: t) |>.tail!)

#guard encodeDirect ['a', 'a', 'b', 'c'] == [multiple 2 'a', single 'b', single 'c']
#guard
  let actual := encodeDirect ['a', 'b', 'b', 'b', 'c', 'b', 'b']
  let expected := [single 'a', multiple 3 'b', single 'c', multiple 2 'b']
  actual == expected
