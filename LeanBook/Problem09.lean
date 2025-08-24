/-
# 問題 9
(中級 🌟🌟) リストの連続する重複要素をサブリストにまとめよ。
-/
import Plausible

variable {α : Type} [BEq α]

partial def pack (l : List α) : List (List α) :=
  match l with
  | [] => []
  | x :: _ =>
    let (packed, rest) := l.span (· == x)
    packed :: pack rest

def List.unpack (l : List (List α)) : List α :=
  match l with
  | [] => []
  | x :: xs => x ++ unpack xs

#test ∀ l : List Nat, (pack l).unpack == l
#test ∀ l : List String, (pack l).unpack == l
