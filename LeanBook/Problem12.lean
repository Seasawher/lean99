/-
# 問題 12
(中級 🌟🌟) 問題11で生成されたランレングス符号化リストから元のリストを復元せよ。
-/
import LeanBook.Problem11

variable {α : Type} [BEq α]

open Data

def decodeModified (l : List (Data α)) : List α :=
  match l with
  | [] => []
  | (multiple n a) :: t => (List.replicate n a) ++ decodeModified t
  | (single a) :: t => a :: decodeModified t

#guard decodeModified [multiple 2 'a', single 'b', multiple 2 'c'] == ['a', 'a', 'b', 'c', 'c']
#guard decodeModified [single 'a', single 'b', single 'c'] == ['a', 'b', 'c']
#guard decodeModified [multiple 3 '2', multiple 2 '1', single '9'] == ['2', '2', '2', '1', '1', '9']
