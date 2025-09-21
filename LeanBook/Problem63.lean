/- # 問題63

与えられたノード数の完全二分木を構成しなさい。
-/
import LeanBook.Problem55

variable {α : Type}

/-- 2分木のノード数 -/
def BinTree.size (t : BinTree α) : Nat :=
  match t with
  | .empty => 0
  | .node _ left right => 1 + left.size + right.size

#guard [tree| 1 * (2 + 3)].size = 3

/-- 2分木の高さ -/
def BinTree.height (t : BinTree α) : Nat :=
  match t with
  | .empty => 0
  | .node _ left right =>
    1 + max left.height right.height

#guard [tree| 1 * (2 + 3)].height = 2
#guard [tree| 1 * (2 * (3 + 4) + 5)].height = 3

/-- 2分木が完全二分木かどうか判定する -/
def BinTree.isComplete (t : BinTree α) : Bool :=
  2 ^ t.height - 1 == t.size

#guard (@BinTree.empty Unit).isComplete
#guard [tree| 1].isComplete
#guard [tree| 1 * (2 + 3)].isComplete
#guard ! [tree| 1 * (2 * (3 + 4) + 5)].isComplete
#guard [tree| 1 * (2 * (3 + 4) + 5 * (6 + 7))].isComplete

/-- 2分木に新しいノードを挿入する -/
def BinTree.insert (t : BinTree α) (x : α) : BinTree α :=
  match t with
  | .empty => .node x .empty .empty
  | .node v .empty .empty => .node v (.leaf x) .empty
  | .node v left right =>
    if left.height < right.height then
      .node v (left.insert x) right
    else if left.height = right.height then
      if left.isComplete && right.isComplete then
        .node v (left.insert x) right
      else if ! left.isComplete then
        .node v (left.insert x) right
      else
        .node v left (right.insert x)
    else
      .node v left (right.insert x)

#eval [tree| 1].insert 2
#eval [tree| 1 * (2 + 3)].insert 4
#eval [tree| 1 * (2 * (4 + ∅) + 3)].insert 5
#eval [tree| 1 * (2 * (4 + 5) + 3 * (6 + ∅))].insert 7

#guard [tree| 1].insert 2 = [tree| 1 * (2 + ∅)]
#guard [tree| 1 * (2 + ∅)].insert 3 = [tree| 1 * (2 + 3)]
#guard [tree| 1 * (2 + 3)].insert 4 = [tree| 1 * (2 * (4 + ∅) + 3)]
-- #guard [tree| 1 * (2 * (4 + ∅) + 3)].insert 5 = [tree| 1 * (2 * (4 + 5) + 3)]
#guard [tree| 1 * (2 * (4 + 5) + 3)].insert 6 = [tree| 1 * (2 * (4 + 5) + 3 * (6 + ∅))]
#guard [tree| 1 * (2 * (4 + 5) + 3 * (6 + ∅))].insert 7 = [tree| 1 * (2 * (4 + 5) + 3 * (6 + 7))]

def completeBinaryTree (x : α) (n : Nat) : BinTree α :=
  List.range n |>.foldl (fun t _ => t.insert x) BinTree.empty

#eval completeBinaryTree 'x' 7
#eval completeBinaryTree 'x' 10
