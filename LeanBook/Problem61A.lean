import LeanBook.Problem61

def leaves {α : Type} (t : BinTree α) : List α :=
  match t with
  | .empty => []
  | .node v .empty .empty => [v]
  | .node _ left right =>
    leaves left ++ leaves right

#guard leaves [tree| 1] = [1]
#guard leaves [tree| 1 * (2 + 3)] = [2,3]
#guard leaves [tree| 1 * (2 * (3 + 4) + 5 * (6 + 7))] = [3,4,6,7]
