import LeanBook.Problem61A

def internals {α : Type} (t : BinTree α) : List α :=
  match t with
  | .empty => []
  | .node _ .empty .empty => [] -- 葉
  | .node v left right =>
    -- 葉じゃない
    [v] ++ internals left ++ internals right

#guard internals [tree| 1] = []
#guard internals [tree| 1 * (2 + 3)] = [1]
#guard internals [tree| 1 * (2 * (3 + 4) + 5 * (6 + 7))] = [1,2,5]
