/-- 2分木 -/
inductive BinTree (α : Type) where
  | empty
  | node (val : α) (left right : BinTree α)

variable {α : Type}

/-- 2分木の葉 -/
def BinTree.leaf (a : α) : BinTree α := .node a .empty .empty

def BinTree.isEmpty (t : BinTree α) : Bool :=
  match t with
  | empty => true
  | node _ _ _ => false

def BinTree.isLeaf (t : BinTree α) : Bool :=
  match t with
  | empty => false
  | node _ left right =>
    left.isEmpty && right.isEmpty

@[inherit_doc]
notation:max "⟦" x "⟧" => BinTree.leaf x

/- ## 2分木の表示 -/

protected def BinTree.toString [ToString α] (t : BinTree α) : String :=
  match t with
  | empty => "∅"
  | node val left right =>
    if t.isLeaf then
      "⟦" ++ toString val ++ "⟧"
    else
      toString val ++ " * " ++ "(" ++ BinTree.toString left ++ " + " ++ BinTree.toString right ++ ")"

instance [ToString α] : ToString (BinTree α) where
  toString := BinTree.toString

#guard toString ⟦1⟧ = "⟦1⟧"
#guard toString (BinTree.node 1 ⟦2⟧ .empty) = "1 * (⟦2⟧ + ∅)"
#guard toString (BinTree.node 1 ⟦2⟧ ⟦3⟧) = "1 * (⟦2⟧ + ⟦3⟧)"
#guard
  let tree := BinTree.node 1
    (left := BinTree.node 2 ⟦3⟧ ⟦4⟧)
    (right := BinTree.node 5 ⟦6⟧ ⟦7⟧)
  toString tree = "1 * (2 * (⟦3⟧ + ⟦4⟧) + 5 * (⟦6⟧ + ⟦7⟧))"
