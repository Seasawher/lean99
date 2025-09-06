/-- 2分木 -/
inductive BinTree (α : Type) where
  | empty
  | node (val : α) (left right : BinTree α)
deriving DecidableEq, BEq

notation:max "∅" => BinTree.empty

variable {α : Type}

/-- 2分木の葉 -/
def BinTree.leaf (a : α) : BinTree α := .node a ∅ ∅

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
      toString val
    else
      toString val ++ " * " ++ "(" ++ BinTree.toString left ++ " + " ++ BinTree.toString right ++ ")"

instance [ToString α] : ToString (BinTree α) where
  toString := BinTree.toString

#guard toString ⟦1⟧ = "1"
#guard toString (BinTree.node 1 ⟦2⟧ .empty) = "1 * (2 + ∅)"
#guard toString (BinTree.node 1 ⟦2⟧ ⟦3⟧) = "1 * (2 + 3)"
#guard
  let tree := BinTree.node 1
    (left := BinTree.node 2 ⟦3⟧ ⟦4⟧)
    (right := BinTree.node 5 ⟦6⟧ ⟦7⟧)
  toString tree = "1 * (2 * (3 + 4) + 5 * (6 + 7))"

/- ## 2分木を表現する構文 -/

/-- 2分木を構成する構文カテゴリ -/
declare_syntax_cat bintree
syntax "[tree| " bintree "]" : term

/-- 基底ケース: `[tree| 42]` のようなものは葉に相当するので正しい構文 -/
syntax num : bintree

/-- 基底ケース: `[tree| ∅]` は空の木に相当するので正しい構文 -/
syntax "∅" : bintree

/-- 再帰ステップ -/
syntax num " * " "(" bintree " + " bintree ")" : bintree

#check_failure [tree| 1 * (2 + 3)]
#check_failure [tree| 1 * (2 + ∅)]
#check_failure [tree| 1 * (2 * (3 + 4) + 5 * (6 + 7))]

macro_rules
  | `([tree| ∅]) => `(BinTree.empty)
  | `([tree| $num:num]) => `(BinTree.leaf $num)
  | `([tree| $v:num * ($l + $r)]) => `(BinTree.node $v [tree| $l] [tree| $r])

#guard
  let actual := [tree| 1 * (2 + 3)]
  let expected := BinTree.node 1 ⟦2⟧ ⟦3⟧
  actual = expected

#guard
  let actual := [tree| 12 * (2 + ∅)]
  let expected := BinTree.node 12 ⟦2⟧ ∅
  actual = expected

#guard
  let actual := [tree| 1 * (2 * (3 + 4) + 5 * (6 + 7))]
  let expected := BinTree.node 1
    (left := BinTree.node 2 ⟦3⟧ ⟦4⟧)
    (right := BinTree.node 5 ⟦6⟧ ⟦7⟧)
  actual = expected

/- ## Repr の定義 -/

def BinTree.reprPrec [ToString α] (tree : BinTree α) : String :=
  "[tree| " ++ toString tree ++ "]"

instance [ToString α] : Repr (BinTree α) where
  reprPrec := fun tree _ => BinTree.reprPrec tree

#eval [tree| 1 * (2 + 3)]
#eval [tree| 12 * (2 + ∅)]
#eval [tree| 1 * (2 * (3 + 4) + 5 * (6 + 7))]
