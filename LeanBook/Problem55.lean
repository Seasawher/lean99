/-
# 問題 55
(中級 🌟🌟) 完全平衡二分木を構成せよ。

完全平衡二分木では、すべてのノードについて「左部分木と右部分木のノード数の差が1以下」という性質が成り立つ。

与えられたノード数に対して、すべての完全平衡二分木を構成する関数 `cbalTree` を実装せよ。すべての解をバックトラックで生成すること。

> **注意**
>
> 完全平衡二分木は（高さ）平衡二分木とは異なる。
-/

/- ## 二分木とその構文定義 -/

/-- 2分木 -/
inductive BinTree (α : Type) where
  | empty
  | node (val : α) (left right : BinTree α)
deriving DecidableEq, BEq

/-- 空の二分木 -/
notation:max "∅" => BinTree.empty

variable {α : Type}

/-- 2分木の葉 -/
def BinTree.leaf (a : α) : BinTree α := .node a ∅ ∅

@[inherit_doc]
notation:max "⟦" x "⟧" => BinTree.leaf x

/- ### 2分木の表示 -/

protected def BinTree.toString [ToString α] (t : BinTree α) : String :=
  match t with
  | empty => "∅"
  | node val .empty .empty =>
    toString val
  | node val left right =>
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

/- ### 2分木を表現する構文 -/

open Lean

/-- 2分木を構成する構文カテゴリ -/
declare_syntax_cat bintree
syntax "[tree| " bintree "]" : term

/-- 木のラベル。ラベルとしては、数値リテラル・文字列リテラル・文字リテラルを許可する -/
syntax tree_label := num <|> str <|> char

/-- 基底ケース: `[tree| 42]`などは正しい構文 -/
syntax tree_label : bintree

/-- 基底ケース: `[tree| ∅]` は空の木に相当するので正しい構文 -/
syntax "∅" : bintree

/-- 再帰ステップ -/
syntax tree_label " * " "(" bintree " + " bintree ")" : bintree

/-- `tree_label`に属する構文を`term`に変換する -/
def expandTreeLabel (stx : TSyntax `tree_label) : MacroM (TSyntax `term) :=
  match stx with
  | `(tree_label| $num:num) => `(term| $num)
  | `(tree_label| $str:str) => `(term| $str)
  | `(tree_label| $char:char) => `(term| $char)
  | _ => Macro.throwUnsupported

macro_rules
  | `([tree| ∅]) => `(BinTree.empty)
  | `([tree| $v:tree_label]) => do
    let label ← expandTreeLabel v
    `(BinTree.leaf $label)
  | `([tree| $v:tree_label * ($l + $r)]) => do
    let label ← expandTreeLabel v
    `(BinTree.node $label [tree| $l] [tree| $r])

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

/- ### Repr の定義 -/

def BinTree.reprPrec [Repr α] (tree : BinTree α) : String :=
  "[tree| " ++ helper tree ++ "]"
where
  helper : BinTree α → String
  | .empty => "∅"
  | .node v .empty .empty => reprStr v
  | .node v left right =>
    reprStr v ++ " * " ++ "(" ++ helper left ++ " + " ++ helper right ++ ")"

instance [Repr α] : Repr (BinTree α) where
  reprPrec := fun tree _ => BinTree.reprPrec tree

#eval [tree| 1 * (2 + 3)]
#eval [tree| 12 * (2 + ∅)]
#eval [tree| 1 * (2 * (3 + 4) + 5 * (6 + 7))]
#eval [tree| 'x' * ('y' + 'z')]

/- ## 回答 -/

/-- 2分木のノード数 -/
def BinTree.nodes {α : Type} : BinTree α → Nat
  | .empty => 0
  | .node _ l r => 1 + l.nodes + r.nodes

/-- 2分木が完全平衡か判定 -/
def BinTree.isCBalanced {α : Type} : BinTree α → Bool
  | .empty => true
  | .node _ l r =>
    Int.natAbs ((l.nodes : Int) - (r.nodes : Int)) ≤ 1 && l.isCBalanced && r.isCBalanced

/-- List型のモナドインスタンス -/
instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

/-- ノード数が `x` の完全平衡二分木をすべて構成する -/
partial def cbalTree (x : Nat) : List (BinTree Unit) :=
  match x with
  | 0 => [.empty]
  | n + 1 => do
    let q := n / 2
    let r := n % 2
    let indices := List.range (q + r + 1) |>.drop q
    let i ← indices
    let left ← cbalTree i
    let right ← cbalTree (n - i)
    pure (BinTree.node () left right)

-- `cbalTree` で生成される木の数を確認
#guard (cbalTree 3).length = 1
#guard (cbalTree 4).length = 4
#guard (cbalTree 7).length = 1

-- `cbalTree` で生成される木はすべて完全平衡
#guard (cbalTree 3)|>.map BinTree.isCBalanced |>.and
#guard (cbalTree 4)|>.map BinTree.isCBalanced |>.and
#guard (cbalTree 5)|>.map BinTree.isCBalanced |>.and
#guard (cbalTree 6)|>.map BinTree.isCBalanced |>.and
