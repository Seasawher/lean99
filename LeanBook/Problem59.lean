/-
# 問題 59

高さ平衡二分木を構成せよ。

高さ平衡二分木では、次の性質がすべてのノードに対して成り立つ：
> その左部分木の高さと右部分木の高さはほぼ等しく、その差は高々 1 である。

与えられた要素と与えられた最大高さに対して、すべての高さ平衡二分木のリストを構成せよ。
-/

/-- 二分木 -/
inductive BinTree (α : Type) where
  | empty : BinTree α
  | node : α → BinTree α → BinTree α → BinTree α

deriving Repr

def leaf {α : Type} (a : α) : BinTree α := .node a .empty .empty

variable {α : Type} [ToString α]

def BinTree.height (t : BinTree α) : Nat :=
  match t with
  | .empty => 0
  | .node _ l r => 1 + max l.height r.height

namespace ListMonad

/-- List型のモナドインスタンス -/
instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f
  map f l := l.map f

end ListMonad

open scoped ListMonad

variable {β : Type}

def List.product (as : List α) (bs : List β) : List (α × β) := do
  let a ← as
  let b ← bs
  return (a, b)

/-- 高さが `height` の高さ平衡二分木をすべて構成する -/
def hbalTrees (height : Nat) : List (BinTree Unit) :=
  match height with
  | 0 => [.empty]
  | 1 => [leaf ()]
  | h + 2 =>
    let t1s := hbalTrees (h + 1)
    let t2s := hbalTrees h
    let ts := List.product t1s t2s ++ List.product t2s t1s
    ts.map fun (t1, t2) => BinTree.node () t1 t2

#guard (hbalTrees 2 |>.length) = 2
#guard (hbalTrees 3 |>.length) = 4
