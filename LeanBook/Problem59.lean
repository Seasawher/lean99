/-
# 問題 59

高さ平衡二分木を構成せよ。

高さ平衡二分木では、次の性質がすべてのノードに対して成り立つ：
> その左部分木の高さと右部分木の高さはほぼ等しく、その差は高々 1 である。

与えられた要素と与えられた最大高さに対して、すべての高さ平衡二分木のリストを構成せよ。
-/
import LeanBook.Problem58

variable {α β : Type}

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
