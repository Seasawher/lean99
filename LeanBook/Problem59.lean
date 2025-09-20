/-
# 問題 59

高さ平衡二分木を構成せよ。

高さ平衡二分木では、次の性質がすべてのノードに対して成り立つ：
> その左部分木の高さと右部分木の高さはほぼ等しく、その差は高々 1 である。

与えられた要素と与えられた最大高さに対して、すべての高さ平衡二分木のリストを構成せよ。
-/
import LeanBook.Problem58

/-- 高さが `height` の高さ平衡二分木をすべて構成する -/
partial def hbalTrees {α : Type} (a : α) (height : Nat) : List (BinTree α) :=
  match height with
  | 0 => [.empty]
  | 1 => [.leaf a]
  | h + 2 => do
    let (hl, hr) ← [(h, h + 1), (h + 1, h + 1), (h + 1, h)]
    let l ← hbalTrees a hl
    let r ← hbalTrees a hr
    return BinTree.node a l r

#guard (hbalTrees 'a' 2).length = 3
#guard (hbalTrees 'a' 3).length = 15

