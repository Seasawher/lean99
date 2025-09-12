/-
# 問題 59

高さ平衡二分木を構成せよ。

高さ平衡二分木では、次の性質がすべてのノードに対して成り立つ：
> その左部分木の高さと右部分木の高さはほぼ等しく、その差は高々 1 である。

与えられた要素と与えられた最大高さに対して、すべての高さ平衡二分木のリストを構成せよ。
-/
import LeanBook.Problem58

/-- 高さが `height` の高さ平衡二分木をすべて構成する -/
partial def hbalTrees (height : Nat) : List (BinTree Unit) :=
  match height with
  | 0 => [.empty]
  | 1 => [.leaf ()]
  | h + 2 => do
    let (hl, hr) ← [(h, h + 1), (h + 1, h + 1), (h + 1, h)]
    let l ← hbalTrees hl
    let r ← hbalTrees hr
    return BinTree.node () l r

#guard (hbalTrees 2).length = 3
#guard (hbalTrees 3).length = 15
