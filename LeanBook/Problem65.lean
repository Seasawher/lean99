/- # 問題65


-/
import LeanBook.Problem64

variable {α : Type} [ToString α]

/-- 二分木のレイアウト情報を受け取って、それのエッジのx座標距離を `2 ^ level` 倍に拡張する -/
def BinTree.expand (tree : BinTree (α × (Nat × Nat))) (level : Nat) : BinTree (α × (Nat × Nat)) :=
  sorry

/-- P64とは異なる二分木の描画レイアウト。

* 一番深いところにある親子ノードの、親ノードと子ノードのx座標距離が`1`
* 木全体の高さを`h`としたとき、深さが`h - k`の子ノードと、その親ノードのx座標距離が`2 ^ k`
-/
def layoutLevelConstant (tree : BinTree α) : BinTree (α × (Nat × Nat)) :=
  sorry
