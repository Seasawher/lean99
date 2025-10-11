/- # 問題65


-/
import LeanBook.Problem64

open Std

variable {α : Type} [ToString α] [Hashable α] [BEq α] [Inhabited α]

/-- 二分木に対して、ラベルごとの位置情報を受け取って、二分木をレイアウト情報を返す -/
def BinTree.attachPos! {β : Type} [Inhabited β] (tree : BinTree α) (pos : HashMap α (β × β)) : BinTree (α × (β × β)) :=
  match tree with
  | .empty => .empty
  | .node v l r =>
    let p := pos[v]!
    .node (v, p) (l.attachPos! pos) (r.attachPos! pos)

#guard
  let actual := [tree| 'a' * ('b' + 'c')]
    |>.attachPos! (HashMap.ofList [('a', (2, 1)), ('b', (1, 0)), ('c', (3, 0))])
  let expected := BinTree.node ('a', (2, 1))
    (BinTree.leaf ('b', (1, 0)))
    (BinTree.leaf ('c', (3, 0)))
  actual == expected

/-- 二分木の根を取得する -/
def BinTree.root? (tree : BinTree α) : Option α :=
  match tree with
  | .empty => none
  | .node v _ _ => some v

/-- 各ノードのy座標はそのまま。x座標を、左からではなくて、木の根ノードから見た相対位置とする。-/
def BinTree.relativeLayout (tree : BinTree (α × (Nat × Nat))) : BinTree (α × (Int × Int)) :=
  let root? := tree.root?
  match root? with
  | none => .empty
  | some (_, (rootX, _)) =>
    tree.shift (fun (x, y) => ((x - rootX : Int), (y : Int)))

#guard
  let tree := [tree| 'u' * ('p' * (∅ + 'q') + ∅)]
  let pos := HashMap.ofList [('u', (3, 1)), ('p', (1, 2)), ('q', (2, 3))]
  let layout := tree.attachPos! pos
  let actual := layout.relativeLayout

  let expectedPos := HashMap.ofList [('u', (0, 1)), ('p', (-2, 2)), ('q', (-1, 3))]
  let expected := tree.attachPos! expectedPos
  actual == expected

/-- 二分木のレイアウト情報を受け取って、それのエッジのx座標距離を `2 ^ level` 倍に拡張する -/
def BinTree.expand (tree : BinTree (α × (Nat × Nat))) (level : Nat) : BinTree (α × (Nat × Nat)) :=
  -- 各ノードのy座標はそのまま
  -- x座標を、左からではなくて、木の根ノードから見た相対位置とする
  let relativeLayout := tree.relativeLayout
  .empty

-- テストコード
-- #eval
--   let tree := [tree| 'u' * ('p' * (∅ + 'q') + ∅)]
--   let pos := HashMap.ofList [('u', (3, 1)), ('p', (1, 2)), ('q', (2, 3))]
--   let layout := tree.attachPos! pos
--   let actual := layout.expand 1

--   let expectedPos := HashMap.ofList [('u', (5, 1)), ('p', (1, 2)), ('q', (3, 3))]
--   let expected := tree.attachPos! expectedPos
--   actual == expected

/-- P64とは異なる二分木の描画レイアウト。

* 一番深いところにある親子ノードの、親ノードと子ノードのx座標距離が`1`
* 木全体の高さを`h`としたとき、深さが`h - k`の子ノードと、その親ノードのx座標距離が`2 ^ k`
-/
def layoutLevelConstant (tree : BinTree α) : BinTree (α × (Nat × Nat)) :=
  sorry
