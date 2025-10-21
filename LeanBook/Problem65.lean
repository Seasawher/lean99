/- # 問題65


-/
import LeanBook.Problem64

open Std

variable {α : Type} [ToString α] [Hashable α] [BEq α] [Inhabited α]

/-- 二分木の根を取得する -/
def BinTree.root? (tree : BinTree α) : Option α :=
  match tree with
  | .empty => none
  | .node v _ _ => some v

/-- `tree` に対して、各ノードにそのノードの高さ情報を付与する。
例:
* `[tree| a * (b + c)]` において b と c の高さは 0 で、a の高さは 1
* `[tree| a * (b * (c + d) + ∅)]` において b の高さは 1 で、a の高さは 2
-/
def BinTree.attachHeight (tree : BinTree α) : BinTree (α × Nat) :=
  -- その木の高さ。これは`（root ノードの高さ) + 1`に等しい
  let globalHeight := tree.height
  let rec go (tree : BinTree α) (depth : Nat) : BinTree (α × Nat) :=
    match tree with
    | .empty => .empty
    | .node v l r =>
      let l' := go l (depth + 1)
      let r' := go r (depth + 1)
      .node (v, globalHeight - depth) l' r'
  go tree 1

#eval BinTree.attachHeight [tree| 'a' * ('b' + 'c')]
#eval BinTree.attachHeight [tree| 'a' * ('b' * ('c' + 'd') + ∅)]

/-- P64とは異なる二分木の描画レイアウト。

高さが`k`のノードと、その親ノードの間のx座標距離が`2 ^ k`
-/
def BinTree.layoutLevelConstant (tree : BinTree α) : BinTree (α × (Nat × Nat)) :=
  helper (tree.attachHeight)
where
  helper (tree : BinTree (α × Nat)) : BinTree (α × (Nat × Nat)) :=
    match tree with
    | .empty => .empty
    | .node (v, _) .empty .empty =>
      .node (v, (1, 1)) .empty .empty
    | .node (v, h) left .empty =>
      let left' := helper left
      let leftShifted := left'.shift (fun (x, y) => (x, y + 1))
      -- 左の部分木の根のノードのX座標
      let leftRootX := left'.root?
        |> (Prod.snd <$> ·)
        |> (Prod.fst <$> ·)
        |>.get!
      -- 根ノードのx座標
      let rootX := leftRootX + (2 ^ (h - 1))
      .node (v, (rootX, 1)) leftShifted .empty
    | .node (v, h) .empty right =>
      let right' := helper right
      let rightShifted := right'.shift (fun (x, y) => (x + (2 ^ (h - 1)), y + 1))
      -- 根ノードのx座標
      .node (v, (1, 1)) .empty rightShifted
    | .node (v, h) left right =>
      let left' := helper left
      let right' := helper right

      let leftShifted := left'.shift (fun (x, y) => (x, y + 1))
      -- 左の部分木の根のノードのx座標
      let leftRootX := left'.root?
        |> (Prod.snd <$> ·)
        |> (Prod.fst <$> ·)
        |>.get!
      -- 右の部分木の根のノードのx座標(単体で描画したとき)
      let rightRootX := right'.root?
        |> (Prod.snd <$> ·)
        |> (Prod.fst <$> ·)
        |>.get!
      -- 根のノードのx座標
      let rootX := leftRootX + (2 ^ (h - 1))
      let rightShifted := right'.shift (fun (x, y) => (x + rootX + (2 ^ (h - 1)) - rightRootX, y + 1))
      .node (v, (rootX, 1)) leftShifted rightShifted

#html BinTree.toHtmlFromLayout (BinTree.layoutLevelConstant [tree| 1 * (∅ + 2)])
#html BinTree.toHtmlFromLayout (BinTree.layoutLevelConstant [tree| 1 * (2 + ∅)])
#html BinTree.toHtmlFromLayout (BinTree.layoutLevelConstant [tree| 1 * (2 + 3)])
#html BinTree.toHtmlFromLayout (BinTree.layoutLevelConstant [tree| 'a' * ('b' * (∅ + 'c') + ∅)])
#html BinTree.toHtmlFromLayout (BinTree.layoutLevelConstant [tree| 'a' * (∅ + 'b' * (∅ + 'c'))])
#html BinTree.toHtmlFromLayout (BinTree.layoutLevelConstant [tree| 1 * (2 * (6 + 7) + 3 * (4 + 5))])
#html BinTree.toHtmlFromLayout (BinTree.layoutLevelConstant [tree| 'a' * ('b' * (∅ + 'c') + 'd' * ('e' + ∅))])
#html BinTree.toHtmlFromLayout (BinTree.layoutLevelConstant [tree| 'n' * ('k' * ('c' * ('a' + 'e' * ('d' + 'g')) + 'm') + 'u' * ('p' * (∅  + 'q') + ∅))])
