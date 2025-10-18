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

/-- 二分木のレイアウト情報を受け取って、それのエッジのx座標距離を `expand` 倍に拡張する -/
def BinTree.expand (tree : BinTree (α × (Nat × Nat))) (expand : Nat) : BinTree (α × (Nat × Nat)) :=
  tree.shift (fun (x, y) => ((x - 1) * expand + 1, y))

-- テストコード
#guard
  let tree := [tree| 'u' * ('p' * (∅ + 'q') + ∅)]
  let pos := HashMap.ofList [('u', (3, 1)), ('p', (1, 2)), ('q', (2, 3))]
  let layout := tree.attachPos! pos
  let actual := layout.expand 2

  let expectedPos := HashMap.ofList [('u', (5, 1)), ('p', (1, 2)), ('q', (3, 3))]
  let expected := tree.attachPos! expectedPos
  actual == expected

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
