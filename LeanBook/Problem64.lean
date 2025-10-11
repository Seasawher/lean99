/- # 問題64

2分木を画像として描画するためのレイアウトを計算する。
-/
/- ## 2分木を画像として描画する

2分木のレイアウト情報 `layout : BinTree (α × (Nat × Nat))` が与えられたときに、その描画情報を SVG 画像として描画する関数をまず実装する。
-/
import LeanBook.Problem63
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay

open ProofWidgets Svg

variable {α : Type} [ToString α]

structure Config where
  /-- ノードを表現する円の半径 -/
  radius : Nat
  /-- ノードの円の塗りつぶし色 (RGB) -/
  fillColor : Float × Float × Float
  /-- ノードのラベルのフォントサイズ -/
  fontsize : Nat

/-- デフォルトの設定値 -/
private def defaultConfig : Config where
  radius := 16
  fillColor := (0.74, 0.87, 1.0)
  fontsize := 14

/-- 2分木のノードの描画情報 -/
structure NodeData (f : Frame) where
  /-- x座標 -/
  x : Float
  /-- y座標 -/
  y : Float
  /-- 上面と下面を反転して計測したy座標 -/
  yf : Float := f.height.toFloat - y
  /-- ノードのラベル -/
  label : String

def NodeData.ofPair (f : Frame) (pair : α × Nat × Nat) (step : Float) : NodeData f :=
  let (a, x, y) := pair
  { x := x.toFloat * step, y := y.toFloat * step, label := toString a }

private def defaultFrame : Frame where
  xmin := 0
  ymin := 0
  xSize := 450
  width := 450
  height := 450

/-- ノード（円とラベル）を作成する -/
def createNodeElement (f : Frame) (node : NodeData f) (config : Config) : Array (Element f) :=
  let (r, g, b) := config.fillColor
  #[
    circle (node.x, node.yf) (.px config.radius)
    |>.setFill (r, g, b),

    text (node.x - 5, node.yf - 5) node.label (.px config.fontsize)
    |>.setFill (0.0, 0.0, 0.0)
  ]

/-- `createNodeElement` の表示結果をテストするための関数 -/
def createNodeHtml (f := defaultFrame) (node : NodeData f) (config := defaultConfig) : Html :=
  let svg : Svg f := { elements := createNodeElement f node config }
  svg.toHtml

#html createNodeHtml (node := { x := 150, y := 30, label := "A" })

/-- エッジ（ノードの親子関係）を作成する -/
def createEdgeElement (f : Frame) (parent child : NodeData f) : Element f :=
  line (parent.x, parent.yf) (child.x, child.yf)
  |>.setStroke (50., 50., 50.) (.px 2)

/-- `createEdgeElement` の表示結果をテストするための関数 -/
def createEdgeHtml (f := defaultFrame) (parent child : NodeData f) : Html :=
  let svg : Svg f := { elements := #[createEdgeElement f parent child] }
  svg.toHtml

#html createEdgeHtml
  (parent := { x := 150, y := 30, label := "A" })
  (child := { x := 100, y := 80, label := "B" })

/-- 二分木のノードを（木の構造を壊して）リストにする -/
def BinTree.toNodes {β : Type} (tree : BinTree β) : List β :=
  match tree with
  | .empty => []
  | .node a left right => a :: (toNodes left ++ toNodes right)

/-- 二分木のエッジをリストにする。(親, 子) のペアにして返すことに注意。 -/
def BinTree.toEdges {β : Type} (tree : BinTree β) : List (β × β) :=
  match tree with
  | .empty => []
  | .node a left right =>
    let leftEdges :=
      match left with
      | .empty => []
      | .node b _ _ => [(a, b)] ++ toEdges left
    let rightEdges :=
      match right with
      | .empty => []
      | .node c _ _ => [(a, c)] ++ toEdges right
    leftEdges ++ rightEdges

#guard [tree| 1 * (2 + 3 * (4 + ∅))].toEdges = [(1, 2), (1, 3), (3, 4)]

def BinTree.toElementsFromLayout (f : Frame) (config : Config) (tree : BinTree (α × (Nat × Nat))) (step : Float) : Array (Svg.Element f) :=
  let nodes : Array (Element f) := tree.toNodes
    |>.map (NodeData.ofPair f (step := step))
    |>.toArray
    |>.map (fun node => createNodeElement f node config)
    |>.flatten

  let edges := tree.toEdges
    |>.map (fun ((v1, x1, y1), (v2, x2, y2)) => (NodeData.ofPair f (v1, x1, y1) step, NodeData.ofPair f (v2, x2, y2) step))
    |>.map (fun (parent, child) => createEdgeElement f parent child)
    |>.toArray

  edges ++ nodes

/-- ２分木の描画情報が与えられたときに、それを SVG 画像として描画する -/
def BinTree.toHtmlFromLayout (tree : BinTree (α × (Nat × Nat))) (step := 30.0) : Html :=
  let svg : Svg defaultFrame := { elements := tree.toElementsFromLayout defaultFrame defaultConfig step }
  svg.toHtml

#html
  let treeLayout := BinTree.node ("A", (2, 1))
    (.node ("B", (1, 2)) .empty .empty)
    (.node ("C", (4, 2))
      (.node ("D", (3, 3)) .empty .empty)
      (.node ("E", (5, 3)) .empty .empty))
  BinTree.toHtmlFromLayout treeLayout

#html BinTree.toHtmlFromLayout (BinTree.leaf (3, (1, 1)))

/- ## 回答 -/

/-- ２分木のレイアウト情報が渡されたときに、各ノードのレイアウト位置を一様にずらす -/
def BinTree.shift {β γ : Type} (tree : BinTree (α × (β × β))) (shiftFn : β × β → γ × γ) : BinTree (α × (γ × γ)) :=
  match tree with
  | .empty => .empty
  | .node (a, (x, y)) left right =>
    let (x', y') := shiftFn (x, y)
    .node (a, (x', y')) (shift left shiftFn) (shift right shiftFn)

/-- ２分木の幅 -/
def BinTree.width (tree : BinTree α) : Nat :=
  tree.nodes - 1

#guard [tree| 1 * (2 + ∅)].width = 1
#guard [tree| 1 * (2 + 3)].width = 2
#guard [tree| 'c' * ('a' + 'h' * ('g' * ('e' + ∅) + ∅))].width = 4

/-- 2分木に対して、描画情報を付与する関数。各ノードの描画位置を指定している。 -/
def BinTree.layout (t : BinTree α) : BinTree (α × (Nat × Nat)) :=
  match t with
  | .empty => .empty
  | .node a .empty .empty =>
    .node (a, (1, 1)) .empty .empty
  | .node a .empty right =>
    let rightLayout := layout right
    let rightShifted := rightLayout.shift (fun (x, y) => (x + 1, y + 1))
    .node (a, (1, 1)) .empty rightShifted
  | .node a left .empty =>
    let leftLayout := layout left
    let leftShifted := leftLayout.shift (fun (x, y) => (x, y + 1))
    .node (a, left.width + 2, 1) leftShifted .empty
  | .node a left right =>
    let leftLayout := layout left
    let rightLayout := layout right
    let leftShifted := leftLayout.shift (fun (x, y) => (x, y + 1))
    let rightShifted := rightLayout.shift (fun (x, y) => (x + (left.width + 2) * 1, y + 1))
    .node (a, (left.width + 2, 1)) leftShifted rightShifted

#guard
  let actual := (BinTree.layout [tree| 'a' * ('b' + ∅)]).toNodes
  let expected := [
    ('a', (2, 1)),
    ('b', (1, 2))
  ]
  actual = expected

#guard
  let actual := (BinTree.layout [tree| 'a' * ('b' + 'c')]).toNodes
  let expected := [
    ('a', (2, 1)),
    ('b', (1, 2)),
    ('c', (3, 2))
  ]
  actual = expected

#guard
  let actual := (BinTree.layout [tree| 'a' * ('b' * ('c' + ∅) + ∅)]).toNodes
  let expected := [
    ('a', (3, 1)),
    ('b', (2, 2)),
    ('c', (1, 3))
  ]
  actual = expected

#guard
  let actual := (BinTree.layout [tree| 'a' * ('b' * (∅ + 'c') + ∅)]).toNodes
  let expected := [
    ('a', (3, 1)),
    ('b', (1, 2)),
    ('c', (2, 3))
  ]
  actual = expected

#guard
  let actual := (BinTree.layout [tree| 'a' * ('b' * (∅ + 'c') + 'd' * ('e' + ∅))]).toNodes
  let expected := [
    ('a', (3, 1)),
    ('b', (1, 2)),
    ('c', (2, 3)),
    ('d', (5, 2)),
    ('e', (4, 3))
  ]
  actual = expected

#html BinTree.toHtmlFromLayout (BinTree.layout [tree| 1 * (∅ + 2)])
#html BinTree.toHtmlFromLayout (BinTree.layout [tree| 1 * (2 + ∅)])
#html BinTree.toHtmlFromLayout (BinTree.layout [tree| 1 * (2 + 3)])
#html BinTree.toHtmlFromLayout (BinTree.layout [tree| 'a' * ('b' * (∅ + 'c') + ∅)])
#html BinTree.toHtmlFromLayout (BinTree.layout [tree| 1 * (2 * (6 + 7) + 3 * (4 + 5))])
#html BinTree.toHtmlFromLayout (BinTree.layout [tree| 'a' * ('b' * (∅ + 'c') + 'd' * ('e' + ∅))])
#html
  let tree := [tree| 'n' * ('k' * ('c' * ('a' + 'h' * ('g' * ('e' + ∅) + ∅)) + 'm') + 'u' * ('p' * (∅ + 's' * ('q' + ∅)) + ∅))]
  BinTree.toHtmlFromLayout tree.layout
