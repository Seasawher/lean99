/-
# 問題 56

二分木が「根を通る垂直線で左右の部分木が鏡像関係にある」とき、その木を対称（symmetric）と呼ぶことにする。与えられた二分木が対称かどうか判定する述語 symmetric/1 を実装せよ。

> ヒント: まず2つの木が鏡像関係かどうか判定する mirror/2 を実装せよ。ノードの内容ではなく構造だけに注目する。
-/
import LeanBook.Problem55

variable {α : Type}

def BinTree.mirror (s t : BinTree α) : Bool :=
  match s, t with
  | .empty, .empty => true
  | .node _ a b, .node _ x y => mirror a y && mirror b x
  | _, _ => false

def BinTree.isSymmetric (t : BinTree α) : Bool :=
  match t with
  | .empty => true
  | .node _ l r => mirror l r

#guard [tree| 1].isSymmetric
#guard ! [tree| 1 * (2 + ∅)].isSymmetric
#guard [tree| 1 * (2 + 2)].isSymmetric
