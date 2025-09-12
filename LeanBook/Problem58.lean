/-
# 問題 58

生成＆テストパラダイムを適用して、指定したノード数の対称かつ完全平衡な二分木をすべて構成せよ。
-/
import LeanBook.Problem57

/-- ノード数が指定された対称かつ完全平衡な二分木をすべて構成する -/
def symCbalTrees (n : Nat) : List (BinTree Unit) :=
  cbalTree n |>.filter BinTree.isSymmetric

#guard (symCbalTrees 5).length = 2
#guard (symCbalTrees 6).length = 0
#guard (symCbalTrees 7).length = 1
#guard (symCbalTrees 8).length = 0
