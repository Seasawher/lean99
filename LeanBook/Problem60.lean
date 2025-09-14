/- # 問題60

与えられたノード数の高さ平衡二分木を構成する

## 問題文

高さが `H` の高さ平衡二分木を考えよう。この木が含みうる最大ノード数はいくつか？

明らかに、最大ノード数は`MaxN = 2^H − 1`である。しかし、最小ノード数 `MinN` はどうだろうか？これはより難しい問題である。再帰的な関係式を見つけ、それを関数 `minNodes` にして「高さ `H` の高さ平衡二分木における最小ノード数」を返すようにしてみよ。

一方で、逆の問いを立てることもできる。すなわち、与えられたノード数 N をもつ高さ平衡二分木の**最大の高さ H** はいくつか？これを計算する関数 `maxHeight` を書いてみよ。

これで、主問題に取り組める：
**与えられたノード数の高さ平衡二分木をすべて構成せよ。**

`N = 15` の場合、高さ平衡二分木はいくつ存在するかを求めよ。

## 回答

### minNodes

`MinNodes` 関数は `MinNodes (h + 2) = MinNodes (h + 1) + MinNodes h + 1` という漸化式を満たすことがわかる。したがって、`MinNodes h` は次のように計算できる。
-/
import LeanBook.Problem59

def MinNodes (h : Nat) : Nat :=
  match h with
  | 0 => 0
  | 1 => 1
  | h + 2 => MinNodes (h + 1) + MinNodes h + 1

#guard MinNodes 1 = 1
#guard MinNodes 2 = 2
#guard MinNodes 3 = 4

/- ### maxHeight

`maxHeight` と `MinNodes` の間には、`maxHeight(N) = max_{H} { minNodes(H) ≤ N }` という関係式が成り立つ。
したがって、`maxHeight` は次のように計算できる。
-/

/-- 与えられたノード数`n`を持つ高さ平衡二分木の最大の高さ -/
def maxHeight (n : Nat) : Nat := Id.run do
  let mut hight := 1
  while MinNodes hight ≤ n do
    hight := hight + 1
  return hight - 1

#guard maxHeight 1 = 1
#guard maxHeight 2 = 2
#guard maxHeight 3 = 2
#guard maxHeight 4 = 3

/- ### 回答

よって以下のように計算ができる。
-/

variable {α : Type}

-- Alternative のインスタンスにする
instance : Alternative List where
  failure := @List.nil
  orElse l l' := List.append l (l' ())

/-- 与えられたノード数の高さ平衡二分木をすべて構成する -/
def hbalTreeNodes (a : α) (n : Nat) : List (BinTree α) := do
  -- ノード数`n`の高さ平衡二分木の高さとしてあり得る値を網羅したリスト
  let minHeight := Nat.log2 (n + 1)
  let heightRange := List.range (1 + maxHeight n)
    |>.drop minHeight
  -- 高さを一つ選択
  let height ← heightRange
  -- 高さを指定すれば高さ平衡二分木は全列挙できるので、ひとつ選択する
  let tree ← hbalTrees a height
  -- ノード数が実際に`n`であるようなものだけフィルターする
  guard <| tree.nodes = n
  return tree

#guard hbalTreeNodes 0 1 = [[tree| 0]]
#guard hbalTreeNodes 0 2 = [[tree| 0 * (∅ + 0)], [tree| 0 * (0 + ∅)]]
#guard (hbalTreeNodes 'x' 15).length = 1553
