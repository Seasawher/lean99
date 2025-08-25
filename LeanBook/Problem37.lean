/-
# 問題 37
(中級 🌟🌟) オイラーのトーシェント関数 φ(m) を（改良版で）計算せよ。

オイラーのトーシェント関数の定義は[問題34](./Problem34.md)を参照。もし[問題36](./Problem36.md)のように素因数分解のリストが分かっていれば、次の式で効率的に φ(m) を計算できる：

$$
φ(m) = ∏_{i=1}^{n} (p_i - 1) * p_i^{(m_i - 1)}
$$
-/

/-- n の素因数とその重複度のリスト型 -/
abbrev PrimeFactor := List (Nat × Nat)

def φ (_n : Nat) (factors : PrimeFactor) : Nat :=
  factors.foldl (fun acc (p, m) => acc * (p - 1) * p ^ (m - 1)) 1

#guard φ 10 [(2, 1), (5, 1)] == 4
#guard φ 20 [(2, 2), (5, 1)] == 8
#guard φ 39 [(3, 1), (13, 1)] == 24
