/-
# 問題 32
(中級 🌟🌟) 2つの正の整数の最大公約数をユークリッドの互除法で求めよ。
-/

-- これは使わないこと
#check Nat.gcd

/-- ユークリッドの互除法 -/
partial def gcd (m n : Nat) : Nat :=
  if m = 0 then
    n
  else
    gcd (n % m) m

#guard gcd 6 0 == 6
#guard gcd 1 37 == 1
#guard gcd 6 15 == 3
#guard gcd 21 3 == 3
#guard gcd 42998431 120019 == 1
