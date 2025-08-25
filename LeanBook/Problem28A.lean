/-
# 問題 28A
(中級 🌟🌟) サブリストの長さでリストのリストをソートせよ。
-/
variable {α : Type}

def lsort (l : List (List α)) : List (List α) :=
  List.mergeSort l (fun l₁ l₂ => l₁.length ≤ l₂.length)

#guard lsort [["a", "b", "c"], ["a", "b"], ["a"]] == [["a"], ["a", "b"], ["a", "b", "c"]]
#guard lsort [[3, 1, 4], [1, 5, 9, 2], [6, 5, 3, 5], [1]] == [[1], [3, 1, 4], [1, 5, 9, 2], [6, 5, 3, 5]]
