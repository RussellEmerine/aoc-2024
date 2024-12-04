import «Aoc2024».GridArray

namespace Day4

namespace Task1

def possible_words_int (p : Int × Int) (len : Nat) : List (List (Int × Int)) := do
  let (i, j) := p
  let (d₁, d₂) ← [(1, 1), (1, 0), (1, -1), (0, -1), (-1, -1), (-1, 0), (-1, 1), (0, 1)]
  return (List.range len).map fun r => (i + d₁ * r, j + d₂ * r)

def possible_words_fin (p : Fin m × Fin n) (len : Nat) : List (List (Fin m × Fin n)) := 
  (possible_words_int (p.fst, p.snd) len).filterMap fun word =>
    word.mapM fun (i, j) =>
      if h : 0 ≤ i ∧ i < m ∧ 0 ≤ j ∧ j < n then
        have hi : i.toNat < m := by
          rw [Int.toNat_lt]
          exact h.right.left
          exact h.left 
        have hj : j.toNat < n := by
          rw [Int.toNat_lt]
          exact h.right.right.right
          exact h.right.right.left 
        some (⟨i.toNat, hi⟩, ⟨j.toNat, hj⟩)
      else 
        none 

def task1 (grid : GridArray m n Char) : Nat :=
  let words := GridArray.indices m n >>= (possible_words_fin · 4)
  words.countP fun word => grid.get <$> word = "XMAS".toList

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day4/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray)))
  println! "Test: {task1 grid}"
  println! "Expected: {18}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day4/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray)))
  println! "Task: {task1 grid}"

end Task1

namespace Task2

def ex_int (p : Int × Int) : List (Int × Int) := 
  let (i, j) := p
  [(i, j), (i - 1, j - 1), (i + 1, j + 1), (i - 1, j + 1), (i + 1, j - 1)]

def possible_ex_fin (p : Fin m × Fin n) : Option (List (Fin m × Fin n)) :=
  let ex := ex_int (p.fst, p.snd)
  ex.mapM fun (i, j) =>
    if h : 0 ≤ i ∧ i < m ∧ 0 ≤ j ∧ j < n then
      have hi : i.toNat < m := by
        rw [Int.toNat_lt]
        exact h.right.left
        exact h.left 
      have hj : j.toNat < n := by
        rw [Int.toNat_lt]
        exact h.right.right.right
        exact h.right.right.left 
      some (⟨i.toNat, hi⟩, ⟨j.toNat, hj⟩)
    else 
      none 

def task2 (grid : GridArray m n Char) : Nat :=
  let exes := (GridArray.indices m n).filterMap possible_ex_fin
  let valid := ["AMSMS", "AMSSM", "ASMMS", "ASMSM"]
  exes.countP fun word => List.elem (grid.get <$> word) (String.toList <$> valid)

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day4/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray)))
  println! "Test: {task2 grid}"
  println! "Expected: {9}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day4/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray)))
  println! "Task: {task2 grid}"

end Task2

def main : IO Unit := do
  println! "Day 4"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day4
