import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Data.List.Basic

namespace Day22

def pruneMod : Nat := 16777216

def mixPrune (a b : Nat) := (a ^^^ b) % pruneMod 

def step (a : Nat) : Nat :=
  let a₁ := mixPrune a (a * 64)
  let a₂ := mixPrune a₁ (a₁ / 32)
  mixPrune a₂ (a₂ * 2048)

abbrev Diff : Set Int := Set.Ioo (-10) 10

abbrev DiffSeq := Diff × Diff × Diff × Diff 

def diff (a b : Fin 10) : Diff where
  val := Int.ofNat b.val - Int.ofNat a.val
  property := by
    rcases a with ⟨a, ha⟩
    rcases b with ⟨b, hb⟩
    dsimp
    rw [Set.mem_Ioo]
    omega

def bananas (a : Nat) (n : Nat) : Std.HashMap DiffSeq Nat := Std.HashMap.ofList <| do
  -- reverse since Std.HashMap.ofList prioritizes later elements
  let tl ← List.iterate step a (n + 1) |>.map (Fin.ofNat' 10) |>.tails.reverse
  if let a₁ :: a₂ :: a₃ :: a₄ :: a₅ :: _ := tl then
    return ((diff a₁ a₂, diff a₂ a₃, diff a₃ a₄, diff a₄ a₅), a₅)
  else
    failure 
  
def mostBananas (as : List Nat) (n : Nat) : Nat := Id.run <| do
  let mut sums := Std.HashMap.empty
  for a in as do
    for (seq, b) in bananas a n do
      sums := sums.alter seq (some <| ·.getD 0 + b)
  return sums.values.max?.getD 0

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day22/test.txt")
  let nums ← IO.ofExcept <| (lines.mapM String.toNat?).elim (Except.error "line is not a number") Except.ok 
  println! "Test: {nums.map step^[2000] |>.toList.sum}"
  println! "Expected: {37327623}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day22/task.txt")
  let nums ← IO.ofExcept <| (lines.mapM String.toNat?).elim (Except.error "line is not a number") Except.ok 
  println! "Task: {nums.map step^[2000] |>.toList.sum}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day22/test2.txt")
  let nums ← IO.ofExcept <| (lines.mapM String.toNat?).elim (Except.error "line is not a number") Except.ok 
  println! "Test: {mostBananas nums.toList 2000}"
  println! "Expected: {23}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day22/task.txt")
  let nums ← IO.ofExcept <| (lines.mapM String.toNat?).elim (Except.error "line is not a number") Except.ok 
  println! "Task: {mostBananas nums.toList 2000}"

end Task2

def main : IO Unit := do
  println! "Day 22"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day22
