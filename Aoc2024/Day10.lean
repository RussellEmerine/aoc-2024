import Std.Data.HashSet.Basic
import «Aoc2024».GridArray

namespace Day10

def scoreAux (grid : GridArray m n Nat) (ps : Std.HashSet (Idx m n)) (i : Nat) : Nat :=
  if i > 9 then
    ps.size
  else
    scoreAux grid (Std.HashSet.ofList <| do
      let p ← ps.toList
      let d ← Direction.univ
      let p' ← (p.move d).toList 
      let () ← guard <| grid.get p' = i
      return p'
    ) (i + 1)
termination_by 10 - i
  
def score (grid : GridArray m n Nat) (p : Idx m n) : Nat :=
  scoreAux grid (if grid.get p = 0 then {p} else {}) 1

def scoreSum (grid : GridArray m n Nat) : Nat :=
  score grid <$> GridArray.indices m n |>.sum 

def ratingAux (grid : GridArray m n Nat) (ps : List (Idx m n)) (i : Nat) : Nat :=
  if i > 9 then
    ps.length
  else
    ratingAux grid (do
      let p ← ps
      let d ← Direction.univ
      let p' ← (p.move d).toList 
      let () ← guard <| grid.get p' = i
      return p'
    ) (i + 1)
termination_by 10 - i
  
def rating (grid : GridArray m n Nat) (p : Idx m n) : Nat :=
  ratingAux grid (if grid.get p = 0 then {p} else {}) 1

def ratingSum (grid : GridArray m n Nat) : Nat :=
  rating grid <$> GridArray.indices m n |>.sum 

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/test.txt")
  let lines ← match lines.mapM (·.toList.mapM (·.toString.toNat?)) with
    | some a => pure a 
    | none => IO.throwServerError "oops had a non-digit in my digit grid"
  let ⟨_, _, grid⟩ ← IO.ofExcept <| GridArray.ofLines (lines.map List.toArray)
  println! "Test: {scoreSum grid}"
  println! "Expected: {36}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/task.txt")
  let lines ← match lines.mapM (·.toList.mapM (·.toString.toNat?)) with
    | some a => pure a 
    | none => IO.throwServerError "oops had a non-digit in my digit grid"
  let ⟨_, _, grid⟩ ← IO.ofExcept <| GridArray.ofLines (lines.map List.toArray)
  println! "Task: {scoreSum grid}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/test.txt")
  let lines ← match lines.mapM (·.toList.mapM (·.toString.toNat?)) with
    | some a => pure a 
    | none => IO.throwServerError "oops had a non-digit in my digit grid"
  let ⟨_, _, grid⟩ ← IO.ofExcept <| GridArray.ofLines (lines.map List.toArray)
  println! "Test: {ratingSum grid}"
  println! "Expected: {81}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day10/task.txt")
  let lines ← match lines.mapM (·.toList.mapM (·.toString.toNat?)) with
    | some a => pure a 
    | none => IO.throwServerError "oops had a non-digit in my digit grid"
  let ⟨_, _, grid⟩ ← IO.ofExcept <| GridArray.ofLines (lines.map List.toArray)
  println! "Task: {ratingSum grid}"

end Task2

def main : IO Unit := do
  println! "Day 10"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day10
