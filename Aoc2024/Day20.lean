import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Dist
import «Aoc2024».Util.GridArray
import «Aoc2024».Util.WeightedGraph
import «Aoc2024».Day16 

namespace Day20

open Day16 -- Maze, Maze.ofLines

def graph (maze : Maze m n) : WeightedGraph (Idx m n) Nat where
  edges p := Direction.univ.filterMap p.move |>.filter maze.grid.get |>.map (·, 1)

def CheatsSavingAtLeast (maze : Maze m n) (t : Nat) : Nat :=
  let bestPathStart := (graph maze).dijkstra maze.startTile
  let bestPathEnd := (graph maze).dijkstra maze.endTile
  List.length <| do
    let p₁ ← GridArray.indices m n
    let d₁ ← Direction.univ
    let d₂ ← Direction.univ
    let p₂ ← p₁.move d₁ |>.bind (·.move d₂) |>.toList
    let () ← guard <| maze.grid.get p₁ ∧ maze.grid.get p₂
    let best ← bestPathStart.get? maze.endTile |>.toList 
    let a ← bestPathStart.get? p₁ |>.toList
    let b ← bestPathEnd.get? p₂ |>.toList
    let () ← guard <| a + b + 2 + t ≤ best
    return () 

def dist (p₁ p₂ : Idx m n) : Nat := 
  p₁.fst.val.dist p₂.fst.val + p₁.snd.val.dist p₂.snd.val
  
def LongCheats (p : Idx m n) (len : Nat) : List (Idx m n) := do
  let d ← Direction.univ
  let p₁ ← List.iterate (·.bind (·.move d)) (p.move d) len |>.reduceOption 
  let p₂ ← List.iterate (·.bind (·.move d.cw)) (some p₁) len |>.reduceOption
  let () ← guard <| dist p p₂ ≤ len 
  return p₂ 

def LongCheatsSavingAtLeast (maze : Maze m n) (len : Nat) (t : Nat) : Nat :=
  let bestPathStart := (graph maze).dijkstra maze.startTile
  let bestPathEnd := (graph maze).dijkstra maze.endTile
  List.length <| do
    let p₁ ← GridArray.indices m n
    let p₂ ← LongCheats p₁ len
    let () ← guard <| maze.grid.get p₁ ∧ maze.grid.get p₂
    let best ← bestPathStart.get? maze.endTile |>.toList 
    let a ← bestPathStart.get? p₁ |>.toList
    let b ← bestPathEnd.get? p₂ |>.toList
    let () ← guard <| a + b + dist p₁ p₂ + t ≤ best
    return () 

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day20/test.txt")
  let ⟨_, _, maze⟩ ← IO.ofExcept <| Maze.ofLines lines 
  println! "Test: {CheatsSavingAtLeast maze 20}"
  println! "Expected: {5}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day20/task.txt")
  let ⟨_, _, maze⟩ ← IO.ofExcept <| Maze.ofLines lines 
  println! "Task: {CheatsSavingAtLeast maze 100}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day20/test.txt")
  let ⟨_, _, maze⟩ ← IO.ofExcept <| Maze.ofLines lines 
  println! "Test: {LongCheatsSavingAtLeast maze 20 76}"
  println! "Expected: {3}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day20/task.txt")
  let ⟨_, _, maze⟩ ← IO.ofExcept <| Maze.ofLines lines 
  println! "Task: {LongCheatsSavingAtLeast maze 20 100}"

end Task2

def main : IO Unit := do
  println! "Day 20"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day20
