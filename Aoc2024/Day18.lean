import Std.Internal.Parsec.String
import «Aoc2024».Util.GridArray 
import «Aoc2024».Util.WeightedGraph
import «Aoc2024».Util.UnionFind 

open Std.Internal.Parsec.String

namespace Day18

def parseFinPair n : Parser (Idx n n) := do
  let a ← digits
  skipString ","
  let b ← digits
  if h : a < n ∧ b < n then
    return (⟨a, h.left⟩, ⟨b, h.right⟩)
  else
    Std.Internal.Parsec.fail "position is out of bounds"

namespace Task1

def solve (ps : Array (Idx (n + 1) (n + 1))) (i : Nat) : Option Nat := do
  let mut grid : GridArray (n + 1) (n + 1) Bool := GridArray.ofFn fun _ _ => true 
  for p in ps[:i] do
    grid := grid.set p false
  let g : WeightedGraph (Idx (n + 1) (n + 1)) Nat := {
    edges p := Direction.univ.filterMap p.move |>.filter grid.get |>.map (·, 1)
  }
  (g.dijkstra (0, 0)).get? (Fin.last n, Fin.last n)

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day18/test.txt")
  let ps ← IO.ofExcept <| lines.mapM (parseFinPair 7).run 
  println! "Test: {solve ps 12}"
  println! "Expected: {22}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day18/task.txt")
  let ps ← IO.ofExcept <| lines.mapM (parseFinPair 71).run 
  println! "Task: {solve ps 1024}"

end Task1

namespace Task2

def solve (ps : Array (Idx (n + 1) (n + 1))) : Option (Idx (n + 1) (n + 1)) := do
  let mut grid : GridArray (n + 1) (n + 1) Bool := GridArray.ofFn fun _ _ => true 
  for p in ps do
    grid := grid.set p false
  let mut uf := UnionFind.empty (Idx.equivFinMul (n + 1) (n + 1)) 
  for p in GridArray.indices (n + 1) (n + 1) do
    for d in Direction.univ do
      if let some p' := (p.move d).filter (grid.get p ∧ grid.get ·) then
        uf := uf.union p p'
  let startIdx : Idx (n + 1) (n + 1) := (0, 0)
  let endIdx : Idx (n + 1) (n + 1) := (Fin.last n, Fin.last n)
  let (uf', b) := uf.checkEquiv startIdx endIdx 
  if b then
    failure 
  uf := uf'
  for p in ps.reverse do
    grid := grid.set p true 
    for d in Direction.univ do
      if let some p' := (p.move d).filter (grid.get p ∧ grid.get ·) then
        uf := uf.union p p'
    let (uf', b) := uf.checkEquiv startIdx endIdx
    if b then
      return p
    uf := uf'
  failure 

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day18/test.txt")
  let ps ← IO.ofExcept <| lines.mapM (parseFinPair 7).run 
  println! "Test: {solve ps}"
  println! "Expected: {some (6, 1)}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day18/task.txt")
  let ps ← IO.ofExcept <| lines.mapM (parseFinPair 71).run 
  println! "Task: {solve ps}"

end Task2

def main : IO Unit := do
  println! "Day 18"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day18
