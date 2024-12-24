import Mathlib.Logic.Equiv.List
import Std.Data.HashSet.Basic 
import «Aoc2024».Counter 
import «Aoc2024».GridArray 
import «Aoc2024».UnionFind 

namespace Day12

namespace Task1

def price (grid : GridArray m n Char) : Nat := Id.run <| do
  let e := Idx.equivFinMul m n 
  let mut uf := UnionFind.empty e
  for p₁ in GridArray.indices m n do
    for p₂ in Direction.univ >>= Option.toList ∘ p₁.move do
      if grid.get p₁ = grid.get p₂ then
        uf := uf.union p₁ p₂
  let mut area : Counter (Idx m n) := Std.HashMap.empty
  let mut perimeter : Counter (Idx m n) := Std.HashMap.empty 
  for p in GridArray.indices m n do
    let (uf', r) := uf.find p
    uf := uf'
    area := Counter.add area r 1 
    for d in Direction.univ do
      if some (grid.get p) ≠ grid.get <$> (p.move d) then
        perimeter := Counter.add perimeter r 1
  let mut roots : Std.HashSet (Idx m n) := {}
  for p in GridArray.indices m n do
    let (uf', r) := uf.find p
    uf := uf'
    roots := roots.insert r
  return roots.toList |>.map (fun p => area[p]! * perimeter[p]!) |>.sum 

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day12/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray)))
  println! "Test: {price grid}"
  println! "Expected: {1930}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day12/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray)))
  println! "Task: {price grid}"

end Task1

namespace Task2

/-

discounted price: number of sides is the same as number of corners.
there is a corner in region X (Y is anything not X, not necessarily one region) when

XY
YY

or

YX
XX

and this is two corners (not four)

XY
YX

so in that case only add for the internal and not external 

-/
def price (grid : GridArray m n Char) : Nat := Id.run <| do
  let e := Idx.equivFinMul m n 
  let mut uf := UnionFind.empty e
  for p₁ in GridArray.indices m n do
    for p₂ in Direction.univ >>= Option.toList ∘ p₁.move do
      if grid.get p₁ = grid.get p₂ then
        uf := uf.union p₁ p₂
  let mut area : Counter (Idx m n) := Std.HashMap.empty
  let mut sides : Counter (Idx m n) := Std.HashMap.empty 
  for p in GridArray.indices m n do
    let (uf', r) := uf.find p
    uf := uf'
    area := Counter.add area r 1 
    for d in Direction.univ do
      -- the first case, 90° internal 
      if some (grid.get p) ≠ grid.get <$> p.move d
       ∧ some (grid.get p) ≠ grid.get <$> p.move d.cw then
        sides := Counter.add sides r 1
      -- the second case, 90° external
      if h : some (grid.get p) ≠ grid.get <$> p.move d
       ∧ (p.move d).isSome
       ∧ grid.get <$> p.move d = grid.get <$> p.move d.cw
       ∧ grid.get <$> p.move d = grid.get <$> (p.move d >>= (·.move d.cw)) then
        let (uf', r) := uf.find ((p.move d).get h.right.left)
        uf := uf'
        sides := Counter.add sides r 1
  let mut roots : Std.HashSet (Idx m n) := {}
  for p in GridArray.indices m n do
    let (uf', r) := uf.find p
    uf := uf'
    roots := roots.insert r
  return roots.toList |>.map (fun p => area[p]! * sides[p]!) |>.sum 

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day12/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray)))
  println! "Test: {price grid}"
  println! "Expected: {1206}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day12/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept (GridArray.ofLines (lines.map (·.toList.toArray)))
  println! "Task: {price grid}"

end Task2

def main : IO Unit := do
  println! "Day 12"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day12
