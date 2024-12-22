import Std.Data.HashSet.Basic
import «Aoc2024».GridArray 

namespace Day8

def antinodes (p₁ p₂ : Idx m n) : List (Idx m n) := do
  let q₁ := (Int.ofNat p₁.fst, Int.ofNat p₁.snd)
  let q₂ := (Int.ofNat p₂.fst, Int.ofNat p₂.snd)
  let a ← [2 * q₁ - q₂, 2 * q₂ - q₁]
  let a := (← a.fst.toNat'.toList, ← a.snd.toNat'.toList)
  -- i wonder if there's a `guard`-like way to do this
  if h : a.fst < m ∧ a.snd < n then
    return (⟨a.fst, h.left⟩, ⟨a.snd, h.right⟩)
  else 
    failure 

def antinode_locations (grid : GridArray m n Char) :
    Std.HashSet (Idx m n) := Std.HashSet.ofList <| do 
  let antennas := GridArray.indices m n |>.filter (grid.get · ≠ '.')
  let p₁ ← antennas 
  let p₂ ← antennas
  let () ← guard <| p₁ ≠ p₂ ∧ grid.get p₁ = grid.get p₂ 
  antinodes p₁ p₂ 

def antinodes' (p₁ p₂ : Idx m n) : List (Idx m n) := do
  let q₁ := (Int.ofNat p₁.fst, Int.ofNat p₁.snd)
  let q₂ := (Int.ofNat p₂.fst, Int.ofNat p₂.snd)
  let d := q₁ - q₂
  let g := d.fst.gcd d.snd 
  let d := (d.fst / g, d.snd / g)
  let x ← List.range 200 |>.map (Int.ofNat · - 100)
  let a := q₁ + x * d
  let a := (← a.fst.toNat'.toList, ← a.snd.toNat'.toList)
  -- i wonder if there's a `guard`-like way to do this
  if h : a.fst < m ∧ a.snd < n then
    return (⟨a.fst, h.left⟩, ⟨a.snd, h.right⟩)
  else 
    failure 

def antinode_locations' (grid : GridArray m n Char) :
    Std.HashSet (Idx m n) := Std.HashSet.ofList <| do 
  let antennas := GridArray.indices m n |>.filter (grid.get · ≠ '.')
  let p₁ ← antennas 
  let p₂ ← antennas
  let () ← guard <| p₁ ≠ p₂ ∧ grid.get p₁ = grid.get p₂ 
  antinodes' p₁ p₂ 

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day8/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept <| GridArray.ofLines <| lines.map <| List.toArray ∘ String.toList 
  println! "Test: {antinode_locations grid |>.size}"
  println! "Expected: {14}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day8/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept <| GridArray.ofLines <| lines.map <| List.toArray ∘ String.toList 
  println! "Test: {antinode_locations grid |>.size}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day8/test.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept <| GridArray.ofLines <| lines.map <| List.toArray ∘ String.toList 
  println! "Test: {antinode_locations' grid |>.size}"
  println! "Expected: {34}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day8/task.txt")
  let ⟨_, _, grid⟩ ← IO.ofExcept <| GridArray.ofLines <| lines.map <| List.toArray ∘ String.toList 
  println! "Test: {antinode_locations' grid |>.size}"

end Task2

def main : IO Unit := do
  println! "Day 8"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day8
