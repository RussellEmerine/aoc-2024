import Std.Internal.Parsec.String
import Mathlib.Data.ZMod.Basic
import «Aoc2024».GridArray

open Std.Internal.Parsec.String

namespace Day14

def parseInt : Parser Int := Int.ofNat <$> digits <|> do
  skipString "-"
  let num ← digits
  return -(Int.ofNat num)

structure Robot (m n : Nat) where
  p : ZMod m × ZMod n
  v : ZMod m × ZMod n 

namespace Robot

def parser (m n : Nat) : Parser (Robot m n) := do
  skipString "p="
  let p₁ ← parseInt
  skipString ","
  let p₂ ← parseInt
  ws
  skipString "v="
  let v₁ ← parseInt
  skipString ","
  let v₂ ← parseInt
  -- this does the necessary coes
  return { p := (p₁, p₂), v := (v₁, v₂) }

def move (robot : Robot m n) (dist : Nat) : Robot m n where 
  p := robot.p + dist • robot.v
  v := robot.v

def safetyFactor (robots : List (Robot m n)) : Nat :=
  let (a, b, c, d) := List.sum <| robots.map fun robot =>
    if robot.p.fst.val < m / 2 ∧ robot.p.snd.val < n / 2 then
      (1, 0, 0, 0)
    else if robot.p.fst.val < m / 2 ∧ robot.p.snd.val > n / 2 then
      (0, 1, 0, 0)
    else if robot.p.fst.val > m / 2 ∧ robot.p.snd.val < n / 2 then
      (0, 0, 1, 0)
    else if robot.p.fst.val > m / 2 ∧ robot.p.snd.val > n / 2 then
      (0, 0, 0, 1)
    else
      (0, 0, 0, 0)
  a * b * c * d 

instance : ToString (List (Robot (m + 1) (n + 1))) where
  toString robots := Id.run <| do
    let mut grid : GridArray (m + 1) (n + 1) Bool := GridArray.ofFn fun _ _ => false
    for robot in robots do
      grid := grid.set robot.p true
    "\n".intercalate (grid.array.toList.map fun row => String.mk (row.toList.map (bool ' ' '*')))

end Robot 

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day14/test.txt")
  let robots ← IO.ofExcept (lines.mapM (Robot.parser 11 7).run)
  let moved := robots.toList.map (Robot.move · 100)
  println! "Test: {Robot.safetyFactor moved}"
  println! "Expected: {12}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day14/task.txt")
  let robots ← IO.ofExcept (lines.mapM (Robot.parser 101 103).run)
  let moved := robots.toList.map (Robot.move · 100)
  println! "Test: {Robot.safetyFactor moved}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day14/task.txt")
  let robots ← IO.ofExcept (lines.mapM (Robot.parser 101 103).run)
  let moved := robots.toList.map (Robot.move · 8159)
  println! "Task 2"
  println! "Step count: {8159}"
  println! "{toString moved}"
/-
After looking into the output of the following code...
  for i in List.range 1000 do
    let moved := robots.toList.map (Robot.move · i)
    println! "Step count: {i}"
    println! "{toString moved}"
    println! ""
I notice there's a vertical pattern at 103j + 22
and a horizontal pattern at 101k + 79.
Setting these equal,
  103j + 22 = 101k + 79
by modular arithmetic magic we have
  2j + 22 = 79 (mod 101) => j = 79
  -2k + 79 = 22 (mod 103) => k = 80
so that's why we do 
  103 * 79 + 22 = 101 * 80 + 79 = 8159 
-/

end Task2

def main : IO Unit := do
  println! "Day 14"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day14
