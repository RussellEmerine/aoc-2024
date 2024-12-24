import Lean.Data.Json.Parser
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Monad
import Mathlib.Algebra.Group.Nat.Even
import «Aoc2024».Counter

namespace Day11

open Std.Internal.Parsec.String

def blink (stones : Counter Nat) : Counter Nat := Id.run <| do
  let mut counter := Std.HashMap.empty 
  for (stone, count) in stones do 
    let d := Nat.log 10 stone + 1
    if stone = 0 then 
      counter := Counter.add counter 1 count
    else if Even d then
      counter := Counter.add counter (stone / 10 ^ (d / 2)) count
      counter := Counter.add counter (stone % 10 ^ (d / 2)) count 
    else
      counter := Counter.add counter (stone * 2024) count
  return counter 

def count_stones (stones : List Nat) (times : Nat) : Nat :=
  stones |> Counter.ofList |> blink^[times] |> Counter.total 

def parser : Parser (Array Nat) := (Lean.Json.Parser.nat <* ws).many

namespace Task1

def main : IO Unit := do
  let line ← IO.FS.readFile (System.FilePath.mk "Data/Day11/test.txt")
  let stones ← IO.ofExcept (parser.run line)
  println! "Test: {count_stones stones.toList 25}"
  println! "Expected: {55312}"
  let line ← IO.FS.readFile (System.FilePath.mk "Data/Day11/task.txt")
  let stones ← IO.ofExcept (parser.run line)
  println! "Task: {count_stones stones.toList 25}"

end Task1

namespace Task2

def main : IO Unit := do
  let line ← IO.FS.readFile (System.FilePath.mk "Data/Day11/task.txt")
  let stones ← IO.ofExcept (parser.run line)
  println! "Task: {count_stones stones.toList 75}"

end Task2

def main : IO Unit := do
  println! "Day 11"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day11
