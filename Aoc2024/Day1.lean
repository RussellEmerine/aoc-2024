import Mathlib.Data.Nat.Dist
import Std.Data.HashMap
import Std.Internal.Parsec.String 

open Std.Internal.Parsec.String 

namespace Day1

def parser : Parser (Nat × Nat) := do
  let a ← digits
  ws
  let b ← digits
  return (a, b) 

def getPairs (input : List String) : Option (List (Nat × Nat)) := 
  input.mapM <| Except.toOption ∘ parser.run

namespace Task1

def task1 (input : List String) : Option Nat := do
  let pairs ← getPairs input
  let (a, b) := pairs.unzip 
  let a := (a.toArray.qsort (·<·)).toList 
  let b := (b.toArray.qsort (·<·)).toList
  return (a.zipWith Nat.dist b).sum 

def main : IO Unit := do
  let test ← IO.FS.lines (System.FilePath.mk "Data/Day1/test.txt")
  println! "Test: {task1 test.toList}"
  println! "Expected: {some 11}"
  let task ← IO.FS.lines (System.FilePath.mk "Data/Day1/task.txt")
  println! "Task: {task1 task.toList}"

end Task1

namespace Task2

def N := 100000

def count (xs : List Nat) : Std.HashMap Nat Nat := 
  xs.foldl (fun a x => a.insert x (a.getD x 0 + 1)) Std.HashMap.empty

def task2 (input : List String) : Option Nat := do
  let pairs ← getPairs input
  let (a, b) := pairs.unzip 
  let a := (a.toArray.qsort (·<·)).toList 
  let b := (b.toArray.qsort (·<·)).toList
  let a := count a
  let b := count b
  return a.fold (fun s a c => s + a * c * b.getD a 0) 0

def main : IO Unit := do
  let test ← IO.FS.lines (System.FilePath.mk "Data/Day1/test.txt")
  println! "Test: {task2 test.toList}"
  println! "Expected: {some 31}"
  let task ← IO.FS.lines (System.FilePath.mk "Data/Day1/task.txt")
  println! "Task: {task2 task.toList}"

end Task2

def main : IO Unit := do
  println! "Day 1"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day1
