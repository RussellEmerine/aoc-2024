import Lean.Data.Json.Parser

namespace Day2

open Std.Internal.Parsec.String 

def parser : Parser (Array Nat) := Std.Internal.Parsec.many <| do
  let a ← Lean.Json.Parser.natNonZero
  ws
  return a

namespace Task1

def safe (report : List Nat) : Bool :=
  let pairs := report.zip report.tail 
  (pairs.all fun (a, b) => a > b ∧ a - b ≤ 3) ∨ pairs.all fun (a, b) => a < b ∧ b - a ≤ 3

def task1 (input : List String) : Option Nat := do
  let data ← input.mapM <| (Array.toList <$> ·) ∘ Except.toOption ∘ parser.run
  let safe_reports := safe <$> data 
  return safe_reports.count Bool.true 

def main : IO Unit := do 
  let test ← IO.FS.lines (System.FilePath.mk "Data/Day2/test.txt")
  println! "Test: {task1 test.toList}"
  println! "Expected: {some 2}"
  let task ← IO.FS.lines (System.FilePath.mk "Data/Day2/task.txt")
  println! "Test: {task1 task.toList}"

end Task1 

namespace Task2

def safe (report : List Nat) : Bool :=
  (List.range report.length).any fun i =>
    let (pre, suf) := report.splitAt i 
    let fixed := pre ++ suf.tail
    Task1.safe fixed 

def task2 (input : List String) : Option Nat := do
  let data ← input.mapM <| (Array.toList <$> ·) ∘ Except.toOption ∘ parser.run
  let safe_reports := safe <$> data 
  return safe_reports.count Bool.true 

def main : IO Unit := do 
  let test ← IO.FS.lines (System.FilePath.mk "Data/Day2/test.txt")
  println! "Test: {task2 test.toList}"
  println! "Expected: {some 4}"
  let task ← IO.FS.lines (System.FilePath.mk "Data/Day2/task.txt")
  println! "Test: {task2 task.toList}"

end Task2

def main : IO Unit := do
  println! "Day 1"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day2 
