import Mathlib.Data.List.Monad
import Mathlib.Data.Nat.Log
import Std.Internal.Parsec.String 

open Std.Internal.Parsec.String 

namespace Day7 

structure Equation where
  value : Nat
  numbers : List Nat

namespace Equation

def parser : Parser Equation := do
  let value ← digits 
  skipString ":"
  let numbers ← (ws *> digits).many
  return { value, numbers := numbers.toList }  

def evaluations (values : List Nat) : List Nat → List Nat
| [] => values
| (x :: xs) => evaluations (values >>= fun v => [v + x, v * x]) xs 

def possible (eq : Equation) : Bool := match eq.numbers with
| [] => false
| (x :: xs) => eq.value ∈ evaluations [x] xs

def concat (x y : Nat) : Nat :=
  let b := Nat.log 10 y + 1
  x * 10 ^ b + y

def evaluations' (max : Nat) (values : List Nat) : List Nat → List Nat
| [] => values
| (x :: xs) => evaluations' max (values >>= fun v => [v + x, v * x, concat v x].filter (· ≤ max)) xs 

def possible' (eq : Equation) : Bool := match eq.numbers with
| [] => false
| (x :: xs) => eq.value ∈ evaluations' eq.value [x] xs

end Equation

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day7/test.txt")
  let eqs ← lines.mapM (IO.ofExcept ∘ Equation.parser.run)
  println! "Test: {eqs.toList.filter Equation.possible |>.map Equation.value |>.sum}"
  println! "Expected: {3749}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day7/task.txt")
  let eqs ← lines.mapM (IO.ofExcept ∘ Equation.parser.run)
  println! "Task: {eqs.toList.filter Equation.possible |>.map Equation.value |>.sum}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day7/test.txt")
  let eqs ← lines.mapM (IO.ofExcept ∘ Equation.parser.run)
  println! "Test: {eqs.toList.filter Equation.possible' |>.map Equation.value |>.sum}"
  println! "Expected: {11387}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day7/task.txt")
  let eqs ← lines.mapM (IO.ofExcept ∘ Equation.parser.run)
  println! "Task: {eqs.toList.filter Equation.possible' |>.map Equation.value |>.sum}"

end Task2

def main : IO Unit := do
  println! "Day 7"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day7
