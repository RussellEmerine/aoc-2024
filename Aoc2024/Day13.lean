import Std.Internal.Parsec.String
import Mathlib.Algebra.Group.Action.Prod

open Std.Internal.Parsec.String

namespace Day13

structure ClawMachine where
  a : Nat × Nat
  b : Nat × Nat
  prize : Nat × Nat

namespace ClawMachine

def win (cm : ClawMachine) (play : Nat × Nat) : Bool :=
  play.fst • cm.a + play.snd • cm.b = cm.prize

def tokens (play : Nat × Nat) : Nat :=
  3 * play.fst + play.snd

/-
x * a₁ + y * b₁ = p₁
x * a₂ + y * b₂ = p₂

x * a₁ * b₂ + y * b₁ * b₂ = p₁ * b₂
x * a₂ * b₁ + y * b₁ * b₂ = p₂ * b₁

x * (a₁ * b₂ - a₂ * b₁) = p₁ * b₂ - p₂ * b₁ 

x * a₁ * a₂ + y * b₁ * a₂ = p₁ * a₂
x * a₁ * a₂ + y * b₂ * a₂ = p₂ * a₁

y * (b₁ * a₂ - b₂ * a₁) = p₁ * a₂ - p₂ * a₁ 
-/
def play (cm : ClawMachine) : Option (Nat × Nat) := do
  let a₁ := Int.ofNat cm.a.fst
  let a₂ := Int.ofNat cm.a.snd
  let b₁ := Int.ofNat cm.b.fst
  let b₂ := Int.ofNat cm.b.snd
  let p₁ := Int.ofNat cm.prize.fst
  let p₂ := Int.ofNat cm.prize.snd
  let x ← Int.toNat' <| (p₁ * b₂ - p₂ * b₁) / (a₁ * b₂ - a₂ * b₁)
  let y ← Int.toNat' <| (p₁ * a₂ - p₂ * a₁) / (b₁ * a₂ - b₂ * a₁)
  let () ← guard <| cm.win (x, y)
  return (x, y)

def minTokens (cm : ClawMachine) : Option Nat := do
  let play ← cm.play
  return 3 * play.fst + play.snd

def parser : Parser ClawMachine := do
  skipString "Button A: X+"
  let a₁ ← digits
  skipString ", Y+"
  let a₂ ← digits
  ws
  skipString "Button B: X+"
  let b₁ ← digits
  skipString ", Y+"
  let b₂ ← digits
  ws
  skipString "Prize: X="
  let p₁ ← digits
  skipString ", Y="
  let p₂ ← digits
  return { a := (a₁, a₂), b := (b₁, b₂), prize := (p₁, p₂) }

end ClawMachine

namespace Task1

def main : IO Unit := do
  let text ← IO.FS.readFile (System.FilePath.mk "Data/Day13/test.txt")
  let cms ← IO.ofExcept (Parser.run (ClawMachine.parser <* ws).many.attempt text)
  println! "Test: {cms.filterMap ClawMachine.minTokens |>.toList |>.sum}"
  println! "Expected: {480}"
  let text ← IO.FS.readFile (System.FilePath.mk "Data/Day13/task.txt")
  let cms ← IO.ofExcept (Parser.run (ClawMachine.parser <* ws).many.attempt text)
  println! "Task: {cms.filterMap ClawMachine.minTokens |>.toList |>.sum}"

end Task1

namespace Task2

def diff : Nat := 10000000000000

def adjust_prize (cm : ClawMachine) : ClawMachine where
  a := cm.a
  b := cm.b
  prize := (cm.prize.fst + diff, cm.prize.snd + diff)

def main : IO Unit := do
  let text ← IO.FS.readFile (System.FilePath.mk "Data/Day13/task.txt")
  let cms ← IO.ofExcept (Parser.run (ClawMachine.parser <* ws).many.attempt text)
  let cms := cms.map adjust_prize
  println! "Task: {cms.filterMap ClawMachine.minTokens |>.toList |>.sum}"

end Task2

def main : IO Unit := do
  println! "Day 13"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day13
