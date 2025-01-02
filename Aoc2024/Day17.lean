import Std.Internal.Parsec.String
import Std.Data.HashSet.Basic
import Mathlib.Data.List.Monad 

open Std.Internal.Parsec.String

namespace Day17

structure Computer where
  a : Nat
  b : Nat
  c : Nat
  i : Nat
  program : Array (Fin 8)

namespace Computer

def parser : Parser Computer := do
  skipString "Register A: "
  let a ← digits
  ws
  skipString "Register B: "
  let b ← digits
  ws
  skipString "Register C: "
  let c ← digits
  ws
  skipString "Program: "
  let hd ← digits
  let tl ← (skipString "," *> digits).many
  let program := #[hd] ++ tl
  let program ← program.mapM fun a => if h : a < 8 then
      pure ⟨a, h⟩
    else
      Std.Internal.Parsec.fail "invalid program code"
  return { a, b, c, i := 0, program }

def combo (c : Computer) : Fin 8 → Nat
| 4 => c.a
| 5 => c.b
| 6 => c.c
| operand => operand 

def step (c : Computer) (out : Array Nat) : Option (Computer × Array Nat) := do
  let op ← c.program.get? c.i
  let operand ← c.program.get? (c.i + 1)
  return match op with
  | 0 => ({
      a := c.a / 2 ^ c.combo operand 
      b := c.b
      c := c.c
      i := c.i + 2
      program := c.program
    }, out)
  | 1 => ({
      a := c.a
      b := c.b ^^^ operand
      c := c.c
      i := c.i + 2
      program := c.program
    }, out)
  | 2 => ({
      a := c.a
      b := c.combo operand % 8
      c := c.c
      i := c.i + 2
      program := c.program
    }, out)
  | 3 => if c.a = 0 then
      ({
        a := c.a
        b := c.b
        c := c.c
        i := c.i + 2
        program := c.program
      }, out)
    else
      ({
        a := c.a
        b := c.b
        c := c.c
        i := operand
        program := c.program
      }, out)
  | 4 => ({
      a := c.a
      b := c.b ^^^ c.c
      c := c.c
      i := c.i + 2
      program := c.program
    }, out)
  | 5 => ({
      a := c.a
      b := c.b
      c := c.c
      i := c.i + 2
      program := c.program
    }, out.push (c.combo operand % 8))
  | 6 => ({
      a := c.a
      b := c.a / 2 ^ c.combo operand
      c := c.c
      i := c.i + 2
      program := c.program
    }, out)
  | 7 => ({
      a := c.a
      b := c.b
      c := c.a / 2 ^ c.combo operand
      i := c.i + 2
      program := c.program
    }, out)

def run (c : Computer) (out : Array Nat) : Nat → Array Nat
| 0 => out
| n + 1 => if let some (c', out') := c.step out then c'.run out' n else out

def output (c : Computer) : String :=
 ",".intercalate <| c.run #[] 1000 |>.map toString |>.toList

def runQuine (c : Computer) (out : Array Nat) : Nat → Bool
| 0 => false
| n + 1 => if (out.zipWith c.program (· == ·)).all id then
    if let some (c', out') := c.step out then 
      c'.runQuine out' n
    else
      c.program.map Fin.val = out  
  else
    false

-- only good enough for the test and not the task 
def findQuine (c : Computer) : Option Nat := List.head? <| List.range 1000000
  |>.filter fun a =>
    let c : Computer := {
      a
      b := c.b
      c := c.c
      i := c.i
      program := c.program 
    }
    c.runQuine #[] 100

end Computer 

namespace Task1

def main : IO Unit := do
  let text ← IO.FS.readFile (System.FilePath.mk "Data/Day17/test.txt")
  let computer ← IO.ofExcept (Computer.parser.run text)
  println! "Test: {computer.output}"
  println! "Expected: {"4,6,3,5,6,3,5,2,1,0"}"
  let text ← IO.FS.readFile (System.FilePath.mk "Data/Day17/task.txt")
  let computer ← IO.ofExcept (Computer.parser.run text)
  println! "Task: {computer.output}"

end Task1

namespace Task2

/-

The program looks like this:

0:
b <- a % 8
b <- b ^ 1
c <- a >> b
b <- b ^ c
b <- b ^ 4
a <- a >> 3
print b % 8 
if a = 0 halt
else
jump 0

so, the printed value just depends on `a`, and `a` shifts down by three each loop

-/

def findOutput (a : Nat) : Fin 8 :=
  let b := a % 8
  let b := b ^^^ 1
  let c := a / (2 ^ b)
  let b := b ^^^ c
  let b := b ^^^ 4
  Fin.ofNat' 8 b

def findQuine (c : Computer) : List Nat := do
  let () ← guard <| c.program = #[2, 4, 1, 1, 7, 5, 4, 4, 1, 4, 0, 3, 5, 5, 3, 0]
  let mut as : Std.HashSet Nat := {0}
  for x in c.program.reverse do
    as := Std.HashSet.ofList <| do
      let a ← as.toList
      let r ← List.range 8
      let () ← guard <| findOutput (a * 8 + r) = x
      return a * 8 + r
  as.toList 

def main : IO Unit := do
  let text ← IO.FS.readFile (System.FilePath.mk "Data/Day17/test2.txt")
  let computer ← IO.ofExcept (Computer.parser.run text)
  println! "Test: {computer.findQuine}"
  println! "Expected: {some 117440}"
  let text ← IO.FS.readFile (System.FilePath.mk "Data/Day17/task.txt")
  let computer ← IO.ofExcept (Computer.parser.run text)
  if let some a := (findQuine computer).min? then
    println! "Task: {a}"
    let c : Computer := {
      a
      b := computer.b
      c := computer.c
      i := computer.i
      program := computer.program
    }
    println! "Output: {c.output}"
    println! "Expected: {c.program}"
  else
    println! "Task: did not find quine"

end Task2

def main : IO Unit := do
  println! "Day 17"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day17
