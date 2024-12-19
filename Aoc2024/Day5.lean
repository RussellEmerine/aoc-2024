import Lean.Data.Json.Parser
import Std.Data.HashMap.Basic
import «Aoc2024».Digraph.TopoSort

open Std.Internal.Parsec.String

namespace Day5

def parseRule : Parser (Nat × Nat) := do
  let a ← Lean.Json.Parser.nat 
  skipString "|"
  let b ← Lean.Json.Parser.nat 
  return (a, b)

def parseUpdate : Parser (List Nat) := do
  let a ← Lean.Json.Parser.nat
  let arr ← (skipString "," *> Lean.Json.Parser.nat).many
  return a :: arr.toList  

def satisfiesRules (update : List Nat) (rules : List (Nat × Nat)) : Bool :=
  let indices : Std.HashMap Nat Nat := Std.HashMap.ofList (update.zip (List.range rules.length))
  rules.all fun (a, b) => match (indices.get? a, indices.get? b) with
  | (some i, some j) => i < j
  | _ => True 

structure UpdateSet where
  (rules : List (Nat × Nat))
  (updates : List (List Nat))

namespace UpdateSet

def readFromFile (file : System.FilePath) : IO UpdateSet := do
  let lines ← IO.FS.lines file
  let mut rules : List (Nat × Nat) := []
  let mut updates : List (List Nat) := []
  for line in lines do
    if let Except.ok rule := parseRule.run line then 
      rules := rule :: rules 
    else if let Except.ok update := parseUpdate.run line then 
      updates := update :: updates
  return { rules, updates }

def solve (u : UpdateSet) : Nat :=
  u.updates.filter (satisfiesRules · u.rules)
  |>.filterMap (fun update => update.get? (update.length / 2))
  |>.sum 

def reorder (u : UpdateSet) : Nat :=
  u.updates.filter (¬satisfiesRules · u.rules)
  |>.filterMap (fun up => do
    let update := up.dedup 
    let T := {x // x ∈ update}
    let _ : Fintype T := List.Subtype.fintype update 
    let sorted ← toposort
      { Adj (x y : T) := u.rules.contains (x.val, y.val) }
      update.attach
      update.mem_attach 
      up.nodup_dedup.attach 
    let x ← sorted.get? (sorted.length / 2)
    return x.val 
  )
  |>.sum 

end UpdateSet

namespace Task1

def main : IO Unit := do
  let u ← UpdateSet.readFromFile (System.FilePath.mk "Data/Day5/test.txt")
  println! "Test: {u.solve}"
  println! "Expected: {143}"
  let u ← UpdateSet.readFromFile (System.FilePath.mk "Data/Day5/task.txt")
  println! "Task: {u.solve}"

end Task1

namespace Task2

def main : IO Unit := do
  let u ← UpdateSet.readFromFile (System.FilePath.mk "Data/Day5/test.txt")
  println! "Test: {u.reorder}"
  println! "Expected: {123}"
  let u ← UpdateSet.readFromFile (System.FilePath.mk "Data/Day5/task.txt")
  println! "Task: {u.reorder}"

end Task2

def main : IO Unit := do
  println! "Day 5"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day5
