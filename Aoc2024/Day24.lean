import Std.Data.HashMap.Basic 
import Std.Data.HashSet.Basic
import Mathlib.Data.List.Basic 

namespace Day24

inductive Op
| And
| Or
| Xor
deriving Hashable, DecidableEq, Repr

namespace Op

def eval : Op → Bool → Bool → Bool
| And, b₁, b₂ => b₁.and b₂
| Or, b₁, b₂ => b₁.or b₂
| Xor, b₁, b₂ => b₁.xor b₂ 

end Op

structure Gate where
  op : Op
  b₁ : String
  b₂ : String
  out : String
deriving Hashable, DecidableEq, Repr 

structure System where
  wires : Std.HashMap String Bool
  -- gates[b] is the gates that take b as an input
  gates : Std.HashMap String (List Gate)
  -- qs[i] is the gates with i inputs determined
  qs : Vector (Std.HashSet Gate) 3

namespace System

def ofLines (lines : Array String) : System := Id.run <| do
  let mut wires := {}
  let mut gates := {}
  let mut q₀ := {}
  let mut q₁ := {}
  let mut q₂ := {}
  for line in lines do
    if let [w, b] := line.splitOn ": " then
      wires := wires.insert w (b = "1")
    if let [b₁, op, b₂, "->", out] := line.splitOn then
      let op := match op with
        | "AND" => Op.And
        | "OR" => Op.Or
        | _ => Op.Xor 
      let gate : Gate := { op, b₁, b₂, out }
      gates := gates.alter b₁ (·.getD [] |> (gate :: ·))
      gates := gates.alter b₂ (·.getD [] |> (gate :: ·))
      match (wires.contains b₁).toNat + (wires.contains b₂).toNat with
        | 0 => q₀ := q₀.insert gate
        | 1 => q₁ := q₁.insert gate
        | _ => q₂ := q₂.insert gate 
  return {
    wires,
    gates,
    qs := #v[q₀, q₁, q₂]
  }

def step (system : System) : Option System := do
  let mut q₀ := system.qs[0]
  let mut q₁ := system.qs[1]
  let mut q₂ := system.qs[2]
  let gate ← q₂.toList.head? 
  q₂ := q₂.erase gate
  for gate' in system.gates[gate.out]?.toList.flatten do
    if gate' ∈ q₀ then
      q₀ := q₀.erase gate'
      q₁ := q₁.insert gate'
    else if gate' ∈ q₁ then
      q₁ := q₁.erase gate'
      q₂ := q₂.insert gate'
  let out := gate.op.eval (← system.wires[gate.b₁]?) (← system.wires[gate.b₂]?)
  return {
    wires := system.wires.insert gate.out out 
    gates := system.gates
    qs := #v[q₀, q₁, q₂]
  }

def run (system : System) : Nat → System
| 0 => system
| (n + 1) =>
  if let some system' := system.step then
    run system' n
  else
    system 

def znum (i : Nat) : String :=
  "z" ++ toString (i / 10) ++ toString (i % 10)

def number (system : System) : Nat :=
  let system' := system.run 1000
  List.range 100
    |>.map (fun i =>
      if system'.wires[znum i]? = some true then
        2 ^ i
      else
        0)
    |>.sum 

end System

structure Adder where
  wires : Std.HashSet String 
  gates : Std.HashMap String Gate

namespace Adder

def num (c : String) (i : Nat) : String := c ++ toString (i / 10) ++ toString (i % 10)

def isNum (s : String) : Bool :=
  "xy".contains (s.get ⟨0⟩) ∧ (s.get ⟨1⟩).isDigit ∧ (s.get ⟨2⟩).isDigit

def getNum (s : String) : Nat :=
  s.drop 1 |>.toNat?.getD 0

def ofLines (lines : Array String) : Adder := Id.run <| do
  let mut gates := {}
  let mut wires := {}
  for line in lines do
    if let [b₁, op, b₂, "->", out] := line.splitOn then
      let op := match op with
        | "AND" => Op.And
        | "OR" => Op.Or
        | _ => Op.Xor 
      let gate : Gate := { op, b₁, b₂, out }
      gates := gates.insert out gate
      wires := wires.insert b₁ |>.insert b₂ |>.insert out 
  return { wires, gates }

def swap (adder : Adder) (b₁ b₂ : String) : Option Adder := do
  let gate₁ ← adder.gates[b₁]?
  let gate₂ ← adder.gates[b₂]?
  return { wires := adder.wires, gates := adder.gates.insert b₁ gate₂ |>.insert b₂ gate₁ }

/-

there are 222 gates in the input, and 44 input and 45 output digits.

x00 XOR y00 -> z00 (0th digit)
x00 AND y00 -> gmk (0th carry)

x01 XOR y01 -> vgr 
vgr XOR gmk -> z01 (1st digit)
vgr AND gmk -> fsm
x01 AND y01 -> jvm
fsm OR jvm -> nwk (1st carry)

...
qdd OR jdb -> z45 (45th carry)

so z45 is the 45th carry and not its own digit.

5 gates each for the rest of the ith digit and ith carry.

This means the standard ripple carry adder with 5-gate full adders is 
the only possible arrangement for this adder to work, and in fact the
full adders must be exactly in the configuration demonstrated for z01
(so that the xi XOR yi can be reused).

-/

def checkWithCarry (adder : Adder) (carry : String) (i : Nat) : Option (List String × String) := do
  let g₁ ← adder.gates[carry]?.filter (·.op = Op.Or)
  let inand ← List.head? <| [g₁.b₁, g₁.b₂].filter fun b =>
    adder.gates[b]?.any fun gate => 
      gate.op = Op.And ∧ getNum gate.b₁ = i ∧ getNum gate.b₂ = i 
  let cxand ← List.head? <| [g₁.b₁, g₁.b₂].filter (· ≠ inand)
  let g₂ ← adder.gates[cxand]?.filter (·.op = Op.And)
  let g₃ ← adder.gates[num "z" i]?.filter (·.op = Op.Xor)
  let () ← guard <| (g₂.b₁, g₂.b₂) ∈ [(g₃.b₁, g₃.b₂), (g₃.b₂, g₃.b₁)]
  let inxor ← List.head? <| [g₂.b₁, g₂.b₂].filter fun b =>
    adder.gates[b]?.any fun gate =>
      gate.op = Op.Xor ∧ getNum gate.b₁ = i ∧ getNum gate.b₂ = i
  let carry' ← List.head? <| [g₂.b₁, g₂.b₂].filter (· ≠ inxor)
  return ([carry, inand, cxand, inxor, num "z" i], carry')

def findSwaps (adder : Adder) (carry : String) (done : Std.HashSet String) (acc : List (String × String)) :
    Nat → Option (List (String × String))
| 0
| 1 => some acc -- don't need to check 0 or 1 because it works in the input
| i + 1 => do
  let mut done := done 
  if let some (done', carry') := checkWithCarry adder carry i then
    for x in done' do
      done := done.insert x
    findSwaps adder carry' done acc i
  else
    -- i'm just going to assume there's never more than one pair of gates interfering with one digit
    for s₁ in adder.gates.keys do
      for s₂ in adder.gates.keys do
        if s₁ < s₂ ∧ s₁ ∉ done ∧ s₂ ∉ done then
          if let some adder' := adder.swap s₁ s₂ then 
            if let some (done', carry') := checkWithCarry adder' carry i then
              for x in done' do
                done := done.insert x
              let ret ← findSwaps adder' carry' done ((s₁, s₂) :: acc) i
              return ret  
    failure 

def names (adder : Adder) (maxDigit : Nat) : Option String := do
  let swaps ← findSwaps adder (num "z" maxDigit) {} [] maxDigit
  let swaps' := (swaps.flatMap fun (a₁, a₂) => [a₁, a₂]).mergeSort
  return ",".intercalate swaps'

end Adder

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day24/test.txt")
  let system := System.ofLines lines
  println! "Test: {system.number}"
  println! "Expected: {4}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day24/task.txt")
  let system := System.ofLines lines
  println! "Task: {system.number}"

end Task1

namespace Task2

def main : IO Unit := do
--  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day24/test2.txt")
--  let adder := Adder.ofLines lines
--  println! "Test: {adder.names 1 1}"
--  println! "Expected: {some "z00, z01"}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day24/task.txt")
  let adder := Adder.ofLines lines
  println! "Task: {adder.names 45}"

end Task2

def main : IO Unit := do
  println! "Day 24"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day24
