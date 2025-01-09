import «Aoc2024».Util.GridArray
import «Aoc2024».Util.WeightedGraph

set_option maxHeartbeats 1000000

namespace Day21

-- all of this should be universe-generic but (Idx m n : Type) and
-- i don't feel like dealing with ULift 

-- outParam so that m and n are determined by α, otherwise if there are 
-- multiple instances for α with different m and n type inference breaks
class EquivSetIdx (α : Type) {m n : outParam Nat} (set : outParam (Set (Idx m n))) where
  e : α ≃ set

namespace EquivSetIdx

variable {α : Type} {m n : Nat} {set : Set (Idx m n)} [EquivSetIdx α set] [DecidablePred (· ∈ set)]

def move (a : α) (d : Direction) : Option α := do
  let p := EquivSetIdx.e a
  let p' ← p.val.move d
  if h : p' ∈ set then
    some <| e.symm ⟨p', h⟩
  else 
    none

end EquivSetIdx

inductive DPad
| Dir : Direction → DPad
| A : DPad
deriving Fintype, Hashable, DecidableEq 

namespace DPad

def univ : List DPad := .A :: .Dir <$> Direction.univ 

abbrev set : Set (Idx 2 3) := {(0, 1), (0, 2), (1, 0), (1, 1), (1, 2)}

def e : DPad ≃ set where
  toFun
  | .Dir .U => ⟨(0, 1), by simp⟩
  | .A => ⟨(0, 2), by simp⟩
  | .Dir .L => ⟨(1, 0), by simp⟩
  | .Dir .D => ⟨(1, 1), by simp⟩
  | .Dir .R => ⟨(1, 2), by simp⟩
  invFun
  | ⟨(0, 0), _⟩ => by contradiction
  | ⟨(0, 1), _⟩ => .Dir .U
  | ⟨(0, 2), _⟩ => .A
  | ⟨(1, 0), _⟩ => .Dir .L
  | ⟨(1, 1), _⟩ => .Dir .D
  | ⟨(1, 2), _⟩ => .Dir .R
  left_inv
  | .A => rfl
  | .Dir .L => rfl
  | .Dir .R => rfl
  | .Dir .U => rfl
  | .Dir .D => rfl
  right_inv  
  | ⟨(0, 0), _⟩ => by contradiction
  | ⟨(0, 1), _⟩ => rfl
  | ⟨(0, 2), _⟩ => rfl
  | ⟨(1, 0), _⟩ => rfl
  | ⟨(1, 1), _⟩ => rfl
  | ⟨(1, 2), _⟩ => rfl

instance : EquivSetIdx DPad set where
  e

end DPad

inductive NumPad
| Num : Fin 10 → NumPad 
| A : NumPad 
deriving Fintype, Hashable, DecidableEq 

namespace NumPad

def univ : List NumPad := .A :: .Num <$> List.finRange 10

abbrev set : Set (Idx 4 3) := {
  (0, 0),
  (0, 1),
  (0, 2),
  (1, 0),
  (1, 1),
  (1, 2),
  (2, 0),
  (2, 1),
  (2, 2),
  (3, 1),
  (3, 2)
}

def e : NumPad ≃ set where
  toFun
  | .Num 7 => ⟨(0, 0), by simp⟩
  | .Num 8 => ⟨(0, 1), by simp⟩
  | .Num 9 => ⟨(0, 2), by simp⟩
  | .Num 4 => ⟨(1, 0), by simp⟩
  | .Num 5 => ⟨(1, 1), by simp⟩
  | .Num 6 => ⟨(1, 2), by simp⟩
  | .Num 1 => ⟨(2, 0), by simp⟩
  | .Num 2 => ⟨(2, 1), by simp⟩
  | .Num 3 => ⟨(2, 2), by simp⟩
  | .Num 0 => ⟨(3, 1), by simp⟩
  | .A => ⟨(3, 2), by simp⟩
  invFun
  | ⟨(0, 0), _⟩ => .Num 7 
  | ⟨(0, 1), _⟩ => .Num 8 
  | ⟨(0, 2), _⟩ => .Num 9 
  | ⟨(1, 0), _⟩ => .Num 4 
  | ⟨(1, 1), _⟩ => .Num 5 
  | ⟨(1, 2), _⟩ => .Num 6 
  | ⟨(2, 0), _⟩ => .Num 1 
  | ⟨(2, 1), _⟩ => .Num 2 
  | ⟨(2, 2), _⟩ => .Num 3
  | ⟨(3, 0), _⟩ => by contradiction 
  | ⟨(3, 1), _⟩ => .Num 0 
  | ⟨(3, 2), _⟩ => .A
  left_inv
  | .Num 7 => rfl
  | .Num 8 => rfl
  | .Num 9 => rfl
  | .Num 4 => rfl
  | .Num 5 => rfl
  | .Num 6 => rfl
  | .Num 1 => rfl
  | .Num 2 => rfl
  | .Num 3 => rfl
  | .Num 0 => rfl
  | .A => rfl
  right_inv 
  | ⟨(0, 0), _⟩ => rfl
  | ⟨(0, 1), _⟩ => rfl
  | ⟨(0, 2), _⟩ => rfl
  | ⟨(1, 0), _⟩ => rfl
  | ⟨(1, 1), _⟩ => rfl
  | ⟨(1, 2), _⟩ => rfl
  | ⟨(2, 0), _⟩ => rfl
  | ⟨(2, 1), _⟩ => rfl
  | ⟨(2, 2), _⟩ => rfl
  | ⟨(3, 0), _⟩ => by contradiction 
  | ⟨(3, 1), _⟩ => rfl
  | ⟨(3, 2), _⟩ => rfl

instance : EquivSetIdx NumPad set where
  e

end NumPad

-- outParam so that β is determined by α, otherwise if there are 
-- multiple instances for α with different β type inference breaks
class Pad (α : Type) (β : outParam Type) where
  step : α → DPad → Option (α × Option β)

namespace Pad

def shortestInput
  {α β : Type} [BEq α] [Hashable α] [Fintype α] [DecidableEq β] [Pad α β]
  (start : α)
  (output : Array β)
: Option Nat :=
  let graph : WeightedGraph (α × Fin (output.size + 1)) Nat := {
    edges x := do
      let (a, i) := x
      let d ← DPad.univ
      let (a', out) ← (Pad.step a d).toList
      if let some out := out then
        let () ← guard <| some out = output.get? i
        return ((a', i + 1), 1)
      else
        return ((a', i), 1)
  }
  let bestPath := graph.dijkstra (start, 0)
  bestPath.toList.filter (·.fst.snd = output.size)
    |>.map Prod.snd
    |>.min?

end Pad

def instPadSelfOfEquivSetIdx
  (α : Type) {m n : Nat} {set : Set (Idx m n)} [DecidablePred (· ∈ set)] [EquivSetIdx α set] 
: Pad α α where
  step
  | a, .Dir d => do
    let p := EquivSetIdx.e a
    let p' ← p.val.move d
    if h : p' ∈ set then 
      some (EquivSetIdx.e.symm ⟨p', h⟩, none)
    else
      none 
  | a, .A => some (a, a)

instance : Pad NumPad NumPad := instPadSelfOfEquivSetIdx NumPad 

instance : Pad DPad DPad := instPadSelfOfEquivSetIdx DPad 

instance {α β γ : Type} [Pad α DPad] [Pad β γ] : Pad (α × β) γ where
  step x d := do
    let (a, b) := x
    let (a', out) ← Pad.step a d
    if let some out := out then
      let (b', out') ← Pad.step b out
      return ((a', b'), out')
    else
      return ((a', b), none)

abbrev Code := Array NumPad

namespace Code

def parse (line : String) : Except String Code :=
  line.toList.toArray.mapM fun c =>
    match c with
    | '0' => .ok (.Num 0)
    | '1' => .ok (.Num 1)
    | '2' => .ok (.Num 2)
    | '3' => .ok (.Num 3)
    | '4' => .ok (.Num 4)
    | '5' => .ok (.Num 5)
    | '6' => .ok (.Num 6)
    | '7' => .ok (.Num 7)
    | '8' => .ok (.Num 8)
    | '9' => .ok (.Num 9)
    | 'A' => .ok (.A)
    | _ => .error "Could not parse string to numpad code"

def numeric (code : Code) : Nat := Id.run <| do
  let mut x : Nat := 0
  for c in code do
    if let .Num d := c then
      x := x * 10 + d
    else
      break
  return x 

def complexity (code : Code) : Option Nat := do
  let start : DPad × DPad × NumPad := (.A, .A, .A)
  let length ← Pad.shortestInput start code
  length * numeric code

def weightsWithWeights
  {α : Type} [BEq α] [Hashable α] [Fintype α] [Pad α α]
  (univ : List α)
  (weights : Std.HashMap (DPad × DPad) Nat) :
    Std.HashMap (α × α) Nat :=
  let g : WeightedGraph (α × Option DPad) Nat := {
    edges x := do
      let (a, d) := x
      let d₁ ← d.toList 
      let d₂ ← DPad.univ
      let w ← weights.get? (d₁, d₂) |>.toList 
      let (a', out) ← (Pad.step a d₂).toList
      if let some out := out then
        return ((out, none), w)
      else
        return ((a', some d₂), w)
  }
  Std.HashMap.ofList <| univ ×ˢ univ |>.filterMap fun (a₁, a₂) =>
    g.dijkstra (a₁, some .A) |>.get? (a₂, none) |>.map ((a₁, a₂), ·)

-- the number of top-level button presses to move from start to end then press end
def nestedWeights : Nat → Std.HashMap (DPad × DPad) Nat
| 0 => Std.HashMap.ofList <| DPad.univ ×ˢ DPad.univ |>.map (·, 1)
| (n + 1) => weightsWithWeights DPad.univ (nestedWeights n)

def nestedShortestInput
  {α : Type} [BEq α] [Hashable α] [Fintype α] [Pad α α]
  (univ : List α)
  (start : α)
  (n : Nat)
  (output : Array α) :
    Nat :=
  let w := weightsWithWeights univ (nestedWeights n)
  let output := output.toList
  List.zipWith (fun a₁ a₂ => w.get? (a₁, a₂)) (start :: output) output
    |>.reduceOption
    |>.sum

def complexity' (code : Code) (n : Nat) : Option Nat :=
  let start : NumPad := .A
  let length := nestedShortestInput NumPad.univ start n code
  some <| length * numeric code

end Code

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day21/test.txt")
  let codes ← IO.ofExcept <| lines.mapM Code.parse 
  println! "Test: {codes.mapM Code.complexity |>.map Array.toList |>.map List.sum}"
  println! "Expected: {some 126384}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day21/task.txt")
  let codes ← IO.ofExcept <| lines.mapM Code.parse 
  println! "Task: {codes.mapM Code.complexity |>.map Array.toList |>.map List.sum}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day21/test.txt")
  let codes ← IO.ofExcept <| lines.mapM Code.parse 
  println! "Test: {codes.mapM (Code.complexity' · 2) |>.map Array.toList |>.map List.sum}"
  println! "Expected: {some 126384}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day21/task.txt")
  let codes ← IO.ofExcept <| lines.mapM Code.parse 
  println! "Task: {codes.mapM (Code.complexity' · 25) |>.map Array.toList |>.map List.sum}"

end Task2

def main : IO Unit := do
  println! "Day 21"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day21
