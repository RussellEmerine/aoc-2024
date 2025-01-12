import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Day23

-- i would do the following but i think the decidability instance screws things up
-- abbrev Network := SimpleGraph String

structure Network where
  (map : Std.HashSet (String × String))

namespace Network

def ofLines (lines : Array String) : Except String Network := do
  let pairs ← lines.mapM fun s =>
    match s.splitOn "-" with
    | [s₁, s₂] =>
      if s₁ = s₂ then
        throw "line links computer to itself"
      else
        pure (s₁, s₂)
    | _ => throw "line does not link two computers"
  return { map := Std.HashSet.ofArray pairs }

def Adj (network : Network) (s₁ s₂ : String) : Bool :=
  (s₁, s₂) ∈ network.map ∨ (s₂, s₁) ∈ network.map 

def alphabet : List Char := "abcdefghijklmnopqrstuvwxyz".toList 

def computers : List String := do
  let c₁ ← alphabet
  let c₂ ← alphabet
  return String.mk [c₁, c₂]

def isChiefCandidate (c : String) : Bool := c.startsWith "t"

def chiefTriples (network : Network) : Nat := List.length <| do
  let c₁ ← computers
  let c₂ ← computers
  -- to avoid overcounting
  let () ← guard <| c₁ < c₂ 
  -- this is put here early to cut runtime from O(V^3) to O(VE),
  -- which is 300,000,000 vs 2,000,000 since the file has ~3000 lines
  let () ← guard <| network.Adj c₁ c₂
  let c₃ ← computers
  -- to avoid overcounting
  let () ← guard <| c₂ < c₃
  -- correctness
  let () ← guard <| network.Adj c₁ c₃ ∧ network.Adj c₂ c₃
  let () ← guard <| isChiefCandidate c₁ ∨ isChiefCandidate c₂ ∨ isChiefCandidate c₃ 
  return ()

def largestSimplexAux (network : Network) (acc : List (List String)) : Nat → List (List String)
| 0 => []
| fuel + 1 =>
  let acc' := do
    let cs ← acc
    let c ← computers
    let () ← guard <| WithTop.some c < (cs.head? : WithTop String)
    let () ← guard <| cs.all (network.Adj c)
    return c :: cs
  if acc'.isEmpty then 
    acc
  else
    largestSimplexAux network acc' fuel 

def largestSimplex (network : Network) : List String :=
  largestSimplexAux network [[]] 3000 |>.head?.getD []

def password (network : Network) : String :=
  ",".intercalate <| largestSimplex network 

end Network

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day23/test.txt")
  let network ← IO.ofExcept (Network.ofLines lines)
  println! "Test: {Network.chiefTriples network}"
  println! "Expected: {7}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day23/task.txt")
  let network ← IO.ofExcept (Network.ofLines lines)
  println! "Task: {Network.chiefTriples network}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day23/test.txt")
  let network ← IO.ofExcept (Network.ofLines lines)
  println! "Test: {network.password}"
  println! "Expected: {"co,de,ka,ta"}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day23/task.txt")
  let network ← IO.ofExcept (Network.ofLines lines)
  println! "Task: {network.password}"

end Task2

def main : IO Unit := do
  println! "Day 23"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day23
