import Batteries.Data.List.Basic
import Mathlib.Data.List.Basic 

namespace Day25

structure Lock where
  pin : Vector (Fin 6) 5
deriving Repr

instance : ToString Lock where
  toString lock := toString lock.pin.toArray

structure Key where
  pin : Vector (Fin 6) 5
deriving Repr 

instance : ToString Key where
  toString key := toString key.pin.toArray

def parse (lines : List String) : Option (Lock ⊕ Key) :=
  let arr := lines.map String.toList
    |>.transpose.map (Fin.ofNat' 6 <| ·.count '#' - 1)
    |>.toArray 
  if h : arr.size = 5 then
    let pin : Vector (Fin 6) 5 := {
      toList := arr.toList
      size_toArray := h 
    }
    if lines.head?.any (·.startsWith "#") then
      return .inl { pin }
    else
      return .inr { pin }
  else
    failure

def fit (lock : Lock) (key : Key) : Bool :=
  lock.pin.zipWith key.pin (·.val + ·.val) |>.all (· < 6)

structure Schematics where
  locks : List Lock
  keys : List Key
deriving Repr 

namespace Schematics

def ofLines (lines : List String) : Except String Schematics := do
  let schematics := lines.splitOn ""
  let items ← (schematics.mapM parse).elim (Except.error "invalid lock or key") Except.ok 
  let (locks, keys) := items.partitionMap id
  return { locks, keys }

def countFits (self : Schematics) : Nat := List.length <| do
  let lock ← self.locks
  let key ← self.keys
  let () ← guard <| fit lock key
  return () 

end Schematics

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day25/test.txt")
  let schematics ← IO.ofExcept <| Schematics.ofLines lines.toList
  println! "Test: {schematics.countFits}"
  println! "Expected: {3}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day25/task.txt")
  let schematics ← IO.ofExcept <| Schematics.ofLines lines.toList 
  println! "Task: {schematics.countFits}"

end Task1

namespace Task2

def main : IO Unit := do
  println! "yay i did it!"

end Task2

def main : IO Unit := do
  println! "Day 25"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day25
