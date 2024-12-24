import Mathlib.Data.List.Monad
import Mathlib.Data.List.Intervals
import Mathlib.Tactic.Linarith
import Batteries.Data.BinaryHeap

open Batteries 

namespace Day9

namespace Task1

def diskMapAux (fid : Nat) (is_file : Bool) (acc : List (Option Nat)) :
    List Char → List (Option Nat)
| [] => acc
| (c :: cs) =>
  let c := c.toString.toNat?.getD 0
  if is_file then
    diskMapAux (fid + 1) false (List.replicate c (some fid) ++ acc) cs 
  else
    diskMapAux fid true (List.replicate c none ++ acc) cs 

def diskMap (s : String) : Array (Option Nat) :=
  diskMapAux 0 true [] s.toList |>.reverse |>.toArray
  
def rearrangeAux (map : Array (Option Nat)) (i : Nat) :
    (j : Nat) → (_ : i + j < map.size) → Array (Option Nat)
| 0, _ => map
| (j + 1), hj =>
  if map[i].isSome then
    rearrangeAux map (i + 1) j (by linarith)
  else if let some fid := map[i + j + 1] then
    let map' := map.set i (some fid) |>.set (i + j + 1) none (by rw [Array.size_set, add_assoc]; exact hj)
    rearrangeAux map' (i + 1) j (by rw [Array.size_set, Array.size_set]; linarith)
  else
    rearrangeAux map i j (by linarith)

def rearrange (map : Array (Option Nat)) (h : map.size ≠ 0) : Array (Option Nat) :=
  rearrangeAux map 0 (map.size - 1) (by rw [zero_add]; exact Nat.sub_one_lt h)

def checksum (map : Array (Option Nat)) : Nat :=
  map.mapIdx (fun i fid => i * fid.getD 0) |>.toList |>.sum 

def main : IO Unit := do
  let line ← IO.FS.readFile (System.FilePath.mk "Data/Day9/test.txt")
  let map := diskMap line
  if h : map.size ≠ 0 then 
    println! "Test: {checksum <| rearrange map h}"
  else
    IO.throwServerError "tried to do empty file"
  println! "Expected: {1928}"
  let line ← IO.FS.readFile (System.FilePath.mk "Data/Day9/task.txt")
  let map := diskMap line
  if h : map.size ≠ 0 then 
    println! "Task: {checksum <| rearrange map h}"
  else
    IO.throwServerError "tried to do empty file"

end Task1

namespace Task2

structure File where
  id : Nat
  start : Nat
  length : Nat
deriving Repr 

structure DiskMap where
  files : List File
  gaps : Vector (BinaryHeap Nat (·>·)) 10

def diskMap (s : String) : DiskMap := Id.run <| do 
  let s := s.toList.map (·.toString.toNat?.getD 0)
  let mut files : List File := []
  let mut gaps : Vector (BinaryHeap Nat (·>·)) 10 :=
    Vector.mkVector 10 (BinaryHeap.empty _)
  let mut fid := 0
  let mut x := 0
  let mut is_file := true 
  for i in s do
    if is_file then
      files := { id := fid, start := x, length := i } :: files
      fid := fid + 1
    else
      let i := Fin.ofNat' 10 i
      gaps := gaps.set i (gaps.get i |>.insert x)
    is_file := ¬is_file
    x := x + i
  return { files := files.reverse, gaps }

def rearrange (map : DiskMap) : DiskMap := Id.run <| do
  let mut files : List File := []
  let mut gaps := map.gaps
  for file in map.files.reverse do
    let pairs := List.finRange 10
      |>.filterMap (fun i => gaps[i].max.map ((·, i)))
      |>.filter (fun (x, i) => i.val ≥ file.length ∧ x < file.start)
    -- not sure why it wouldn't let me use List.min? with toLex 
    if let some (x, i) := match pairs with
      | [] => none
      | p :: ps => some <| ps.foldr (fun (x y : Nat × Fin 10) => if x.lexLt y then x else y) p
    then
      gaps := gaps.set i gaps[i].popMax
      gaps := gaps.set (i - file.length) (gaps[i - file.length] |>.insert (x + file.length))
      files := { id := file.id, start := x, length := file.length } :: files
    else
      files := file :: files
  return { files, gaps }

def checksum (map : DiskMap) : Nat :=
  List.sum <| map.files.map fun file =>
    List.Ico file.start (file.start + file.length) |>.map (· * file.id) |>.sum 

def main : IO Unit := do
  let line ← IO.FS.readFile (System.FilePath.mk "Data/Day9/test.txt")
  println! "Test: {line |> diskMap |> rearrange |> checksum}"
  println! "Expected: {2858}"
  let line ← IO.FS.readFile (System.FilePath.mk "Data/Day9/task.txt")
  println! "Task: {line |> diskMap |> rearrange |> checksum}"

end Task2

def main : IO Unit := do
  println! "Day 9"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day9
