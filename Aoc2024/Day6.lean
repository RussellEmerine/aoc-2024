import Std.Data.HashSet.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import «Aoc2024».GridArray

namespace Day6

universe u

variable {α : Type u} [DecidableEq α] [Hashable α] 

def iteratesAux (f : α → α) (a : α) (set : Std.HashSet α) : ℕ → Std.HashSet α
| 0 => set
| (n + 1) => iteratesAux f (f a) (set.insert a) n

def iterates [Fintype α] (f : α → α) (a : α) : Std.HashSet α :=
  iteratesAux f a Std.HashSet.empty (Fintype.card α + 1)

lemma iteratesAux_add_one (f : α → α) (a : α) (set : Std.HashSet α) (n : ℕ) :
    iteratesAux f a set (n + 1)
      = insert (f^[n] a) (iteratesAux f a set n) := by
  induction n generalizing a set 
  case zero =>
    simp [iteratesAux]
  case succ h =>
    unfold iteratesAux 
    rw [h, ← Function.iterate_succ_apply]

lemma mem_iteratesAux_iff (f : α → α) (a : α) (n : ℕ) {x : α} :
    x ∈ iteratesAux f a Std.HashSet.empty n ↔ x ∈ (Nat.iterate f · a) '' {i | i < n} := by
  induction n
  case zero =>
    simp [iteratesAux]
  case succ n h =>
    simp [iteratesAux_add_one]
    rw [h]
    fconstructor
    case mp =>
      intro hx
      cases hx
      case inl hx =>
        exact ⟨n, n.lt_add_one, hx⟩
      case inr hx =>
        rcases hx with ⟨i, hi, hx⟩
        refine ⟨i, lt_trans hi n.lt_add_one, hx⟩
    case mpr =>
      intro ⟨i, h, hx⟩
      by_cases hi : i < n
      · exact Or.inr ⟨i, hi, hx⟩
      · convert Or.inl hx 
        linarith

theorem mem_iterates_iff [Fintype α] (f : α → α) (a : α) (x : α) :
    x ∈ iterates f a ↔ x ∈ Set.range (Nat.iterate f · a) := by
  classical 
  unfold iterates
  rw [mem_iteratesAux_iff, Set.mem_image, Set.mem_range]
  refine ⟨fun ⟨n, _, hn⟩ => ⟨n, hn⟩, ?_⟩
  intro ⟨n, hn⟩
  subst hn
  let src := Finset.range (Fintype.card α + 1)
  let dst := Finset.univ.filter (fun y => y ∈ Set.range (Nat.iterate f · a))
  have hc : dst.card < src.card := by
    rw [Finset.card_range, Nat.lt_add_one_iff]
    exact dst.card_le_univ
  have hf : ∀ i ∈ src, f^[i] a ∈ dst := by
    intro i hi
    rw [Finset.mem_filter, Set.mem_range]
    exact ⟨Finset.mem_univ _, i, rfl⟩
  rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc hf with ⟨i, hi, j, hj, hij', h⟩
  clear hc hf
  wlog hij : i < j generalizing i j 
  · exact this j hj i hi (Ne.symm hij') h.symm (lt_of_le_of_ne (not_lt.mp hij) hij'.symm)
  rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
  clear hij hij'
  rw [Finset.mem_range] at hj
  by_cases hn : n < i + k + 1
  · refine ⟨n, ?_, rfl⟩
    rw [Set.mem_setOf]
    exact hn.trans hj
  · rw [not_lt] at hn
    rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
    clear hn
    refine ⟨i + m % (k + 1), ?_, ?_⟩
    · rw [Set.mem_setOf]
      apply lt_trans _ hj
      rw [add_assoc]
      apply add_lt_add_left
      exact Nat.mod_lt _ k.zero_lt_succ
    rw [add_assoc, add_comm i, Function.iterate_add_apply] at h
    calc f^[i + m % (k + 1)] a
     _ = f^[m % (k + 1) + i] a                                     := by rw [add_comm]
     _ = f^[m % (k + 1)] (f^[i] a)                                 := by rw [Function.iterate_add_apply]
     _ = f^[m % (k + 1)] (f^[k + 1]^[m / (k + 1) + 1] (f^[i] a))   := by rw [Function.iterate_fixed h.symm]
     _ = f^[m % (k + 1) + (k + 1) * (m / (k + 1) + 1) + i] a       := by
       rw [← Function.iterate_mul, ← Function.iterate_add_apply, ← Function.iterate_add_apply]
     _ = f^[(k + 1) * (m / (k + 1)) + m % (k + 1) + (k + 1) + i] a := by congr! 1; linarith
     _ = f^[m + (k + 1) + i] a                                     := by rw [Nat.div_add_mod]
     _ = f^[i + k + 1 + m] a                                       := by congr! 1; linarith 

abbrev Position (_ : GridArray m n Bool) := Option (Idx m n × Direction)

namespace Position

variable {m n : ℕ} {grid : GridArray m n Bool}

def start (p : Idx m n) : Position grid := some (p, Direction.U)

def next : Position grid → Position grid
| none => none
| some (p, d) => do
  let p' ← p.move d
  return if grid.get p' then (p', d) else (p, d.cw)

end Position

structure Map (m n : ℕ) where
  (grid : GridArray m n Bool)
  (start : Position grid)

namespace Map

def ofLines (lines : Array String) : Except String ((m : ℕ) × (n : ℕ) × Map m n) := do
  let ⟨m, n, grid⟩ ← GridArray.ofLines (lines.map (·.toList.toArray))
  let start ← match (GridArray.indices m n).filter (fun p => grid.get p = '^') |>.head? with
    | some p => Except.ok p 
    | none => Except.error "did not find starting position of guard"
  return ⟨m, n, grid.map (· ≠ '#'), some ⟨start, Direction.U⟩⟩

def cells (map : Map m n) : Std.HashSet (Idx m n) :=
  let positions := iterates Position.next map.start
  positions.toList.filterMap (Option.map Prod.fst) |> Std.HashSet.ofList

-- works fine but takes 90 seconds lol
def loop_cells (map : Map m n) : List (Idx m n) := do
  let p ← map.cells.toList
  let () ← guard <| some (p, Direction.U) ≠ map.start ∧ map.grid.get p 
  let map' : Map m n := {
    grid := map.grid.modify p fun _ => false,
    start := map.start
  }
  let () ← guard <| none ∉ iterates Position.next map'.start 
  return p 

end Map

namespace Task1

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day6/test.txt")
  let ⟨_, _, map⟩ ← IO.ofExcept (Map.ofLines lines)
  println! "Test: {map.cells.size}"
  println! "Expected: {41}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day6/task.txt")
  let ⟨_, _, map⟩ ← IO.ofExcept (Map.ofLines lines)
  println! "Task: {map.cells.size}"

end Task1

namespace Task2

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day6/test.txt")
  let ⟨_, _, map⟩ ← IO.ofExcept (Map.ofLines lines)
  println! "Test: {map.loop_cells.length}"
  println! "Expected: {6}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day6/task.txt")
  let ⟨_, _, map⟩ ← IO.ofExcept (Map.ofLines lines)
  println! "Task: {map.loop_cells.length}"

end Task2

def main : IO Unit := do
  println! "Day 6"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day6
