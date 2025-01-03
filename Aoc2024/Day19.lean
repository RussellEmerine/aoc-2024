import Mathlib.Data.List.Basic
import Std.Data.HashSet.Basic

namespace Day19

universe u

variable {α : Type u} [DecidableEq α]

def covers (ps : List (List α)) : List α → Std.HashSet Nat
| [] => {0}
| as@(_ :: tl) =>
  let s := covers ps tl
  if ps.filter (· <+: as) |>.any (as.length - ·.length ∈ s) then 
    s.insert as.length 
  else
    s

def coversAll (ps : List (List α)) (as : List α) : Bool :=
  as.length ∈ covers ps as

def hasCover (ps : List (List α)) (as : List α) : Prop :=
  ∃ (xs : List (List α)), xs ⊆ ps ∧ xs.flatten = as

def hasCoverNeNil (ps : List (List α)) (as : List α) : Prop :=
  ∃ (xs : List (List α)), xs ⊆ ps ∧ xs.flatten = as ∧ xs.all (· ≠ [])

theorem hasCover_iff_hasCoverNeNil (ps : List (List α)) (as : List α)
: hasCover ps as ↔ hasCoverNeNil ps as := by
  refine ⟨?_, ?_⟩
  · intro ⟨cs, h₁, h₂⟩
    refine ⟨cs.filter (· ≠ []), Trans.trans cs.filter_subset' h₁, ?_, by simp⟩
    rw [List.flatten_filter_ne_nil]
    exact h₂
  · intro ⟨cs, h₁, h₂, h⟩
    exact ⟨cs, h₁, h₂⟩

theorem covers_iff_hasCoverNeNil_with_length (ps : List (List α)) (n : Nat)
: ∀ (as : List α), as.length = n → ∀ i,
    i ∈ covers ps as ↔ i ≤ as.length ∧ hasCoverNeNil ps (as.drop (as.length - i)) := by
  classical 
  induction n
  case zero =>
    intro as has i
    rw [List.length_eq_zero] at has 
    subst has
    simp [covers]
    refine ⟨?_, fun h => h.left.symm⟩
    intro h
    subst h
    exact ⟨rfl, [], List.nil_subset _, List.flatten_nil, List.all_nil⟩
  case succ n ih =>
  intro as has i
  cases as
  case nil => contradiction
  case cons a as =>
  simp at has
  specialize ih as has 
  unfold covers
  simp
  have h : hasCoverNeNil ps (a :: as) ↔
      ∃ p, p ∈ ps ∧ p <+: a :: as ∧ as.length + 1 - p.length ∈ covers ps as := by
    refine ⟨?_, ?_⟩
    · intro ⟨xs, hxs₁, hxs₂, hxs₃⟩
      cases xs
      case nil => contradiction
      case cons x xs =>
      simp at *
      refine ⟨x, hxs₁.left, ?_, ?_⟩
      · rw [← hxs₂]
        apply List.prefix_append
      rw [ih]
      refine ⟨?_, ?_⟩
      · simp
        rw [Nat.succ_le_iff, List.length_pos]
        exact hxs₃.left
      refine ⟨xs, hxs₁.right, ?_, ?_⟩
      · replace hxs₂ : xs.flatten = (a :: as).drop x.length := by
          rw [← hxs₂, List.drop_append_of_le_length le_rfl]
          simp
        rw [hxs₂]
        cases x
        case nil => exact hxs₃.left.elim rfl 
        case cons c x =>
        simp
        by_cases x.length ≤ as.length
        case pos h => rw [Nat.sub_sub_self h]
        case neg h =>
        push_neg at h
        rw [Nat.sub_eq_zero_of_le (le_of_lt h), Nat.sub_zero]
        rw [List.drop_eq_nil_of_le (le_of_lt h), List.drop_eq_nil_of_le le_rfl]
      · simp 
        exact hxs₃.right
    · intro ⟨p, hp₁, hp₂, hp₃⟩
      rw [ih] at hp₃
      rcases hp₃ with ⟨hp₃, xs, hxs₁, hxs₂, hxs₃⟩
      simp at *
      refine ⟨p :: xs, ?_, ?_, ?_⟩
      · rw [List.cons_subset]
        exact ⟨hp₁, hxs₁⟩
      · rw [List.flatten_cons]
        rw [List.prefix_iff_eq_append] at hp₂
        convert hp₂
        rw [hxs₂]
        cases p
        case nil =>
          simp at hp₃
        case cons c x =>
        simp
        by_cases x.length ≤ as.length
        case pos h => rw [Nat.sub_sub_self h]
        case neg h =>
        push_neg at h
        rw [Nat.sub_eq_zero_of_le (le_of_lt h), Nat.sub_zero]
        rw [List.drop_eq_nil_of_le (le_of_lt h), List.drop_eq_nil_of_le le_rfl]
      · simp
        refine ⟨?_, hxs₃⟩
        by_contra h
        subst h
        simp at hp₃
  conv =>
    lhs
    congr
    congr
    rw [← h]
  clear h
  split_ifs
  case pos h =>
    rw [Std.HashSet.mem_insert]
    by_cases as.length + 1 = i
    case pos hi =>
      subst hi
      simpa
    case neg hi =>
      refine ⟨?_, ?_⟩
      · intro h
        cases h
        case inl h => simp at h; contradiction
        case inr h =>
        rw [ih] at h
        rcases h with ⟨hi₁, hi₂⟩
        refine ⟨Nat.le_add_right_of_le hi₁, ?_⟩
        rw [Nat.sub_add_comm hi₁, List.drop_succ_cons]
        exact hi₂
      · intro ⟨hi₁, hi₂⟩
        right
        rw [ih]
        replace hi₁ : i ≤ as.length := by
          rw [Nat.le_succ_iff] at hi₁
          cases hi₁
          case _ => assumption
          case inr hi₁ =>
            subst hi₁
            contradiction
        rw [Nat.sub_add_comm hi₁, List.drop_succ_cons] at hi₂
        exact ⟨hi₁, hi₂⟩
  case neg h =>
    rw [ih]
    refine ⟨?_, ?_⟩
    · intro ⟨hi₁, hi₂⟩
      refine ⟨Nat.le_add_right_of_le hi₁, ?_⟩
      rw [Nat.sub_add_comm hi₁, List.drop_succ_cons]
      exact hi₂
    · intro ⟨hi₁, hi₂⟩
      rw [Nat.le_add_one_iff] at hi₁
      cases hi₁
      case inl hi₁ =>
        rw [Nat.sub_add_comm hi₁, List.drop_succ_cons] at hi₂
        exact ⟨hi₁, hi₂⟩
      case inr hi₁ =>
        subst hi₁
        simp at hi₂ 
        contradiction 

theorem covers_iff_hasCover (ps : List (List α)) (as : List α)
: coversAll ps as ↔ hasCover ps as := by
  unfold coversAll
  simp 
  rw [hasCover_iff_hasCoverNeNil]
  rw [covers_iff_hasCoverNeNil_with_length ps as.length as rfl as.length]
  simp

def CountCovers (ps : List (List α)) : List α → Std.HashMap Nat Nat
| [] => {(0, 1)}
| as@(_ :: tl) =>
  let s := CountCovers ps tl
  s.insert as.length (ps.filter (· <+: as) |>.filterMap (s.get? <| as.length - ·.length) |>.sum)

def CountCoversAll (ps : List (List α)) (as : List α) : Nat :=
  (CountCovers ps as).getD as.length 0 

namespace Task1

def solve (lines : Array String) : Option Nat := do
  let ps ← lines.get? 0
  let ps := (ps.splitOn ", ").map String.toList 
  return lines[2:].toArray.map String.toList |>.filter (coversAll ps) |>.size

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day19/test.txt")
  println! "Test: {solve lines}"
  println! "Expected: {6}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day19/task.txt")
  println! "Task: {solve lines}"

end Task1

namespace Task2

def solve (lines : Array String) : Option Nat := do
  let ps ← lines.get? 0
  let ps := (ps.splitOn ", ").map String.toList 
  return lines[2:].toArray.map String.toList |>.map (CountCoversAll ps) |>.toList |>.sum 

def main : IO Unit := do
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day19/test.txt")
  println! "Test: {solve lines}"
  println! "Expected: {16}"
  let lines ← IO.FS.lines (System.FilePath.mk "Data/Day19/task.txt")
  println! "Task: {solve lines}"

end Task2

def main : IO Unit := do
  println! "Day 19"
  println! "Task 1"
  Task1.main
  println! ""
  println! "Task 2"
  Task2.main
  println! ""

end Day19
