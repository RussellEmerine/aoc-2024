import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Logic.Equiv.Fin

def Array.modify' (a : Array α) (i : Fin a.size) (f : α → α) : Array α := 
  a.set i (f a[i])

theorem Array.size_modify' (a : Array α) (i : Fin a.size) (f : α → α)
: (a.modify' i f).size = a.size := by
  unfold modify'
  rw [Array.size_set]

-- (i, j) where i is the row number and j is the col number
-- row 0 on top, col 0 on left
abbrev Idx m n := Fin m × Fin n

inductive Direction
| U
| D
| L
| R
deriving Fintype, Hashable, DecidableEq, Repr

namespace Direction

def cw : Direction → Direction
| U => R
| R => D
| D => L
| L => U

def ccw : Direction → Direction
| U => L
| L => D
| D => R
| R => U

def univ : List Direction := [U, L, D, R]

end Direction

namespace Idx

variable {m n : ℕ}

def rotate (p : Idx m n) : Direction → Idx m n
| .U => ((finRotate _).symm p.fst, p.snd) 
| .D => (finRotate _ p.fst, p.snd) 
| .L => (p.fst, (finRotate _).symm p.snd) 
| .R => (p.fst, finRotate _ p.snd) 

def move (p : Idx m n) : Direction → Option (Idx m n)
| .U => if 0 < p.fst.val then some ((finRotate _).symm p.fst, p.snd) else none 
| .D => if p.fst.val + 1 < m then some (finRotate _ p.fst, p.snd) else none 
| .L => if 0 < p.snd.val then some (p.fst, (finRotate _).symm p.snd) else none 
| .R => if p.snd.val + 1 < n then some (p.fst, finRotate _ p.snd) else none 

def equivFinMul (m n : Nat) : Equiv (Idx m n) (Fin (m * n)) where
  toFun p := {
    val := n * p.fst.val + p.snd.val
    isLt := by
      rcases p with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      cases m
      case zero => exact (i.not_lt_zero hi).elim 
      case succ m =>
      cases n
      case zero => exact (j.not_lt_zero hj).elim 
      case succ n =>
      dsimp
      rw [mul_comm, add_mul]
      apply add_lt_add_of_le_of_lt
      · apply Nat.mul_le_mul_right
        exact Nat.lt_add_one_iff.mp hi
      · rw [Nat.one_mul]
        exact hj
  }
  invFun i := ({
    val := i / n
    isLt := by
      rw [Nat.div_lt_iff_lt_mul]
      · exact i.is_lt
      · by_contra h
        replace h := Nat.eq_zero_of_not_pos h
        subst h
        rw [mul_zero] at i
        exact i.elim0
  }, {
    val := i % n
    isLt := by
      apply Nat.mod_lt
      by_contra h
      replace h := Nat.eq_zero_of_not_pos h
      subst h
      rw [mul_zero] at i
      exact i.elim0
  })
  left_inv p := by
    rcases p with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    ext
    · dsimp
      rw [Nat.mul_add_div (Nat.zero_lt_of_lt hj)]
      rw [Nat.div_eq_of_lt hj, add_zero]
    · dsimp
      rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hj
  right_inv i := by
    ext
    dsimp
    rw [Nat.div_add_mod i.val n]

end Idx 

structure GridArray (m n : ℕ) (α) where
  (array : Array (Array α))
  (h₁ : array.size = m)
  (h₂ : ∀ {i} (h : i < array.size), array[i].size = n)
deriving DecidableEq

namespace GridArray

instance [Hashable α] : Hashable (GridArray m n α) where
  hash grid := mixHash 20 (hash grid.array)

def indices (m n : ℕ) : List (Idx m n) :=
  Prod.mk <$> List.finRange m <*> List.finRange n

variable {m n} {α}

def ofMatrix (mat : Matrix (Fin m) (Fin n) α) : GridArray m n α where
  array := Array.ofFn (fun i => Array.ofFn (mat i))
  h₁ := by rw [Array.size_ofFn]
  h₂ := fun h => by rw [Array.getElem_ofFn _ _ h, Array.size_ofFn]

def ofFn (f : Fin m → Fin n → α) : GridArray m n α :=
  ofMatrix (Matrix.of f)

instance [Inhabited α] : Inhabited (GridArray m n α) where
  default := ofFn default 

instance [ToString α] : ToString (GridArray m n α) where
  toString grid := toString grid.array

def get (grid : GridArray m n α) (p : Idx m n) : α :=
  have : p.fst < grid.array.size := by
    rw [grid.h₁]
    exact p.fst.is_lt
  have : p.snd < grid.array[p.fst].size := by
    rw [Fin.getElem_fin, grid.h₂ _]
    exact p.snd.is_lt
  grid.array[p.fst][p.snd]

def map (f : α → β) (grid : GridArray m n α) : GridArray m n β :=
  ofFn fun i j => f (grid.get (i, j))

def modify (grid : GridArray m n α) (p : Idx m n) (f : α → α)
: GridArray m n α := {
    array := grid.array.modify' ⟨p.fst, by rw [grid.h₁]; exact p.fst.is_lt⟩ fun row =>
      row.modify p.snd f
    h₁ := by rw [Array.size_modify']; exact grid.h₁
    h₂ := by
      intro i hi
      unfold Array.modify'
      dsimp
      rw [Array.get_set]
      split_ifs
      · rw [Array.size_modify, grid.h₂]
      · apply grid.h₂
      convert hi using 1
      rw [Array.size_modify']
  }

def set (grid : GridArray m n α) (p : Idx m n) (a : α)
: GridArray m n α :=
  grid.modify p (Function.const _ a)

def values (grid : GridArray m n α) : List α :=
  grid.get <$> indices m n 

def transpose (grid : GridArray m n α) : GridArray n m α :=
  ofFn fun j i => grid.get (i, j)

def row (grid : GridArray m n α) (i : Fin m) : Array α :=
  grid.array[i]'(by rw [grid.h₁]; exact i.is_lt)

def col (grid : GridArray m n α) (j : Fin n) : Array α :=
  ((fun i => grid.get (i, j)) <$> List.finRange m).toArray 

def ofLines' (lines : Array (Array α)) : Except String ((m : ℕ) × (n : ℕ) × GridArray (m + 1) (n + 1) α) := do
  let m := lines.size
  if hm : 0 < m then
    let n := lines[0].size
    if hn : 0 < n ∧ ∀ {i} (hi : i < m), lines[i].size = n then
      return ⟨m - 1, n - 1, {
        array := lines 
        h₁ := by rw [Nat.sub_add_cancel hm]
        h₂ := by intro i hi; rw [hn.right, Nat.sub_add_cancel hn.left]
      }⟩
    else Except.error "can't make GridArray of uneven array"
  else Except.error "can't make GridArray of empty array"

def ofLines (lines : Array (Array α)) : Except String ((m : ℕ) × (n : ℕ) × GridArray m n α) := do
  let ⟨m, n, grid⟩ ← ofLines' lines
  return ⟨m + 1, n + 1, grid⟩ 
  
-- reverse the ordering *of the rows*, e.g. [[a, b], [c, d]] => [[c, d], [a, b]]
def reverseRows (grid : GridArray m n α) : GridArray m n α where
  array := grid.array.reverse
  h₁ := by rw [Array.size_reverse, grid.h₁]
  h₂ := by
    intro i hi
    have := grid.array.reverse.getElem_mem_toList hi
    rw [Array.toList_reverse, List.mem_reverse, List.mem_iff_get] at this
    rcases this with ⟨j, hj⟩
    rw [← hj, List.get_eq_getElem, ← Array.getElem_eq_getElem_toList, grid.h₂ j.is_lt]

-- [[a, b], [c, d]] => [[b, a], [d, c]]
def reverseCols (grid : GridArray m n α) : GridArray m n α :=
  grid.transpose.reverseRows.transpose

end GridArray
