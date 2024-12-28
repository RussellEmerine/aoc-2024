import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fintype.Basic

universe u

-- LawfulBEq V to ensure List.instDecidableMemOfLawfulBEq
variable {V : Type u} [DecidableEq V] [LawfulBEq V] [Hashable V] [Fintype V]

def toposort (G : Digraph V) [DecidableRel G.Adj] (l : List V) (_ : ∀ v, v ∈ l) (_ : l.Nodup) : Option (List V) := do
  let mut out := []
  for _ in l do
    let x ← l.filter (fun x => x ∉ out ∧ ∀ y ∉ out, ¬G.Adj x y) |>.head? 
    out := x :: out 
  return out 

/-
hmmmm

structure TopoSortState (G : Digraph V) [DecidableRel G.Adj] where
  (out : List V)
  -- Really this should be a HashMap 
  (count : V → ℕ)
  (q : List V)

namespace TopoSortState

variable (G : Digraph V) [DecidableRel G.Adj]

def start (l : List V) (_ : ∀ v, v ∈ l) (_ : l.Nodup) : TopoSortState G where
  out := []
  count v := Fintype.card {u // G.Adj v u}
  q := l.filter fun v => ∀ u, ¬G.Adj v u

def next (state : TopoSortState G) : Option (TopoSortState G) :=
  if hx : state.q = [] then
    none
  else
    let x := state.q.head hx
    some {
      out := x :: state.out
      count v := state.count v - if G.Adj v x then 1 else 0
      q :=  state.q.tail
    }

end TopoSortState

def toposort (G : Digraph V) [DecidableRel G.Adj] (l : List V) (h₁ : ∀ v, v ∈ l) (h₂ : l.Nodup) : Option (List V) := do
  let mut state := TopoSortState.start G l h₁ h₂
  for _ in l do
    state ← state.next
  return state.out 

lol i was gonna do this whole correctness thing but it turns out you 
need all the lists to be nodup as well, which i've decided is too much.

structure TopoSortState (G : Digraph V) [DecidableRel G.Adj] where
  (out : List V)
  -- Really this should be a HashMap but if I need an efficient version
  -- then I'll just reimplement without the proofy parts.
  (count : V → ℕ)
  (q : List V)
  (loopless : ∀ v ∈ out, ¬G.Adj v v)
  (ordered : out.Pairwise fun u v => ¬G.Adj v u)
  (hout : ∀ u ∈ out, ∀ v ∉ out, ¬G.Adj u v)
  (hcount : ∀ v, count v = Fintype.card {u // G.Adj v u ∧ u ∉ out})
  (hq : ∀ v, v ∈ q ↔ v ∉ out ∧ count v = 0)
  (nodup : q.Nodup)

namespace TopoSortState

variable (G : Digraph V) [DecidableRel G.Adj]

def start (l : List V) (univ : ∀ v, v ∈ l) (nodup : l.Nodup) : TopoSortState G where
  out := []
  count v := Fintype.card {u // G.Adj v u}
  q := l.filter fun v => ∀ u, ¬G.Adj v u
  loopless v hv := (List.not_mem_nil v hv).elim
  ordered := List.Pairwise.nil
  hout := by simp 
  hcount v := by simp
  hq v := by simp [univ, Fintype.card_eq_zero_iff]
  nodup := nodup.filter _
  
def next (state : TopoSortState G) : Option (TopoSortState G) :=
  if hx : state.q = [] then
    none
  else
    let x := state.q.head hx
    some {
      out := x :: state.out
      count v := state.count v - if G.Adj v x then 1 else 0
      q := state.q.tail
      loopless v hv := by
        cases hv
        · have := state.hq x
          simp [List.head_mem hx, state.hcount x, Fintype.card_eq_zero_iff] at this
          rcases this with ⟨h₁, h₂⟩
          intro h
          exact h₁ (h₂ x h)
        · exact state.loopless _ _
      ordered := by
        rw [List.pairwise_cons]
        refine ⟨?_, state.ordered⟩
        intro v hv
        apply state.hout v hv 
        have := state.hq x
        simp [List.head_mem hx] at this
        exact this.left
      hout u hu v hv := by
        cases hu
        · replace hv := List.not_mem_of_not_mem_cons hv
          contrapose! hv
          have := state.hq x
          simp [List.head_mem hx, state.hcount x, Fintype.card_eq_zero_iff] at this
          exact this.right _ hv
        · replace hv := List.not_mem_of_not_mem_cons hv
          exact state.hout _ _ _ hv
      hcount v := by
        dsimp
        rw [state.hcount, Fintype.card_subtype, Fintype.card_subtype]
        conv => {
          lhs
          rw [← Finset.filter_filter, Finset.filter_comm]
        }
        conv => {
          rhs
          rw [← Finset.filter_filter, Finset.filter_comm]
        }
        suffices h : Finset.univ.filter (fun u => u ∉ state.out)
            = insert x (Finset.univ.filter (fun u => u ∉ x :: state.out)) by
          rw [h]
          rw [Finset.filter_insert]
          split_ifs with hv
          · rw [Finset.card_insert_eq_ite]
            split_ifs with h
            · simp at h
            · simp
          · rw [Nat.sub_zero]
        ext u
        simp
        by_cases hu : u = x
        · subst hu
          simp
          exact ((state.hq x).mp (List.head_mem hx)).left
        · simp [hu]
      hq v := by
        
        sorry
    }

  

end TopoSortState
-/
