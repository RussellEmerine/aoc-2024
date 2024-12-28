import Batteries.Data.UnionFind
import Mathlib.Logic.Equiv.Basic

universe u

variable {α : Type u} {n : ℕ}

structure UnionFind (e : α ≃ Fin n) : Type u where
  uf : Batteries.UnionFind
  h : n = uf.size

namespace UnionFind

def empty (e : α ≃ Fin n) : UnionFind e where
  uf := Batteries.UnionFind.push^[n] (Batteries.UnionFind.mkEmpty n)
  h := by
    suffices h : ∀ i, i = (Batteries.UnionFind.push^[i] (Batteries.UnionFind.mkEmpty n)).size by
      exact h n
    intro i
    induction i
    case zero => simp [Batteries.UnionFind.mkEmpty]
    case succ i ih =>
      rw [Nat.add_comm, Function.iterate_add_apply]
      simp [Batteries.UnionFind.push, ← ih]
      rw [Nat.add_comm]

variable {e : α ≃ Fin n}

instance : EmptyCollection (UnionFind e) := ⟨.empty e⟩

def find (self : UnionFind e) (a : α) : UnionFind e × α := 
  let s := self.uf.find ((e a).cast self.h)
  have h : n = s.fst.size := by rw [Batteries.UnionFind.find_size, ← self.h]
  ({
    uf := s.fst,
    h
  }, e.symm (s.snd.val.cast h.symm))

def union (self : UnionFind e) (a b : α) : UnionFind e where
  uf := self.uf.union ((e a).cast self.h) ((e b).cast self.h)
  h := by simp [Batteries.UnionFind.union, self.h]

def checkEquiv (self : UnionFind e) (a b : α) : UnionFind e × Bool :=
  let (s, r₁) := self.find a
  let (s, r₂) := s.find b
  (s, e r₁ = e r₂)

end UnionFind

