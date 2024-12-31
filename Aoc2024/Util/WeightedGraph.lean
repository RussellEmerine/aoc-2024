import Mathlib.Algebra.Order.Monoid.Canonical.Basic
import Batteries.Data.BinaryHeap
import Mathlib.Data.Fintype.Card

universe u v

structure WeightedGraph (V : Type u) (W : Type v) where
  edges : V → List (V × W)

namespace WeightedGraph

variable {V : Type u} {W : Type v} [CanonicallyOrderedAddCommMonoid W] [∀ (x y : W), Decidable (x < y)]

-- not doing the correctness proof because heaps do not actively enforce the heap invariant

def dijkstraAux [BEq V] [Hashable V] 
  (g : WeightedGraph V W)
  (q : Batteries.BinaryHeap (W × V) (·.fst > ·.fst))
  (map : Std.HashMap V W)
: ℕ → Std.HashMap V W
| 0 => map
| (n + 1) =>
  match q.extractMax with
  | (none, _) => map
  | (some (d, a), q'') => Id.run <| do
    let mut map' := map
    let mut q' := q''
    if ¬map'.contains a then
      map' := map'.insert a d
      for (c, w) in g.edges a do
        q' := q'.insert (d + w, c)
    return dijkstraAux g q' map' n

def dijkstra [BEq V] [Hashable V] [Fintype V] (g : WeightedGraph V W) (r : V)
: Std.HashMap V W :=
  dijkstraAux g (Batteries.BinaryHeap.singleton _ (0, r)) {} (Fintype.card V * Fintype.card V * Fintype.card V)
-- i think the iteration bound is actually |V|² but just in case

end WeightedGraph
