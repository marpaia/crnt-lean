import CRNT.Multistationarity.TrueSRChordExtraction
import CRNT.Multistationarity.TrueSRPathAccessors

/-!
# Spanning paths whose interior avoids the cycle's reaction vertices

`no_spanning_path_of_trueSRCriterion` takes a species-to-reaction path with both endpoints on an
even cycle and an *edge* hypothesis `hnd`: between any two consecutive on-cycle positions the
path must not traverse a cycle edge.  `hnd` quantifies over every position, which is awkward for
a producer that only controls the path's reaction vertices.

`no_reaction_interior_path_of_trueSRCriterion` replaces that global condition by a single local
one.  Suppose only the *reaction* vertices of the interior are known to miss the cycle — the
interior species vertices may well lie on it.  Alternation (`TrueSRPath.species_iff_even`) puts
every reaction vertex at an odd position, and an edge with both endpoints on the cycle has an
on-cycle reaction endpoint; so that endpoint must be the terminal position, and the only edge
`hnd` can fail at is the last one.  The hypothesis therefore collapses to: the final edge is not
a cycle edge.

This is the form a minimal directed causal path supplies.  Running the path into the off-cycle
class from an on-cycle *reaction* vertex, and taking it minimal for the predicate "is an
on-cycle reaction vertex", leaves the interior free of on-cycle reactions but says nothing about
interior species.  It is strictly weaker than
`no_offCycle_interior_path_of_trueSRCriterion`, which demands the whole interior be off the
cycle.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

open TrueSRPath TrueSRCycle

/-- **Only the interior reaction vertices matter.**  A species-to-reaction path with both
endpoints on an even cycle, whose interior *reaction* vertices miss the cycle and whose final
edge is not a cycle edge, is forbidden by the true-SR criterion.

The interior species vertices are unconstrained: an edge with both endpoints on the cycle has a
reaction endpoint on the cycle, that endpoint sits at an odd position, and `hint` forces the
only such position to be the last one. -/
theorem no_reaction_interior_path_of_trueSRCriterion (hSR : N.TrueSRStrongCriterion) {M : ℕ}
    (C : N.TrueSRCycle n) (hC : C.Even)
    (huniq : ∀ e f : N.TrueSREdge, e.reaction = f.reaction → e.species = f.species →
      e.endpoint = f.endpoint)
    (Q : N.TrueSRPath M)
    (h0 : C.HasVertex (Q.vertex ⟨0, by omega⟩))
    (hlast : C.HasVertex (Q.vertex ⟨M, by omega⟩))
    (hint : ∀ p : Fin (M + 1), p.1 ≠ M → p.1 % 2 ≠ 0 → ¬ C.HasVertex (Q.vertex p))
    (hlastL : C.HasVertex (Q.vertex ⟨M - 1, by have := Q.length_pos; omega⟩) →
      ∀ t : Fin n,
        ¬ (Q.edge ⟨M - 1, by have := Q.length_pos; omega⟩).SameIncidence (C.leftEdge t))
    (hlastR : C.HasVertex (Q.vertex ⟨M - 1, by have := Q.length_pos; omega⟩) →
      ∀ t : Fin n,
        ¬ (Q.edge ⟨M - 1, by have := Q.length_pos; omega⟩).SameIncidence (C.rightEdge t)) :
    False := by
  have hMpos : 0 < M := Q.length_pos
  refine no_spanning_path_of_trueSRCriterion hSR C hC huniq Q h0 hlast ?_
  intro p hcast hsucc
  have hp : p.1 < M := p.isLt
  have hpM : p.1 = M - 1 := by
    rcases Nat.even_or_odd p.1 with hev | hod
    · -- `p` even: the reaction endpoint is at `p + 1`, so `hint` forces `p + 1 = M`
      have hpar : p.1 % 2 = 0 := Nat.even_iff.mp hev
      by_contra hne
      have hlt : p.1 + 1 < M + 1 := by omega
      have hne' : (⟨p.1 + 1, hlt⟩ : Fin (M + 1)).1 ≠ M := by
        show p.1 + 1 ≠ M
        omega
      have hodd : (⟨p.1 + 1, hlt⟩ : Fin (M + 1)).1 % 2 ≠ 0 := by
        show (p.1 + 1) % 2 ≠ 0
        omega
      refine hint ⟨p.1 + 1, hlt⟩ hne' hodd ?_
      have he : (⟨p.1 + 1, hlt⟩ : Fin (M + 1)) = p.succ := Fin.ext rfl
      rw [he]
      exact hsucc
    · -- `p` odd: the reaction endpoint is at `p` itself, which is interior
      have hpar : p.1 % 2 = 1 := Nat.odd_iff.mp hod
      exfalso
      have hlt : p.1 < M + 1 := by omega
      have hne' : (⟨p.1, hlt⟩ : Fin (M + 1)).1 ≠ M := by
        show p.1 ≠ M
        omega
      have hodd : (⟨p.1, hlt⟩ : Fin (M + 1)).1 % 2 ≠ 0 := by
        show p.1 % 2 ≠ 0
        omega
      refine hint ⟨p.1, hlt⟩ hne' hodd ?_
      have he : (⟨p.1, hlt⟩ : Fin (M + 1)) = Fin.castSucc p := Fin.ext rfl
      rw [he]
      exact hcast
  have hpen : C.HasVertex (Q.vertex ⟨M - 1, by omega⟩) := by
    have he : (⟨M - 1, by omega⟩ : Fin (M + 1)) = Fin.castSucc p := by
      apply Fin.ext
      show M - 1 = p.1
      omega
    rw [he]
    exact hcast
  have hpe : p = (⟨M - 1, by omega⟩ : Fin M) := Fin.ext (by omega)
  rw [hpe]
  exact ⟨hlastL hpen, hlastR hpen⟩

/-- **Producer-friendly form.**  The final edge fails to be a cycle edge as soon as its species
endpoint is not a cycle *neighbour* of its reaction endpoint: a cycle edge at reaction
`C.reaction k` carries either `C.species k` (the left edge) or `C.species ((k+1) % n)` (the
right edge), so ruling out both indices rules out every cycle edge.

This is the shape a causal producer can discharge.  A positive causal step out of an on-cycle
reaction `C.reaction k` cannot land on `C.species k`, where the same class flux is negative; and
landing on an on-cycle species other than `C.species ((k+1) % n)` is the non-neighbour chord that
`no_nonneighbor_chord` already forbids. -/
theorem no_reaction_interior_path_of_neighbourFree_of_trueSRCriterion
    (hSR : N.TrueSRStrongCriterion) {M : ℕ}
    (C : N.TrueSRCycle n) (hC : C.Even)
    (huniq : ∀ e f : N.TrueSREdge, e.reaction = f.reaction → e.species = f.species →
      e.endpoint = f.endpoint)
    (Q : N.TrueSRPath M)
    (h0 : C.HasVertex (Q.vertex ⟨0, by omega⟩))
    (hlast : C.HasVertex (Q.vertex ⟨M, by omega⟩))
    (hint : ∀ p : Fin (M + 1), p.1 ≠ M → p.1 % 2 ≠ 0 → ¬ C.HasVertex (Q.vertex p))
    (hnb : ∀ t k : Fin n,
      (Q.edge ⟨M - 1, by have := Q.length_pos; omega⟩).species = C.species t →
      (Q.edge ⟨M - 1, by have := Q.length_pos; omega⟩).reaction = C.reaction k →
      t ≠ k ∧ t.1 ≠ (k.1 + 1) % n) :
    False := by
  have hMpos : 0 < M := Q.length_pos
  refine no_reaction_interior_path_of_trueSRCriterion hSR C hC huniq Q h0 hlast hint
    (fun _ t hsame => ?_) (fun _ t hsame => ?_)
  · obtain ⟨hs, hr, -⟩ := hsame
    rw [C.left_species t] at hs
    rw [C.left_reaction t] at hr
    exact (hnb t t hs hr).1 rfl
  · obtain ⟨hs, hr, -⟩ := hsame
    rw [C.right_species t] at hs
    rw [C.right_reaction t] at hr
    have hlt : (t.1 + 1) % n < n := Nat.mod_lt _ (by have := C.nontrivial; omega)
    exact (hnb ⟨(t.1 + 1) % n, hlt⟩ t hs hr).2 rfl

end CRNT.Network
