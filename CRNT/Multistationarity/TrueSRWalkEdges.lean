import CRNT.Multistationarity.TrueSRGlueMaps

/-!
# The edge set of a glued cycle

Banaji--Craciun's Lemma 10 concludes that two even cycles have an S-to-R intersection *equal to
the chord*.  To feed `no_shared_path_of_trueSRCriterion` we therefore need to know the glued
cycle's edge set exactly: it is the union of the two paths' edge sets, and nothing else.

Two steps: every walk position is either an even position or the successor of one
(`walk_pos_cases`), which identifies a cycle's edge set with its walk's; then the glue's branch
equations identify that with `P`'s edges together with `Q`'s.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

@[simp] theorem TrueSRClosedWalk.toCycle_leftEdge (W : N.TrueSRClosedWalk n) (t : Fin n) :
    (W.toCycle).leftEdge t = W.edge (evenPos t) := rfl

@[simp] theorem TrueSRClosedWalk.toCycle_rightEdge (W : N.TrueSRClosedWalk n) (t : Fin n) :
    (W.toCycle).rightEdge t = W.edge (walkSucc (evenPos t)) := rfl

/-- Every walk position is an even position or the successor of one. -/
theorem walk_pos_cases (hn : 0 < n) (m : Fin (2 * n)) :
    (∃ t : Fin n, m = evenPos t) ∨ (∃ t : Fin n, m = walkSucc (evenPos t)) := by
  have hm := m.isLt
  have hdiv : m.1 / 2 < n := by omega
  by_cases h : m.1 % 2 = 0
  · exact Or.inl ⟨⟨m.1 / 2, hdiv⟩, Fin.ext (by show m.1 = 2 * (m.1 / 2); omega)⟩
  · refine Or.inr ⟨⟨m.1 / 2, hdiv⟩, Fin.ext ?_⟩
    rw [walkSucc_evenPos_val]
    show m.1 = 2 * (m.1 / 2) + 1
    omega

/-- **A glued cycle's edges are exactly the two paths' edges.** -/
theorem TrueSRClosedWalk.containsEdge_iff (W : N.TrueSRClosedWalk n) (e : N.TrueSREdge) :
    (W.toCycle).ContainsEdge e ↔ ∃ m, e.SameIncidence (W.edge m) := by
  constructor
  · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
    · exact ⟨evenPos t, by simpa using ht⟩
    · exact ⟨walkSucc (evenPos t), by simpa using ht⟩
  · rintro ⟨m, hm⟩
    have hn : 0 < n := by have := W.nontrivial; omega
    rcases walk_pos_cases hn m with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact Or.inl ⟨t, by rw [ht] at hm; simpa using hm⟩
    · exact Or.inr ⟨t, by rw [ht] at hm; simpa using hm⟩

namespace TrueSRPath

variable {i j : ℕ} (P : N.TrueSRPath (2 * j + 1)) (Q : N.TrueSRPath (2 * i + 1))

/-- Each glue edge comes from one of the two paths. -/
theorem glueEdge_cases (m : Fin (2 * (i + j + 1))) :
    (∃ p, glueEdge P Q m = P.edge p) ∨ (∃ q, glueEdge P Q m = Q.edge q) := by
  by_cases h : m.1 ≤ 2 * j
  · exact Or.inl ⟨_, glueEdge_left P Q h⟩
  · exact Or.inr ⟨_, glueEdge_right P Q h⟩

/-- Every edge of `P` occurs in the glue. -/
theorem glueEdge_of_P (p : Fin (2 * j + 1)) :
    ∃ m : Fin (2 * (i + j + 1)), glueEdge P Q m = P.edge p := by
  have hp := p.isLt
  refine ⟨⟨p.1, by omega⟩, ?_⟩
  rw [glueEdge_left_val P Q p.1 rfl (by omega) hp]

/-- Every edge of `Q` occurs in the glue. -/
theorem glueEdge_of_Q (q : Fin (2 * i + 1)) :
    ∃ m : Fin (2 * (i + j + 1)), glueEdge P Q m = Q.edge q := by
  have hq := q.isLt
  refine ⟨⟨2 * i + 2 * j + 1 - q.1, by omega⟩, ?_⟩
  rw [glueEdge_right_val P Q q.1 (by simp; omega) (by simp; omega) hq]

@[simp] theorem glueWalk_edge (h : Gluable P Q) (hn : 2 ≤ i + j + 1) :
    (glueWalk P Q h hn).edge = glueEdge P Q := rfl

/-- **The glued cycle contains exactly the edges of the two paths.** -/
theorem glueCycle_containsEdge_iff (h : Gluable P Q) (hn : 2 ≤ i + j + 1)
    (e : N.TrueSREdge) :
    (glueCycle P Q h hn).ContainsEdge e ↔
      (∃ p, e.SameIncidence (P.edge p)) ∨ (∃ q, e.SameIncidence (Q.edge q)) := by
  rw [glueCycle, TrueSRClosedWalk.containsEdge_iff]
  simp only [glueWalk_edge]
  constructor
  · rintro ⟨m, hm⟩
    rcases glueEdge_cases P Q m with ⟨p, hp⟩ | ⟨q, hq⟩
    · exact Or.inl ⟨p, by rw [← hp]; exact hm⟩
    · exact Or.inr ⟨q, by rw [← hq]; exact hm⟩
  · rintro (⟨p, hp⟩ | ⟨q, hq⟩)
    · obtain ⟨m, hm⟩ := glueEdge_of_P P Q p
      exact ⟨m, by rw [hm]; exact hp⟩
    · obtain ⟨m, hm⟩ := glueEdge_of_Q P Q q
      exact ⟨m, by rw [hm]; exact hq⟩

end TrueSRPath

end CRNT.Network
