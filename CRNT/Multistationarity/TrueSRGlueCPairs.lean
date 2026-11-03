import CRNT.Multistationarity.TrueSRSeamParity

/-!
# c-pairs of a glued cycle, position by position

`numCPairs (glueCycle P Q) = c(P) + c(Q) + s(P,Q)` is a `Finset` card computation on top of
three pointwise facts, proved here: below the seam the c-pair condition is intrinsic to `P`,
above it intrinsic to `Q`, and at the single seam position `t = j` it compares `P`'s last edge
with `Q`'s last edge.  In particular there is exactly **one** seam position, which is why the
species-to-reaction parity conclusion differs from Shinar--Feinberg A.4/A.5 (see
`TrueSRSeamParity.lean`).
-/

namespace CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {i j : ℕ}
  (P : N.TrueSRPath (2 * j + 1)) (Q : N.TrueSRPath (2 * i + 1))
  (h : Gluable P Q) (hn : 2 ≤ i + j + 1)

theorem glueCycle_leftEdge (t : Fin (i + j + 1)) :
    (glueCycle P Q h hn).leftEdge t = glueEdge P Q (evenPos t) := rfl

theorem glueCycle_rightEdge (t : Fin (i + j + 1)) :
    (glueCycle P Q h hn).rightEdge t = glueEdge P Q (walkSucc (evenPos t)) := rfl

/-- Below the seam, the c-pair condition is intrinsic to `P`. -/
theorem glueCycle_isCPair_below (t : Fin (i + j + 1)) (ht : t.1 < j) :
    (glueCycle P Q h hn).isCPair t ↔
      (P.edge ⟨2 * t.1, by omega⟩).endpoint = (P.edge ⟨2 * t.1 + 1, by omega⟩).endpoint := by
  have htl := t.isLt
  have hev : (evenPos t).1 = 2 * t.1 := rfl
  have hod : (walkSucc (evenPos t)).1 = 2 * t.1 + 1 := walkSucc_evenPos_val t
  rw [TrueSRCycle.isCPair, glueCycle_leftEdge, glueCycle_rightEdge,
    glueEdge_left_val P Q (2 * t.1) hev (by omega) (by omega),
    glueEdge_left_val P Q (2 * t.1 + 1) hod (by omega) (by omega)]

/-- **The single seam position** `t = j`: `P`'s last edge against `Q`'s last edge. -/
theorem glueCycle_isCPair_seam (hj : j < i + j + 1) :
    (glueCycle P Q h hn).isCPair ⟨j, hj⟩ ↔
      (P.edge ⟨2 * j, by omega⟩).endpoint = (Q.edge ⟨2 * i, by omega⟩).endpoint := by
  have hev : (evenPos (⟨j, hj⟩ : Fin (i + j + 1))).1 = 2 * j := rfl
  have hod : (walkSucc (evenPos (⟨j, hj⟩ : Fin (i + j + 1)))).1 = 2 * j + 1 :=
    walkSucc_evenPos_val ⟨j, hj⟩
  rw [TrueSRCycle.isCPair, glueCycle_leftEdge, glueCycle_rightEdge,
    glueEdge_left_val P Q (2 * j) hev (by omega) (by omega),
    glueEdge_right_val P Q (2 * i) (by omega) (by rw [hod]; omega) (by omega)]

/-- Above the seam, the c-pair condition is intrinsic to `Q`. -/
theorem glueCycle_isCPair_above (t : Fin (i + j + 1)) (ht : j < t.1) :
    (glueCycle P Q h hn).isCPair t ↔
      (Q.edge ⟨2 * i + 2 * j - 2 * t.1 + 1, by have := t.isLt; omega⟩).endpoint
        = (Q.edge ⟨2 * i + 2 * j - 2 * t.1, by have := t.isLt; omega⟩).endpoint := by
  have htl := t.isLt
  have hev : (evenPos t).1 = 2 * t.1 := rfl
  have hod : (walkSucc (evenPos t)).1 = 2 * t.1 + 1 := walkSucc_evenPos_val t
  rw [TrueSRCycle.isCPair, glueCycle_leftEdge, glueCycle_rightEdge,
    glueEdge_right_val P Q (2 * i + 2 * j - 2 * t.1 + 1) (by rw [hev]; omega)
      (by rw [hev]; omega) (by omega),
    glueEdge_right_val P Q (2 * i + 2 * j - 2 * t.1) (by rw [hod]; omega)
      (by rw [hod]; omega) (by omega)]

end CRNT.Network.TrueSRPath
