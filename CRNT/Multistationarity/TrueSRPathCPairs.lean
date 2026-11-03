import CRNT.Multistationarity.TrueSRGlueCPairs

/-!
# Intrinsic c-pair predicate of a path, and the glue reindexing

`numCPairs (glueCycle P Q) = pathCPairs P + s(P,Q) + pathCPairs Q` needs the two blocks of
cycle positions matched against the two paths' *own* interior reaction vertices.  A path of
length `2j+1` has `j+1` reactions, at odd positions `1, 3, …, 2j+1`; the last is the shared
endpoint, so `j` are interior, indexed by `r : Fin j` with incident edges `P.edge (2r)` and
`P.edge (2r+1)`.

The reindexing is the error-prone part and is pinned here: below the seam it is `t ↦ t`, above
the seam it is `t ↦ i - (t - j)`, which reverses orientation because the glue traverses `Q`
backwards.
-/

namespace CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- The c-pair condition at a path's `r`-th interior reaction vertex. -/
def CPairAt {j : ℕ} (P : N.TrueSRPath (2 * j + 1)) (r : Fin j) : Prop :=
  (P.edge ⟨2 * r.1, by have := r.isLt; omega⟩).endpoint
    = (P.edge ⟨2 * r.1 + 1, by have := r.isLt; omega⟩).endpoint

section

variable {i j : ℕ} (P : N.TrueSRPath (2 * j + 1)) (Q : N.TrueSRPath (2 * i + 1))
  (h : Gluable P Q) (hn : 2 ≤ i + j + 1)

/-- Below the seam the glue reindexes by the identity. -/
theorem isCPair_below_iff (t : Fin (i + j + 1)) (ht : t.1 < j) :
    (glueCycle P Q h hn).isCPair t ↔ CPairAt P ⟨t.1, ht⟩ := by
  rw [glueCycle_isCPair_below P Q h hn t ht]
  rfl

/-- Above the seam the glue reindexes by `t ↦ i - (t - j)`, reversing orientation. -/
theorem isCPair_above_iff (t : Fin (i + j + 1)) (ht : j < t.1) :
    (glueCycle P Q h hn).isCPair t ↔
      CPairAt Q ⟨i - (t.1 - j), by have := t.isLt; omega⟩ := by
  have htl := t.isLt
  rw [glueCycle_isCPair_above P Q h hn t ht, CPairAt, eq_comm]
  have e1 : 2 * (i - (t.1 - j)) = 2 * i + 2 * j - 2 * t.1 := by omega
  have e2 : 2 * (i - (t.1 - j)) + 1 = 2 * i + 2 * j - 2 * t.1 + 1 := by omega
  rw [show (⟨2 * (i - (t.1 - j)), by omega⟩ : Fin (2 * i + 1))
        = ⟨2 * i + 2 * j - 2 * t.1, by omega⟩ from Fin.ext e1,
    show (⟨2 * (i - (t.1 - j)) + 1, by omega⟩ : Fin (2 * i + 1))
        = ⟨2 * i + 2 * j - 2 * t.1 + 1, by omega⟩ from Fin.ext e2]

/-- The reindexing above the seam is injective. -/
theorem above_reindex_inj {t t' : Fin (i + j + 1)} (ht : j < t.1) (ht' : j < t'.1)
    (he : i - (t.1 - j) = i - (t'.1 - j)) : t = t' := by
  have := t.isLt
  have := t'.isLt
  exact Fin.ext (by omega)

/-- The reindexing above the seam is surjective onto `Fin i`. -/
theorem above_reindex_surj (r : Fin i) :
    ∃ t : Fin (i + j + 1), j < t.1 ∧ i - (t.1 - j) = r.1 := by
  have hr := r.isLt
  refine ⟨⟨j + (i - r.1), by omega⟩, ?_, ?_⟩
  · show j < j + (i - r.1)
    omega
  · show i - (j + (i - r.1) - j) = r.1
    omega

end

end CRNT.Network.TrueSRPath
