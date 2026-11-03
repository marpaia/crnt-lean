import CRNT.Multistationarity.TrueSRPathCPairs

/-!
# The two blocks of the c-pair count

`numCPairs (glueCycle P Q) = pathCPairs P + s(P,Q) + pathCPairs Q` splits the cycle's positions
into `t < j`, `t = j` and `t > j`.  This file identifies the cards of the two outer blocks with
the paths' own interior c-pair counts, via the reindexings pinned in `TrueSRPathCPairs.lean`.
The middle block is a singleton and the filter splitting is then routine.
-/

namespace CRNT.Network.TrueSRPath

open Finset

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {i j : ℕ}
  (P : N.TrueSRPath (2 * j + 1)) (Q : N.TrueSRPath (2 * i + 1))
  (h : Gluable P Q) (hn : 2 ≤ i + j + 1)

/-- The block below the seam has the same c-pair count as `P`'s interior. -/
theorem card_block_below [DecidablePred (CPairAt P)]
    [DecidablePred (glueCycle P Q h hn).isCPair] :
    ((univ.filter (fun t : Fin (i + j + 1) => t.1 < j)).filter
        (glueCycle P Q h hn).isCPair).card
      = (univ.filter (CPairAt P)).card := by
  have himg : ((univ.filter (fun t : Fin (i + j + 1) => t.1 < j)).filter
      (glueCycle P Q h hn).isCPair)
      = (univ.filter (CPairAt P)).image
        (fun r : Fin j => (⟨r.1, by have := r.isLt; omega⟩ : Fin (i + j + 1))) := by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨hlt, hcp⟩
      exact ⟨⟨t.1, hlt⟩, (isCPair_below_iff P Q h hn t hlt).mp hcp, Fin.ext rfl⟩
    · rintro ⟨r, hr, hrt⟩
      have hval : t.1 = r.1 := by rw [← hrt]
      have hlt : t.1 < j := by rw [hval]; exact r.isLt
      refine ⟨hlt, (isCPair_below_iff P Q h hn t hlt).mpr ?_⟩
      have : (⟨t.1, hlt⟩ : Fin j) = r := Fin.ext hval
      rw [this]; exact hr
  rw [himg, card_image_of_injective]
  intro a b hab
  exact Fin.ext (by have := congrArg Fin.val hab; simpa using this)

/-- The block above the seam has the same c-pair count as `Q`'s interior. -/
theorem card_block_above [DecidablePred (CPairAt Q)]
    [DecidablePred (glueCycle P Q h hn).isCPair] :
    ((univ.filter (fun t : Fin (i + j + 1) => j < t.1)).filter
        (glueCycle P Q h hn).isCPair).card
      = (univ.filter (CPairAt Q)).card := by
  have himg : ((univ.filter (fun t : Fin (i + j + 1) => j < t.1)).filter
      (glueCycle P Q h hn).isCPair)
      = (univ.filter (CPairAt Q)).image
        (fun r : Fin i => (⟨j + (i - r.1), by have := r.isLt; omega⟩ : Fin (i + j + 1))) := by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨hgt, hcp⟩
      have htl := t.isLt
      refine ⟨⟨i - (t.1 - j), by omega⟩, (isCPair_above_iff P Q h hn t hgt).mp hcp, ?_⟩
      apply Fin.ext
      show j + (i - (i - (t.1 - j))) = t.1
      omega
    · rintro ⟨r, hr, hrt⟩
      have hr' := r.isLt
      have hval : t.1 = j + (i - r.1) := by rw [← hrt]
      have hgt : j < t.1 := by rw [hval]; omega
      refine ⟨hgt, (isCPair_above_iff P Q h hn t hgt).mpr ?_⟩
      have : (⟨i - (t.1 - j), by have := t.isLt; omega⟩ : Fin i) = r := by
        apply Fin.ext
        show i - (t.1 - j) = r.1
        rw [hval]; omega
      rw [this]; exact hr
  rw [himg, card_image_of_injective]
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  have := congrArg Fin.val hab
  simp only at this
  exact Fin.ext (by omega)

end CRNT.Network.TrueSRPath
