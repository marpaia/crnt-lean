import CRNT.Multistationarity.TrueSRGlueBlocks

/-!
# The c-pair count of a glued cycle

`numCPairs (glueCycle P Q) = pathCPairs P + s(P,Q) + pathCPairs Q`, where the middle term is the
single seam indicator.  This is the identity behind the species-to-reaction parity statement:
for three paths with common endpoints the intrinsic terms each appear twice and cancel mod 2,
leaving the three seam indicators, whose sum is odd by the pigeonhole in `TrueSRSeamParity.lean`.
-/

namespace CRNT.Network.TrueSRPath

open Finset

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {i j : ℕ}
  (P : N.TrueSRPath (2 * j + 1)) (Q : N.TrueSRPath (2 * i + 1))
  (h : Gluable P Q) (hn : 2 ≤ i + j + 1)

/-- The middle block is the single seam position. -/
theorem card_block_seam [DecidablePred (glueCycle P Q h hn).isCPair] (hj : j < i + j + 1) :
    ((univ.filter (fun t : Fin (i + j + 1) => t.1 = j)).filter
        (glueCycle P Q h hn).isCPair).card
      = if (glueCycle P Q h hn).isCPair ⟨j, hj⟩ then 1 else 0 := by
  have hsing : (univ.filter (fun t : Fin (i + j + 1) => t.1 = j)) = {⟨j, hj⟩} := by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun ht => Fin.ext ht, fun ht => by rw [ht]⟩
  rw [hsing, filter_singleton]
  split <;> simp

/-- **The c-pair count splits as `P`-interior + seam + `Q`-interior.** -/
theorem glueCycle_numCPairs_split [DecidablePred (CPairAt P)] [DecidablePred (CPairAt Q)]
    [DecidablePred (glueCycle P Q h hn).isCPair] (hj : j < i + j + 1) :
    ((univ.filter (glueCycle P Q h hn).isCPair)).card
      = (univ.filter (CPairAt P)).card
        + (if (glueCycle P Q h hn).isCPair ⟨j, hj⟩ then 1 else 0)
        + (univ.filter (CPairAt Q)).card := by
  have hpart : (univ.filter (glueCycle P Q h hn).isCPair) =
      (((univ.filter (fun t : Fin (i + j + 1) => t.1 < j)).filter (glueCycle P Q h hn).isCPair)
        ∪ ((univ.filter (fun t : Fin (i + j + 1) => t.1 = j)).filter (glueCycle P Q h hn).isCPair))
        ∪ ((univ.filter (fun t : Fin (i + j + 1) => j < t.1)).filter (glueCycle P Q h hn).isCPair) := by
    ext t
    simp only [mem_union, mem_filter, mem_univ, true_and]
    constructor
    · intro ht
      rcases lt_trichotomy t.1 j with h1 | h1 | h1
      · exact Or.inl (Or.inl ⟨h1, ht⟩)
      · exact Or.inl (Or.inr ⟨h1, ht⟩)
      · exact Or.inr ⟨h1, ht⟩
    · rintro ((⟨_, ht⟩ | ⟨_, ht⟩) | ⟨_, ht⟩) <;> exact ht
  have hd1 : Disjoint ((univ.filter (fun t : Fin (i + j + 1) => t.1 < j)).filter (glueCycle P Q h hn).isCPair)
      ((univ.filter (fun t : Fin (i + j + 1) => t.1 = j)).filter (glueCycle P Q h hn).isCPair) := by
    refine disjoint_left.mpr ?_
    intro a ha hb
    simp only [mem_filter, mem_univ, true_and] at ha hb
    omega
  have hd2 : Disjoint
      (((univ.filter (fun t : Fin (i + j + 1) => t.1 < j)).filter (glueCycle P Q h hn).isCPair)
        ∪ ((univ.filter (fun t : Fin (i + j + 1) => t.1 = j)).filter (glueCycle P Q h hn).isCPair))
      ((univ.filter (fun t : Fin (i + j + 1) => j < t.1)).filter (glueCycle P Q h hn).isCPair) := by
    refine disjoint_left.mpr ?_
    intro a ha hb
    simp only [mem_union, mem_filter, mem_univ, true_and] at ha hb
    rcases ha with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  rw [hpart, card_union_of_disjoint hd2, card_union_of_disjoint hd1,
    card_block_below P Q h hn, card_block_seam P Q h hn hj, card_block_above P Q h hn]

end CRNT.Network.TrueSRPath
