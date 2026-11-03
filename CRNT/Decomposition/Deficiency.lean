import CRNT.Decomposition.ReactionPartition
import CRNT.Decomposition.Rank

/-!
# Deficiency bookkeeping for reaction decompositions

For each reaction block define its linear deficiency

`δ_i = rank(∂_i) - rank(S_i)`.

The parent deficiency is `rank(∂)-rank(S)`.  Stoichiometric independence forces
`rank(S)=Σ rank(S_i)`; incidence independence forces `rank(∂)=Σ rank(∂_i)`.
Thus the standard Feinberg inequalities and the bi-independent additivity theorem are
pure rank arithmetic.
-/

namespace CRNT

namespace Network

namespace ReactionPartition

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Linear deficiency of one reaction block. -/
noncomputable def blockDeficiencyInt (D : ReactionPartition N ι) (i : ι) : ℤ :=
  (D.blockIncidenceRank i : ℤ) - (D.blockStoichRank i : ℤ)

/-- Total block deficiency. -/
noncomputable def totalBlockDeficiencyInt (D : ReactionPartition N ι) : ℤ :=
  ∑ i, D.blockDeficiencyInt i

/-- Parent deficiency in incidence-rank form. -/
theorem network_deficiency_eq_incidence_sub_stoich (D : ReactionPartition N ι) :
    N.deficiencyInt = (N.incidenceRank : ℤ) - (N.stoichRank : ℤ) := by
  -- `deficiencyInt = n - ℓ - s` and `rank ∂ + ℓ = n`, so `n - ℓ = rank ∂`
  have h := N.incidenceRank_add_numLinkageClasses
  simp only [Network.deficiencyInt]
  omega

/-- Stoichiometric independence gives additive stoichiometric rank. -/
theorem stoichRank_eq_sum_blockStoichRank (D : ReactionPartition N ι)
    (hind : D.StoichIndependent) :
    N.stoichRank = ∑ i, D.blockStoichRank i := by
  exact (D.sum_blockStoichRank_eq_stoichRank_of_independent hind).symm

/-- Incidence independence gives additive incidence rank. -/
theorem incidenceRank_eq_sum_blockIncidenceRank (D : ReactionPartition N ι)
    (hind : D.IncidenceIndependent) :
    N.incidenceRank = ∑ i, D.blockIncidenceRank i := by
  exact (D.sum_blockIncidenceRank_eq_incidenceRank_of_independent hind).symm

/-- Stoichiometric independence yields the Feinberg inequality
`δ(N) ≤ Σ δ_i`. -/
theorem deficiency_le_totalBlockDeficiency_of_stoichIndependent
    (D : ReactionPartition N ι) (hind : D.StoichIndependent) :
    N.deficiencyInt ≤ D.totalBlockDeficiencyInt := by
  rw [D.network_deficiency_eq_incidence_sub_stoich,
    D.stoichRank_eq_sum_blockStoichRank hind]
  unfold totalBlockDeficiencyInt blockDeficiencyInt
  -- rank of a sum of incidence subspaces is at most the sum of ranks
  have hinc : N.incidenceRank ≤ ∑ i, D.blockIncidenceRank i :=
    D.incidenceRank_le_sum_blockIncidenceRank
  -- restate over ℤ with the cast pushed inside the sum, which is the form `omega` sees
  have hinc' : (N.incidenceRank : ℤ) ≤ ∑ i, (D.blockIncidenceRank i : ℤ) := by
    exact_mod_cast hinc
  push_cast
  -- `omega` treats `∑ (aᵢ - bᵢ)` as opaque; split it into a difference of sums first
  rw [Finset.sum_sub_distrib]
  omega

/-- Incidence independence yields the reverse Feinberg inequality
`Σ δ_i ≤ δ(N)`. -/
theorem totalBlockDeficiency_le_deficiency_of_incidenceIndependent
    (D : ReactionPartition N ι) (hind : D.IncidenceIndependent) :
    D.totalBlockDeficiencyInt ≤ N.deficiencyInt := by
  rw [D.network_deficiency_eq_incidence_sub_stoich,
    D.incidenceRank_eq_sum_blockIncidenceRank hind]
  unfold totalBlockDeficiencyInt blockDeficiencyInt
  have hsto : N.stoichRank ≤ ∑ i, D.blockStoichRank i :=
    D.stoichRank_le_sum_blockStoichRank
  have hsto' : (N.stoichRank : ℤ) ≤ ∑ i, (D.blockStoichRank i : ℤ) := by
    exact_mod_cast hsto
  push_cast
  -- `omega` treats `∑ (aᵢ - bᵢ)` as opaque; split it into a difference of sums first
  rw [Finset.sum_sub_distrib]
  omega

/-- **Bi-independent deficiency additivity.** -/
theorem deficiency_eq_totalBlockDeficiency_of_biIndependent
    (D : ReactionPartition N ι) (hbi : D.BiIndependent) :
    N.deficiencyInt = D.totalBlockDeficiencyInt := by
  apply le_antisymm
  · exact D.deficiency_le_totalBlockDeficiency_of_stoichIndependent hbi.1
  · exact D.totalBlockDeficiency_le_deficiency_of_incidenceIndependent hbi.2

/-- Every block deficiency is nonnegative because the complex map sends the block
incidence space onto the block stoichiometric space. -/
theorem blockDeficiency_nonneg (D : ReactionPartition N ι) (i : ι) :
    0 ≤ D.blockDeficiencyInt i := by
  unfold blockDeficiencyInt
  -- proved in `CRNT/Decomposition/BlockDeficiency.lean` via
  -- `map_complexMap_blockIncidence` and `Submodule.finrank_map_le`
  have hrank : D.blockStoichRank i ≤ D.blockIncidenceRank i :=
    D.blockStoichRank_le_blockIncidenceRank i
  push_cast
  omega

/-- Under bi-independence, a deficiency-zero parent has deficiency-zero blocks. -/
theorem blocks_deficiencyZero_of_biIndependent_of_deficiencyZero
    (D : ReactionPartition N ι) (hbi : D.BiIndependent) (h0 : N.DeficiencyZero) :
    ∀ i, D.blockDeficiencyInt i = 0 := by
  have hsum : D.totalBlockDeficiencyInt = 0 := by
    rw [← D.deficiency_eq_totalBlockDeficiency_of_biIndependent hbi]
    exact h0
  intro i
  have hnonneg : ∀ j, 0 ≤ D.blockDeficiencyInt j := D.blockDeficiency_nonneg
  have hle : D.blockDeficiencyInt i ≤ D.totalBlockDeficiencyInt := by
    unfold totalBlockDeficiencyInt
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  rw [hsum] at hle
  exact le_antisymm hle (hnonneg i)

end ReactionPartition

end Network

end CRNT
