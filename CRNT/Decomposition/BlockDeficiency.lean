import CRNT.Decomposition.Rank
import CRNT.Decomposition.Deficiency
import CRNT.Deficiency.Definition
import CRNT.Deficiency.DeficiencyOne

/-!
# Block deficiencies and Feinberg decomposition inequalities

For a reaction block, the natural deficiency is the incidence rank minus the
stoichiometric rank.  This is equivalent to `n_i - l_i - s_i` when the block is viewed
as its own reaction graph, but the rank formulation avoids rebuilding a temporary
network.  The classical decomposition inequalities then become direct rank arithmetic.
-/

namespace CRNT
namespace Network
namespace ReactionPartition

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Deficiency of a reaction block, expressed intrinsically through its incidence and
stoichiometric ranks. -/
noncomputable def blockDeficiency (D : ReactionPartition N ι) (i : ι) : ℕ :=
  D.blockIncidenceRank i - D.blockStoichRank i

/-- The block deficiency can therefore be written without truncated subtraction
ambiguity. -/
theorem blockIncidenceRank_eq_blockStoichRank_add_deficiency
    (D : ReactionPartition N ι) (i : ι) :
    D.blockIncidenceRank i = D.blockStoichRank i + D.blockDeficiency i := by
  unfold blockDeficiency
  have h := D.blockStoichRank_le_blockIncidenceRank i
  omega

/-- Sum of block deficiencies. -/
noncomputable def totalBlockDeficiency (D : ReactionPartition N ι) : ℕ :=
  ∑ i : ι, D.blockDeficiency i

/-- In a bi-independent decomposition of a deficiency-zero network every block has
zero deficiency. -/
theorem blockDeficiency_eq_zero_of_biIndependent_deficiencyZero
    (D : ReactionPartition N ι) (hbi : D.BiIndependent)
    (hδ : N.deficiency = 0) (i : ι) : D.blockDeficiency i = 0 := by
  have hsum : D.totalBlockDeficiency = 0 := by
    have hZ := D.deficiency_eq_totalBlockDeficiency_of_biIndependent hbi
    have hcast : (D.totalBlockDeficiency : ℤ) = D.totalBlockDeficiencyInt := by
      unfold totalBlockDeficiency totalBlockDeficiencyInt blockDeficiency blockDeficiencyInt
      push_cast [Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := D.blockStoichRank_le_blockIncidenceRank i
      omega
    have hdefZ : N.deficiencyInt = 0 := by
      rw [N.deficiencyInt_eq_deficiency, hδ]; rfl
    omega
  unfold totalBlockDeficiency at hsum
  exact Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.mp hsum i (Finset.mem_univ i)

/-- Under bi-independence, global deficiency zero is equivalent to blockwise deficiency
zero. -/
theorem deficiencyZero_iff_all_blocks_deficiencyZero
    (D : ReactionPartition N ι) (hbi : D.BiIndependent) :
    N.deficiency = 0 ↔ ∀ i : ι, D.blockDeficiency i = 0 := by
  constructor
  · intro h i
    exact D.blockDeficiency_eq_zero_of_biIndependent_deficiencyZero hbi h i
  · intro h
    -- go through the ℤ form, where the additivity theorem lives
    have hZ := D.deficiency_eq_totalBlockDeficiency_of_biIndependent hbi
    have hz : D.totalBlockDeficiencyInt = 0 := by
      unfold totalBlockDeficiencyInt blockDeficiencyInt
      refine Finset.sum_eq_zero fun i _ => ?_
      have hb := h i
      have hr := D.blockStoichRank_le_blockIncidenceRank i
      unfold blockDeficiency at hb
      omega
    have : N.deficiencyInt = 0 := by rw [hZ, hz]
    rw [N.deficiencyInt_eq_deficiency] at this
    exact_mod_cast this

end ReactionPartition
end Network
end CRNT
