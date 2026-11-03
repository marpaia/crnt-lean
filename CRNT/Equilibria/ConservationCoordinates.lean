import CRNT.Flux.PSemiflow
import CRNT.Stoich.ConservationDimension
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Conservation coordinates for stoichiometric classes

The stoichiometric compatibility relation can be characterized dually by conservation
laws. Two concentration vectors are compatible iff every linear conservation law takes
the same value on them. Consequently the codimension of a compatibility class is the
dimension of the conservation-law space `S^⊥`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The full linear space of conservation laws. -/
noncomputable def conservationSubspace (N : Network S) : Submodule ℝ (S → ℝ) :=
  orthSum N.stoichSubspace

/-- The profile of a concentration against a conservation law. -/
def conservationCoordinate (w : S → ℝ) (x : Concentration S) : ℝ :=
  weightedTotal w x

/-- Compatibility implies equality of all conservation coordinates. -/
theorem conservationCoordinates_eq_of_stoichCompatible (N : Network S)
    {x y : Concentration S} (hxy : N.StoichCompatible x y) :
    ∀ w ∈ N.conservationSubspace,
      conservationCoordinate w x = conservationCoordinate w y := by
  intro w hw
  exact N.weightedTotal_eq_of_stoichCompatible hw hxy

/-- **Dual characterization of stoichiometric compatibility.** -/
theorem stoichCompatible_iff_conservationCoordinates_eq (N : Network S)
    (x y : Concentration S) :
    N.StoichCompatible x y ↔
      ∀ w ∈ N.conservationSubspace,
        conservationCoordinate w x = conservationCoordinate w y := by
  constructor
  · exact N.conservationCoordinates_eq_of_stoichCompatible
  · intro h
    rw [StoichCompatible, ← orthSum_orthSum N.stoichSubspace]
    rw [mem_orthSum]
    intro w hw
    have heq := h w hw
    unfold conservationCoordinate weightedTotal at heq
    have hzero : ∑ s : S, w s * (y s - x s) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith
    simpa [Pi.sub_apply, mul_comm] using hzero

/-- A compatibility class is exactly a level set of the full conservation profile. -/
theorem compatibilityClass_eq_conservationLevelSet (N : Network S)
    (x₀ : Concentration S) :
    N.compatibilityClass x₀ =
      {x | ∀ w ∈ N.conservationSubspace,
        conservationCoordinate w x = conservationCoordinate w x₀} := by
  ext x
  simp only [Set.mem_setOf_eq]
  rw [mem_compatibilityClass, N.stoichCompatible_iff_conservationCoordinates_eq]
  simp only [eq_comm]

/-- Dimension of the conservation-law space. -/
theorem finrank_conservationSubspace (N : Network S) :
    Module.finrank ℝ N.conservationSubspace + N.stoichRank = Fintype.card S := by
  rw [conservationSubspace, finrank_orthSum]
  change (Fintype.card S - N.stoichRank) + N.stoichRank = Fintype.card S
  have hle := N.stoichRank_le_card
  omega

/-- The number of independent conservation coordinates is the codimension of the
stoichiometric subspace. -/
theorem finrank_conservationSubspace_eq_codim (N : Network S) :
    Module.finrank ℝ N.conservationSubspace = Fintype.card S - N.stoichRank := by
  have h := N.finrank_conservationSubspace
  omega

/-- Full-rank stoichiometry is equivalent to absence of nonzero conservation laws. -/
theorem stoichRank_full_iff_no_conservationLaw (N : Network S) :
    N.stoichRank = Fintype.card S ↔ N.conservationSubspace = ⊥ := by
  simpa [conservationSubspace, conservationLawSpace] using
    N.stoichRank_eq_card_iff_conservationLawSpace_eq_bot

/-- If the stoichiometric rank is full, all concentration vectors are compatible. -/
theorem stoichCompatible_all_of_fullRank (N : Network S)
    (hfull : N.stoichRank = Fintype.card S) (x y : Concentration S) :
    N.StoichCompatible x y := by
  have hbot := (N.stoichRank_full_iff_no_conservationLaw).1 hfull
  rw [N.stoichCompatible_iff_conservationCoordinates_eq]
  intro w hw
  rw [hbot] at hw
  have hw0 : w = 0 := by simpa using hw
  subst w
  simp [conservationCoordinate, weightedTotal]

end Network
end CRNT
