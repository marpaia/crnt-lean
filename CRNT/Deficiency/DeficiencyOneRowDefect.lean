import CRNT.Theorems.DeficiencyZero.Existence
import CRNT.Deficiency.DeficiencyOne

/-!
# The row-space defect of a deficiency-one network

The transpose stoichiometric row space is contained in the transpose incidence row space.  The
codimension of this inclusion is exactly the network deficiency.  In particular, at deficiency one
the two row spaces differ by precisely one dimension.  This is the linear-algebraic form of the
single scalar obstruction in the Boros/Feinberg existence construction.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- At deficiency one, the incidence-transpose row space has exactly one more dimension than the
stoichiometric-transpose row space. -/
theorem finrank_range_incidenceTranspose_eq_stoichTranspose_add_one
    (N : Network S) (hδ : N.DeficiencyOne) :
    Module.finrank ℝ (LinearMap.range (Matrix.transpose N.incidenceMatrix).mulVecLin) =
      Module.finrank ℝ (LinearMap.range (Matrix.transpose N.stoichMatrix).mulVecLin) + 1 := by
  rw [N.finrank_range_incidenceTranspose, N.finrank_range_stoichTranspose,
    N.incidenceRank_eq_stoichRank_add]
  have hfin : Module.finrank ℝ N.deficiencySubspace = 1 :=
    (N.deficiencyOne_iff_deficiency_eq_one).mp hδ
  rw [hfin]

/-- Equivalently, the stoichiometric-transpose row space is a proper hyperplane in the
incidence-transpose row space. -/
theorem range_stoichTranspose_lt_range_incidenceTranspose_of_deficiencyOne
    (N : Network S) (hδ : N.DeficiencyOne) :
    LinearMap.range (Matrix.transpose N.stoichMatrix).mulVecLin <
      LinearMap.range (Matrix.transpose N.incidenceMatrix).mulVecLin := by
  refine lt_of_le_of_ne N.range_stoichTranspose_le ?_
  intro heq
  have hfin := congrArg (fun U : Submodule ℝ (N.R → ℝ) => Module.finrank ℝ U) heq
  have hgap := N.finrank_range_incidenceTranspose_eq_stoichTranspose_add_one hδ
  rw [hfin] at hgap
  omega

end Network
end CRNT
