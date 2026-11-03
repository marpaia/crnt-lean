import Scaffold.CRNTExpansion.AdvancedDeficiencyKernel
import Scaffold.CRNTExpansion.AdvancedDeficiencyOrientation

/-!
# Linear-map form of the ADA oriented stoichiometric kernel

`AdvancedDeficiencyKernel` introduced the basis-free predicate

`sum_r alpha_r * reactionVector(r) = 0`.

This file packages the same construction as an actual linear map `L_O`.  That is the correct object
for the published ADA: a future basis of `ker L_O` can be chosen without changing the canonical
coordinate-functional definition of the rows `w_r`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The oriented stoichiometric map `L_O`. -/
noncomputable def orientedStoichLinearMap (N : Network S) (O : Finset N.R) :
    ((↥O) → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun := fun alpha => ∑ r : ↥O, alpha r • N.reactionVector r.1
  map_add' := by
    intro a b
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    simp [mul_smul, Finset.smul_sum]

/-- The predicate used in `AdvancedDeficiencyKernel` is exactly membership in `ker L_O`. -/
theorem orientedStoichKernel_iff_mem_ker (N : Network S) (O : Finset N.R)
    (alpha : (↥O) → ℝ) :
    N.OrientedStoichKernel O alpha ↔ alpha ∈ LinearMap.ker (N.orientedStoichLinearMap O) := by
  rfl

/-- A zero ADA row is precisely a coordinate functional that vanishes on `ker L_O`. -/
theorem kernelCoordinateZero_iff_vanishes_on_ker (N : Network S) (O : Finset N.R)
    (r : ↥O) :
    N.KernelCoordinateZero O r ↔
      ∀ alpha : (↥O) → ℝ,
        alpha ∈ LinearMap.ker (N.orientedStoichLinearMap O) → alpha r = 0 := by
  rfl

/-- A concrete orientation feeds directly into the canonical `L_O` construction. -/
noncomputable def ADAOrientation.linearMap {N : Network S} (O : N.ADAOrientation) :
    ((↥O.selected) → ℝ) →ₗ[ℝ] (S → ℝ) :=
  N.orientedStoichLinearMap O.selected

end Network
end CRNT
