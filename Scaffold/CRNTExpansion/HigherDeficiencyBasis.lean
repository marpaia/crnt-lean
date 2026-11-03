import Scaffold.CRNTExpansion.HigherDeficiencyCoordinates
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Finite coordinates for local higher-deficiency modes

`HigherDeficiencyCoordinates` deliberately kept the local steady-state modes basis-free.  This file
adds the optional finite coordinate layer needed by constructive higher-deficiency algorithms.
The basis is chosen **separately in each linkage-class deficiency subspace**; under tight linkage
deficiency its coordinate count is exactly the linkage-class deficiency.
-/

namespace CRNT
namespace Network

open Module

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A fixed finite basis of one linkage-class deficiency subspace. -/
noncomputable def linkageDeficiencyBasis (N : Network S) (q : Quotient N.linkedSetoid) :
    Basis (Fin (Module.finrank ℝ (N.linkageDeficiencySubspace q))) ℝ
      (N.linkageDeficiencySubspace q) :=
  Module.finBasis ℝ (N.linkageDeficiencySubspace q)

/-- Coordinates of the canonical steady-state linkage mode in the chosen local basis. -/
noncomputable def steadyStateLinkageCoordinates
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x)
    (q : Quotient N.linkedSetoid) :
    Fin (Module.finrank ℝ (N.linkageDeficiencySubspace q)) → ℝ :=
  (N.linkageDeficiencyBasis q).equivFun (N.steadyStateLinkageMode h κ hss q)

/-- Under tightness, the number of local coordinates is exactly `δ_q`. -/
theorem linkageDeficiencyCoordinateCount_eq
    (N : Network S) (h : N.TightLinkageDeficiency) (q : Quotient N.linkedSetoid) :
    Module.finrank ℝ (N.linkageDeficiencySubspace q) = (N.linkageDeficiency q).toNat :=
  N.finrank_linkageDeficiencySubspace_eq_of_tight h q

/-- Vanishing of the chosen coordinate vector is equivalent to vanishing of the canonical local
mode; the criterion is therefore basis-independent even though the coordinates are not. -/
theorem steadyStateLinkageCoordinates_eq_zero_iff
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x)
    (q : Quotient N.linkedSetoid) :
    N.steadyStateLinkageCoordinates h κ hss q = 0 ↔
      N.steadyStateLinkageMode h κ hss q = 0 := by
  constructor
  · intro hz
    apply (N.linkageDeficiencyBasis q).equivFun.injective
    simpa [steadyStateLinkageCoordinates] using hz
  · intro hz
    simp [steadyStateLinkageCoordinates, hz]

/-- Complex balance at a steady state is equivalent to vanishing of the finite coordinate vectors
on every deficient linkage class. -/
theorem isComplexBalanced_iff_deficientLinkageCoordinatesVanish
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x) :
    N.IsComplexBalanced κ x ↔
      ∀ q : Quotient N.linkedSetoid, q ∈ N.deficientLinkageClasses →
        N.steadyStateLinkageCoordinates h κ hss q = 0 := by
  rw [N.isComplexBalanced_iff_deficientSteadyStateModesVanish h κ hss]
  constructor
  · intro hm q hq
    exact (N.steadyStateLinkageCoordinates_eq_zero_iff h κ hss q).2 (hm q hq)
  · intro hc q hq
    exact (N.steadyStateLinkageCoordinates_eq_zero_iff h κ hss q).1 (hc q hq)

end Network
end CRNT
