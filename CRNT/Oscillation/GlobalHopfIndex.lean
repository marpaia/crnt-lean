import CRNT.Oscillation.GlobalHopfSpectralCrossing
import CRNT.Oscillation.FiedlerGlobalHopf
import CRNT.Oscillation.SpectralOpenness

/-!
# Spectral index for analytic global Hopf continuation

Fiedler's theorem is not merely "there is an imaginary eigenvalue".  Its global alternative is
triggered by a nonzero net change of the unstable spectral index along an analytic equilibrium
branch.  This file formalizes the finite-dimensional index side.  The only remaining nonlinear
kernel is then the global-Hopf alternative itself.
-/

namespace CRNT

open Polynomial Complex Filter Set

namespace Matrix

variable {I : Type} [DecidableEq I] [Fintype I]

/-- Algebraic multiplicity of characteristic roots in the open right half plane. -/
noncomputable def unstableMultiplicity (M : Matrix I I ℝ) : ℕ :=
  ((M.map (algebraMap ℝ ℂ)).charpoly.roots.filter (fun z => 0 < z.re)).card

/-- A Hurwitz matrix has unstable multiplicity zero. -/
theorem unstableMultiplicity_eq_zero_of_hurwitz
    {M : Matrix I I ℝ} (hM : M.IsHurwitzReal) :
    unstableMultiplicity M = 0 := by
  unfold unstableMultiplicity
  rw [Multiset.card_eq_zero]
  apply Multiset.filter_eq_nil.2
  intro z hz
  exact not_lt_of_ge (le_of_lt (hM z hz))

/-- A strict RHP eigenvalue forces positive unstable multiplicity. -/
theorem unstableMultiplicity_pos_of_hasUnstableEigenvalue
    {M : Matrix I I ℝ} (hM : M.HasUnstableEigenvalue) :
    0 < unstableMultiplicity M := by
  obtain ⟨z, hz, hzpos⟩ := hM
  unfold unstableMultiplicity
  apply (Multiset.card_pos).2
  intro hzero
  have hmem : z ∈
      ((M.map (algebraMap ℝ ℂ)).charpoly.roots.filter (fun w => 0 < w.re)) :=
    Multiset.mem_filter.mpr ⟨hz, hzpos⟩
  rw [hzero] at hmem
  simpa using hmem

end Matrix

/-- Parameters at which the continuation Jacobian has nonzero imaginary-axis spectrum. -/
def hopfCenterSet {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) : Set ℝ :=
  {μ | ∃ z : ℂ,
    z ∈ ((C.jacobian μ).map (algebraMap ℝ ℂ)).charpoly.roots ∧
    z.re = 0 ∧ z ≠ 0}

/-- The unstable spectral index along a continuation. -/
noncomputable def unstableIndex {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) (μ : ℝ) : ℕ :=
  Matrix.unstableMultiplicity (C.jacobian μ)

namespace SmoothEquilibriumContinuation

variable {I : Type} [DecidableEq I] [Fintype I]

/-- The initial unstable index is zero. -/
theorem unstableIndex_zero (C : SmoothEquilibriumContinuation I) :
    unstableIndex C 0 = 0 :=
  Matrix.unstableMultiplicity_eq_zero_of_hurwitz C.stableAtZero

/-- The final unstable index is positive. -/
theorem unstableIndex_one_pos (C : SmoothEquilibriumContinuation I) :
    0 < unstableIndex C 1 :=
  Matrix.unstableMultiplicity_pos_of_hasUnstableEigenvalue C.unstableAtOne

/-- Therefore the endpoint spectral index changes. -/
theorem unstableIndex_endpoints_ne (C : SmoothEquilibriumContinuation I) :
    unstableIndex C 0 ≠ unstableIndex C 1 := by
  rw [C.unstableIndex_zero]
  exact Nat.ne_of_lt C.unstableIndex_one_pos

/-- Some Hopf center lies in `[0,1]`. The spectral-boundary theorem gives an imaginary-axis
eigenvalue, and nonsingularity excludes zero. -/
theorem hopfCenterSet_inter_Icc_nonempty (C : SmoothEquilibriumContinuation I) :
    (hopfCenterSet C ∩ Set.Icc (0 : ℝ) 1).Nonempty := by
  haveI : Nonempty I := by
    by_contra h
    haveI : IsEmpty I := not_nonempty_iff.mp h
    obtain ⟨z, hz, _⟩ := C.unstableAtOne
    simp [Matrix.charpoly_isEmpty] at hz
  let μ := C.stabilityBoundary
  obtain ⟨z, hz, hzre⟩ :=
    Matrix.exists_imaginary_axis_eigenvalue_of_not_hurwitz_not_unstable
      (C.jacobian μ) inferInstance C.not_hurwitz_stabilityBoundary
      C.not_unstable_stabilityBoundary
  have hzne : z ≠ 0 := by
    intro hz0
    have hdetComplex : ((C.jacobian μ).map (algebraMap ℝ ℂ)).det = 0 := by
      rw [Matrix.det_eq_prod_roots_charpoly]
      exact Multiset.prod_eq_zero (by simpa [hz0] using hz)
    have hdet : (C.jacobian μ).det = 0 := by
      apply (FaithfulSMul.algebraMap_eq_zero_iff ℝ ℂ).mp
      rw [RingHom.map_det]
      exact hdetComplex
    exact C.nonsingular μ hdet
  exact ⟨μ, ⟨z, hz, hzre, hzne⟩, C.stabilityBoundary_mem⟩

end SmoothEquilibriumContinuation

/-- Finite-dimensional index package consumed by the analytic global-Hopf alternative. -/
structure GlobalHopfIndexData
    {I : Type} [DecidableEq I] [Fintype I]
    (C : AnalyticEquilibriumContinuation I) : Type where
  endpointChange : unstableIndex C.toSmoothEquilibriumContinuation 0 ≠
    unstableIndex C.toSmoothEquilibriumContinuation 1
  centersNonempty :
    (hopfCenterSet C.toSmoothEquilibriumContinuation ∩ Set.Icc (0 : ℝ) 1).Nonempty

/-- Every analytic continuation in the Fiedler setup has nonzero endpoint index change and a Hopf
center in the physical interval. -/
noncomputable def AnalyticEquilibriumContinuation.indexData
    {I : Type} [DecidableEq I] [Fintype I]
    (C : AnalyticEquilibriumContinuation I) : GlobalHopfIndexData C where
  endpointChange := C.toSmoothEquilibriumContinuation.unstableIndex_endpoints_ne
  centersNonempty := C.toSmoothEquilibriumContinuation.hopfCenterSet_inter_Icc_nonempty

/-- **Irreducible nonlinear Fiedler kernel.**

All finite-dimensional spectral work is removed from this proposition.  It is the analytic global
Hopf alternative itself: an analytic equilibrium branch with nonzero unstable-index change has a
nonstationary positive periodic solution on the branch interval. -/
def AnalyticGlobalHopfIndexTarget : Prop :=
  ∀ (I : Type) [DecidableEq I] [Fintype I]
    (C : AnalyticEquilibriumContinuation I)
    (_H : GlobalHopfIndexData C),
    Nonempty (PositiveContinuationPeriodicWitness C.toSmoothEquilibriumContinuation)

/-- The index-form global Hopf theorem implies the historical Fiedler interface. -/
theorem fiedlerAnalyticGlobalHopf_of_index
    (hIndex : AnalyticGlobalHopfIndexTarget) :
    FiedlerAnalyticGlobalHopfTarget := by
  intro I _ _ C
  exact hIndex I C C.indexData

end CRNT
