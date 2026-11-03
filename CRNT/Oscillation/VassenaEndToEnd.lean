import CRNT.Oscillation.VassenaAnalyticity
import CRNT.Oscillation.VassenaCriteria

/-!
# End-to-end Vassena 2025 mass-action criteria

All CRN realization work for the two full-matrix criteria is already present elsewhere:

* a positive stationary reaction flux realizes `B(v) D` at a positive steady state for every
  positive diagonal `D`;
* Criterion I supplies a Hurwitz endpoint and, through the finite `P^-_0` theorem, an unstable
  positive diagonal endpoint;
* Criterion II supplies an unstable endpoint and, through Fisher--Fuller diagonal stabilization,
  a Hurwitz positive diagonal endpoint;
* the exponential diagonal interpolation is positive, analytic, steady, and has Jacobian exactly
  `B(v) D(mu)` throughout;
* invertibility of `B(v)` rules out zero eigenvalues on the complete continuation;
* `VassenaAnalyticity` closes the CRN-specific analyticity requirement.

This file composes those pieces.  Consequently the full-matrix Vassena criteria depend only on the
two finite matrix theorems and the analytic Fiedler/global-Hopf theorem itself.  No separate CRN
realization target remains for this route.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

namespace FluxCriterionIWitness

variable {N : Network S}

/-- Criterion I canonically supplies all CRN data needed by the analytic global-Hopf theorem. -/
noncomputable def globalHopfData
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    (w : FluxCriterionIWitness N) : N.FluxGlobalHopfData where
  toFluxJacobianStabilityTransition := w.stabilityTransition hP0
  coreInvertible := w.criterion.stable.det_ne_zero

/-- End-to-end Criterion-I oscillatory capacity. -/
theorem oscillatoryCapacity_of_fiedler
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    (hFiedler : FiedlerAnalyticGlobalHopfTarget)
    (w : FluxCriterionIWitness N) : N.OscillatoryCapacity :=
  (w.globalHopfData hP0).oscillatoryCapacity_of_fiedler_closed hFiedler

end FluxCriterionIWitness

namespace FluxCriterionIIWitness

variable {N : Network S}

/-- Criterion II likewise supplies a complete analytic global-Hopf continuation.  Fisher--Fuller
membership already includes nonsingularity of the full core matrix. -/
noncomputable def globalHopfData
    (hFF : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (w : FluxCriterionIIWitness N) : N.FluxGlobalHopfData where
  toFluxJacobianStabilityTransition := w.stabilityTransition hFF
  coreInvertible := w.criterion.fisherFuller.det_ne_zero

/-- End-to-end Criterion-II oscillatory capacity. -/
theorem oscillatoryCapacity_of_fiedler
    (hFF : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (hFiedler : FiedlerAnalyticGlobalHopfTarget)
    (w : FluxCriterionIIWitness N) : N.OscillatoryCapacity :=
  (w.globalHopfData hFF).oscillatoryCapacity_of_fiedler_closed hFiedler

end FluxCriterionIIWitness

/-- The two full-matrix Vassena criteria now assemble into the public realization theorem.  The
remaining dependencies are purely finite matrix theory plus the analytic global-Hopf theorem. -/
theorem vassenaFluxCriteriaRealization_of_fiedler
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    (hFF : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (hFiedler : FiedlerAnalyticGlobalHopfTarget) :
    VassenaFluxCriteriaRealizationTarget := by
  intro T _ _ N h
  rcases h with hI | hII
  · obtain ⟨w⟩ := hI
    exact w.oscillatoryCapacity_of_fiedler hP0 hFiedler
  · obtain ⟨w⟩ := hII
    exact w.oscillatoryCapacity_of_fiedler hFF hFiedler

end Network

end CRNT
