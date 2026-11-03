import CRNT.Oscillation.GlobalHopfContinuation
import Mathlib.Analysis.Analytic.Basic

/-!
# Analytic global-Hopf interface used by the Vassena criteria

The published nonlinear step behind the 2025 mass-action criteria is an analytic global-Hopf
continuation theorem (in the form quoted from Fiedler): an analytic one-parameter vector field with
a branch of equilibria, nonsingular Jacobian along the branch, and a net change of stability admits
nonstationary periodic solutions.

`GlobalHopfContinuation` already contains all of the differential, equilibrium, positivity,
linearization, endpoint-stability, and nonsingularity data.  This file adds the missing analyticity
hypothesis explicitly, so the literature theorem is never represented as a theorem about an
arbitrary smooth family.
-/

namespace CRNT

/-- A `SmoothEquilibriumContinuation` whose joint parameter/state vector field is real analytic on
all of parameter-state space.  This is the regularity assumption appearing in the Fiedler theorem
used by the mass-action criteria. -/
structure AnalyticEquilibriumContinuation
    (I : Type) [DecidableEq I] [Fintype I]
    extends SmoothEquilibriumContinuation I where
  fieldAnalytic : AnalyticOnNhd ℝ
    (fun p : ℝ × (I → ℝ) => field p.1 p.2) Set.univ

/-- The exact analytic global-Hopf theorem target used by the CRN continuation layer.

The endpoint hypotheses in the underlying smooth record are deliberately the stronger
"Hurwitz-stable at zero / strictly unstable at one" form produced by the Vassena criteria; this is
a concrete net change of stability.  Nonsingularity rules out zero-eigenvalue crossings.  The
periodic witness is required to lie in the positive orthant and at a parameter in `[0,1]`, matching
the physical CRN application rather than an unconstrained polynomial ODE on all of `R^n`. -/
def FiedlerAnalyticGlobalHopfTarget : Prop :=
  ∀ (I : Type) [DecidableEq I] [Fintype I]
    (C : AnalyticEquilibriumContinuation I),
    Nonempty (PositiveContinuationPeriodicWitness C.toSmoothEquilibriumContinuation)

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Remaining CRN-specific regularity lemma for the Vassena continuation: its proof-erased joint
mass-action family is analytic in parameter and state.  The field is built from exponentials,
reciprocals of positive exponential monomials, finite products, and finite sums, so this is an
analytic-calculus statement rather than a dynamical assumption. -/
def FluxGlobalHopfAnalyticityTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T]
    (N : Network T) (W : N.FluxGlobalHopfData),
    AnalyticOnNhd ℝ
      (fun p : ℝ × (T → ℝ) =>
        W.toFluxJacobianStabilityTransition.continuationField p.1 p.2)
      Set.univ

namespace FluxGlobalHopfData

variable {N : Network S}

/-- Upgrade the already-closed smooth Vassena continuation to the exact analytic continuation
consumed by Fiedler's global-Hopf theorem. -/
noncomputable def toAnalyticEquilibriumContinuation
    (hAnalytic : FluxGlobalHopfAnalyticityTarget)
    (W : N.FluxGlobalHopfData) : AnalyticEquilibriumContinuation S where
  toSmoothEquilibriumContinuation := W.toSmoothEquilibriumContinuation
  fieldAnalytic := hAnalytic N W

/-- Once the analytic-calculus lemma and Fiedler theorem are available, the Vassena continuation
produces ordinary mass-action oscillatory capacity with no additional matrix or CRN realization
work. -/
theorem oscillatoryCapacity_of_fiedler
    (hAnalytic : FluxGlobalHopfAnalyticityTarget)
    (hFiedler : FiedlerAnalyticGlobalHopfTarget)
    (W : N.FluxGlobalHopfData) : N.OscillatoryCapacity := by
  let C := W.toAnalyticEquilibriumContinuation hAnalytic
  obtain ⟨P⟩ := hFiedler S C
  exact ⟨W.toFluxJacobianStabilityTransition.continuationRates P.parameter,
    ⟨W.positivePeriodicOrbitOfContinuationWitness P⟩⟩

end FluxGlobalHopfData

end Network

end CRNT
