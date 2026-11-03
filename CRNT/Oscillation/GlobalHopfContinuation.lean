import CRNT.Oscillation.VassenaContinuation

/-!
# Generic global-Hopf continuation interface

`VassenaContinuation` constructs a very specific smooth one-parameter mass-action family.  The
remaining Fiedler/Alexander--Yorke step is not CRN-specific: it is a global bifurcation theorem for a
smooth finite-dimensional ODE family with a smooth equilibrium branch, a stable endpoint, an
unstable endpoint, and no zero eigenvalue along the branch.

This module separates those layers.  The CRN continuation is converted to a generic continuation
record, and any positive periodic orbit returned by the generic global-Hopf theorem is converted
back into an actual positive mass-action periodic orbit with the corresponding continuation rate
constants.
-/

namespace CRNT

/-- Smooth finite-dimensional equilibrium continuation prepared for a global-Hopf theorem. -/
structure SmoothEquilibriumContinuation
    (I : Type) [DecidableEq I] [Fintype I] where
  field : ℝ → (I → ℝ) → (I → ℝ)
  equilibrium : ℝ → (I → ℝ)
  jacobian : ℝ → Matrix I I ℝ
  /-- Continuity of the Jacobian path along the equilibrium branch. -/
  jacobianContinuous : Continuous jacobian
  /-- The actual state derivative of the vector field along the equilibrium branch. -/
  linearization : ℝ → ((I → ℝ) →L[ℝ] (I → ℝ))
  /-- The operator and matrix presentations of the linearization agree pointwise. -/
  linearization_apply : ∀ μ v, linearization μ v = (jacobian μ).mulVec v
  fieldSmooth : ContDiff ℝ (⊤ : WithTop ℕ∞)
    (fun p : ℝ × (I → ℝ) => field p.1 p.2)
  equilibriumSmooth : ContDiff ℝ (⊤ : WithTop ℕ∞) equilibrium
  steady : ∀ μ, field μ (equilibrium μ) = 0
  /-- The continuation follows physically admissible positive equilibria throughout the parameter
  interval used by the CRN global-Hopf argument. -/
  equilibriumPositive : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ∀ i, 0 < equilibrium μ i
  /-- `jacobian μ` is not merely auxiliary spectral data: it is the Fréchet derivative of the
  actual ODE field at the corresponding equilibrium. -/
  hasFDerivAt_equilibrium : ∀ μ,
    HasFDerivAt (field μ) (linearization μ) (equilibrium μ)
  stableAtZero : Matrix.IsHurwitzReal (jacobian 0)
  unstableAtOne : Matrix.HasUnstableEigenvalue (jacobian 1)
  nonsingular : ∀ μ, (jacobian μ).det ≠ 0

/-- A nonconstant positive periodic trajectory somewhere on a continuation. -/
structure PositiveContinuationPeriodicWitness
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) : Type where
  parameter : ℝ
  parameter_mem : parameter ∈ Set.Icc (0 : ℝ) 1
  trajectory : PeriodicTrajectory (C.field parameter)
  positive : ∀ t i, 0 < trajectory.orbit t i

/-- Exact arbitrary-dimensional global-Hopf frontier.

All CRN realization, steady-state construction, smoothness, endpoint stability change, and exclusion
of zero eigenvalues have been removed.  A proof of this proposition is now purely a theorem of
finite-dimensional smooth dynamical systems/global bifurcation theory. -/
def GlobalHopfContinuationTarget : Prop :=
  ∀ (I : Type) [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I),
    Nonempty (PositiveContinuationPeriodicWitness C)

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

namespace FluxGlobalHopfData

variable {N : Network S}

/-- Forget the CRN-specific origin of a Vassena continuation and expose exactly the smooth ODE data
consumed by a generic global-Hopf theorem. -/
noncomputable def toSmoothEquilibriumContinuation
    (W : N.FluxGlobalHopfData) : SmoothEquilibriumContinuation S where
  field := W.toFluxJacobianStabilityTransition.continuationField
  equilibrium := W.toFluxJacobianStabilityTransition.continuationState
  jacobian := fun μ =>
    N.massActionJacobian
      (W.toFluxJacobianStabilityTransition.continuationRates μ)
      (W.toFluxJacobianStabilityTransition.continuationState μ)
  jacobianContinuous := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have hdiag : Continuous fun μ : ℝ =>
        W.toFluxJacobianStabilityTransition.continuationDiagonal μ j :=
      (exponentialDiagonalPath_contDiff_apply (n := 0) j).continuous
    have hrw : (fun μ : ℝ =>
        N.massActionJacobian
          (W.toFluxJacobianStabilityTransition.continuationRates μ)
          (W.toFluxJacobianStabilityTransition.continuationState μ) i j) =
        (fun μ =>
          (N.fluxJacobianCore W.toFluxJacobianStabilityTransition.flux *
            Matrix.diagonal (W.toFluxJacobianStabilityTransition.continuationDiagonal μ)) i j) := by
      funext μ
      rw [W.toFluxJacobianStabilityTransition.continuation_jacobian]
    rw [hrw]
    simp only [Matrix.mul_diagonal]
    exact continuous_const.mul hdiag
  linearization := fun μ =>
    N.massActionJacobianCLM
      (W.toFluxJacobianStabilityTransition.continuationRates μ)
      (W.toFluxJacobianStabilityTransition.continuationState μ)
  linearization_apply := by
    intro μ v
    exact N.massActionJacobianCLM_apply
      (W.toFluxJacobianStabilityTransition.continuationRates μ)
      (W.toFluxJacobianStabilityTransition.continuationState μ) v
  fieldSmooth := W.continuationPackage.fieldSmooth
  equilibriumSmooth := W.continuationPackage.equilibriumSmooth
  steady := W.continuationPackage.steady
  equilibriumPositive := by
    intro μ hμ i
    exact exponentialDiagonalState_positive
      W.toFluxJacobianStabilityTransition.transition.stablePositive μ i
  hasFDerivAt_equilibrium := by
    intro μ
    have hfield : W.toFluxJacobianStabilityTransition.continuationField μ
        = fun x => N.massActionVectorField
            (W.toFluxJacobianStabilityTransition.continuationRates μ) x := by
      funext x
      exact W.toFluxJacobianStabilityTransition.continuationField_eq_massAction μ x
    rw [hfield]
    exact N.massActionVectorField_hasFDerivAt
      (W.toFluxJacobianStabilityTransition.continuationRates μ)
      (W.toFluxJacobianStabilityTransition.continuationState μ)
  stableAtZero := W.continuationPackage.stableAtZero
  unstableAtOne := W.continuationPackage.unstableAtOne
  nonsingular := W.continuationPackage.nonsingular

/-- Convert a positive periodic trajectory of the generic continuation back to a genuine positive
mass-action periodic orbit at that parameter. -/
noncomputable def positivePeriodicOrbitOfContinuationWitness
    (W : N.FluxGlobalHopfData)
    (P : PositiveContinuationPeriodicWitness W.toSmoothEquilibriumContinuation) :
    N.PositivePeriodicOrbit
      (W.toFluxJacobianStabilityTransition.continuationRates P.parameter) := by
  let κ := W.toFluxJacobianStabilityTransition.continuationRates P.parameter
  have hfield : W.toSmoothEquilibriumContinuation.field P.parameter
      = N.massActionVectorField κ := by
    funext x
    exact W.toFluxJacobianStabilityTransition.continuationField_eq_massAction P.parameter x
  let Q : PeriodicTrajectory (N.massActionVectorField κ) :=
    P.trajectory.congrField hfield
  exact
    { orbit := Q.orbit
      period := Q.period
      period_pos := Q.period_pos
      positive := by
        intro t i
        exact P.positive t i
      solution := fun t s => (hasDerivAt_pi.mp (Q.solution t)) s
      periodic := Q.periodic
      nonconstant := Q.nonconstant }

/-- The generic global-Hopf theorem immediately yields mass-action oscillatory capacity for the
Vassena continuation. -/
theorem oscillatoryCapacity_of_globalHopfContinuation
    (hHopf : GlobalHopfContinuationTarget)
    (W : N.FluxGlobalHopfData) : N.OscillatoryCapacity := by
  obtain ⟨P⟩ := hHopf S W.toSmoothEquilibriumContinuation
  exact ⟨W.toFluxJacobianStabilityTransition.continuationRates P.parameter,
    ⟨W.positivePeriodicOrbitOfContinuationWitness P⟩⟩

end FluxGlobalHopfData

end Network


/-- The generic smooth-continuation theorem is strictly stronger than the CRN-specific diagonal-
scaling target previously exposed by `VassenaContinuation`.  This adapter lets the older Vassena
API consume the generic theorem without duplicating any CRN realization argument. -/
theorem diagonalScalingGlobalHopfTarget_of_globalHopfContinuation
    (hHopf : GlobalHopfContinuationTarget) :
    Network.DiagonalScalingGlobalHopfTarget := by
  intro T _ _ N hW
  obtain ⟨W⟩ := hW
  exact Network.FluxGlobalHopfData.oscillatoryCapacity_of_globalHopfContinuation hHopf W

end CRNT
