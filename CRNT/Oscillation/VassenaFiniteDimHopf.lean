import CRNT.Oscillation.VassenaContinuation
import CRNT.Dynamics.HopfGate3Matrix
import CRNT.Dynamics.HopfGate4

/-!
# Finite-dimensional local-Hopf certificates along Vassena continuations

The general diagonal-scaling continuation in `VassenaContinuation` ends at an arbitrary-dimensional
global-Hopf theorem.  In three and four dimensions the repository already has explicit
Routh--Hurwitz/Hopf boundary gates.  This module packages those gates directly on the continuation.

These are **local algebraic crossing certificates**.  They do not replace center-manifold,
transversality, and nonlinear Hopf realization data, but they avoid using the arbitrary-dimensional
global theorem whenever a concrete crossing parameter can be certified.
-/

namespace CRNT

open Matrix Polynomial Complex

namespace Network

/-- A certified cubic Routh--Hurwitz boundary point on a Vassena diagonal-scaling continuation. -/
structure FluxFin3HopfBoundaryWitness (N : Network (Fin 3))
    (W : N.FluxGlobalHopfData) where
  μ : ℝ
  realEigenvalue : ℂ
  pairEigenvalue : ℂ
  realEigenvalue_im : realEigenvalue.im = 0
  vieta2 :
    (-(N.massActionJacobian
      (W.toFluxJacobianStabilityTransition.continuationRates μ)
      (W.toFluxJacobianStabilityTransition.continuationState μ)).trace : ℂ)
      = -(realEigenvalue + pairEigenvalue + (starRingEnd ℂ) pairEigenvalue)
  vieta1 :
    ((N.massActionJacobian
      (W.toFluxJacobianStabilityTransition.continuationRates μ)
      (W.toFluxJacobianStabilityTransition.continuationState μ)).c₂Fin3 : ℂ)
      = realEigenvalue * pairEigenvalue
        + realEigenvalue * ((starRingEnd ℂ) pairEigenvalue)
        + pairEigenvalue * ((starRingEnd ℂ) pairEigenvalue)
  vieta0 :
    (-(N.massActionJacobian
      (W.toFluxJacobianStabilityTransition.continuationRates μ)
      (W.toFluxJacobianStabilityTransition.continuationState μ)).det : ℂ)
      = -(realEigenvalue * pairEigenvalue * ((starRingEnd ℂ) pairEigenvalue))
  trace_pos :
    0 < -(N.massActionJacobian
      (W.toFluxJacobianStabilityTransition.continuationRates μ)
      (W.toFluxJacobianStabilityTransition.continuationState μ)).trace
  det_pos :
    0 < -(N.massActionJacobian
      (W.toFluxJacobianStabilityTransition.continuationRates μ)
      (W.toFluxJacobianStabilityTransition.continuationState μ)).det
  boundary :
    (-(N.massActionJacobian
      (W.toFluxJacobianStabilityTransition.continuationRates μ)
      (W.toFluxJacobianStabilityTransition.continuationState μ)).det)
      = (-(N.massActionJacobian
          (W.toFluxJacobianStabilityTransition.continuationRates μ)
          (W.toFluxJacobianStabilityTransition.continuationState μ)).trace)
        * (N.massActionJacobian
          (W.toFluxJacobianStabilityTransition.continuationRates μ)
          (W.toFluxJacobianStabilityTransition.continuationState μ)).c₂Fin3

namespace FluxFin3HopfBoundaryWitness

variable {N : Network (Fin 3)} {W : N.FluxGlobalHopfData}

/-- The certified continuation boundary has a purely imaginary nonzero conjugate pair and a strictly
stable third eigenvalue. -/
theorem crossing (H : N.FluxFin3HopfBoundaryWitness W) :
    H.realEigenvalue.re < 0 ∧
      H.pairEigenvalue.re = 0 ∧ H.pairEigenvalue.im ≠ 0 ∧
      H.pairEigenvalue.im ^ 2 =
        (N.massActionJacobian
          (W.toFluxJacobianStabilityTransition.continuationRates H.μ)
          (W.toFluxJacobianStabilityTransition.continuationState H.μ)).c₂Fin3 := by
  exact massActionJacobian_fin_three_hopf_crossing N
    (W.toFluxJacobianStabilityTransition.continuationRates H.μ)
    (W.toFluxJacobianStabilityTransition.continuationState H.μ)
    H.realEigenvalue H.pairEigenvalue H.realEigenvalue_im
    H.vieta2 H.vieta1 H.vieta0 H.trace_pos H.det_pos H.boundary

/-- The crossing occurs at an actual positive steady state of the continuation. -/
theorem isSteady (H : N.FluxFin3HopfBoundaryWitness W) :
    N.IsMassActionSteadyState
      (W.toFluxJacobianStabilityTransition.continuationRates H.μ)
      (W.toFluxJacobianStabilityTransition.continuationState H.μ) :=
  W.toFluxJacobianStabilityTransition.continuation_isSteady H.μ

end FluxFin3HopfBoundaryWitness

/-- Quartic coefficient/eigenpair data at one continuation parameter.

The repository currently has a coefficient-level quartic Hopf gate rather than a matrix-level
`Fin 4` wrapper, so the characteristic-polynomial coefficient identification is carried explicitly
here. -/
structure FluxFin4HopfBoundaryWitness (N : Network (Fin 4))
    (W : N.FluxGlobalHopfData) where
  μ : ℝ
  z₁ : ℂ
  z₃ : ℂ
  a₃ : ℝ
  a₂ : ℝ
  a₁ : ℝ
  a₀ : ℝ
  vieta3 : (a₃ : ℂ) = -(z₁ + (starRingEnd ℂ) z₁ + z₃ + (starRingEnd ℂ) z₃)
  vieta2 : (a₂ : ℂ) = z₁ * (starRingEnd ℂ) z₁ + z₁ * z₃
      + z₁ * (starRingEnd ℂ) z₃ + (starRingEnd ℂ) z₁ * z₃
      + (starRingEnd ℂ) z₁ * (starRingEnd ℂ) z₃ + z₃ * (starRingEnd ℂ) z₃
  vieta1 : (a₁ : ℂ) = -(z₁ * (starRingEnd ℂ) z₁ * z₃
      + z₁ * (starRingEnd ℂ) z₁ * (starRingEnd ℂ) z₃
      + z₁ * z₃ * (starRingEnd ℂ) z₃
      + (starRingEnd ℂ) z₁ * z₃ * (starRingEnd ℂ) z₃)
  vieta0 : (a₀ : ℂ) = z₁ * (starRingEnd ℂ) z₁ * z₃ * (starRingEnd ℂ) z₃
  a₃_pos : 0 < a₃
  a₀_pos : 0 < a₀
  hurwitzBoundary : a₁ ^ 2 + a₃ ^ 2 * a₀ = a₃ * a₂ * a₁
  /-- The coefficient data are the characteristic coefficients of the continuation Jacobian.
  This explicit equality is what ties the coefficient-level quartic gate to the CRN. -/
  charpoly_eq :
    ((N.massActionJacobian
      (W.toFluxJacobianStabilityTransition.continuationRates μ)
      (W.toFluxJacobianStabilityTransition.continuationState μ)).map
        (algebraMap ℝ ℂ)).charpoly
      = X ^ 4 + C (a₃ : ℂ) * X ^ 3 + C (a₂ : ℂ) * X ^ 2
        + C (a₁ : ℂ) * X + C (a₀ : ℂ)

namespace FluxFin4HopfBoundaryWitness

variable {N : Network (Fin 4)} {W : N.FluxGlobalHopfData}

/-- The quartic boundary contains one nonzero purely imaginary conjugate pair while the other pair
remains strictly in the left half-plane. -/
theorem crossing (H : N.FluxFin4HopfBoundaryWitness W) :
    (H.z₁.re = 0 ∧ H.z₁.im ≠ 0 ∧ H.z₃.re < 0) ∨
      (H.z₃.re = 0 ∧ H.z₃.im ≠ 0 ∧ H.z₁.re < 0) :=
  hopf_crossing_gate_quartic H.z₁ H.z₃ H.a₃ H.a₂ H.a₁ H.a₀
    H.vieta3 H.vieta2 H.vieta1 H.vieta0
    H.a₃_pos H.a₀_pos H.hurwitzBoundary

/-- As in dimension three, the boundary point is an actual positive steady state. -/
theorem isSteady (H : N.FluxFin4HopfBoundaryWitness W) :
    N.IsMassActionSteadyState
      (W.toFluxJacobianStabilityTransition.continuationRates H.μ)
      (W.toFluxJacobianStabilityTransition.continuationState H.μ) :=
  W.toFluxJacobianStabilityTransition.continuation_isSteady H.μ

end FluxFin4HopfBoundaryWitness

end Network

end CRNT
