-- `toSpanSingleton_isInvertible` lives here (as `CRNT.toSpanSingleton_isInvertible`); the
-- file previously referenced it through the unrelated `PlanarHopfData` namespace.
import CRNT.Dynamics.TransversalCrossingTime
import CRNT.Oscillation.FloquetReturnBridge
import CRNT.Oscillation.ReturnMapPersistence

/-!
# Floquet nondegeneracy as the return-map IFT condition

Banaji-style persistence of a periodic orbit is an implicit-function theorem on a Poincare section.
The relevant linear condition is not invertibility of the full autonomous monodromy displacement
(the autonomous multiplier `1` makes that singular), but invertibility of `DP-I` on the transverse
section.

For planar systems the section is one-dimensional.  This file formalizes the scalar algebra:
`P'(x0) != 1` is exactly the invertibility of the scalar derivative of `P-id`.  A concrete
Floquet/section calculation therefore only has to identify the nontrivial Floquet multiplier with
`P'(x0)`.
-/

namespace CRNT

open Filter Topology

/-- A `C¹` parameterized scalar return map near a reference periodic orbit. -/
structure ScalarParameterizedReturnMapData where
  returnMap : ℝ → ℝ → ℝ
  parameter : ℝ
  base : ℝ
  fixed : returnMap parameter base = base
  contDiffAt_displacement :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ => returnMap p.1 p.2 - p.2) (parameter, base)
  derivative : ℝ
  hasDerivAt_state : HasDerivAt (returnMap parameter) derivative base
  /-- Exact transverse Fréchet derivative of the displacement.  A concrete parameterized section
  proves this by differentiating the return map in its scalar section coordinate. -/
  stateDerivativeMap_eq :
    (fderiv ℝ (fun p : ℝ × ℝ => returnMap p.1 p.2 - p.2) (parameter, base) ∘L
      ContinuousLinearMap.inr ℝ ℝ ℝ)
      = ContinuousLinearMap.toSpanSingleton ℝ (derivative - 1)

namespace ScalarParameterizedReturnMapData

/-- The scalar derivative of the displacement `P-id`. -/
theorem hasDerivAt_displacement_state (D : ScalarParameterizedReturnMapData) :
    HasDerivAt (fun x => D.returnMap D.parameter x - x) (D.derivative - 1) D.base := by
  -- `HasDerivAt.sub` produces the function-subtraction form `P - id`; that is defeq to the
  -- pointwise form, so `exact` works where `simpa` reports an instance mismatch.
  exact D.hasDerivAt_state.sub (hasDerivAt_id D.base)

/-- If the return derivative is not one, the transverse displacement derivative is invertible. -/
theorem displacementDerivative_ne_zero (D : ScalarParameterizedReturnMapData)
    (hne : D.derivative ≠ 1) : D.derivative - 1 ≠ 0 :=
  sub_ne_zero.mpr hne

/-- Scalar return-map nondegeneracy supplies the generic IFT persistence package. -/
noncomputable def toReturnMapPersistenceData
    (D : ScalarParameterizedReturnMapData) (hne : D.derivative ≠ 1) :
    ReturnMapPersistenceData ℝ := by
  refine returnMapPersistenceDataOfDerivativeInvertible
    D.returnMap D.parameter D.base D.fixed D.contDiffAt_displacement ?_
  rw [D.stateDerivativeMap_eq]
  exact toSpanSingleton_isInvertible (D.displacementDerivative_ne_zero hne)

end ScalarParameterizedReturnMapData

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {κ : N.RateConstants}

/-- Planar Floquet nondegeneracy coupled to a scalar parameterized Poincare map.

The only Floquet-specific input retained here is the exact identification of the return derivative
with the nontrivial multiplier.  Everything after that is generic IFT machinery. -/
structure ScalarFloquetPersistenceBridge
    (P : N.NondegeneratePositivePeriodicOrbit κ) where
  returnData : ScalarParameterizedReturnMapData
  multiplier : ℂ
  hasMultiplier : P.floquet.HasMultiplier multiplier
  nontrivial : multiplier ≠ 1
  /-- For a real one-dimensional section the nontrivial multiplier is real and equals `P'`. -/
  multiplier_real : multiplier.im = 0
  derivative_eq : returnData.derivative = multiplier.re
  /-- Nondegeneracy on the section: the selected nontrivial multiplier is not `1`. -/
  derivative_ne_one : returnData.derivative ≠ 1

namespace ScalarFloquetPersistenceBridge

variable {P : N.NondegeneratePositivePeriodicOrbit κ}

/-- A scalar Floquet/return identification produces the exact IFT persistence data used by the
periodic-orbit inheritance layer. -/
noncomputable def persistenceData
    (B : N.ScalarFloquetPersistenceBridge P) : ReturnMapPersistenceData ℝ :=
  B.returnData.toReturnMapPersistenceData B.derivative_ne_one

end ScalarFloquetPersistenceBridge

end Network

end CRNT
