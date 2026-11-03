import CRNT.Oscillation.PlanarFlowBox

/-!
# Canonical planar flow-box regularity obligation

The inverse-function-theorem layer is complete in `PlanarFlowBox.lean`.  The derivative of the
supplied trajectory family with respect to its initial point is still an explicit ODE obligation:
the repository's variational estimate gives directional derivatives, but does not yet prove the
Fréchet remainder needed by the flow-box map.  This file keeps that boundary explicit and provides
the adapter from a certified strict derivative to the flow-box regularity record.
-/

namespace CRNT
namespace Planar

/-- A certified strict derivative is exactly the local flow-box regularity data consumed by the
inverse-function argument. -/
theorem canonicalFlowBoxRegularity_of_strictDerivative
    {field : Phase2 → Phase2} (D : FlowTrappingData field) (q : Phase2)
    (h : HasStrictFDerivAt (canonicalFlowBoxMap D q)
      ((canonicalFlowBoxLinear field q).toContinuousLinearMap) 0) :
    Nonempty (CanonicalFlowBoxRegularity D q) :=
  ⟨⟨h⟩⟩

end Planar
end CRNT
