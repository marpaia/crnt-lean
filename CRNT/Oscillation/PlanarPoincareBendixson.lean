import CRNT.Oscillation.PlanarJordanCrossingOrder

/-!
# Direct Poincare--Bendixson closure from local return ordering

This module replaces the earlier over-strong return-interval formulation.  A minimal compact
invariant omega-set need not contain a whole affine section interval.  The correct classical proof
shows instead that its recurrent point must itself be periodic.
-/

namespace CRNT
namespace Planar

/-- Universal inputs needed by the direct minimal-set proof. -/
structure PoincareBendixsonKernelBundle : Prop where
  flowRegularity : CanonicalFlowRegularityTarget
  jordanSeparation : SimplePlanarLoop.JordanSeparationTarget
  straightEdgeLocalSide : StraightEdgeJordanSideTarget

namespace PoincareBendixsonKernelBundle

/-- Complete local return-ordering theorem. -/
theorem returnOrdering (K : PoincareBendixsonKernelBundle) :
    JordanLocalReturnOrderingTarget :=
  jordanReturnOrdering_of_localSide
    K.jordanSeparation K.straightEdgeLocalSide K.flowRegularity

/-- Every equilibrium-free minimal omega subset contains a periodic orbit. -/
theorem minimalPeriodicOrbit (K : PoincareBendixsonKernelBundle) :
    MinimalPeriodicOrbitTarget :=
  minimalPeriodicOrbit_of_ordering K.returnOrdering K.flowRegularity

/-- Full omega-limit Poincare--Bendixson classification used by rank-two CRNs. -/
theorem omegaClassification (K : PoincareBendixsonKernelBundle) :
    PoincareBendixsonOmegaClassificationTarget :=
  poincareBendixsonOmegaClassification_of_minimalPeriodic K.minimalPeriodicOrbit

end PoincareBendixsonKernelBundle

end Planar
end CRNT
