import CRNT.Oscillation.PlanarPoincareBendixson
import CRNT.Oscillation.PlanarGreenJordanApproximation
import CRNT.Oscillation.PlanarDivergenceRegularity

/-!
# End-to-end planar global-dynamics adapters

The Poincare--Bendixson path now uses the mathematically correct minimal-set endpoint: a recurrent
point itself becomes periodic.  It no longer requires an affine return interval to lie inside the
minimal omega-set.

The Bendixson--Dulac path uses the actual boundary line integral, internal C1/divergence regularity,
finite-domain Green identities, and a Jordan-domain approximation theorem.
-/

namespace CRNT
namespace Planar

/-- Universal planar kernels sufficient for both global planar routes. -/
structure PlanarGlobalKernelBundle : Prop where
  flowRegularity : CanonicalFlowRegularityTarget
  jordanSeparation : SimplePlanarLoop.JordanSeparationTarget
  straightEdgeLocalSide : StraightEdgeJordanSideTarget
  jordanGridApproximation : JordanGridApproximationTarget

namespace PlanarGlobalKernelBundle

/-- Poincare--Bendixson inputs. -/
def poincareBendixsonBundle (K : PlanarGlobalKernelBundle) :
    PoincareBendixsonKernelBundle where
  flowRegularity := K.flowRegularity
  jordanSeparation := K.jordanSeparation
  straightEdgeLocalSide := K.straightEdgeLocalSide

/-- Complete Poincare--Bendixson omega-limit classification. -/
theorem poincareBendixsonOmegaClassification
    (K : PlanarGlobalKernelBundle) :
    PoincareBendixsonOmegaClassificationTarget :=
  K.poincareBendixsonBundle.omegaClassification

/-- Jordan separation constructs the bounded periodic interior. -/
theorem jordanInterior (K : PlanarGlobalKernelBundle) :
    PeriodicJordanInteriorTarget :=
  periodicJordanInterior_of_jordanSeparation K.jordanSeparation

/-- Convex containment is already a corollary of the Jordan separation record. -/
theorem jordanContainment (K : PlanarGlobalKernelBundle) :
    JordanInteriorContainmentTarget :=
  jordanInteriorContainment_of_jordanSeparation K.jordanSeparation

/-- Divergence regularity is internal. -/
theorem dulacRegularity (_K : PlanarGlobalKernelBundle) :
    JordanDulacRegularityTarget :=
  jordanDulacRegularity_proved

/-- Green's theorem on the periodic Jordan domain follows from the finite-domain theorem plus the
Jordan grid approximation. -/
theorem greenDivergence (K : PlanarGlobalKernelBundle) :
    PeriodicGreenDivergenceTarget :=
  periodicGreenDivergence_of_gridTarget K.jordanGridApproximation

/-- Dulac-specific Jordan construction. -/
theorem jordanDulacInteriorConstruction
    (K : PlanarGlobalKernelBundle) :
    JordanDulacInteriorConstructionTarget :=
  jordanDulacInteriorConstruction_of_foundations
    K.jordanInterior K.jordanContainment K.dulacRegularity

/-- Public Bendixson--Dulac exclusion target, given local Lipschitz continuity.

The Lipschitz hypothesis is now explicit: see
`bendixsonDulacTarget_of_jordan_green_of_locallyLipschitz` in
`CRNT/Oscillation/DulacLineIntegral.lean` for why it cannot be derived from the C¹-on-the-region
assumption that `BendixsonDulacTarget` carries. -/
theorem bendixsonDulac
    (K : PlanarGlobalKernelBundle)
    (hlipAll : ∀ field : Phase2 → Phase2, LocallyLipschitz field) :
    BendixsonDulacTarget :=
  bendixsonDulacTarget_of_jordan_green_of_locallyLipschitz
    K.jordanDulacInteriorConstruction
    (greenDivergencePeriodicJordan_of_foundation
      K.jordanSeparation K.jordanContainment K.dulacRegularity K.greenDivergence)
    hlipAll

end PlanarGlobalKernelBundle

end Planar
end CRNT
