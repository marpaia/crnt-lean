import CRNT.Oscillation.PlanarEndToEnd
import CRNT.Oscillation.GreenJordanReduction
import CRNT.Oscillation.PlanarReturnOrdering

/-!
# Compatibility adapters for the refined oscillation frontiers

The oscillation development was deliberately refined in stages.  Some early modules exposed broad
frontier propositions such as "construct a recurrent section" or "construct a Green/Jordan
certificate".  Later modules isolate strictly smaller mathematical kernels.

This file makes the refinement monotone for downstream users: proving the newer, sharper theorem
automatically supplies the older interface whenever the implication is sound.  No converse is
claimed and no theorem assumption is strengthened silently.
-/

namespace CRNT
namespace Planar

/-- Canonical return ordering gives the older minimal-set recurrent-section theorem. -/
theorem minimalSetRecurrentSection_of_ordering
    (horder : CanonicalReturnOrderingTarget) :
    MinimalSetRecurrentSectionTarget :=
  minimalSetRecurrentSection_of_canonical
    (canonicalMinimalReturn_of_ordering horder)

/-- Canonical return ordering also gives the omega-limit recurrent-section construction. -/
theorem omegaRecurrentSectionConstruction_of_ordering
    (horder : CanonicalReturnOrderingTarget) :
    OmegaRecurrentSectionConstructionTarget :=
  omegaRecurrentSection_of_minimalSet
    (minimalSetRecurrentSection_of_ordering horder)

/-- Forgetting the omega-containment strengthening recovers the original recurrent-section target. -/
theorem recurrentSectionConstruction_of_ordering
    (horder : CanonicalReturnOrderingTarget) :
    RecurrentSectionConstructionTarget := by
  intro field D hsmooth
  obtain ⟨R⟩ := omegaRecurrentSectionConstruction_of_ordering horder field D hsmooth
  exact ⟨R.toRecurrentSectionData⟩

/-- The modern Jordan/regularity/Green decomposition constructs the old analytic Dulac area data. -/
theorem dulacAreaConstruction_of_foundations
    (hJordan : PeriodicJordanInteriorTarget)
    (hSep : SimplePlanarLoop.JordanSeparationTarget)
    (hContain : JordanInteriorContainmentTarget)
    (hRegular : JordanDulacRegularityTarget)
    (hGreen : PeriodicGreenDivergenceTarget) :
    DulacAreaConstructionTarget :=
  dulacAreaConstruction_of_jordan_green
    (jordanDulacInteriorConstruction_of_foundations hJordan hContain hRegular)
    (greenDivergencePeriodicJordan_of_foundation hSep hContain hRegular hGreen)

/-- The same refined decomposition constructs the historical proof-relevant Green/Jordan
certificate for every already-simple cycle. -/
theorem greenJordanCertificateConstruction_of_foundations
    (hJordan : PeriodicJordanInteriorTarget)
    (hSep : SimplePlanarLoop.JordanSeparationTarget)
    (hContain : JordanInteriorContainmentTarget)
    (hRegular : JordanDulacRegularityTarget)
    (hGreen : PeriodicGreenDivergenceTarget) :
    GreenJordanCertificateConstructionTarget := by
  have harea : DulacAreaConstructionTarget :=
    dulacAreaConstruction_of_foundations hJordan hSep hContain hRegular hGreen
  intro field D P hsimple hinside
  obtain ⟨A⟩ := harea field D P hsimple hinside
  exact ⟨A.toGreenJordanCycleCertificate⟩

/-- Hence the refined foundations close the old simple-cycle Green/Jordan kernel too. -/
theorem greenJordanSimpleCycleKernel_of_foundations
    (hJordan : PeriodicJordanInteriorTarget)
    (hSep : SimplePlanarLoop.JordanSeparationTarget)
    (hContain : JordanInteriorContainmentTarget)
    (hRegular : JordanDulacRegularityTarget)
    (hGreen : PeriodicGreenDivergenceTarget) :
    GreenJordanSimpleCycleKernelTarget :=
  greenJordanSimpleCycleKernel_of_certificateConstruction
    (greenJordanCertificateConstruction_of_foundations
      hJordan hSep hContain hRegular hGreen)

end Planar
end CRNT
