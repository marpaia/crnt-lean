import CRNT.Oscillation.PlanarNoCrossing
import CRNT.Oscillation.PlanarRecurrentSection
import CRNT.Oscillation.PlanarCanonicalReturn

/-!
# Ordered canonical returns in the planar Poincare--Bendixson proof

At this stage the global planar argument has already supplied a nonempty compact invariant minimal
set `M`, every point of `M` is recurrent, every point is non-equilibrium, the canonical transversal
through such a point is explicit, and autonomous uniqueness forbids flow-line crossings.

The remaining classical geometry is the ordering argument: choose a recurrent point `q`, use a
local flow box around the canonical transversal through `q`, and show that sufficiently late
returns induce a continuous self-map of a compact scalar interval.  Once that interval exists,
`ReturnInterval` supplies a fixed point and closes it to a genuine periodic orbit.

This file packages the *output* of that ordering argument in canonical coordinates and proves all
remaining conversions.  Thus a future proof of the local flow-box/ordering lemma has no CRN or
return-map bookkeeping left to do.
-/

namespace CRNT
namespace Planar

/-- Canonically coordinated return-strip data produced by the planar ordering argument. -/
structure CanonicalOrderedReturnData {field : Phase2 → Phase2}
    {D : FlowTrappingData field} (M : MinimalOmegaData D) where
  q : Phase2
  q_mem : q ∈ M.carrier
  xsection : TransversalSection (E := Phase2)
  field_eq : xsection.field = field
  section_point : xsection.point = q
  section_normal : xsection.normal = field q
  returnInterval : xsection.ReturnIntervalData
  /-- The return interval uses the explicit canonical scalar coordinate. -/
  point_eq_canonical : ∀ u,
    returnInterval.point u = canonicalSectionPoint field q u
  /-- Every certified section state lies in the chosen minimal invariant set. -/
  interval_in_minimal :
    ∀ u ∈ Set.Icc returnInterval.left returnInterval.right,
      returnInterval.point u ∈ M.carrier
  /-- Invariance is recorded in the real-time flow representation consumed by the periodic-orbit
  closure, avoiding any later conversion between the NNReal semiflow and complete trajectories. -/
  interval_flow_in_minimal :
    ∀ u ∈ Set.Icc returnInterval.left returnInterval.right, ∀ t : ℝ,
      xsection.flow (returnInterval.point u) t ∈ M.carrier
  /-- The canonical base point is actually in the compact scalar interval. -/
  base_mem : (0 : ℝ) ∈ Set.Icc returnInterval.left returnInterval.right

namespace CanonicalOrderedReturnData

variable {field : Phase2 → Phase2} {D : FlowTrappingData field}
  {M : MinimalOmegaData D}

/-- The interval base coordinate is definitionally the recurrent point `q`. -/
theorem point_zero (R : CanonicalOrderedReturnData M) :
    R.returnInterval.point 0 = R.q := by
  rw [R.point_eq_canonical]
  exact canonicalSectionPoint_zero field R.q

/-- Canonical ordering data already contains the stronger omega-return data used by the public
Poincare--Bendixson classification. -/
noncomputable def toOmegaRecurrentSectionData
    (R : CanonicalOrderedReturnData M) : OmegaRecurrentSectionData D where
  xsection := R.xsection
  field_eq := R.field_eq
  returnInterval := R.returnInterval
  point_in_omega := by
    intro u hu
    exact M.subset_omega (R.interval_in_minimal u hu)
  intervalFlowInOmega := by
    intro u hu t
    exact M.subset_omega (R.interval_flow_in_minimal u hu t)

/-- And, more strongly, it produces the minimal-set recurrent-section package. -/
noncomputable def toMinimalRecurrentSectionData
    (R : CanonicalOrderedReturnData M) : MinimalRecurrentSectionData M where
  toOmegaRecurrentSectionData := R.toOmegaRecurrentSectionData
  interval_in_minimal := R.interval_in_minimal

/-- It also produces the canonical wrapper used by the sharpened planar target. -/
noncomputable def toCanonicalMinimalRecurrentSectionData
    (R : CanonicalOrderedReturnData M) : CanonicalMinimalRecurrentSectionData M where
  toMinimalRecurrentSectionData := R.toMinimalRecurrentSectionData
  q := R.q
  q_mem := R.q_mem
  section_point := R.section_point
  section_normal := R.section_normal
  baseCoordinate := 0
  baseCoordinate_mem := R.base_mem
  point_baseCoordinate := R.point_zero

end CanonicalOrderedReturnData

/-- The irreducible local-flow-box/planar-ordering theorem.

Everything before this proposition (minimal-set recurrence, canonical section coordinates,
transversality and no-crossing) and everything after it (compact-interval fixed point and periodic
closure) is formalized in the repository. -/
def CanonicalReturnOrderingTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : FlowTrappingData field)
    (M : MinimalOmegaData D),
    ContDiff ℝ 1 field → Nonempty (CanonicalOrderedReturnData M)

/-- The ordered-return theorem closes the canonical recurrent-section target. -/
theorem canonicalMinimalReturn_of_ordering
    (horder : CanonicalReturnOrderingTarget) :
    CanonicalMinimalReturnTarget := by
  intro field D M hsmooth
  obtain ⟨R⟩ := horder field D M hsmooth
  exact ⟨R.toCanonicalMinimalRecurrentSectionData⟩

/-- Hence the same single local planar theorem yields the complete omega-limit
Poincare--Bendixson classification. -/
theorem poincareBendixsonOmegaClassification_of_ordering
    (horder : CanonicalReturnOrderingTarget) :
    PoincareBendixsonOmegaClassificationTarget :=
  poincareBendixsonOmegaClassification_of_canonical
    (canonicalMinimalReturn_of_ordering horder)

end Planar
end CRNT
