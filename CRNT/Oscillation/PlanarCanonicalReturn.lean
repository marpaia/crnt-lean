import CRNT.Oscillation.PlanarMinimalSet
import CRNT.Oscillation.PlanarTransversalGeometry

/-!
# Canonical recurrent return sections for Poincare--Bendixson

`PlanarMinimalSet` reduces the planar existence theorem to constructing a recurrent transversal
interval in a minimal compact invariant omega set.  `PlanarTransversalGeometry` removes another
choice: at any point `q` of that set, the affine section through `q` with normal `field q` is
canonical and automatically transversal.

This file records the sharpened remaining target.  A proof no longer gets to choose an arbitrary
section: it must construct the return interval on the canonical section through a recurrent point.
Everything after that construction is already closed by the return-interval fixed-point theorem.
-/

namespace CRNT

-- `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope; without this open the bracket is
-- not a valid token.
open scoped InnerProductSpace


namespace Planar

/-- Minimal-set return data whose Poincare section is the canonical affine transversal through a
chosen recurrent point `q`. -/
structure CanonicalMinimalRecurrentSectionData {field : Phase2 → Phase2}
    {D : FlowTrappingData field} (M : MinimalOmegaData D)
    extends MinimalRecurrentSectionData M where
  q : Phase2
  q_mem : q ∈ M.carrier
  section_point : toMinimalRecurrentSectionData.xsection.point = q
  section_normal : toMinimalRecurrentSectionData.xsection.normal = field q
  /-- The certified scalar interval actually contains the canonical base point. -/
  baseCoordinate : ℝ
  baseCoordinate_mem :
    baseCoordinate ∈ Set.Icc
      toMinimalRecurrentSectionData.returnInterval.left
      toMinimalRecurrentSectionData.returnInterval.right
  point_baseCoordinate :
    toMinimalRecurrentSectionData.returnInterval.point baseCoordinate = q

namespace CanonicalMinimalRecurrentSectionData

variable {field : Phase2 → Phase2} {D : FlowTrappingData field}
    {M : MinimalOmegaData D}

/-- The section carried by canonical recurrent data is genuinely transversal at its canonical
minimal-set point. -/
theorem transversal_at_q (R : CanonicalMinimalRecurrentSectionData M) :
    ⟪field R.q, field R.q⟫_ℝ ≠ 0 :=
  M.canonicalTransversal R.q_mem

/-- Forgetting canonicality recovers exactly the minimal recurrent-section data already consumed by
the Poincare--Bendixson closure theorem. -/
def forget (R : CanonicalMinimalRecurrentSectionData M) : MinimalRecurrentSectionData M :=
  R.toMinimalRecurrentSectionData

end CanonicalMinimalRecurrentSectionData

/-- Sharpened geometric residue of Poincare--Bendixson.

For an equilibrium-free minimal compact invariant set of a `C¹` planar flow, construct a compact
self-return interval on the canonical transversal through some recurrent point of that set.  The
recurrence, canonical transversality, scalar fixed-point theorem, and periodic-orbit closure are all
already formalized elsewhere. -/
def CanonicalMinimalReturnTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : FlowTrappingData field)
    (M : MinimalOmegaData D),
    ContDiff ℝ 1 field → Nonempty (CanonicalMinimalRecurrentSectionData M)

/-- The canonical target implies the previously exposed minimal recurrent-section target. -/
theorem minimalSetRecurrentSection_of_canonical
    (hcanon : CanonicalMinimalReturnTarget) :
    MinimalSetRecurrentSectionTarget := by
  intro field D M hsmooth
  obtain ⟨R⟩ := hcanon field D M hsmooth
  exact ⟨R.forget⟩

/-- Therefore a proof of the canonical return-interval theorem closes the complete omega-limit
Poincare--Bendixson classification used by the CRN oscillation layer. -/
theorem poincareBendixsonOmegaClassification_of_canonical
    (hcanon : CanonicalMinimalReturnTarget) :
    PoincareBendixsonOmegaClassificationTarget :=
  poincareBendixsonOmegaClassification_of_minimalSet
    (minimalSetRecurrentSection_of_canonical hcanon)

end Planar

end CRNT
