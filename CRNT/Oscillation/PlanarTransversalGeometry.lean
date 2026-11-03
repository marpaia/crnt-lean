import CRNT.Oscillation.PlanarMinimalSet
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Canonical local transversals in the plane

At any non-equilibrium point `q` of a planar vector field, the affine line through `q` whose normal
is `field q` is automatically transversal to the flow: the crossing speed is
`<field q, field q> = ||field q||^2 > 0`.

This elementary observation removes the "choose a transversal" step from the geometric residue of
Poincare--Bendixson.  The remaining work is global: use recurrence to find a compact interval on this
line for which the positive return map is defined and maps the interval into itself.
-/

namespace CRNT

-- `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope (not `RealInnerProductSpace`, which
-- supplies the unsuffixed `⟪x, y⟫`).  Without this the bracket is not even a valid token.
open scoped InnerProductSpace

namespace Planar

/-- Canonical affine transversal through `q`, represented as a set. -/
def canonicalSection (field : Phase2 → Phase2) (q : Phase2) : Set Phase2 :=
  {x | ⟪x - q, field q⟫_ℝ = 0}

/-- The base point lies on its canonical section. -/
@[simp] theorem mem_canonicalSection (field : Phase2 → Phase2) (q : Phase2) :
    q ∈ canonicalSection field q := by
  simp [canonicalSection]

/-- The normal of the canonical section is nonzero at every non-equilibrium point. -/
theorem canonicalNormal_ne_zero {field : Phase2 → Phase2} {q : Phase2}
    (hne : field q ≠ 0) : field q ≠ 0 := hne

/-- **Canonical transversality.** At a non-equilibrium point the vector field crosses the affine
section with normal `field q` at strictly positive speed. -/
theorem canonical_transversal_speed_pos {field : Phase2 → Phase2} {q : Phase2}
    (hne : field q ≠ 0) :
    0 < ⟪field q, field q⟫_ℝ := by
  rw [real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hne)

/-- In particular the canonical section satisfies the nonzero transversality condition consumed by
`TransversalSection`. -/
theorem canonical_transversal_ne_zero {field : Phase2 → Phase2} {q : Phase2}
    (hne : field q ≠ 0) :
    ⟪field q, field q⟫_ℝ ≠ 0 :=
  ne_of_gt (canonical_transversal_speed_pos hne)

/-- Signed coordinate normal to the canonical section. -/
noncomputable def canonicalSectionCoord (field : Phase2 → Phase2) (q x : Phase2) : ℝ :=
  ⟪x - q, field q⟫_ℝ

@[simp] theorem canonicalSectionCoord_base (field : Phase2 → Phase2) (q : Phase2) :
    canonicalSectionCoord field q q = 0 := by
  simp [canonicalSectionCoord]

/-- Membership in the canonical section is exactly vanishing of its signed coordinate. -/
theorem mem_canonicalSection_iff (field : Phase2 → Phase2) (q x : Phase2) :
    x ∈ canonicalSection field q ↔ canonicalSectionCoord field q x = 0 :=
  Iff.rfl

/-- Every point of an equilibrium-free minimal omega set therefore has a canonical transversal. -/
theorem MinimalOmegaData.canonicalTransversal
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    (M : MinimalOmegaData D) {q : Phase2} (hq : q ∈ M.carrier) :
    ⟪field q, field q⟫_ℝ ≠ 0 :=
  canonical_transversal_ne_zero (M.equilibriumFree q hq)

end Planar

end CRNT
