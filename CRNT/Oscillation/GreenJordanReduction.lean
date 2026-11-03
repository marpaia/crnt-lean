import CRNT.Oscillation.PlanarDulac
import CRNT.Oscillation.SimpleCycle

/-!
# Green/Jordan reduction for Bendixson--Dulac

`PlanarDulac` already proves the local differential identities and `SimpleCycle` proves that every
periodic orbit of a locally Lipschitz autonomous planar field has a least-period simple closed
representative.  The remaining classical argument is global planar integration: build the Jordan
interior of that simple cycle and apply Green's divergence theorem.

This module isolates that residue into a concrete certificate object and proves the contradiction
once such a certificate is available.  A future Jordan/Green implementation therefore only has to
construct the certificate; the CRN/Dulac logic does not have to be revisited.
-/

namespace CRNT

namespace Planar

/-- Integration data attached to one simple closed periodic orbit inside a Dulac region.

`boundaryFlux` and `divergenceArea` are deliberately scalar values rather than committing this layer
to one particular line/surface integration representation.  The eventual Green theorem fills these
values from actual integrals. -/
structure GreenJordanCycleCertificate
    {field : Phase2 → Phase2} (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field) where
  simple : P.SimpleClosedCycle
  inside : Set.range P.orbit ⊆ D.region
  /-- Boundary flux of `D.dulac • field` around one positively oriented traversal. -/
  boundaryFlux : ℝ
  /-- Area integral of `div(D.dulac • field)` over the Jordan interior. -/
  divergenceArea : ℝ
  /-- The tangency identity makes the boundary flux zero. -/
  boundaryFlux_zero : boundaryFlux = 0
  /-- Orientation of the displayed traversal relative to the positive Jordan boundary orientation.
  It is `+1` for counterclockwise and `-1` for clockwise traversal. -/
  orientation : ℝ
  orientation_sq : orientation ^ 2 = 1
  /-- Green's divergence theorem identifies boundary flux with the oriented area integral. -/
  green : boundaryFlux = orientation * divergenceArea
  /-- Strict one-sign divergence on a nonempty Jordan interior makes the area integral nonzero. -/
  divergenceArea_ne_zero : divergenceArea ≠ 0

namespace GreenJordanCycleCertificate

/-- A completed Green/Jordan certificate is contradictory. -/
theorem false_of_certificate
    {field : Phase2 → Phase2} {D : BendixsonDulacData field}
    {P : PeriodicTrajectory field}
    (C : GreenJordanCycleCertificate D P) : False := by
  apply C.divergenceArea_ne_zero
  have horient : C.orientation ≠ 0 := by
    intro h0
    have hsq := C.orientation_sq
    rw [h0, zero_pow (by norm_num)] at hsq
    norm_num at hsq
  have hmul : C.orientation * C.divergenceArea = 0 := by
    rw [← C.green, C.boundaryFlux_zero]
  exact (mul_eq_zero.mp hmul).resolve_left horient

end GreenJordanCycleCertificate

/-- Exact remaining Jordan/Green construction problem after all ODE uniqueness and Dulac calculus
have been discharged. -/
def GreenJordanCertificateConstructionTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field),
    P.SimpleClosedCycle → Set.range P.orbit ⊆ D.region →
      Nonempty (GreenJordanCycleCertificate D P)

/-- A certificate-construction theorem proves the simple-cycle Green/Jordan kernel. -/
theorem greenJordanSimpleCycleKernel_of_certificateConstruction
    (hconstruct : GreenJordanCertificateConstructionTarget) :
    GreenJordanSimpleCycleKernelTarget := by
  intro field D P hsimple hinside
  obtain ⟨C⟩ := hconstruct field D P hsimple hinside
  exact C.false_of_certificate

/-- Consequently the same construction theorem yields the full Bendixson--Dulac exclusion target
for locally Lipschitz fields.  `BendixsonDulacData.smooth_field` supplies local Lipschitz regularity
on the open region; callers that need a global field can use an extension/cutoff before invoking
this theorem. -/
def GreenJordanDulacConstructionTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field),
    Set.range P.orbit ⊆ D.region →
      Nonempty (GreenJordanCycleCertificate D P.leastPeriodRepresentative)

/-- The construction target directly supplies the older `GreenJordanDulacKernelTarget`. -/
theorem greenJordanDulacKernel_of_construction
    (hconstruct : GreenJordanDulacConstructionTarget) :
    GreenJordanDulacKernelTarget := by
  intro field D P hinside
  obtain ⟨C⟩ := hconstruct field D P hinside
  exact C.false_of_certificate

end Planar

end CRNT
