import CRNT.Oscillation.GreenJordanReduction
-- `Phase2 = EuclideanSpace ℝ (Fin 2)` has no measure structure without these two:
-- `…Lp.MeasurableSpace` transports the measurable/Borel structure across `WithLp`, and
-- `…Haar.OfBasis` supplies `measureSpaceOfInnerProductSpace` (hence `volume`).
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.MeanValue
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The sign-integration step in Bendixson--Dulac

The previous Green/Jordan reduction intentionally isolated the missing planar integration theorem,
but its smallest certificate still carried `divergenceArea_ne_zero` as input.  This file discharges
that part from ordinary measure/integration hypotheses.

On a connected measurable Jordan interior, continuity and integrability of the scaled divergence,
together with positive area, let the first mean-value theorem write the area integral as
`divergence(c) * area`.  The Dulac strict-one-sign hypothesis then makes that product nonzero.
Thus the remaining genuinely geometric theorem only has to construct the Jordan interior and prove
Green's boundary/area identity; it no longer has to separately assert the sign of the area integral.
-/

namespace CRNT

open MeasureTheory Set

namespace Planar

/-- Analytic data for the Jordan interior of a simple periodic orbit.

`oneIntegral_pos` is a proof-relevant positive-area statement written directly in the Bochner
integral language used by the mean-value theorem.  A future Jordan-domain construction can derive it
from openness/nonemptiness and finite volume without coupling this module to one particular area
representation. -/
structure DulacAreaData
    {field : Phase2 → Phase2} (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field) where
  simple : P.SimpleClosedCycle
  inside : Set.range P.orbit ⊆ D.region
  interior : Set Phase2
  interior_nonempty : interior.Nonempty
  interior_open : IsOpen interior
  interior_connected : IsConnected interior
  interior_measurable : MeasurableSet interior
  interior_finite : volume interior ≠ ⊤
  interior_subset_region : interior ⊆ D.region
  divergence_continuous :
    ContinuousOn (divergence (fun x => D.dulac x • field x)) interior
  divergence_integrable :
    IntegrableOn (divergence (fun x => D.dulac x • field x)) interior
  /-- The actual boundary flux around the simple periodic orbit. -/
  boundaryFlux : ℝ
  boundaryFlux_zero : boundaryFlux = 0
  /-- Orientation of the orbit traversal relative to the positive Jordan orientation. -/
  orientation : ℝ
  orientation_sq : orientation ^ 2 = 1
  /-- Green's divergence theorem on the Jordan interior, including boundary orientation. -/
  green : boundaryFlux = orientation *
    (∫ x : Phase2 in interior, divergence (fun y => D.dulac y • field y) x)

namespace DulacAreaData

variable {field : Phase2 → Phase2} {D : BendixsonDulacData field}
  {P : PeriodicTrajectory field}

/-- Strict one-sign divergence on positive area forces a nonzero area integral. -/
theorem divergenceIntegral_ne_zero (A : DulacAreaData D P) :
    (∫ x : Phase2 in A.interior,
      divergence (fun y => D.dulac y • field y) x) ≠ 0 := by
  let g : Phase2 → ℝ := divergence (fun y => D.dulac y • field y)
  have hprod : IntegrableOn (fun x : Phase2 => g x * (1 : ℝ)) A.interior := by
    simpa [g] using A.divergence_integrable
  have hone_int : IntegrableOn (fun _ : Phase2 => (1 : ℝ)) A.interior := by
    exact MeasureTheory.integrableOn_const A.interior_finite
  have hone_nonneg : ∀ᵐ x : Phase2 ∂(volume.restrict A.interior),
      0 ≤ (1 : ℝ) := by simp
  obtain ⟨c, hc, hmean⟩ :=
    exists_eq_const_mul_setIntegral_of_ae_nonneg
      A.interior_connected A.interior_measurable
      (by simpa [g] using A.divergence_continuous)
      hone_int hprod hone_nonneg
  have hmean' :
      (∫ x : Phase2 in A.interior, g x) =
        g c * (∫ _x : Phase2 in A.interior, (1 : ℝ)) := by
    simpa [g] using hmean
  have hvol_ne : volume.real A.interior ≠ 0 :=
    (MeasureTheory.measureReal_ne_zero_iff A.interior_finite).2
      (A.interior_open.measure_ne_zero volume A.interior_nonempty)
  have hvol_pos : 0 < volume.real A.interior :=
    lt_of_le_of_ne MeasureTheory.measureReal_nonneg (Ne.symm hvol_ne)
  have hone_pos : 0 < ∫ _x : Phase2 in A.interior, (1 : ℝ) := by
    change 0 < ∫ _x : Phase2, (1 : ℝ) ∂(volume.restrict A.interior)
    rw [MeasureTheory.integral_const]
    simpa using hvol_pos
  rw [hmean']
  have hc_region : c ∈ D.region := A.interior_subset_region hc
  rcases D.oneSign with hpos | hneg
  · exact mul_ne_zero (ne_of_gt (hpos c hc_region)) (ne_of_gt hone_pos)
  · exact mul_ne_zero (ne_of_lt (hneg c hc_region)) (ne_of_gt hone_pos)

/-- The analytic Jordan-area data are already contradictory: Green identifies the nonzero signed
area integral with the boundary flux, while tangency makes that flux zero. -/
theorem false_of_areaData (A : DulacAreaData D P) : False := by
  have horient : A.orientation ≠ 0 := by
    intro h0
    have hfld := A.orientation_sq
    rw [h0, zero_pow (by norm_num)] at hfld
    norm_num at hfld
  have hmul : A.orientation *
      (∫ x : Phase2 in A.interior, divergence (fun y => D.dulac y • field y) x) = 0 := by
    rw [← A.green, A.boundaryFlux_zero]
  exact A.divergenceIntegral_ne_zero ((mul_eq_zero.mp hmul).resolve_left horient)

/-- Forget the stronger analytic data to the older minimal Green/Jordan certificate. -/
noncomputable def toGreenJordanCycleCertificate (A : DulacAreaData D P) :
    GreenJordanCycleCertificate D P where
  simple := A.simple
  inside := A.inside
  boundaryFlux := A.boundaryFlux
  divergenceArea :=
    ∫ x : Phase2 in A.interior,
      divergence (fun y => D.dulac y • field y) x
  boundaryFlux_zero := A.boundaryFlux_zero
  orientation := A.orientation
  orientation_sq := A.orientation_sq
  green := A.green
  divergenceArea_ne_zero := A.divergenceIntegral_ne_zero

end DulacAreaData

/-- The reduced Jordan/Green construction target after the sign-integration argument has been
formalized.  The remaining theorem must construct the Jordan interior and prove Green's identity;
nonvanishing of the divergence integral follows automatically. -/
def DulacAreaConstructionTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field),
    P.SimpleClosedCycle → Set.range P.orbit ⊆ D.region →
      Nonempty (DulacAreaData D P)

/-- The reduced area construction theorem implies the simple-cycle Green/Jordan kernel. -/
theorem greenJordanSimpleCycleKernel_of_areaConstruction
    (harea : DulacAreaConstructionTarget) :
    GreenJordanSimpleCycleKernelTarget := by
  intro field D P hsimple hinside
  obtain ⟨A⟩ := harea field D P hsimple hinside
  exact A.false_of_areaData

end Planar

end CRNT
