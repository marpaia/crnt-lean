import CRNT.Oscillation.DulacAreaSign
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Actual boundary line integral for Bendixson--Dulac

The earlier Green/Jordan certificates carried an abstract scalar `boundaryFlux`.  That is useful for
separating concerns, but the zero-flux part is not a frontier: along an exact ODE orbit the tangent
vector is the vector field itself, so the Dulac-scaled field has zero normal flux pointwise.

Here the boundary flux is the genuine time-parametrized line integral over one period.  It is proved
zero without any Jordan or Green theorem.  The remaining geometric work is therefore exactly:

1. construct the bounded Jordan interior of the simple periodic orbit;
2. prove Green's divergence identity relating this already-defined line integral to the area integral.
-/

namespace CRNT

namespace Planar

open MeasureTheory Set

/-- Oriented flux line integral of a planar field `G` around one displayed period of `P`. -/
noncomputable def periodBoundaryFlux
    {field : Phase2 → Phase2} (G : Phase2 → Phase2)
    (P : PeriodicTrajectory field) : ℝ :=
  ∫ t : ℝ in (0 : ℝ)..P.period,
    boundaryFluxDensity (G (P.orbit t)) (field (P.orbit t))

/-- The Dulac-scaled field has exactly zero boundary flux around every exact periodic trajectory. -/
theorem periodBoundaryFlux_dulac_zero
    {field : Phase2 → Phase2} (B : Phase2 → ℝ)
    (P : PeriodicTrajectory field) :
    periodBoundaryFlux (fun x => B x • field x) P = 0 := by
  unfold periodBoundaryFlux
  simp [Planar.PeriodicTrajectory.dulac_scaled_flux_density_zero]

/-- Jordan-domain data without Green's theorem.  This contains only the geometric/measure-theoretic
properties of the bounded interior and enough divergence regularity for the sign-integration lemma. -/
structure JordanDulacInteriorData
    {field : Phase2 → Phase2} (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field) where
  simple : P.SimpleClosedCycle
  inside : Set.range P.orbit ⊆ D.region
  interior : Set Phase2
  interior_nonempty : interior.Nonempty
  interior_open : IsOpen interior
  interior_connected : IsConnected interior
  interior_measurable : MeasurableSet interior
  /-- The interior is genuinely bounded, not merely of finite volume. -/
  bounded : Bornology.IsBounded interior
  /-- **The interior is the Jordan interior of this very orbit.**  Without this clause the
  field `interior` is unconstrained (any open connected subset of the region would do), and
  `GreenDivergencePeriodicJordanTarget` below is then false: its left-hand side depends only
  on `P` while its right-hand side would range over unrelated domains. -/
  boundary_eq : frontier interior = P.orbitSet
  interior_subset_region : interior ⊆ D.region
  divergence_continuous :
    ContinuousOn (divergence (fun x => D.dulac x • field x)) interior
  divergence_integrable :
    IntegrableOn (divergence (fun x => D.dulac x • field x)) interior

/-- **Pure Jordan-domain construction target.**  This contains no Green identity and no boundary
flux claim. -/
def JordanDulacInteriorConstructionTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field),
    P.SimpleClosedCycle → Set.range P.orbit ⊆ D.region →
      Nonempty (JordanDulacInteriorData D P)

/-- **Pure Green theorem target for a periodic Jordan boundary.**  The left side is the actual line
integral already defined above; the right side is the divergence area integral over the constructed
Jordan interior. -/
def GreenDivergencePeriodicJordanTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field) (J : JordanDulacInteriorData D P),
    ∃ σ : ℝ, σ ^ 2 = 1 ∧
      periodBoundaryFlux (fun x => D.dulac x • field x) P = σ *
        (∫ x : Phase2 in J.interior,
          divergence (fun y => D.dulac y • field y) x)

namespace JordanDulacInteriorData

variable {field : Phase2 → Phase2} {D : BendixsonDulacData field}
  {P : PeriodicTrajectory field}

/-- Boundedness gives finite volume, so the old `interior_finite` field is redundant. -/
theorem interior_finite (J : JordanDulacInteriorData D P) : volume J.interior ≠ ⊤ :=
  J.bounded.measure_lt_top.ne

/-- Jordan interior + Green's identity automatically assemble the stronger `DulacAreaData`; the
boundary-flux-zero field is no longer an assumption. -/
noncomputable def toDulacAreaData
    (J : JordanDulacInteriorData D P)
    (hGreen : GreenDivergencePeriodicJordanTarget) : DulacAreaData D P where
  simple := J.simple
  inside := J.inside
  interior := J.interior
  interior_nonempty := J.interior_nonempty
  interior_open := J.interior_open
  interior_connected := J.interior_connected
  interior_measurable := J.interior_measurable
  interior_finite := J.bounded.measure_lt_top.ne
  interior_subset_region := J.interior_subset_region
  divergence_continuous := J.divergence_continuous
  divergence_integrable := J.divergence_integrable
  boundaryFlux := periodBoundaryFlux (fun x => D.dulac x • field x) P
  boundaryFlux_zero := periodBoundaryFlux_dulac_zero D.dulac P
  orientation := Classical.choose (hGreen field D P J)
  orientation_sq := (Classical.choose_spec (hGreen field D P J)).1
  green := (Classical.choose_spec (hGreen field D P J)).2

/-- The two irreducible geometric theorems immediately give the Bendixson--Dulac contradiction. -/
theorem false_of_jordan_green
    (J : JordanDulacInteriorData D P)
    (hGreen : GreenDivergencePeriodicJordanTarget) : False :=
  (J.toDulacAreaData hGreen).false_of_areaData

end JordanDulacInteriorData

/-- Jordan construction plus Green's theorem closes the former area-construction target. -/
theorem dulacAreaConstruction_of_jordan_green
    (hJordan : JordanDulacInteriorConstructionTarget)
    (hGreen : GreenDivergencePeriodicJordanTarget) :
    DulacAreaConstructionTarget := by
  intro field D P hsimple hinside
  obtain ⟨J⟩ := hJordan field D P hsimple hinside
  exact ⟨J.toDulacAreaData hGreen⟩

/-- Jordan + Green close Bendixson--Dulac **given local Lipschitz continuity of the field**.

The extra hypothesis is not decoration. `BendixsonDulacTarget` assumes only `ContDiffOn ℝ 1 field
D.region`, i.e. C¹ *on the Dulac region*; the flow argument downstream needs `LocallyLipschitz
field` globally. An earlier version of this proof produced that from
`smooth_field.locallyLipschitzOn` via a `locallyLipschitz_of_forall_mem` step -- a lemma that does
not exist, and could not, since being locally Lipschitz on a subset says nothing off that subset.
Its own comment claimed to be "avoiding silently assuming global C1 outside the Dulac region",
which is exactly what it did.

Closing the gap to the unqualified `BendixsonDulacTarget` needs either a C¹-extension result off
the region or a restatement of the downstream flow lemmas in terms of `LocallyLipschitzOn`. Until
then the hypothesis is explicit. -/
theorem bendixsonDulacTarget_of_jordan_green_of_locallyLipschitz
    (hJordan : JordanDulacInteriorConstructionTarget)
    (hGreen : GreenDivergencePeriodicJordanTarget)
    (hlipAll : ∀ field : Phase2 → Phase2, LocallyLipschitz field) :
    BendixsonDulacTarget := by
  have harea := dulacAreaConstruction_of_jordan_green hJordan hGreen
  have hkernel := greenJordanSimpleCycleKernel_of_areaConstruction harea
  intro field D hopen hconv hfield hB P hinside
  let D' : BendixsonDulacData field :=
    { region := D.region
      dulac := D.dulac
      oneSign := D.oneSign
      open_region := hopen
      convex_region := hconv
      smooth_field := hfield
      smooth_dulac := hB }
  have hlip : LocallyLipschitz field := hlipAll field
  exact noPeriodicTrajectoryInRegion_of_simpleGreenJordanKernel
    hkernel D' hlip P hinside

end Planar
end CRNT
