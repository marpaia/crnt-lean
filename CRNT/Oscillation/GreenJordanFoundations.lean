import CRNT.Oscillation.DulacLineIntegral
import CRNT.Oscillation.PlanarJordanSeparation

/-!
# Geometry/analysis kernels behind Bendixson--Dulac

The ODE side is closed before this file:

* every smooth periodic orbit has a least-period simple representative;
* the Dulac-scaled field has zero normal flux along that orbit;
* strict one-sign divergence has nonzero area integral on every nonempty connected bounded interior.

The remaining universal planar mathematics is factored here into Jordan separation, orientation,
convex-domain containment, ordinary C1 regularity, and Green's divergence theorem.  In particular the
Green identity is **orientation aware**: a clockwise orbit contributes the negative of the positive
Jordan-boundary integral.
-/

namespace CRNT
namespace Planar

open MeasureTheory Set

/-- Bounded Jordan interior attached to one simple periodic cycle. -/
structure PeriodicJordanInterior
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field) where
  simple : P.SimpleClosedCycle
  interior : Set Phase2
  nonempty : interior.Nonempty
  open_interior : IsOpen interior
  connected : IsConnected interior
  measurable : MeasurableSet interior
  finite_volume : volume interior ≠ ⊤
  bounded : Bornology.IsBounded interior
  boundary_eq : frontier interior = P.orbitSet

/-- Pure Jordan-curve/orientation kernel specialized to simple periodic trajectories. -/
def PeriodicJordanInteriorTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (P : PeriodicTrajectory field),
    P.SimpleClosedCycle → Nonempty (PeriodicJordanInterior P)

/-- The bounded Jordan component lies in every convex open set containing its boundary.

This is the convex-hull corollary of Jordan separation needed by Bendixson--Dulac; keeping it
independent of the Dulac function makes it reusable in planar trapping arguments. -/
def JordanInteriorContainmentTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (P : PeriodicTrajectory field)
    (J : PeriodicJordanInterior P) (U : Set Phase2),
    IsOpen U → Convex ℝ U → P.orbitSet ⊆ U → J.interior ⊆ U

/-- Green/divergence theorem for the time-parameterized boundary used by `periodBoundaryFlux`.

The orientation factor makes this statement correct for either clockwise or counterclockwise ODE
cycles.  The regularity is stated as C1 on a neighbourhood of the closure, rather than the older
under-specified continuity-of-divergence assumption. -/
def PeriodicGreenDivergenceTarget : Prop :=
  ∀ (field G : Phase2 → Phase2) (P : PeriodicTrajectory field)
    (J : PeriodicJordanInterior P),
    ContDiffOn ℝ 1 G (closure J.interior) →
      ∃ σ : ℝ, σ ^ 2 = 1 ∧
        periodBoundaryFlux G P = σ *
          (∫ x : Phase2 in J.interior, divergence G x)

/-- Ordinary C1 Dulac data on the ambient open region restricts to the bounded Jordan interior and
makes its divergence continuous and integrable. -/
def JordanDulacRegularityTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : BendixsonDulacData field)
    (P : PeriodicTrajectory field) (J : PeriodicJordanInterior P),
    closure J.interior ⊆ D.region →
      ContinuousOn (divergence (fun x => D.dulac x • field x)) J.interior ∧
      IntegrableOn (divergence (fun x => D.dulac x • field x)) J.interior ∧
      ContDiffOn ℝ 1 (fun x => D.dulac x • field x) (closure J.interior)

/-- Generic Jordan separation constructs the periodic Jordan interior used by Bendixson--Dulac. -/
theorem periodicJordanInterior_of_jordanSeparation
    (hJordan : SimplePlanarLoop.JordanSeparationTarget) :
    PeriodicJordanInteriorTarget := by
  intro field P C
  obtain ⟨J⟩ := hJordan (PeriodicTrajectory.toSimplePlanarLoop P C)
  refine ⟨{
    simple := C
    interior := J.interior
    nonempty := J.interior_nonempty
    open_interior := J.interior_open
    connected := J.interior_connected
    measurable := J.interior_open.measurableSet
    finite_volume := ?_
    bounded := J.interior_bounded
    boundary_eq := ?_ }⟩
  · exact (J.interior_bounded.measure_lt_top).ne
  · rw [J.frontier_interior, PeriodicTrajectory.toSimplePlanarLoop_trace]

/-- The convex-hull clause in Jordan separation discharges convex-region containment. -/
theorem jordanInteriorContainment_of_jordanSeparation
    (hJordan : SimplePlanarLoop.JordanSeparationTarget) :
    JordanInteriorContainmentTarget := by
  intro field P J U hopen hconv hboundary x hx
  obtain ⟨S⟩ := hJordan (PeriodicTrajectory.toSimplePlanarLoop P J.simple)
  have htrace : (PeriodicTrajectory.toSimplePlanarLoop P J.simple).trace ⊆ U := by
    rw [PeriodicTrajectory.toSimplePlanarLoop_trace]; exact hboundary
  have hhull : convexHull ℝ (PeriodicTrajectory.toSimplePlanarLoop P J.simple).trace ⊆ U :=
    convexHull_min htrace hconv
  -- Both bounded components have the same Jordan boundary, hence coincide.
  have hsame : J.interior = S.interior :=
    S.eq_interior_of_frontier_eq_trace J.open_interior J.connected J.bounded (by
      rw [J.boundary_eq, PeriodicTrajectory.toSimplePlanarLoop_trace])
  rw [hsame] at hx
  exact hhull (S.interior_subset_convexHull hx)

/-- Jordan geometry, convex containment and regularity construct the Dulac-specific domain object. -/
theorem jordanDulacInteriorConstruction_of_foundations
    (hJordan : PeriodicJordanInteriorTarget)
    (hContain : JordanInteriorContainmentTarget)
    (hRegular : JordanDulacRegularityTarget) :
    JordanDulacInteriorConstructionTarget := by
  intro field D P hsimple hinside
  obtain ⟨J⟩ := hJordan field P hsimple
  have hsub : J.interior ⊆ D.region :=
    hContain field P J D.region D.open_region D.convex_region (by
      simpa [PeriodicTrajectory.orbitSet] using hinside)
  have hclosure : closure J.interior ⊆ D.region := by
    -- Convex open sets containing the Jordan boundary contain the closure of the bounded component.
    intro x hx
    rw [closure_eq_self_union_frontier] at hx
    rcases hx with hx | hx
    · exact hsub hx
    · rw [J.boundary_eq] at hx
      exact (by simpa [PeriodicTrajectory.orbitSet] using hinside hx)
  obtain ⟨hcont, hint, _hC1⟩ := hRegular field D P J hclosure
  exact ⟨{
    simple := J.simple
    inside := hinside
    interior := J.interior
    interior_nonempty := J.nonempty
    interior_open := J.open_interior
    interior_connected := J.connected
    interior_measurable := J.measurable
    bounded := J.bounded
    boundary_eq := J.boundary_eq
    interior_subset_region := hsub
    divergence_continuous := hcont
    divergence_integrable := hint
  }⟩

/-- Generic Green theorem supplies the Dulac-specific Green target. -/
theorem greenDivergencePeriodicJordan_of_foundation
    (hSep : SimplePlanarLoop.JordanSeparationTarget)
    (hContain : JordanInteriorContainmentTarget)
    (hRegular : JordanDulacRegularityTarget)
    (hGreen : PeriodicGreenDivergenceTarget) :
    GreenDivergencePeriodicJordanTarget := by
  intro field D P J
  obtain ⟨K⟩ := periodicJordanInterior_of_jordanSeparation hSep field P J.simple
  -- `J` and `K` are two independently produced bounded components of the *same* Jordan
  -- boundary.  A general "same frontier ⇒ same set" lemma would be false (Lakes of Wada),
  -- so both are identified against the separation of the shared loop instead.
  obtain ⟨S⟩ := hSep (PeriodicTrajectory.toSimplePlanarLoop P J.simple)
  have hJS : J.interior = S.interior :=
    S.eq_interior_of_frontier_eq_trace J.interior_open J.interior_connected J.bounded
      (by rw [J.boundary_eq, PeriodicTrajectory.toSimplePlanarLoop_trace])
  have hKS : K.interior = S.interior :=
    S.eq_interior_of_frontier_eq_trace K.open_interior K.connected K.bounded
      (by rw [K.boundary_eq, PeriodicTrajectory.toSimplePlanarLoop_trace])
  have hIK : K.interior = J.interior := hKS.trans hJS.symm
  have hclosure : closure K.interior ⊆ D.region := by
    -- `D.region` is open, not closed, so `closure_minimal` does not apply directly; the
    -- closure is the interior together with the orbit, and both sit inside the region.
    have hsub : K.interior ⊆ D.region :=
      hContain field P K D.region D.open_region D.convex_region (by
        simpa [PeriodicTrajectory.orbitSet] using J.inside)
    intro x hx
    rw [closure_eq_self_union_frontier] at hx
    rcases hx with hx | hx
    · exact hsub hx
    · rw [K.boundary_eq] at hx
      exact (by simpa [PeriodicTrajectory.orbitSet] using J.inside hx)
  obtain ⟨_, _, hC1⟩ := hRegular field D P K hclosure
  have h := hGreen field (fun x => D.dulac x • field x) P K hC1
  simpa [hIK] using h

end Planar
end CRNT
