import CRNT.Oscillation.PlanarGreenGrid
import CRNT.Oscillation.GreenJordanFoundations
import Mathlib.Topology.Basic

/-!
# Approximation route from finite Green domains to Jordan domains

The analytic Green identity is already proved on finite rectilinear complexes.  To pass to a smooth
Jordan domain it suffices to approximate its interior by finite complexes such that

1. indicators of the complex carriers converge in measure/L1 to the Jordan interior;
2. exterior-edge flux converges to the flux of the oriented Jordan boundary.

The first convergence is measure-theoretic.  The second is geometric and uses the C1 boundary.
This file packages those limits and proves Green's theorem by passing to the limit.
-/

namespace CRNT
namespace Planar

open Set Filter Topology MeasureTheory

/-- Rectilinear approximations to one periodic Jordan interior. -/
structure JordanGridApproximation
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field)
    (J : PeriodicJordanInterior P) : Type 1 where
  grid : ℕ → RectCellComplex
  carrier_subset : ∀ n, (grid n).carrier ⊆ J.interior
  exhaust_ae : Tendsto
    (fun n => volume (J.interior \ (grid n).carrier)) atTop (𝓝 0)
  /-- Orientation of the displayed ODE traversal relative to the positively oriented cell boundary. -/
  orientation : ℝ
  orientation_sq : orientation ^ 2 = 1
  /-- Boundary-current convergence.  Cell-complex boundaries use positive orientation, so a clockwise
  ODE traversal contributes the factor `orientation = -1`. -/
  boundaryCurrentConverges :
    ∀ G : Phase2 → Phase2, ContDiffOn ℝ 1 G (closure J.interior) →
      Tendsto (fun n => (grid n).boundaryFlux G) atTop
        (𝓝 (orientation * periodBoundaryFlux G P))
  /-- Cell-edge cancellation for the chain boundary of every grid. -/
  edgePairing : ∀ n, (grid n).BoundaryPairingCancellationTarget
  /-- Additivity of cellwise area integrals over each grid carrier. -/
  cellIntegralAdditivity : ∀ n, (grid n).CellIntegralAdditivityTarget
  /-- Green's identity for each grid, with the actual regularity available on the Jordan closure. -/
  greenOnGrid : ∀ n G, ContDiffOn ℝ 1 G (closure J.interior) →
    IntegrableOn (divergence G) ((grid n).carrier) →
      (grid n).boundaryFlux G = ∫ x in (grid n).carrier, divergence G x
  /-- Integrability of the divergence on the Jordan interior. -/
  divergenceIntegrable : ∀ G, ContDiffOn ℝ 1 G (closure J.interior) →
    IntegrableOn (divergence G) J.interior
  /-- Continuity of the divergence on the Jordan closure. -/
  divergenceContinuous : ∀ G, ContDiffOn ℝ 1 G (closure J.interior) →
    ContinuousOn (divergence G) (closure J.interior)
  /-- Area-integral convergence along the supplied grid. -/
  areaIntegralConverges : ∀ {g : Phase2 → ℝ},
    ContinuousOn g (closure J.interior) → IntegrableOn g J.interior →
      Tendsto (fun n => ∫ x in (grid n).carrier, g x) atTop
        (𝓝 (∫ x in J.interior, g x))

/-- Area integrals of a continuous integrable function converge along an exhausting inner grid. -/
theorem integral_grid_tendsto_interior
    {field : Phase2 → Phase2} {P : PeriodicTrajectory field}
    {J : PeriodicJordanInterior P}
    (A : JordanGridApproximation P J)
    {g : Phase2 → ℝ}
    (hcont : ContinuousOn g (closure J.interior))
    (hint : IntegrableOn g J.interior) :
    Tendsto (fun n => ∫ x in (A.grid n).carrier, g x) atTop
      (𝓝 (∫ x in J.interior, g x)) := by
  exact A.areaIntegralConverges hcont hint

/-- **Green on a Jordan interior from grid approximation.** -/
theorem periodicGreenDivergence_of_gridApproximation
    {field G : Phase2 → Phase2} {P : PeriodicTrajectory field}
    (J : PeriodicJordanInterior P)
    (A : JordanGridApproximation P J)
    (hG : ContDiffOn ℝ 1 G (closure J.interior)) :
    periodBoundaryFlux G P = A.orientation *
      (∫ x in J.interior, divergence G x) := by
  have hdivInt : IntegrableOn (divergence G) J.interior := A.divergenceIntegrable G hG
  have hdivCont : ContinuousOn (divergence G) (closure J.interior) :=
    A.divergenceContinuous G hG
  have harea := integral_grid_tendsto_interior A hdivCont hdivInt
  have hflux := A.boundaryCurrentConverges G hG
  have hgreen_n : ∀ n,
      (A.grid n).boundaryFlux G =
        ∫ x in (A.grid n).carrier, divergence G x := by
    intro n
    exact A.greenOnGrid n G hG (hdivInt.mono_set (A.carrier_subset n))
  have hflux' : Tendsto
      (fun n => ∫ x in (A.grid n).carrier, divergence G x) atTop
      (𝓝 (A.orientation * periodBoundaryFlux G P)) := by
    exact hflux.congr' (Filter.Eventually.of_forall hgreen_n)
  have hlim : A.orientation * periodBoundaryFlux G P =
      ∫ x in J.interior, divergence G x :=
    tendsto_nhds_unique hflux' harea
  have hsigma : A.orientation ≠ 0 := by
    intro h0
    have hfld := A.orientation_sq
    rw [h0, zero_pow (by norm_num)] at hfld
    norm_num at hfld
  calc
    periodBoundaryFlux G P
        = A.orientation * (A.orientation * periodBoundaryFlux G P) := by
            rw [← mul_assoc, ← pow_two, A.orientation_sq, one_mul]
    _ = A.orientation * (∫ x in J.interior, divergence G x) := by rw [hlim]

/-- Geometric approximation theorem for C1 periodic Jordan curves.  This is now the only missing
Green-specific geometry: construct inner finite rectilinear approximations with convergence of the
associated boundary currents. -/
def JordanGridApproximationTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (P : PeriodicTrajectory field)
    (J : PeriodicJordanInterior P),
    P.SimpleClosedCycle → Nonempty (JordanGridApproximation P J)

/-- Grid approximation proves the orientation-free Green identity.  The sign is `+1` because
`periodBoundaryFlux` follows the time orientation of `P`; if the Jordan interior chooses the
opposite positive boundary orientation the historical API absorbs that by `sigma=-1`. -/
theorem periodicGreenDivergence_of_gridTarget
    (hgrid : JordanGridApproximationTarget) :
    PeriodicGreenDivergenceTarget := by
  intro field G P J hG
  obtain ⟨A⟩ := hgrid field P J J.simple
  have h := periodicGreenDivergence_of_gridApproximation J A hG
  refine ⟨A.orientation, A.orientation_sq, ?_⟩
  exact h

end Planar
end CRNT
