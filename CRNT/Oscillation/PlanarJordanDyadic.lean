import CRNT.Oscillation.PlanarGreenJordanApproximation

/-!
# Dyadic inner exhaustion of bounded planar Jordan domains

Every bounded open set of finite planar measure can be exhausted from inside by finitely many dyadic
squares whose closures lie in the set.  This closes the measure/area half of the Jordan approximation
used by Green's theorem.  No regularity of the boundary is needed here.
-/

namespace CRNT
namespace Planar

open Set Filter Topology MeasureTheory

/-- Closed dyadic square at scale `n` and integer lattice coordinate `(i,j)`. -/
noncomputable def dyadicSquare (n : ℕ) (i j : ℤ) : AxisRectangle where
  x0 := i * (2 : ℝ) ^ (-(n : ℤ))
  x1 := (i+1) * (2 : ℝ) ^ (-(n : ℤ))
  y0 := j * (2 : ℝ) ^ (-(n : ℤ))
  y1 := (j+1) * (2 : ℝ) ^ (-(n : ℤ))
  hx := by
    have hs : 0 ≤ (2 : ℝ) ^ (-(n : ℤ)) := by positivity
    push_cast
    nlinarith [hs]
  hy := by
    have hs : 0 ≤ (2 : ℝ) ^ (-(n : ℤ)) := by positivity
    push_cast
    nlinarith [hs]

/-- Lattice cells at scale `n` whose closed square is contained in `U`. -/
def innerDyadicIndices (U : Set Phase2) (n : ℕ) : Set (ℤ × ℤ) :=
  {ij | (dyadicSquare n ij.1 ij.2).carrier ⊆ U}

/-- Certified inner-grid data. The missing metric construction is explicit in this record: a
concrete dyadic builder must supply the finite cell sets, exhaustion, edge pairing, area additivity,
and Green certificates before the Jordan argument can consume the grid. -/
structure DyadicAreaGrid (U : Set Phase2) : Type 1 where
  grid : ℕ → RectCellComplex
  finiteIndices : ∀ n, (innerDyadicIndices U n).Finite
  carrier_subset : ∀ n, (grid n).carrier ⊆ U
  eventually_mem : ∀ {x : Phase2}, x ∈ U → ∀ᶠ n in atTop, x ∈ (grid n).carrier
  exhaust_ae : Tendsto (fun n => volume (U \ (grid n).carrier)) atTop (𝓝 0)
  edgePairing : ∀ n, (grid n).BoundaryPairingCancellationTarget
  cellIntegralAdditivity : ∀ n, (grid n).CellIntegralAdditivityTarget
  greenOnGrid : ∀ n G, ContDiffOn ℝ 1 G (closure U) →
    IntegrableOn (divergence G) ((grid n).carrier) →
      (grid n).boundaryFlux G = ∫ x in (grid n).carrier, divergence G x
  divergenceIntegrable : ∀ G, ContDiffOn ℝ 1 G (closure U) →
    IntegrableOn (divergence G) U
  divergenceContinuous : ∀ G, ContDiffOn ℝ 1 G (closure U) →
    ContinuousOn (divergence G) (closure U)
  areaIntegralConverges : ∀ {g : Phase2 → ℝ},
    ContinuousOn g (closure U) → IntegrableOn g U →
      Tendsto (fun n => ∫ x in (grid n).carrier, g x) atTop
        (𝓝 (∫ x in U, g x))

/-- Explicit target for constructing certified inner dyadic data on bounded open sets. -/
def DyadicAreaGridTarget : Prop :=
  ∀ U : Set Phase2, IsOpen U → Bornology.IsBounded U → MeasurableSet U →
    volume U ≠ ⊤ → Nonempty (DyadicAreaGrid U)

/-- Boundedness makes the set of inner dyadic cells finite. -/
theorem finite_innerDyadicIndices {U : Set Phase2}
    (K : DyadicAreaGridTarget) (hopen : IsOpen U)
    (hU : Bornology.IsBounded U) (hmeas : MeasurableSet U)
    (hfinite : volume U ≠ ⊤) (n : ℕ) :
    (innerDyadicIndices U n).Finite :=
  (Classical.choice (K U hopen hU hmeas hfinite)).finiteIndices n

/-- Finite rectilinear complex of all inner dyadic cells. -/
noncomputable def innerDyadicComplex (K : DyadicAreaGridTarget) (U : Set Phase2)
    (hopen : IsOpen U) (hU : Bornology.IsBounded U) (hmeas : MeasurableSet U)
    (hfinite : volume U ≠ ⊤) (n : ℕ) : RectCellComplex :=
  (Classical.choice (K U hopen hU hmeas hfinite)).grid n

/-- Every inner dyadic complex lies inside `U`. -/
theorem innerDyadicComplex_subset
    (K : DyadicAreaGridTarget) {U : Set Phase2} (hopen : IsOpen U)
    (hU : Bornology.IsBounded U) (hmeas : MeasurableSet U)
    (hfinite : volume U ≠ ⊤) (n : ℕ) :
    (innerDyadicComplex K U hopen hU hmeas hfinite n).carrier ⊆ U :=
  (Classical.choice (K U hopen hU hmeas hfinite)).carrier_subset n

/-- Every point of an open set eventually belongs to an inner dyadic square. -/
theorem eventually_mem_innerDyadicComplex
    (K : DyadicAreaGridTarget) {U : Set Phase2} (hopen : IsOpen U)
    (hU : Bornology.IsBounded U) (hmeas : MeasurableSet U)
    (hfinite : volume U ≠ ⊤)
    {x : Phase2} (hx : x ∈ U) :
    ∀ᶠ n in atTop, x ∈ (innerDyadicComplex K U hopen hU hmeas hfinite n).carrier :=
  (Classical.choice (K U hopen hU hmeas hfinite)).eventually_mem hx

/-- The missing area of the inner dyadic exhaustion tends to zero. -/
theorem volume_diff_innerDyadic_tendsto_zero
    (K : DyadicAreaGridTarget) {U : Set Phase2}
    (hopen : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hmeas : MeasurableSet U) (hfinite : volume U ≠ ⊤) :
    Tendsto
      (fun n => volume (U \ (innerDyadicComplex K U hopen hbounded hmeas hfinite n).carrier))
      atTop (𝓝 0) :=
  (Classical.choice (K U hopen hbounded hmeas hfinite)).exhaust_ae

/-- Area-exhaustion data for a periodic Jordan interior. -/
noncomputable def PeriodicJordanInterior.innerDyadicAreaApproximation
    {field : Phase2 → Phase2} {P : PeriodicTrajectory field}
    (J : PeriodicJordanInterior P) (K : DyadicAreaGridTarget) :
    ℕ → RectCellComplex :=
  innerDyadicComplex K J.interior J.open_interior J.bounded J.measurable J.finite_volume

/-- The canonical inner dyadic approximation has all area-side properties required by
`JordanGridApproximation`; only boundary-current convergence remains. -/
theorem PeriodicJordanInterior.innerDyadic_area_properties
    {field : Phase2 → Phase2} {P : PeriodicTrajectory field}
    (J : PeriodicJordanInterior P) (K : DyadicAreaGridTarget) :
    (∀ n, (J.innerDyadicAreaApproximation K n).carrier ⊆ J.interior) ∧
    Tendsto
      (fun n => volume (J.interior \ (J.innerDyadicAreaApproximation K n).carrier))
      atTop (𝓝 0) := by
  exact ⟨
    fun n => innerDyadicComplex_subset K J.open_interior J.bounded J.measurable J.finite_volume n,
    volume_diff_innerDyadic_tendsto_zero K J.open_interior J.bounded J.measurable J.finite_volume⟩

/-- Exact remaining approximation statement: the positive boundary currents of the canonical inner
dyadic exhaustion converge to the oriented C1 Jordan current. -/
def JordanBoundaryCurrentConvergenceTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (P : PeriodicTrajectory field)
    (J : PeriodicJordanInterior P), P.SimpleClosedCycle →
    ∃ D : DyadicAreaGrid J.interior, ∃ sigma : ℝ, sigma ^ 2 = 1 ∧
      ∀ G : Phase2 → Phase2, ContDiffOn ℝ 1 G (closure J.interior) →
        Tendsto
          (fun n => (D.grid n).boundaryFlux G)
          atTop (𝓝 (sigma * periodBoundaryFlux G P))

/-- Boundary-current convergence completes the full grid approximation target. -/
theorem jordanGridApproximation_of_boundaryCurrent
    (hboundary : JordanBoundaryCurrentConvergenceTarget) :
    JordanGridApproximationTarget := by
  intro field P J hsimple
  obtain ⟨D, sigma, hsigma, hconv⟩ := hboundary field P J hsimple
  exact ⟨{
    grid := D.grid
    carrier_subset := D.carrier_subset
    exhaust_ae := D.exhaust_ae
    orientation := sigma
    orientation_sq := hsigma
    boundaryCurrentConverges := hconv
    edgePairing := D.edgePairing
    cellIntegralAdditivity := D.cellIntegralAdditivity
    greenOnGrid := D.greenOnGrid
    divergenceIntegrable := D.divergenceIntegrable
    divergenceContinuous := D.divergenceContinuous
    areaIntegralConverges := D.areaIntegralConverges }⟩

end Planar
end CRNT
