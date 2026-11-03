import CRNT.Oscillation.FloquetPersistenceBridge
import CRNT.Oscillation.ReturnMap

/-!
# Scalar-section persistence to genuine periodic trajectories

For a planar autonomous system the Poincare section is one-dimensional.  The generic
`ReturnMapPersistenceData ℝ` from `FloquetPersistenceBridge` therefore contains the exact IFT branch
of scalar section coordinates.  This file reconnects that scalar branch to an ambient
`TransversalSection` family and closes each nearby scalar fixed point into an actual periodic orbit.

This is the section-coordinate analogue of `ReturnMapFamilyPersistence`, which works directly in the
ambient phase space.
-/

namespace CRNT

open Filter Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A family of ambient Poincare sections coordinated by the scalar return map used by the IFT. -/
structure ScalarPersistentReturnOrbitData (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  persistence : ReturnMapPersistenceData ℝ
  xsection : ℝ → TransversalSection (E := E)
  /-- Embed a scalar section coordinate into the actual section at parameter `μ`. -/
  point : ℝ → ℝ → E
  /-- Scalar return and ambient return agree under the embedding. -/
  returnMap_eq : ∀ μ u,
    (xsection μ).returnMap (point μ u) = point μ (persistence.returnMap μ u)
  /-- Semigroup law along points on the implicit branch. -/
  eventually_semigroup :
    ∀ᶠ μ in 𝓝 persistence.parameter, ∀ a b : ℝ,
      (xsection μ).flow (point μ (persistence.fixedPointBranch μ)) (a + b) =
        (xsection μ).flow
          ((xsection μ).flow (point μ (persistence.fixedPointBranch μ)) a) b
  /-- Flow starts at the embedded branch point. -/
  eventually_flow_zero :
    ∀ᶠ μ in 𝓝 persistence.parameter,
      (xsection μ).flow (point μ (persistence.fixedPointBranch μ)) 0 =
        point μ (persistence.fixedPointBranch μ)
  /-- Returns remain positive-time returns. -/
  eventually_crossing_pos :
    ∀ᶠ μ in 𝓝 persistence.parameter,
      0 < (xsection μ).crossingTime (point μ (persistence.fixedPointBranch μ))
  /-- The branch stays away from equilibria. -/
  eventually_field_ne_zero :
    ∀ᶠ μ in 𝓝 persistence.parameter,
      (xsection μ).field (point μ (persistence.fixedPointBranch μ)) ≠ 0

namespace ScalarPersistentReturnOrbitData

/-- The IFT scalar branch is an ambient Poincare fixed-point branch after embedding. -/
theorem eventually_ambient_fixedPoint (D : ScalarPersistentReturnOrbitData E) :
    ∀ᶠ μ in 𝓝 D.persistence.parameter,
      (D.xsection μ).returnMap (D.point μ (D.persistence.fixedPointBranch μ)) =
        D.point μ (D.persistence.fixedPointBranch μ) := by
  filter_upwards [D.persistence.eventually_fixedPointBranch] with μ hμ
  rw [D.returnMap_eq, hμ]

/-- Every sufficiently nearby parameter has a genuine nonconstant periodic trajectory of the
ambient vector field. -/
theorem eventually_periodicTrajectory
    (D : ScalarPersistentReturnOrbitData E) :
    ∀ᶠ μ in 𝓝 D.persistence.parameter,
      Nonempty (PeriodicTrajectory (D.xsection μ).field) := by
  filter_upwards [D.eventually_ambient_fixedPoint, D.eventually_semigroup,
    D.eventually_flow_zero, D.eventually_crossing_pos, D.eventually_field_ne_zero]
    with μ hfix hsemi hzero hpos hfield
  exact ⟨(D.xsection μ).periodicTrajectoryOfReturnMapFixedPoint
    hsemi hzero hfix hpos hfield⟩

/-- Stronger witness form retaining the exact ambient branch orbit. -/
structure BranchTrajectory (D : ScalarPersistentReturnOrbitData E) (μ : ℝ) where
  trajectory : PeriodicTrajectory (D.xsection μ).field
  orbit_eq : trajectory.orbit =
    (D.xsection μ).flow (D.point μ (D.persistence.fixedPointBranch μ))

/-- Produce the chosen branch trajectory with its exact flow representation. -/
theorem eventually_branchTrajectory
    (D : ScalarPersistentReturnOrbitData E) :
    ∀ᶠ μ in 𝓝 D.persistence.parameter, Nonempty (D.BranchTrajectory μ) := by
  filter_upwards [D.eventually_ambient_fixedPoint, D.eventually_semigroup,
    D.eventually_flow_zero, D.eventually_crossing_pos, D.eventually_field_ne_zero]
    with μ hfix hsemi hzero hpos hfield
  let P := (D.xsection μ).periodicTrajectoryOfReturnMapFixedPoint
    hsemi hzero hfix hpos hfield
  exact ⟨⟨P, rfl⟩⟩

end ScalarPersistentReturnOrbitData

end CRNT
