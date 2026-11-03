import CRNT.Oscillation.ReturnMapPersistence
import CRNT.Oscillation.ReturnMap

/-!
# From implicit persistence of return-map fixed points to persistent periodic trajectories

`ReturnMapPersistence` proves the finite-dimensional implicit-function step: a `C¹` parameterized
return map with invertible transverse derivative has a nearby branch of fixed points.  This file
closes the next logical step.  If those parameterized maps are genuine Poincare return maps and the
usual flow/positive-return/non-equilibrium facts hold along the implicit branch, then every nearby
parameter carries an exact nonconstant periodic trajectory.

This is deliberately generic in the phase space.  A Banaji-style CRN inheritance theorem can now
focus on constructing the parameterized transversal sections and proving the return-map regularity;
the IFT-to-periodic-orbit glue is no longer part of that frontier.
-/

namespace CRNT

open Filter Topology
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A parameterized family of genuine transversal return maps whose fixed-point branch is supplied
by `ReturnMapPersistenceData`.

The eventual hypotheses are intentionally stated only along the implicit branch.  This is the
minimal information needed to close the branch into periodic trajectories; no global flow theorem
is hidden in the structure. -/
structure PersistentReturnOrbitData (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  persistence : ReturnMapPersistenceData E
  xsection : ℝ → TransversalSection (E := E)
  /-- The finite-dimensional map used by the IFT is the Poincare map of the supplied section. -/
  returnMap_eq : ∀ μ x, persistence.returnMap μ x = (xsection μ).returnMap x
  /-- Autonomy/uniqueness gives the semigroup law along the persisting branch. -/
  eventually_semigroup :
    ∀ᶠ μ in 𝓝 persistence.parameter, ∀ a b : ℝ,
      (xsection μ).flow (persistence.fixedPointBranch μ) (a + b) =
        (xsection μ).flow
          ((xsection μ).flow (persistence.fixedPointBranch μ) a) b
  /-- The flow starts at the branch state. -/
  eventually_flow_zero :
    ∀ᶠ μ in 𝓝 persistence.parameter,
      (xsection μ).flow (persistence.fixedPointBranch μ) 0 =
        persistence.fixedPointBranch μ
  /-- The return remains genuinely forward in time. -/
  eventually_crossing_pos :
    ∀ᶠ μ in 𝓝 persistence.parameter,
      0 < (xsection μ).crossingTime (persistence.fixedPointBranch μ)
  /-- The branch does not collapse to an equilibrium. -/
  eventually_field_ne_zero :
    ∀ᶠ μ in 𝓝 persistence.parameter,
      (xsection μ).field (persistence.fixedPointBranch μ) ≠ 0

namespace PersistentReturnOrbitData

/-- A periodic trajectory produced specifically from the implicit fixed-point branch at parameter
`μ`, together with the definitional identification of its orbit with the section flow through that
branch point.  Keeping this identification explicit is important for transferring positivity and
other trajectory properties from flow estimates. -/
-- No `: Type` ascription: `E : Type*` lives in universe `u_1`, so `PeriodicTrajectory`
-- lands at `u_1 + 1`, which does not fit in `Type 0`.  Let Lean infer the level.
structure BranchPeriodicTrajectory (D : PersistentReturnOrbitData E) (μ : ℝ) where
  trajectory : PeriodicTrajectory (D.xsection μ).field
  orbit_eq : trajectory.orbit =
    (D.xsection μ).flow (D.persistence.fixedPointBranch μ)

/-- Along the implicit branch, the actual Poincare return map fixes the branch state. -/
theorem eventually_section_fixedPoint (D : PersistentReturnOrbitData E) :
    ∀ᶠ μ in 𝓝 D.persistence.parameter,
      (D.xsection μ).returnMap (D.persistence.fixedPointBranch μ) =
        D.persistence.fixedPointBranch μ := by
  filter_upwards [D.persistence.eventually_fixedPointBranch] with μ hμ
  rw [← D.returnMap_eq]
  exact hμ

/-- The persistent fixed-point branch gives a *chosen* periodic trajectory whose orbit is the
section flow through the branch point.  This stronger form is used when properties such as
positivity are known for that specific flow line. -/
theorem eventually_branchPeriodicTrajectory (D : PersistentReturnOrbitData E) :
    ∀ᶠ μ in 𝓝 D.persistence.parameter,
      Nonempty (D.BranchPeriodicTrajectory μ) := by
  filter_upwards [D.eventually_section_fixedPoint, D.eventually_semigroup,
    D.eventually_flow_zero, D.eventually_crossing_pos, D.eventually_field_ne_zero]
    with μ hfix hsemi hzero hpos hfield
  let P : PeriodicTrajectory (D.xsection μ).field :=
    (D.xsection μ).periodicTrajectoryOfReturnMapFixedPoint
      hsemi hzero hfix hpos hfield
  exact ⟨⟨P, rfl⟩⟩

/-- **IFT persistence closes to actual periodic trajectories.** Every sufficiently nearby
parameter carries an exact nonconstant periodic trajectory of its parameterized vector field. -/
theorem eventually_periodicTrajectory (D : PersistentReturnOrbitData E) :
    ∀ᶠ μ in 𝓝 D.persistence.parameter,
      Nonempty (PeriodicTrajectory (D.xsection μ).field) := by
  filter_upwards [D.eventually_branchPeriodicTrajectory] with μ hμ
  obtain ⟨B⟩ := hμ
  exact ⟨B.trajectory⟩


end PersistentReturnOrbitData

end CRNT
