import CRNT.Oscillation.PlanarJordanDyadic
import CRNT.Oscillation.PlanarDivergenceRegularity

/-!
# Boundary-current convergence for C1 Jordan curves

`PlanarGreenRectangle` and `PlanarGreenGrid` prove Green's theorem on finite rectilinear cell
complexes. `PlanarJordanDyadic` records the missing dyadic construction and its boundary-current
convergence as explicit targets. This file keeps the normal-flux definition and the normalized-loop
derivative fact, and adapts a supplied boundary-current target to the grid theorem. The polygonal
current argument itself is not present in this checkout, so it is not asserted as an unconditional
proof here.
-/

namespace CRNT

-- `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope; without this open the bracket is
-- not a valid token.
open scoped InnerProductSpace

namespace Planar

open Set Filter MeasureTheory

/-- Normal flux of a C1 parameterized curve on `[a,b]`. -/
noncomputable def curveFlux (G : Phase2 → Phase2) (γ γ' : ℝ → Phase2) (a b : ℝ) : ℝ :=
  ∫ t in Set.uIcc a b, ⟪G (γ t), quarterTurn (γ' t)⟫_ℝ

/-- The least-period normalized periodic orbit is C1 and its derivative is the normalized vector
field tangent. -/
theorem normalizedLoop_hasDeriv
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field) (s : ℝ) :
    HasDerivAt P.normalizedLoop
      (P.period • field (P.normalizedLoop s)) s := by
  change HasDerivAt (P.orbit ∘ fun u : ℝ => u * P.period)
    (P.period • field (P.orbit (s * P.period))) s
  have hscale : HasDerivAt (fun u : ℝ => u * P.period) P.period s := by
    simpa using (hasDerivAt_id s).mul_const P.period
  exact (P.solution (s * P.period)).scomp s hscale

/-- The polygonal and dyadic-current construction required for the Jordan-grid theorem is an
explicit mathematical target. `PlanarJordanDyadic` gives its exact shape, including the certified
inner grid, area data, and limiting flux current. -/
theorem jordanGridApproximation_proved
    (hboundary : JordanBoundaryCurrentConvergenceTarget) :
    JordanGridApproximationTarget :=
  jordanGridApproximation_of_boundaryCurrent hboundary

end Planar
end CRNT
