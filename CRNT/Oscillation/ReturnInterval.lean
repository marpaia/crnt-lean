import CRNT.Oscillation.ReturnMap
import CRNT.Analysis.FixedPoint

/-!
# A compact return interval forces a periodic orbit

The final step of the classical Poincare--Bendixson argument is one-dimensional.  Once a transversal
section has been parameterized by a compact interval and its positive-time return map continuously
maps that interval into itself, the one-dimensional Brouwer/intermediate-value theorem gives a fixed
point.  `ReturnMap.periodicTrajectoryOfReturnMapFixedPoint` then closes that fixed point into an exact
nonconstant periodic trajectory.

This module proves that complete fixed-point/rotation-closure step.  The remaining global planar
work is geometric: construct such a recurrent return interval from an equilibrium-free compact
omega-limit set.
-/

namespace CRNT

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace TransversalSection

/-- A compact scalar interval of a transversal section on which the Poincare return map is a
continuous self-map.  The semigroup/zero/positivity/non-equilibrium fields are exactly the hypotheses
needed to turn any scalar fixed point into a genuine nonconstant periodic trajectory. -/
structure ReturnIntervalData (S : TransversalSection (E := E)) where
  left : ℝ
  right : ℝ
  left_le_right : left ≤ right
  /-- Parameterization of section states. -/
  point : ℝ → E
  /-- Scalar coordinate of the return map. -/
  scalarReturn : ℝ → ℝ
  continuousReturn : ContinuousOn scalarReturn (Icc left right)
  mapsToReturn : MapsTo scalarReturn (Icc left right) (Icc left right)
  /-- State-space return-map compatibility with the scalar coordinate. -/
  returnMap_eq : ∀ u ∈ Icc left right,
    S.returnMap (point u) = point (scalarReturn u)
  /-- Semigroup law along every candidate section state. -/
  semigroup : ∀ u ∈ Icc left right, ∀ a b : ℝ,
    S.flow (point u) (a + b) = S.flow (S.flow (point u) a) b
  /-- Flow starts at the parameterized section state. -/
  flow_zero : ∀ u ∈ Icc left right, S.flow (point u) 0 = point u
  /-- Return time is genuinely positive throughout the interval. -/
  crossing_pos : ∀ u ∈ Icc left right, 0 < S.crossingTime (point u)
  /-- No point of the interval is an equilibrium. -/
  field_ne_zero : ∀ u ∈ Icc left right, S.field (point u) ≠ 0

namespace ReturnIntervalData

variable {S : TransversalSection (E := E)}

/-- The scalar return map has a fixed point in the certified compact interval. -/
theorem exists_scalar_fixedPoint (D : S.ReturnIntervalData) :
    ∃ u ∈ Icc D.left D.right, D.scalarReturn u = u :=
  CRNT.Analysis.fixedPoint_Icc D.left_le_right D.continuousReturn D.mapsToReturn

/-- A scalar fixed point is a state-space Poincare return-map fixed point. -/
theorem returnMap_fixed_of_scalar_fixed
    (D : S.ReturnIntervalData) {u : ℝ}
    (hu : u ∈ Icc D.left D.right) (hfix : D.scalarReturn u = u) :
    S.returnMap (D.point u) = D.point u := by
  rw [D.returnMap_eq u hu, hfix]

/-- **Compact return interval theorem.** A continuous self-returning transversal interval contains
an exact nonconstant periodic trajectory of the ambient vector field. -/
theorem exists_periodicTrajectory (D : S.ReturnIntervalData) :
    Nonempty (PeriodicTrajectory S.field) := by
  obtain ⟨u, hu, hufix⟩ := D.exists_scalar_fixedPoint
  exact ⟨S.periodicTrajectoryOfReturnMapFixedPoint
    (D.semigroup u hu)
    (D.flow_zero u hu)
    (D.returnMap_fixed_of_scalar_fixed hu hufix)
    (D.crossing_pos u hu)
    (D.field_ne_zero u hu)⟩

/-- Witness-producing form of `exists_periodicTrajectory`. -/
theorem periodicTrajectory (D : S.ReturnIntervalData) :
    ∃ P : PeriodicTrajectory S.field, True := by
  obtain ⟨P⟩ := D.exists_periodicTrajectory
  exact ⟨P, trivial⟩

end ReturnIntervalData

end TransversalSection

end CRNT
