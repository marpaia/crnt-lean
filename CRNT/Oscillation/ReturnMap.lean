import CRNT.Oscillation.Basic
import CRNT.Dynamics.ReturnMapPeriodicOrbit

/-!
# Poincare-return certificates as generic periodic trajectories

`CRNT.Dynamics.ReturnMapPeriodicOrbit` already proves the geometric closure theorem: a positive-time
fixed point of a Poincare return map closes a flow line into a nonconstant periodic orbit.  This file
adapts that result to the common `PeriodicTrajectory` API used by the oscillation layer.

This is an actual theorem bridge, not a frontier interface.  Any future Hopf, trapping-region, or
computer-assisted argument that produces a return-map fixed point can therefore feed the same
oscillation certificate vocabulary.
-/

namespace CRNT

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace TransversalSection

variable (S : TransversalSection (E := E))

/-- A positive-time fixed point of the Poincare return map gives an exact nonconstant periodic
trajectory of the section's vector field. -/
noncomputable def periodicTrajectoryOfReturnMapFixedPoint {x : E}
    (hsemi : ∀ a b : ℝ, S.flow x (a + b) = S.flow (S.flow x a) b)
    (hx0 : S.flow x 0 = x)
    (hfix : S.returnMap x = x)
    (hpos : 0 < S.crossingTime x)
    (hfield : S.field x ≠ 0) :
    PeriodicTrajectory S.field := by
  have hper : Function.Periodic (S.flow x) (S.crossingTime x) :=
    S.isPeriodic_returnMap_fixedPoint hsemi hfix
  have hnc2 : ∃ s t, S.flow x s ≠ S.flow x t :=
    S.nonconstant_of_field_ne_zero hx0 hfield
  have hnc : ∃ t, S.flow x t ≠ S.flow x 0 := by
    obtain ⟨s, t, hst⟩ := hnc2
    by_cases hs : S.flow x s = S.flow x 0
    · refine ⟨t, ?_⟩
      intro ht
      exact hst (hs.trans ht.symm)
    · exact ⟨s, hs⟩
  exact
    { orbit := S.flow x
      period := S.crossingTime x
      period_pos := hpos
      solution := fun t => S.hasDeriv_flow x t
      periodic := hper
      nonconstant := hnc }

end TransversalSection

end CRNT
