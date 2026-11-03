import CRNT.Oscillation.FloquetReturnBridge
import CRNT.Oscillation.ScalarSectionInterpolation
import CRNT.Oscillation.GlobalAttraction

/-!
# Planar Floquet stability to class-global attraction

The planar Floquet route now consists of three separately auditable ingredients:

1. identify the nontrivial Floquet multiplier with the derivative of a scalar Poincare map;
2. use `|P'| < 1` to obtain a nonlinear contracting local return interval;
3. interpolate the convergent section hits into continuous time.

This file packages those pieces and then composes them with the independent global absorption theorem
from `GlobalAttraction`.  Thus local Floquet stability and global attraction remain logically
separate, as they should.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {κ : N.RateConstants}

/-- Complete nonlinear attraction data for one scalar Floquet return-map realization. -/
structure ScalarFloquetAttractionData
    (P : N.LinearlyStablePositivePeriodicOrbit κ) (f : ℝ → ℝ) (x₀ : ℝ) where
  bridge : N.ScalarFloquetReturnBridge P f x₀
  contraction : ScalarLocalContraction f x₀
  basin : Set (Concentration S)
  /-- Openness makes the local basin genuinely non-vacuous: compactness of the periodic orbit
  then supplies a positive-radius orbit tube contained in it. -/
  basin_open : IsOpen basin
  /-- The geometric periodic orbit lies inside the local attraction basin. -/
  orbit_in_basin : Set.range P.orbit.orbit ⊆ basin
  /-- Every exact solution beginning in the local basin admits a section-coordinate interpolation
  driven by the chosen contracting return map. -/
  interpolation :
    ∀ x ∈ basin, ∀ γ : ℝ → Concentration S,
      γ 0 = x →
      (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
      Nonempty (ScalarSectionInterpolationData contraction bridge.fixed
        P.orbit.toPeriodicTrajectory γ)

namespace ScalarFloquetAttractionData

variable {P : N.LinearlyStablePositivePeriodicOrbit κ} {f : ℝ → ℝ} {x₀ : ℝ}

/-- The scalar Floquet/interpolation package gives genuine continuous-time orbital attraction on its
local basin. -/
theorem locallyAttracts
    (D : N.ScalarFloquetAttractionData P f x₀) :
    P.orbit.GloballyAttractsSolutions D.basin := by
  intro x hx γ hγ0 hsol ε hε
  obtain ⟨G⟩ := D.interpolation x hx γ hγ0 hsol
  have hattr := G.attractsTrajectory
  obtain ⟨T, hnear⟩ := hattr ε hε
  refine ⟨max 0 T, le_max_left _ _, ?_⟩
  intro t ht
  have hT : T ≤ t := le_trans (le_max_right _ _) ht
  exact hnear t hT

/-- If the positive stoichiometric class is eventually absorbed into the local Floquet basin, the
same orbit is a class-global limit cycle. -/
noncomputable def globalLimitCycleOnClass
    (D : N.ScalarFloquetAttractionData P f x₀)
    (henter : N.SolutionsEventuallyEnter κ
      (N.positiveCompatibilityClass (P.orbit.orbit 0)) D.basin) :
    N.GlobalLimitCycleOnClass κ :=
  P.orbit.globalLimitCycleOnClass_of_localAttraction_and_absorption
    D.basin D.locallyAttracts henter

/-- Propositional form of the class-global result. -/
theorem hasGlobalLimitCycleOnClass
    (D : N.ScalarFloquetAttractionData P f x₀)
    (henter : N.SolutionsEventuallyEnter κ
      (N.positiveCompatibilityClass (P.orbit.orbit 0)) D.basin) :
    N.HasGlobalLimitCycleOnClass κ :=
  ⟨D.globalLimitCycleOnClass henter⟩

end ScalarFloquetAttractionData

end Network

end CRNT

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Exact planar realization target behind the general Floquet orbital-stability interface.  The
spectral-to-scalar contraction theorem is already closed; this target asks only for the concrete
scalar section/continuous-time interpolation package around each linearly stable orbit. -/
def ScalarFloquetAttractionConstructionTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T)
    (κ : N.RateConstants) (P : N.LinearlyStablePositivePeriodicOrbit κ),
      ∃ (f : ℝ → ℝ) (x₀ : ℝ), Nonempty (N.ScalarFloquetAttractionData P f x₀)

/-- A scalar-section construction theorem closes the broad Floquet orbital-stability target. -/
theorem floquetOrbitalStability_of_scalarAttraction
    (hscalar : ScalarFloquetAttractionConstructionTarget) :
    FloquetOrbitalStabilityTarget := by
  intro T _ _ N κ P
  obtain ⟨f, x₀, D⟩ := hscalar N κ P
  obtain ⟨D⟩ := D
  exact P.orbit.exists_tube_attraction_of_open_basin
    D.basin_open D.orbit_in_basin D.locallyAttracts

end Network
end CRNT
