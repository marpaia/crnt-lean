import CRNT.Oscillation.PlanarSectionCoordinates
import CRNT.Oscillation.SimpleCycle

/-!
# No-crossing consequences of autonomous ODE uniqueness

The planar Poincare--Bendixson proof uses more than recurrence: it repeatedly uses the fact that two
integral curves of a locally Lipschitz autonomous field cannot cross and then separate.  This file
packages that fact independently of any Jordan argument.

These lemmas are deliberately stated for global exact solutions and then specialized to
`FlowTrappingData.trajectory`.  They are the dynamical input for ordering successive intersections
with the canonical one-dimensional transversal.
-/

namespace CRNT

-- `ℝ≥0` is scoped notation for `NNReal`; without this it does not parse and shows up as
-- `LE Type` / `OfNat Type 0` instance failures.
open scoped NNReal


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {field : E → E}

/-- Translate an exact autonomous solution in time. -/
theorem exactSolution_timeShift
    {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (field (γ t)) t) (a : ℝ) :
    ∀ t, HasDerivAt (fun u => γ (u + a))
      (field (γ (t + a))) t := by
  intro t
  have hshift : HasDerivAt (fun u : ℝ => u + a) 1 t := by
    simpa using (hasDerivAt_id t).add_const a
  simpa [Function.comp_def] using (hγ (t + a)).scomp t hshift

/-- **No crossing.** If two exact solutions of an autonomous field meet once, their corresponding
time shifts are identical for all real time. -/
theorem exactSolutions_eq_shift_of_hit
    (huniq : GlobalSolutionUnique field)
    {γ₁ γ₂ : ℝ → E}
    (hγ₁ : ∀ t, HasDerivAt γ₁ (field (γ₁ t)) t)
    (hγ₂ : ∀ t, HasDerivAt γ₂ (field (γ₂ t)) t)
    {t₁ t₂ : ℝ} (hhit : γ₁ t₁ = γ₂ t₂) :
    (fun u => γ₁ (u + t₁)) = (fun u => γ₂ (u + t₂)) := by
  apply huniq
  · exact exactSolution_timeShift hγ₁ t₁
  · exact exactSolution_timeShift hγ₂ t₂
  · simpa using hhit

/-- Pointwise form of no crossing. -/
theorem exactSolutions_shift_eq_of_hit
    (huniq : GlobalSolutionUnique field)
    {γ₁ γ₂ : ℝ → E}
    (hγ₁ : ∀ t, HasDerivAt γ₁ (field (γ₁ t)) t)
    (hγ₂ : ∀ t, HasDerivAt γ₂ (field (γ₂ t)) t)
    {t₁ t₂ : ℝ} (hhit : γ₁ t₁ = γ₂ t₂) (u : ℝ) :
    γ₁ (u + t₁) = γ₂ (u + t₂) :=
  congrFun (exactSolutions_eq_shift_of_hit huniq hγ₁ hγ₂ hhit) u

/-- Two solutions meeting at the same time have equal initial states. -/
theorem initial_eq_of_same_time_hit
    (huniq : GlobalSolutionUnique field)
    {γ₁ γ₂ : ℝ → E}
    (hγ₁ : ∀ t, HasDerivAt γ₁ (field (γ₁ t)) t)
    (hγ₂ : ∀ t, HasDerivAt γ₂ (field (γ₂ t)) t)
    (hzero₁ : γ₁ 0 = x₁) (hzero₂ : γ₂ 0 = x₂)
    {t : ℝ} (hhit : γ₁ t = γ₂ t) : x₁ = x₂ := by
  have hshift := exactSolutions_eq_shift_of_hit huniq hγ₁ hγ₂ hhit
  have hback := congrFun hshift (-t)
  simpa [hzero₁, hzero₂] using hback

namespace Planar

/-- Smooth planar fields have the global no-crossing property for the complete trajectories carried
by `FlowTrappingData`. -/
theorem FlowTrappingData.trajectory_noCrossing
    {field : Phase2 → Phase2} (D : FlowTrappingData field)
    (hsmooth : ContDiff ℝ 1 field)
    {x y : Phase2} {tx ty : ℝ}
    (hhit : D.trajectory x tx = D.trajectory y ty) :
    ∀ u : ℝ, D.trajectory x (u + tx) = D.trajectory y (u + ty) := by
  have huniq : GlobalSolutionUnique field :=
    globalSolutionUnique_of_locallyLipschitz hsmooth.locallyLipschitz
  intro u
  exact exactSolutions_shift_eq_of_hit huniq
    (D.trajectory_solution x) (D.trajectory_solution y) hhit u

/-- For every fixed real time, the complete-flow map is injective. -/
theorem FlowTrappingData.trajectory_injective
    {field : Phase2 → Phase2} (D : FlowTrappingData field)
    (hsmooth : ContDiff ℝ 1 field) (t : ℝ) :
    Function.Injective (fun x : Phase2 => D.trajectory x t) := by
  intro x y hxy
  have h := D.trajectory_noCrossing hsmooth hxy (-t)
  simpa [D.trajectory_zero] using h

/-- The nonnegative semiflow inherited from those complete trajectories is injective at each time. -/
theorem FlowTrappingData.flow_injective
    {field : Phase2 → Phase2} (D : FlowTrappingData field)
    (hsmooth : ContDiff ℝ 1 field) (t : ℝ≥0) :
    Function.Injective (D.flow t) := by
  intro x y hxy
  rw [D.flow_eq_trajectory, D.flow_eq_trajectory] at hxy
  exact D.trajectory_injective hsmooth (t : ℝ) hxy

/-- If the same complete trajectory meets the same point at two distinct times, their time
difference is a period of that trajectory. -/
theorem FlowTrappingData.period_of_selfIntersection
    {field : Phase2 → Phase2} (D : FlowTrappingData field)
    (hsmooth : ContDiff ℝ 1 field) {x : Phase2} {s t : ℝ}
    (hst : s < t) (hhit : D.trajectory x s = D.trajectory x t) :
    Function.Periodic (D.trajectory x) (t - s) := by
  have huniq : GlobalSolutionUnique field :=
    globalSolutionUnique_of_locallyLipschitz hsmooth.locallyLipschitz
  intro u
  have h := exactSolutions_shift_eq_of_hit huniq
    (D.trajectory_solution x) (D.trajectory_solution x) hhit (u - s)
  -- `convert … using 1` pairs the wrong sides here; normalise the time arguments instead.
  have e1 : u - s + s = u := by ring
  have e2 : u - s + t = u + (t - s) := by ring
  rw [e1, e2] at h
  exact h.symm

end Planar
end CRNT
