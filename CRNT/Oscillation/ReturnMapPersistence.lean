import CRNT.Oscillation.ReturnMap
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Persistence of a nondegenerate return-map fixed point

Periodic-orbit persistence is most cleanly proved on a Poincare section.  Once the flow/section
construction has reduced the problem to a finite-dimensional return map `P μ x`, a periodic orbit is
a fixed point of `P μ`.  The displacement

`F(μ,x) = P μ x - x`

therefore vanishes at the unperturbed orbit.  If the derivative in the section coordinate `x` is
invertible, the Banach-space implicit function theorem gives a nearby branch of fixed points.

This module proves that generic implicit-function step.  It deliberately does not assume that an
arbitrary map is a Poincare map: CRN inheritance modules must separately construct the parameterized
section/return map and verify that its section derivative is invertible.  For a nondegenerate
periodic orbit, the latter is the return-map form of excluding multiplier `1` in transverse
directions.
-/

namespace CRNT

open Filter Topology

/-- Data needed to persist a fixed point of a parameterized map by the implicit function theorem.
`E` should be the local coordinate space of a Poincare section, not the full autonomous phase
space. -/
structure ReturnMapPersistenceData
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] where
  /-- Parameterized section return map. -/
  returnMap : ℝ → E → E
  /-- Reference parameter. -/
  parameter : ℝ
  /-- Reference fixed point. -/
  base : E
  /-- The reference point is fixed. -/
  fixed : returnMap parameter base = base
  /-- `C¹` regularity of the fixed-point displacement near the reference point. -/
  contDiffAt_displacement :
    ContDiffAt ℝ 1 (fun p : ℝ × E => returnMap p.1 p.2 - p.2) (parameter, base)
  /-- The derivative of `P - id` in the section coordinate is invertible. -/
  stateDerivativeInvertible :
    (fderiv ℝ (fun p : ℝ × E => returnMap p.1 p.2 - p.2) (parameter, base) ∘L
      ContinuousLinearMap.inr ℝ ℝ E).IsInvertible

namespace ReturnMapPersistenceData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The fixed-point displacement used by the IFT. -/
def displacement (D : ReturnMapPersistenceData E) (p : ℝ × E) : E :=
  D.returnMap p.1 p.2 - p.2

@[simp] theorem displacement_base (D : ReturnMapPersistenceData E) :
    D.displacement (D.parameter, D.base) = 0 := by
  simp [displacement, D.fixed]

/-- IFT branch of section states near the reference parameter. -/
noncomputable def fixedPointBranch (D : ReturnMapPersistenceData E) : ℝ → E :=
  D.contDiffAt_displacement.implicitFunction (by norm_num) D.stateDerivativeInvertible

/-- The IFT branch solves the displacement equation for all parameters sufficiently close to the
reference parameter. -/
theorem eventually_displacement_fixedPointBranch_eq_zero (D : ReturnMapPersistenceData E) :
    ∀ᶠ μ in 𝓝 D.parameter, D.displacement (μ, D.fixedPointBranch μ) = 0 := by
  have h := D.contDiffAt_displacement.eventually_apply_implicitFunction
    (by norm_num) D.stateDerivativeInvertible
  filter_upwards [h] with μ hμ
  -- `fixedPointBranch` *is* the implicit function; unfold it so `hμ` matches
  -- `hμ` is stated on the unfolded displacement, so unfold both `fixedPointBranch` and
  -- `displacement` in the goal before rewriting
  show D.returnMap μ (D.fixedPointBranch μ) - D.fixedPointBranch μ = 0
  simp only [fixedPointBranch]
  rw [hμ]
  simpa [displacement] using D.displacement_base

/-- Equivalently, the implicit branch consists of actual return-map fixed points near the reference
parameter. -/
theorem eventually_fixedPointBranch (D : ReturnMapPersistenceData E) :
    ∀ᶠ μ in 𝓝 D.parameter,
      D.returnMap μ (D.fixedPointBranch μ) = D.fixedPointBranch μ := by
  filter_upwards [D.eventually_displacement_fixedPointBranch_eq_zero] with μ hμ
  simpa [displacement, sub_eq_zero] using hμ

/-- The implicit fixed-point branch is `C¹` at the reference parameter. -/
theorem contDiffAt_fixedPointBranch (D : ReturnMapPersistenceData E) :
    ContDiffAt ℝ 1 D.fixedPointBranch D.parameter := by
  exact D.contDiffAt_displacement.contDiffAt_implicitFunction
    (by norm_num) D.stateDerivativeInvertible

/-- Hence the fixed-point branch is continuous at the reference parameter. -/
theorem continuousAt_fixedPointBranch (D : ReturnMapPersistenceData E) :
    ContinuousAt D.fixedPointBranch D.parameter :=
  D.contDiffAt_fixedPointBranch.continuousAt

end ReturnMapPersistenceData

/-- Constructor theorem making the exact analytic boundary explicit: once a parameterized section
return map is `C¹` and the transverse derivative of `P - id` is invertible, the persistence data are
fully available and the IFT theorems above apply. -/
def returnMapPersistenceDataOfDerivativeInvertible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : ℝ → E → E) (μ₀ : ℝ) (x₀ : E)
    (hfixed : P μ₀ x₀ = x₀)
    (hC1 : ContDiffAt ℝ 1 (fun p : ℝ × E => P p.1 p.2 - p.2) (μ₀, x₀))
    (hinv :
      (fderiv ℝ (fun p : ℝ × E => P p.1 p.2 - p.2) (μ₀, x₀) ∘L
        ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    ReturnMapPersistenceData E where
  returnMap := P
  parameter := μ₀
  base := x₀
  fixed := hfixed
  contDiffAt_displacement := hC1
  stateDerivativeInvertible := hinv

end CRNT
