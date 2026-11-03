import CRNT.Reduction.Intermediates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Multi-intermediate elimination by a Schur complement

For a fixed core concentration, mass-action equations for genuine intermediates are linear in
the intermediate concentrations.  Writing

`0 = A_H h + b(x_core)`

with an invertible transient/intermediate block `A_H`, the unique intermediate state is
`h = -A_H⁻¹ b`.  Substitution into the core equations produces the exact reduced vector field

`f_red(x) = f_core(x) - C A_H⁻¹ b(x)`.

This is the linear-algebra heart of the Feliu--Wiuf intermediate elimination theorem.
-/

namespace CRNT

open scoped BigOperators

/-- Abstract block decomposition of a CRN steady-state equation into core and intermediate
coordinates.  It is deliberately independent of an implementation-specific reduced-network
constructor. -/
structure IntermediateLinearBlock (Core H : Type)
    [Fintype Core] [DecidableEq Core] [Fintype H] [DecidableEq H] where
  A : Matrix H H ℝ
  input : (Core → ℝ) → (H → ℝ)
  coreField : (Core → ℝ) → (Core → ℝ)
  coupling : (H → ℝ) →ₗ[ℝ] (Core → ℝ)
  invertible : IsUnit A.det

namespace IntermediateLinearBlock

variable {Core H : Type}
  [Fintype Core] [DecidableEq Core] [Fintype H] [DecidableEq H]

/-- Unique eliminated intermediate concentration. -/
noncomputable def eliminatedIntermediate (B : IntermediateLinearBlock Core H)
    (x : Core → ℝ) : H → ℝ :=
  -(B.A⁻¹.mulVec (B.input x))

/-- Reduced core vector field after exact steady-state elimination. -/
noncomputable def reducedField (B : IntermediateLinearBlock Core H)
    (x : Core → ℝ) : Core → ℝ :=
  B.coreField x + B.coupling (B.eliminatedIntermediate x)

/-- The eliminated intermediate vector solves the internal linear steady-state equation. -/
theorem eliminatedIntermediate_solves (B : IntermediateLinearBlock Core H)
    (x : Core → ℝ) :
    B.A.mulVec (B.eliminatedIntermediate x) + B.input x = 0 := by
  unfold eliminatedIntermediate
  rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, B.A.mul_nonsing_inv B.invertible,
    Matrix.one_mulVec]
  simp

/-- Uniqueness of the internal steady-state solution. -/
theorem eliminatedIntermediate_unique (B : IntermediateLinearBlock Core H)
    (x : Core → ℝ) {h : H → ℝ}
    (hh : B.A.mulVec h + B.input x = 0) :
    h = B.eliminatedIntermediate x := by
  have hinj : Function.Injective B.A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (B.A.isUnit_iff_isUnit_det.mpr B.invertible)
  apply hinj
  have hs := B.eliminatedIntermediate_solves x
  funext i
  have hh_i := congrFun hh i
  have hs_i := congrFun hs i
  dsimp at hh_i hs_i ⊢
  linarith

/-- Full block steady states are equivalent to reduced core steady states plus the unique
eliminated intermediate concentration. -/
theorem fullSteady_iff_reducedSteady (B : IntermediateLinearBlock Core H)
    (x : Core → ℝ) (h : H → ℝ) :
    (B.A.mulVec h + B.input x = 0 ∧ B.coreField x + B.coupling h = 0) ↔
      (h = B.eliminatedIntermediate x ∧ B.reducedField x = 0) := by
  constructor
  · rintro ⟨hH, hC⟩
    have heq := B.eliminatedIntermediate_unique x hH
    subst heq
    exact ⟨rfl, hC⟩
  · rintro ⟨rfl, hred⟩
    exact ⟨B.eliminatedIntermediate_solves x, hred⟩

/-- The steady-state projection from the full system to the reduced core is injective because
intermediate coordinates are uniquely reconstructed. -/
theorem fullSteady_coreProjection_injective (B : IntermediateLinearBlock Core H) :
    ∀ {x : Core → ℝ} {h₁ h₂ : H → ℝ},
      B.A.mulVec h₁ + B.input x = 0 →
      B.A.mulVec h₂ + B.input x = 0 → h₁ = h₂ := by
  intro x h₁ h₂ hh₁ hh₂
  rw [B.eliminatedIntermediate_unique x hh₁, B.eliminatedIntermediate_unique x hh₂]

/-- If the inverse-transient block has the expected sign (`-A⁻¹ ≥ 0`) and the core input is
nonnegative, eliminated intermediate concentrations are nonnegative.  This is the M-matrix
positivity ingredient in kinetic intermediate removal. -/
def HasPositiveElimination (B : IntermediateLinearBlock Core H) : Prop :=
  ∀ x : Core → ℝ, (∀ i, 0 ≤ B.input x i) →
    ∀ h, 0 ≤ B.eliminatedIntermediate x h

/-- Strict production paths upgrade nonnegative elimination to strict positivity. -/
def HasStrictPositiveElimination (B : IntermediateLinearBlock Core H) : Prop :=
  ∀ x : Core → ℝ, (∀ i, 0 ≤ B.input x i) →
    (∃ i, 0 < B.input x i) →
    ∀ h, 0 < B.eliminatedIntermediate x h

end IntermediateLinearBlock
end CRNT
