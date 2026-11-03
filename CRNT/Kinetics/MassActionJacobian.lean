import CRNT.Kinetics.MassAction
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.Matrix.Mul

/-!
# Differentiability of the mass-action vector field

The mass-action vector field `x ↦ ∑ r, κ r · (∏ s, x_s ^ source_r s) · reactionVector r` is a
polynomial map of the concentrations, hence differentiable everywhere on `Concentration S = S → ℝ`
(no positivity needed). This module establishes that smoothness from the bottom up: the source
monomial, the per-reaction rate, and the assembled vector field are each `Differentiable ℝ`. It is
the analytic foundation for the mass-action Jacobian used in the Craciun–Feinberg injectivity theory.

Depends on: `CRNT.Kinetics.MassAction`, Mathlib
`Analysis.Calculus.FDeriv`.
-/

namespace CRNT

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The mass-action monomial `x ↦ ∏ s, x_s ^ (y_s)` of a complex `y` is differentiable: a finite
product of coordinate powers. -/
theorem massActionMonomial_differentiable (y : Complex S) :
    Differentiable ℝ (fun x : Concentration S => y.massActionMonomial x) := by
  intro x
  simp only [Complex.massActionMonomial]
  exact (HasFDerivAt.finsetProd fun s _ =>
    ((differentiable_apply s).pow (y s)).differentiableAt.hasFDerivAt).differentiableAt

/-- The `j`-th partial derivative of the source monomial `∏ s, x_s ^ (y_s)`, in the polynomial form
`y_j · x_j ^ (y_j - 1) · ∏_{s ≠ j} x_s ^ (y_s)` valid at every point. -/
def massActionMonomialGrad (y : Complex S) (x : Concentration S) (j : S) : ℝ :=
  (y j : ℝ) * x j ^ (y j - 1) * ∏ s ∈ Finset.univ.erase j, x s ^ (y s)

/-- The source-monomial gradient, multiplied by the differentiated concentration, reconstructs the
source stoichiometric coefficient times the source monomial.  This cross-multiplied form avoids a
division and therefore remains valid even on the boundary. -/
theorem massActionMonomialGrad_mul_coord (y : Complex S) (x : Concentration S) (j : S) :
    massActionMonomialGrad y x j * x j = (y j : ℝ) * y.massActionMonomial x := by
  classical
  by_cases hj : y j = 0
  · simp [massActionMonomialGrad, Complex.massActionMonomial, hj]
  · have hj1 : 1 ≤ y j := Nat.one_le_iff_ne_zero.mpr hj
    have hmem : j ∈ (Finset.univ : Finset S) := Finset.mem_univ j
    have hsplit : y.massActionMonomial x =
        x j ^ y j * ∏ s ∈ Finset.univ.erase j, x s ^ y s := by
      exact (Finset.mul_prod_erase Finset.univ (fun s => x s ^ y s) hmem).symm
    have hpow : x j ^ y j = x j ^ (y j - 1) * x j := by
      conv_lhs => rw [show y j = (y j - 1) + 1 by omega]
      rw [pow_succ]
    rw [massActionMonomialGrad, hsplit, hpow]
    ring

/-- The Fréchet derivative of the source monomial is the dot product with its gradient:
`∑ j, (∂_j monomial) • proj_j`. -/
theorem massActionMonomial_hasFDerivAt (y : Complex S) (x : Concentration S) :
    HasFDerivAt (fun x : Concentration S => y.massActionMonomial x)
      (∑ j, massActionMonomialGrad y x j •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j) x := by
  have hfac : ∀ s : S, HasFDerivAt (fun x : Concentration S => x s ^ (y s))
      ((y s • x s ^ (y s - 1)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s) x :=
    fun s => (hasFDerivAt_apply s x).pow (y s)
  have h := HasFDerivAt.finsetProd (u := (Finset.univ : Finset S)) (fun s _ => hfac s)
  simp only [Complex.massActionMonomial]
  refine h.congr_fderiv (Finset.sum_congr rfl fun s _ => ?_)
  rw [massActionMonomialGrad, smul_smul, nsmul_eq_mul]
  congr 1
  ring

namespace Network

/-- The mass-action rate of a reaction, `x ↦ κ r · monomial`, is differentiable. -/
theorem massActionRate_differentiable (N : Network S) (κ : N.RateConstants) (r : N.R) :
    Differentiable ℝ (fun x : Concentration S => N.massActionRate κ r x) := by
  simp only [Network.massActionRate]
  exact (massActionMonomial_differentiable _).const_mul (κ.k r)

/-- The mass-action vector field is differentiable everywhere: each component is a finite sum of
rates scaled by reaction-vector entries. -/
theorem massActionVectorField_differentiable (N : Network S) (κ : N.RateConstants) :
    Differentiable ℝ (fun x : Concentration S => N.massActionVectorField κ x) := by
  apply differentiable_pi''
  intro s
  simp only [Network.massActionVectorField]
  exact Differentiable.fun_sum fun r _ => (N.massActionRate_differentiable κ r).mul_const _

/-- The mass-action Jacobian as a continuous linear operator at `x`: the Fréchet derivative of the
vector field, in outer-product form `v ↦ ∑ r, κ_r · (∇monomial_r · v) · reactionVector r`. -/
noncomputable def massActionJacobianCLM (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : Concentration S →L[ℝ] Concentration S :=
  ∑ r : N.R, (κ.k r • (∑ j, massActionMonomialGrad (N.reaction r).source x j •
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j)).smulRight (N.reactionVector r)

/-- **The mass-action Jacobian is the Fréchet derivative of the vector field.** Differentiating
`∑ r, κ_r · monomial_r · reactionVector r` term by term, each reaction contributes the rank-one
operator `(κ_r · ∇monomial_r) ⊗ reactionVector r`. -/
theorem massActionVectorField_hasFDerivAt (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) :
    HasFDerivAt (fun x => N.massActionVectorField κ x) (N.massActionJacobianCLM κ x) x := by
  have hfun : (fun x : Concentration S => N.massActionVectorField κ x)
      = ∑ r : N.R, (fun x => N.massActionRate κ r x • N.reactionVector r) := by
    funext x s
    simp only [Network.massActionVectorField, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hr : ∀ r : N.R,
      HasFDerivAt (fun x : Concentration S => N.massActionRate κ r x • N.reactionVector r)
        ((κ.k r • (∑ j, massActionMonomialGrad (N.reaction r).source x j •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) j)).smulRight
            (N.reactionVector r)) x := by
    intro r
    simp only [Network.massActionRate]
    exact ((massActionMonomial_hasFDerivAt (N.reaction r).source x).const_mul (κ.k r)).smul_const
      (N.reactionVector r)
  rw [hfun]
  exact HasFDerivAt.sum fun r _ => hr r

/-- The mass-action Jacobian matrix at `x`: entry `(i, j)` is `∂(ẋ_i)/∂x_j`, namely
`∑ r, κ_r · (∂_j monomial_r) · reactionVector r i`. -/
def massActionJacobian (N : Network S) (κ : N.RateConstants) (x : Concentration S) :
    Matrix S S ℝ :=
  fun i j => ∑ r : N.R,
    κ.k r * massActionMonomialGrad (N.reaction r).source x j * N.reactionVector r i

/-- The Jacobian operator acts as the Jacobian matrix: `J(x) · v = massActionJacobian · v`. This
bridges the Fréchet-derivative operator to the explicit matrix whose determinant and principal
minors drive the Craciun–Feinberg injectivity analysis. -/
theorem massActionJacobianCLM_apply (N : Network S) (κ : N.RateConstants)
    (x v : Concentration S) :
    N.massActionJacobianCLM κ x v = (N.massActionJacobian κ x).mulVec v := by
  funext i
  simp only [massActionJacobianCLM, massActionJacobian, sum_apply, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, smul_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Pi.smul_apply, Matrix.mulVec_eq_sum, Matrix.transpose_apply, op_smul_eq_mul]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ => by ring

end Network

end CRNT
