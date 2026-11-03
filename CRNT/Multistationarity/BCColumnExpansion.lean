import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Basic.Real.Basic

/-!
# Column expansion of the determinant of a product of rectangular matrices

For `A : Matrix S K R` and `B : Matrix K S R`, multilinearity of the determinant in the rows of
`(A * B)ᵀ` gives

```
det (A * B) = ∑ f : S → K, (∏ t, B (f t) t) * det (A.submatrix id f).
```

This is the form of the Cauchy--Binet formula used in the Banaji--Craciun argument: when
`B k t = w k t * A t k` with `w ≥ 0`, every summand is a nonnegative monomial in `w` times the
coefficient `(∏ t, A t (f t)) * det (A.submatrix id f)`, so nonnegativity of all coefficients
and positivity of one summand give `0 < det (A * B)`.

Nothing here is an axiom or a `sorry`.
-/

open Finset

namespace CRNT
namespace DetCycle

variable {S K : Type*} [Fintype S] [DecidableEq S] [Fintype K] [DecidableEq K]

theorem det_mul_eq_sum_columns {R : Type*} [CommRing R] (A : Matrix S K R) (B : Matrix K S R) :
    (A * B).det = ∑ f : S → K, (∏ t, B (f t) t) * (A.submatrix id f).det := by
  rw [← Matrix.det_transpose]
  have h : (A * B).transpose = fun t => ∑ k, B k t • (fun s => A s k) := by
    funext t s
    simp [Matrix.mul_apply, Finset.sum_apply, mul_comm]
  have hs := (Matrix.detRowAlternating : (S → R) [⋀^S]→ₗ[R] R).toMultilinearMap.map_sum
    (fun (t : S) (k : K) => (B k t • fun s => A s k : S → R))
  simp only [AlternatingMap.coe_multilinearMap] at hs
  rw [Matrix.det, h, hs]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  have h2 := (Matrix.detRowAlternating : (S → R) [⋀^S]→ₗ[R] R).toMultilinearMap.map_smul_univ
    (fun t => B (f t) t) (fun t s => A s (f t))
  simp only [AlternatingMap.coe_multilinearMap] at h2
  rw [h2, smul_eq_mul]
  congr 1
  rw [← Matrix.det_transpose (A.submatrix id f)]
  rfl

/-- Positivity of `det (A * B)` for `B k t = w k t * A t k`, from nonnegative coefficients and
one positive summand. -/
theorem det_mul_pos_of_coeff_nonneg (A : Matrix S K ℝ) (w : K → S → ℝ)
    (hw : ∀ k t, 0 ≤ w k t)
    (hcoef : ∀ f : S → K, 0 ≤ (∏ t, A t (f t)) * (A.submatrix id f).det)
    (f₀ : S → K)
    (hf₀ : 0 < (∏ t, w (f₀ t) t) * ((∏ t, A t (f₀ t)) * (A.submatrix id f₀).det)) :
    0 < (A * Matrix.of (fun k t => w k t * A t k)).det := by
  rw [det_mul_eq_sum_columns]
  have hterm : ∀ f : S → K, (∏ t, (Matrix.of (fun k t => w k t * A t k)) (f t) t) *
      (A.submatrix id f).det =
      (∏ t, w (f t) t) * ((∏ t, A t (f t)) * (A.submatrix id f).det) := by
    intro f
    simp only [Matrix.of_apply, Finset.prod_mul_distrib]
    ring
  simp_rw [hterm]
  have hnn : ∀ f ∈ (Finset.univ : Finset (S → K)),
      0 ≤ (∏ t, w (f t) t) * ((∏ t, A t (f t)) * (A.submatrix id f).det) := fun f _ =>
    mul_nonneg (Finset.prod_nonneg fun t _ => hw _ _) (hcoef f)
  exact lt_of_lt_of_le hf₀
    (Finset.single_le_sum (f := fun f : S → K =>
      (∏ t, w (f t) t) * ((∏ t, A t (f t)) * (A.submatrix id f).det)) hnn
      (Finset.mem_univ f₀))

end DetCycle
end CRNT
