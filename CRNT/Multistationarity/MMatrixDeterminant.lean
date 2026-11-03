import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# The determinant sign criterion for a nonsingular M-matrix

For a real Z-matrix `B` (nonpositive off-diagonal entries), the existence of a strictly positive
vector `x` with `B *ᵥ x > 0` is the nonsingular M-matrix criterion.  The classical result of
Berman (1967), developed in Berman–Plemmons, *Nonnegative Matrices in the Mathematical Sciences*
(1979; first edition 1979), states that such a matrix has positive determinant.  This module
proves that criterion by continuously scaling the off-diagonal entries to zero; strict diagonal
dominance after weighting the rows by `x` keeps every matrix on the path nonsingular.

The application to the fully open affine total-degree theorem is left for a later integration
step.  It is a statement about affine mass-action fields only and does not establish the
higher-order total-degree theorem.
-/

open scoped BigOperators
open scoped Matrix

namespace CRNT
namespace Network

open Set

variable {S : Type} [Fintype S] [DecidableEq S]

/-- A real Z-matrix with a positive vector mapped to a positive vector has positive determinant.
This is the nonsingular M-matrix determinant criterion (Berman, 1967). -/
theorem det_pos_of_negZMatrix_of_pos_mulVec (B : Matrix S S ℝ) (x : S → ℝ)
    (hBii : ∀ i, 0 < B i i) (hBoff : ∀ i j, i ≠ j → B i j ≤ 0)
    (hx : ∀ i, 0 < x i) (hBx : ∀ i, 0 < (B *ᵥ x) i) : 0 < B.det := by
  classical
  by_cases hS : IsEmpty S
  · simp
  ·
    let D : Matrix S S ℝ := Matrix.diagonal fun i => B i i
    let A : ℝ → Matrix S S ℝ := fun t => D + t • (B - D)
    have hdiag : ∀ t i, A t i i = B i i := by
      intro t i
      simp [A, D]
    have hoff : ∀ t i j, i ≠ j → A t i j = t * B i j := by
      intro t i j hij
      simp [A, D, Matrix.diagonal_apply_ne _ hij, sub_eq_add_neg]
    have hpath_ne : ∀ t ∈ Icc (0 : ℝ) 1, (A t).det ≠ 0 := by
      intro t ht hdet
      let C : Matrix S S ℝ := A t * Matrix.diagonal x
      have hmuldiag : ∀ i j, C i j = A t i j * x j := by
        intro i j
        simp [C, Matrix.mul_apply, Matrix.diagonal_apply]
      have hCdiag : ∀ i, ‖C i i‖ = B i i * x i := by
        intro i
        rw [hmuldiag i i, hdiag t i]
        rw [Real.norm_eq_abs, abs_of_pos (mul_pos (hBii i) (hx i))]
      have hrow : ∀ i,
          ∑ j ∈ (Finset.univ.erase i), ‖C i j‖ < ‖C i i‖ := by
        intro i
        have hsplit : (∑ j : S, B i j * x j) =
            B i i * x i + ∑ j ∈ (Finset.univ.erase i), B i j * x j := by
          rw [← Finset.sum_erase_add (Finset.univ : Finset S)
            (fun j => B i j * x j) (Finset.mem_univ i)]
          simp
        have hsum : ∑ j ∈ (Finset.univ.erase i), (-B i j) * x j < B i i * x i := by
          have hrowpos : 0 < ∑ j : S, B i j * x j := by
            simpa [Matrix.mulVec_apply, dotProduct, Matrix.row_apply] using hBx i
          rw [hsplit] at hrowpos
          have hneg : ∑ j ∈ (Finset.univ.erase i), (-B i j) * x j =
              -∑ j ∈ (Finset.univ.erase i), B i j * x j := by
            rw [← Finset.sum_neg_distrib]
            congr 1
            ext j
            ring
          rw [hneg]
          linarith
        have hsum_nonneg : ∀ j ∈ (Finset.univ.erase i), 0 ≤ (-B i j) * x j := by
          intro j hj
          exact mul_nonneg (neg_nonneg.mpr (hBoff i j (Ne.symm (Finset.mem_erase.mp hj).1))) (le_of_lt (hx j))
        have ht0 : 0 ≤ t := ht.1
        have ht1 : t ≤ 1 := ht.2
        have hnormsum :
            (∑ j ∈ (Finset.univ.erase i), ‖C i j‖) =
              ∑ j ∈ (Finset.univ.erase i), t * ((-B i j) * x j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hmuldiag i j]
          rw [hoff t i j (Ne.symm (Finset.mem_erase.mp hj).1)]
          simp only [Real.norm_eq_abs]
          rw [abs_of_nonpos]
          · ring
          · exact mul_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonneg_of_nonpos ht0
                (hBoff i j (Ne.symm (Finset.mem_erase.mp hj).1)))
              (le_of_lt (hx j))
        rw [hnormsum, hCdiag i]
        calc
          ∑ j ∈ (Finset.univ.erase i), t * ((-B i j) * x j)
              = t * ∑ j ∈ (Finset.univ.erase i), (-B i j) * x j := by rw [Finset.mul_sum]
          _ ≤ ∑ j ∈ (Finset.univ.erase i), (-B i j) * x j := by
                calc
                  t * ∑ j ∈ (Finset.univ.erase i), (-B i j) * x j
                      ≤ 1 * ∑ j ∈ (Finset.univ.erase i), (-B i j) * x j :=
                        mul_le_mul_of_nonneg_right ht1 (Finset.sum_nonneg hsum_nonneg)
                  _ = _ := by ring
          _ < B i i * x i := hsum
      have hCdet : C.det ≠ 0 := det_ne_zero_of_sum_row_lt_diag hrow
      have hprod : C.det = (A t).det * ∏ i, x i := by
        change ((A t) * Matrix.diagonal x).det = _
        rw [Matrix.det_mul, Matrix.det_diagonal]
      apply hCdet
      rw [hprod, hdet, zero_mul]
    have hcont : ContinuousOn (fun t : ℝ => (A t).det) (Icc 0 1) := by
      have hA : Continuous (fun t : ℝ => A t) := by
        change Continuous (fun t : ℝ => D + t • (B - D))
        fun_prop
      exact (hA.matrix_det).continuousOn
    have hstart : 0 < (A 0).det := by
      simp only [A, zero_smul, add_zero, D, Matrix.det_diagonal]
      exact Finset.prod_pos fun i _ => hBii i
    have hfinish : 0 < (A 1).det := by
      by_contra h
      have hle : (A 1).det ≤ 0 := le_of_not_gt h
      have hz : (0 : ℝ) ∈ Icc ((A 1).det) ((A 0).det) := ⟨hle, le_of_lt hstart⟩
      have hmem := intermediate_value_Icc' (zero_le_one : (0 : ℝ) ≤ 1) hcont hz
      obtain ⟨t, ht, hzero⟩ := hmem
      have hne := hpath_ne t ht
      exact hne (by simpa using hzero)
    simpa [A, D] using hfinish

end Network
end CRNT
