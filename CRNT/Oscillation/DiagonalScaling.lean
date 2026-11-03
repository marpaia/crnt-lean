import CRNT.Oscillation.HalfPlanePolynomial
import CRNT.Oscillation.VassenaContinuation
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FunProp

/-!
# Positive diagonal scalings from principal-minor data

This file closes the first of the two finite matrix theorems used by the Vassena criteria and
sets up the induction step for Fisher--Fuller stabilization.

The key identity is

`det ((M D)_I) = det(M_I) * prod_{i in I} d_i`.

If `M` is not `P^-_0`, choose a principal minor with the wrong strict sign and let all columns
outside that principal block tend to zero.  The corresponding characteristic-polynomial
coefficient tends to exactly that negative signed minor.  For a sufficiently small *positive*
scaling the coefficient remains negative.  `HalfPlanePolynomial` then implies a strict
right-half-plane root.
-/

namespace Matrix

open Polynomial Filter Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Right multiplication by a diagonal matrix simply scales column `j` by `d j`. -/
@[simp] theorem mul_diagonal_apply (M : Matrix n n ℝ) (d : n → ℝ) (i j : n) :
    (M * Matrix.diagonal d) i j = M i j * d j := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

/-- Principal determinants under right diagonal scaling. -/
theorem principalDet_mul_diagonal (M : Matrix n n ℝ) (d : n → ℝ) (I : Finset n) :
    principalDet (M * Matrix.diagonal d) I =
      principalDet M I * ∏ i ∈ I, d i := by
  classical
  unfold principalDet
  let dI : I → ℝ := fun i => d i.1
  have hmat :
      (M * Matrix.diagonal d).submatrix (fun i : I => (i : n)) (fun i : I => (i : n)) =
        M.submatrix (fun i : I => (i : n)) (fun i : I => (i : n)) * Matrix.diagonal dI := by
    ext i j
    simp [mul_diagonal_apply, dI]
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal]
  simp [dI, Finset.prod_attach]

/-- Scale columns in `I` by `1` and all other columns by `eps`. -/
def isolatePrincipalScaling (I : Finset n) (eps : ℝ) : n → ℝ :=
  fun i => if i ∈ I then 1 else eps

@[simp] theorem isolatePrincipalScaling_mem {I : Finset n} {eps : ℝ} {i : n}
    (hi : i ∈ I) : isolatePrincipalScaling I eps i = 1 := by
  simp [isolatePrincipalScaling, hi]

@[simp] theorem isolatePrincipalScaling_not_mem {I : Finset n} {eps : ℝ} {i : n}
    (hi : i ∉ I) : isolatePrincipalScaling I eps i = eps := by
  simp [isolatePrincipalScaling, hi]

/-- The isolating scaling is strictly positive for `eps > 0`. -/
theorem isolatePrincipalScaling_pos {I : Finset n} {eps : ℝ} (heps : 0 < eps) :
    ∀ i, 0 < isolatePrincipalScaling I eps i := by
  intro i
  by_cases hi : i ∈ I <;> simp [isolatePrincipalScaling, hi, heps]

/-- At `eps = 0`, a product over a set `J` of the isolating column weights vanishes unless
`J ⊆ I`. -/
theorem prod_isolatePrincipalScaling_zero (I J : Finset n) :
    (∏ j ∈ J, isolatePrincipalScaling I 0 j) = if J ⊆ I then 1 else 0 := by
  classical
  by_cases hsub : J ⊆ I
  · rw [if_pos hsub]
    apply Finset.prod_eq_one
    intro j hj
    simp [isolatePrincipalScaling, hsub hj]
  · rw [if_neg hsub]
    obtain ⟨j, hjJ, hjI⟩ := Finset.not_subset.mp hsub
    refine Finset.prod_eq_zero hjJ ?_
    simp [isolatePrincipalScaling, hjI]

/-- If two finite sets have the same cardinality and one is contained in the other, they are equal. -/
theorem eq_of_subset_of_card_eq {I J : Finset n} (hJI : J ⊆ I) (hcard : J.card = I.card) :
    J = I := by
  exact Finset.eq_of_subset_of_card_le hJI (by omega)

/-- The characteristic coefficient isolating an `I`-minor at zero scaling is exactly its signed
principal determinant. -/
theorem charpoly_coeff_isolate_zero (M : Matrix n n ℝ) (I : Finset n) :
    (M * Matrix.diagonal (isolatePrincipalScaling I 0)).charpoly.coeff
        (Fintype.card n - I.card) =
      (-1 : ℝ) ^ I.card * principalDet M I := by
  classical
  rw [Matrix.charpoly_coeff_eq_sum_minors _ I.card (Finset.card_le_univ I)]
  have hsum :
      (∑ J ∈ Finset.powersetCard I.card (Finset.univ : Finset n),
        ((M * Matrix.diagonal (isolatePrincipalScaling I 0)).submatrix
          (fun j : J => (j : n)) (fun j : J => (j : n))).det) = principalDet M I := by
    rw [show principalDet M I =
      ∑ J ∈ Finset.powersetCard I.card (Finset.univ : Finset n),
        if J = I then principalDet M I else 0 by
      simp only [Finset.sum_ite_eq', Finset.mem_powersetCard]
      simp [Finset.subset_univ]]
    apply Finset.sum_congr rfl
    intro J hJ
    have hcard : J.card = I.card := (Finset.mem_powersetCard.mp hJ).2
    change principalDet (M * Matrix.diagonal (isolatePrincipalScaling I 0)) J = _
    rw [principalDet_mul_diagonal, prod_isolatePrincipalScaling_zero]
    by_cases hJI : J ⊆ I
    · have hEq : J = I := Finset.eq_of_subset_of_card_le hJI (by omega)
      simp [hJI, hEq]
    · have hne : J ≠ I := by
        intro hEq
        subst J
        exact hJI (Finset.Subset.rfl)
      simp [hJI, hne]
  rw [hsum]

/-- The isolated characteristic coefficient is continuous in `eps`. -/
theorem continuous_charpoly_coeff_isolate (M : Matrix n n ℝ) (I : Finset n) :
    Continuous (fun eps : ℝ =>
      (M * Matrix.diagonal (isolatePrincipalScaling I eps)).charpoly.coeff
        (Fintype.card n - I.card)) := by
  let coeffSum : ℝ → ℝ := fun eps => (-1 : ℝ) ^ I.card *
    ∑ J ∈ Finset.powersetCard I.card (Finset.univ : Finset n),
      ((M * Matrix.diagonal (isolatePrincipalScaling I eps)).submatrix
        (fun j : J => (j : n)) (fun j : J => (j : n))).det
  have hform : (fun eps : ℝ =>
      (M * Matrix.diagonal (isolatePrincipalScaling I eps)).charpoly.coeff
        (Fintype.card n - I.card)) = coeffSum := by
    funext eps
    simpa [coeffSum] using
      (Matrix.charpoly_coeff_eq_sum_minors
        (M * Matrix.diagonal (isolatePrincipalScaling I eps)) I.card
        (Finset.card_le_univ I))
  have hscale : Continuous (fun eps : ℝ => isolatePrincipalScaling I eps) := by
    apply continuous_pi
    intro i
    change Continuous (fun eps : ℝ => if i ∈ I then 1 else eps)
    by_cases hi : i ∈ I
    · simpa only [if_pos hi] using (continuous_const : Continuous fun _ : ℝ => (1 : ℝ))
    · simp only [if_neg hi]
      exact continuous_id
  rw [hform]
  dsimp [coeffSum]
  fun_prop

/-- A negative signed principal minor gives a strict unstable positive right-diagonal scaling. -/
theorem exists_positive_scaling_unstable_of_signedPrincipalDet_neg
    (M : Matrix n n ℝ) {I : Finset n}
    (hI : (-1 : ℝ) ^ I.card * principalDet M I < 0) :
    ∃ d : n → ℝ, (∀ i, 0 < d i) ∧
      (M * Matrix.diagonal d).HasUnstableEigenvalue := by
  let c : ℝ → ℝ := fun eps =>
    (M * Matrix.diagonal (isolatePrincipalScaling I eps)).charpoly.coeff
      (Fintype.card n - I.card)
  have hc0 : c 0 < 0 := by
    simpa [c, charpoly_coeff_isolate_zero] using hI
  have hccont : ContinuousAt c 0 :=
    (continuous_charpoly_coeff_isolate M I).continuousAt
  have hev : ∀ᶠ eps in 𝓝 0, c eps < 0 :=
    hccont.eventually_lt_const hc0
  obtain ⟨eps, hepspos, hepsmem⟩ : ∃ eps : ℝ, 0 < eps ∧ c eps < 0 := by
    have hevpos : ∀ᶠ eps in 𝓝[>] (0 : ℝ), c eps < 0 :=
      hev.filter_mono nhdsWithin_le_nhds
    obtain ⟨eps, hneg, hpos⟩ := (hevpos.and self_mem_nhdsWithin).exists
    exact ⟨eps, hpos, hneg⟩
  refine ⟨isolatePrincipalScaling I eps, isolatePrincipalScaling_pos hepspos, ?_⟩
  let A := M * Matrix.diagonal (isolatePrincipalScaling I eps)
  obtain ⟨z, hzroot, hzpos⟩ :=
    Polynomial.exists_root_re_pos_of_monic_coeff_neg
      (p := A.charpoly) (Matrix.charpoly_monic A) hepsmem
  refine ⟨(z : ℂ), ?_, hzpos⟩
  have hzmap : Polynomial.eval z ((A.map (algebraMap ℝ ℂ)).charpoly) = 0 := by
    rw [Matrix.charpoly_map]
    rw [← Polynomial.eval₂_eq_eval_map]
    exact hzroot
  have hp0 : (A.map (algebraMap ℝ ℂ)).charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  exact (Polynomial.mem_roots hp0).mpr hzmap

/-- **Vassena Criterion-I matrix theorem, closed.** Failure of `P^-_0` supplies a wrong-sign
principal minor; isolating that block gives a positive diagonal scaling with a strict
right-half-plane eigenvalue. -/
theorem notPMinusZeroImpliesUnstableScaling : NotPMinusZeroImpliesUnstableScalingTarget := by
  intro m _ _ M hnot
  change ¬ ∀ I : Finset m, 0 ≤ principalDet (-M) I at hnot
  push_neg at hnot
  obtain ⟨I, hIneg⟩ := hnot
  apply exists_positive_scaling_unstable_of_signedPrincipalDet_neg M
  rw [← principalDet_neg M I]
  exact hIneg

end Matrix
