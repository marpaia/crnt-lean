import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Large positive coordinates in a zero-sum vector

On a finite coordinate set, zero sum prevents a large negative entry from dominating the norm:
a sufficiently large Euclidean norm forces a positive coordinate above any fixed threshold.
-/

namespace CRNT
namespace Analysis

open scoped BigOperators

theorem exists_coordinate_gt_of_zero_sum_of_norm_large
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (z : ι → ℝ) (hsum : (∑ i, z i) = 0) {L : ℝ}
    (hlarge : (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ) * L < ‖toEuclid z‖) :
    ∃ i, L < z i := by
  classical
  let s : Finset ℝ := Finset.univ.image z
  have hs : s.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨z i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let m : ℝ := s.max' hs
  have hzle : ∀ i, z i ≤ m := by
    intro i
    exact Finset.le_max' s (z i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hm_mem : m ∈ s := by
    exact Finset.max'_mem s hs
  obtain ⟨i₀, -, hi₀⟩ := Finset.mem_image.mp hm_mem
  have hmax : z i₀ = m := hi₀
  let n : ℝ := (Fintype.card ι : ℝ)
  have hn0 : 0 < n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
  have hm0 : 0 ≤ m := by
    by_contra hnot
    have hmneg : m < 0 := lt_of_not_ge hnot
    have hnonpos : ∀ i ∈ (Finset.univ : Finset ι), z i ≤ 0 := by
      intro i _
      exact (hzle i).trans hmneg.le
    have hstrict : z i₀ < 0 := by rw [hmax]; exact hmneg
    have hsumneg : (∑ i, z i) < 0 :=
      Finset.sum_neg' hnonpos ⟨i₀, Finset.mem_univ i₀, hstrict⟩
    linarith
  have hcoord_lower : ∀ i, -(n * m) ≤ z i := by
    intro i
    have hsum_erase :
        (∑ j ∈ Finset.univ.erase i, z j) + z i = 0 := by
      have h := Finset.sum_erase_add (Finset.univ : Finset ι) z (Finset.mem_univ i)
      simpa [hsum] using h
    have hsum_le : (∑ j ∈ Finset.univ.erase i, z j) ≤
        (Fintype.card (Finset.univ.erase i) : ℝ) * m := by
      calc
        (∑ j ∈ Finset.univ.erase i, z j) ≤
            ∑ j ∈ Finset.univ.erase i, m :=
          Finset.sum_le_sum fun j _ => hzle j
        _ = (Fintype.card (Finset.univ.erase i) : ℝ) * m := by simp
    have hcard : (Fintype.card (Finset.univ.erase i) : ℝ) ≤ n := by
      rw [Fintype.card_coe]
      dsimp [n]
      exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
    have hsum_le' : (∑ j ∈ Finset.univ.erase i, z j) ≤ n * m :=
      le_trans hsum_le (mul_le_mul_of_nonneg_right hcard hm0)
    linarith
  have hcoord_abs : ∀ i, |z i| ≤ n * m := by
    intro i
    have hupper : z i ≤ n * m := by
      calc
        z i ≤ m := hzle i
        _ ≤ n * m := by nlinarith
    exact abs_le.mpr ⟨hcoord_lower i, hupper⟩
  have hsup : (⨆ i, ‖inner ℝ (EuclideanSpace.basisFun ι ℝ i) (toEuclid z)‖) ≤ n * m := by
    apply ciSup_le
    intro i
    have hinner : inner ℝ (EuclideanSpace.basisFun ι ℝ i) (toEuclid z) = z i := by
      rw [EuclideanSpace.basisFun_inner]
      simp [CRNT.toEuclid_apply]
    rw [hinner, Real.norm_eq_abs]
    exact hcoord_abs i
  have hnorm : ‖toEuclid z‖ ≤ Real.sqrt n * (⨆ i,
      ‖inner ℝ (EuclideanSpace.basisFun ι ℝ i) (toEuclid z)‖) := by
    simpa [n] using
      (EuclideanSpace.basisFun ι ℝ).norm_le_card_mul_iSup_norm_inner (toEuclid z)
  have hsup0 : 0 ≤ (⨆ i,
      ‖inner ℝ (EuclideanSpace.basisFun ι ℝ i) (toEuclid z)‖) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact le_trans (norm_nonneg _) (Finite.le_ciSup
      (fun j => ‖inner ℝ (EuclideanSpace.basisFun ι ℝ j) (toEuclid z)‖) i)
  have hsqrt : Real.sqrt n ≤ n := by
    calc
      Real.sqrt n ≤ Real.sqrt (n * n) := Real.sqrt_le_sqrt (by nlinarith)
      _ = n := by rw [show n * n = n ^ 2 by ring, Real.sqrt_sq hn0.le]
  have hnorm_le : ‖toEuclid z‖ ≤ n * n * m := by
    calc
      ‖toEuclid z‖ ≤ Real.sqrt n *
          (⨆ i, ‖inner ℝ (EuclideanSpace.basisFun ι ℝ i) (toEuclid z)‖) := hnorm
      _ ≤ n * (n * m) := mul_le_mul hsqrt hsup hsup0 hn0.le
      _ = n * n * m := by ring
  have hnSq : 0 < n * n := mul_pos hn0 hn0
  have hm_large : L < m := by nlinarith [hlarge, hnorm_le]
  exact ⟨i₀, by rw [hmax]; exact hm_large⟩

end Analysis
end CRNT
