import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic

/-!
# Finite negative-budget allocation

Finite bookkeeping used by Proposition 4.6. Repeated use of the same descending partner is harmless
if each non-descending reaction receives only the share `δ/(card R + 1)` of its partner's negative
term.
-/

open scoped BigOperators

namespace CRNT

variable {R : Type} [Fintype R] [DecidableEq R]

/-- Uniform fraction of the negative budget assigned to one reaction. -/
noncomputable def finiteNegativeShare (δ : ℝ) (R : Type) [Fintype R] : ℝ :=
  δ / ((Fintype.card R : ℝ) + 1)

theorem finiteNegativeShare_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < finiteNegativeShare δ R := by
  unfold finiteNegativeShare
  exact div_pos hδ (by positivity)

theorem card_mul_finiteNegativeShare_le {δ : ℝ} (hδ : 0 ≤ δ) :
    (Fintype.card R : ℝ) * finiteNegativeShare δ R ≤ δ := by
  let m : ℝ := Fintype.card R
  have hm : 0 ≤ m := by positivity
  have hden : 0 < m + 1 := by linarith
  have hfrac : m / (m + 1) ≤ 1 := (div_le_one hden).2 (by linarith)
  calc
    (Fintype.card R : ℝ) * finiteNegativeShare δ R
        = δ * (m / (m + 1)) := by simp [finiteNegativeShare, m]; ring
    _ ≤ δ := by simpa using mul_le_mul_of_nonneg_left hfrac hδ

/-- **Finite partner-budget lemma.** -/
theorem sum_negative_partner_budget
    (bad : R → Prop) [DecidablePred bad]
    (partner : R → R) (z : R → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hpartner : ∀ r, bad r → ¬ bad (partner r))
    (hz : ∀ r, ¬ bad r → z r ≤ 0) :
    δ * (∑ r ∈ Finset.univ.filter (fun r => ¬ bad r), z r) ≤
      finiteNegativeShare δ R *
        (∑ r ∈ Finset.univ.filter bad, z (partner r)) := by
  classical
  let D : Finset R := Finset.univ.filter (fun r => ¬ bad r)
  let B : Finset R := Finset.univ.filter bad
  let Q : ℝ := ∑ p ∈ D, -z p
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    exact Finset.sum_nonneg fun p hp => neg_nonneg.mpr (hz p (by simpa [D] using (Finset.mem_filter.mp hp).2))
  have hselected : ∑ r ∈ B, -z (partner r) ≤ (B.card : ℝ) * Q := by
    calc
      ∑ r ∈ B, -z (partner r) ≤ ∑ _r ∈ B, Q := by
        apply Finset.sum_le_sum
        intro r hr
        have hpD : partner r ∈ D := by
          simp [D, hpartner r (by simpa [B] using (Finset.mem_filter.mp hr).2)]
        exact Finset.single_le_sum
          (fun p hp => neg_nonneg.mpr (hz p (by simpa [D] using (Finset.mem_filter.mp hp).2))) hpD
      _ = (B.card : ℝ) * Q := by simp [nsmul_eq_mul]
  have hBcard : (B.card : ℝ) ≤ (Fintype.card R : ℝ) := by
    exact_mod_cast Finset.card_le_univ B
  have hselected' : ∑ r ∈ B, -z (partner r) ≤ (Fintype.card R : ℝ) * Q :=
    hselected.trans (mul_le_mul_of_nonneg_right hBcard hQ)
  by_cases hδ0 : δ = 0
  · simp [hδ0, finiteNegativeShare]
  · have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
    have hshare : 0 ≤ finiteNegativeShare δ R := (finiteNegativeShare_pos hδpos).le
    have hscaled := mul_le_mul_of_nonneg_left hselected' hshare
    have hbudget := card_mul_finiteNegativeShare_le (R := R) hδ
    have hscaled2 :
        finiteNegativeShare δ R * (∑ r ∈ B, -z (partner r)) ≤ δ * Q := by
      calc
        finiteNegativeShare δ R * (∑ r ∈ B, -z (partner r))
            ≤ finiteNegativeShare δ R * ((Fintype.card R : ℝ) * Q) := hscaled
        _ = ((Fintype.card R : ℝ) * finiteNegativeShare δ R) * Q := by ring
        _ ≤ δ * Q := mul_le_mul_of_nonneg_right hbudget hQ
    have hD : (∑ r ∈ D, z r) = -Q := by
      dsimp [Q]
      rw [← Finset.sum_neg_distrib]
      ring
    have hB : (∑ r ∈ B, z (partner r)) = -∑ r ∈ B, -z (partner r) := by
      rw [← Finset.sum_neg_distrib]
      ring
    rw [hD, hB]
    linarith

end CRNT
