import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A weighted edge-sum estimate

This packages the final scalar step in Boros's single-linkage argument. A large successor
term along one edge dominates the bounded cost contributed by every edge in a finite graph.
-/

namespace CRNT
namespace Analysis

open scoped BigOperators

/-- A large weighted successor term forces positivity of the full edge sum. -/
theorem boros_weightedEdgeSum_pos
    {E V : Type*} [Fintype E] [DecidableEq E]
    (source target : E → V) (gap : V → ℝ) (rate : E → ℝ)
    {b kmin kmax : ℝ}
    (hgap : ∀ v, 0 ≤ gap v)
    (hkmin_pos : 0 < kmin)
    (hkmin : ∀ e, kmin ≤ rate e)
    (hkmax : ∀ e, rate e ≤ kmax)
    (hlarge : ∃ e, b < Real.exp (-gap (source e)) * gap (target e))
    (hbudget : (Fintype.card E : ℝ) * kmax < kmin * b) :
    0 < ∑ e, rate e * Real.exp (-gap (source e)) *
      (gap (target e) - gap (source e)) := by
  classical
  rcases hlarge with ⟨e₀, he₀⟩
  have hkmax_nonneg : 0 ≤ kmax :=
    le_trans hkmin_pos.le (le_trans (hkmin e₀) (hkmax e₀))
  have hrate_nonneg (e : E) : 0 ≤ rate e := le_trans hkmin_pos.le (hkmin e)
  have hsuccessor_nonneg (e : E) :
      0 ≤ rate e * (Real.exp (-gap (source e)) * gap (target e)) :=
    mul_nonneg (hrate_nonneg e)
      (mul_nonneg (le_of_lt (Real.exp_pos _)) (hgap _))
  have hchosen_factor_nonneg :
      0 ≤ Real.exp (-gap (source e₀)) * gap (target e₀) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (hgap _)
  have hchosen_weighted :
      kmin * b < rate e₀ *
        (Real.exp (-gap (source e₀)) * gap (target e₀)) := by
    calc
      kmin * b < kmin *
          (Real.exp (-gap (source e₀)) * gap (target e₀)) :=
        mul_lt_mul_of_pos_left he₀ hkmin_pos
      _ ≤ rate e₀ * (Real.exp (-gap (source e₀)) * gap (target e₀)) :=
        mul_le_mul_of_nonneg_right (hkmin e₀) hchosen_factor_nonneg
  have hsuccessor_sum : kmin * b <
      ∑ e : E, rate e *
        (Real.exp (-gap (source e)) * gap (target e)) := by
    exact lt_of_lt_of_le hchosen_weighted
      (Finset.single_le_sum (f := fun e : E => rate e *
        (Real.exp (-gap (source e)) * gap (target e)))
        (fun e _ => hsuccessor_nonneg e) (Finset.mem_univ e₀))
  have hgap_exp_unit (x : ℝ) (hx : 0 ≤ x) : x * Real.exp (-x) ≤ 1 := by
    calc
      x * Real.exp (-x) ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one x
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by norm_num)
      _ = 1 := by simp
  have hcost_le (e : E) :
      rate e * (gap (source e) * Real.exp (-gap (source e))) ≤ kmax := by
    have hfactor_nonneg : 0 ≤ gap (source e) * Real.exp (-gap (source e)) :=
      mul_nonneg (hgap _) (le_of_lt (Real.exp_pos _))
    calc
      rate e * (gap (source e) * Real.exp (-gap (source e))) ≤
          kmax * (gap (source e) * Real.exp (-gap (source e))) :=
        mul_le_mul_of_nonneg_right (hkmax e) hfactor_nonneg
      _ ≤ kmax * 1 := mul_le_mul_of_nonneg_left
        (hgap_exp_unit _ (hgap _)) hkmax_nonneg
      _ = kmax := by ring
  have hcost_sum :
      ∑ e : E, rate e *
        (gap (source e) * Real.exp (-gap (source e))) ≤
          (Fintype.card E : ℝ) * kmax := by
    calc
      ∑ e : E, rate e *
          (gap (source e) * Real.exp (-gap (source e))) ≤
          ∑ _e : E, kmax := Finset.sum_le_sum (fun e _ => hcost_le e)
      _ = (Fintype.card E : ℝ) * kmax := by simp
  have hsplit :
      (∑ e : E, rate e * Real.exp (-gap (source e)) *
          (gap (target e) - gap (source e))) =
        (∑ e : E, rate e *
          (Real.exp (-gap (source e)) * gap (target e))) -
        (∑ e : E, rate e *
          (gap (source e) * Real.exp (-gap (source e)))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro e _
    ring
  rw [hsplit]
  linarith

end Analysis
end CRNT
