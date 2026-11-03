import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# The central limit theorem for Poisson laws

The fluctuation law of a Poisson(`r`) variable, `(N − r)/√r` (`poissonFluct r`), converges weakly to
the standard Gaussian as `r → ∞` (`tendsto_poissonFluct`). Proof: its characteristic function is
`exp(r (e^{iu/√r} − 1) − iu√r)` (`charFun_poissonFluct`) and the exponent tends to `−u²/2`
(`tendsto_poisson_exponent`, third-order bound on `e^x`); Lévy's continuity theorem
(`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) concludes.
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology NNReal

namespace CRNT

/-- `r (e^{iu/√r} − 1) − iu√r → −u²/2` as `r → ∞`. -/
theorem tendsto_poisson_exponent (u : ℝ) :
    Tendsto (fun r : ℝ => (r : ℂ) * (cexp (((u / Real.sqrt r : ℝ) : ℂ) * I) - 1) -
      ((u * Real.sqrt r : ℝ) : ℂ) * I) atTop (𝓝 ((-(u ^ 2 / 2) : ℝ) : ℂ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun r : ℝ => 2 / 9 * |u| ^ 3 / Real.sqrt r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop)
  refine squeeze_zero' (Eventually.of_forall fun r => norm_nonneg _) ?_ hlim
  have hev : ∀ᶠ r : ℝ in atTop, 0 < r ∧ |u| / Real.sqrt r ≤ 1 := by
    have h1 : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
    have h2 : ∀ᶠ r : ℝ in atTop, |u| / Real.sqrt r ≤ 1 := by
      have : Tendsto (fun r : ℝ => |u| / Real.sqrt r) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
      exact this.eventually (ge_mem_nhds zero_lt_one)
    exact h1.and h2
  filter_upwards [hev] with r ⟨hr, hsmall⟩
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  set x : ℂ := ((u / Real.sqrt r : ℝ) : ℂ) * I with hx
  have hxn : ‖x‖ = |u| / Real.sqrt r := by
    rw [hx, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hs]
  have hb := Complex.exp_bound (x := x) (by rw [hxn]; exact hsmall) (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℂ) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ]
  rw [hsum] at hb
  -- the algebra: the expression equals `r (e^x − 1 − x − x²/2)`
  have hr1 : (r : ℝ) * (u / Real.sqrt r) = u * Real.sqrt r := by
    rw [mul_div_assoc', div_eq_iff hs.ne']; linear_combination (-u) * hsq
  have hr2 : (r : ℝ) * (u / Real.sqrt r) ^ 2 = u ^ 2 := by
    rw [div_pow, Real.sq_sqrt hr.le]; field_simp
  have h1 : (r : ℂ) * x = ((u * Real.sqrt r : ℝ) : ℂ) * I := by
    rw [hx, ← mul_assoc, ← Complex.ofReal_mul, hr1]
  have h2 : (r : ℂ) * x ^ 2 = -((u ^ 2 : ℝ) : ℂ) := by
    rw [hx, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, ← mul_assoc, ← Complex.ofReal_mul, hr2]
    ring
  have halg : (r : ℂ) * (cexp x - 1) - ((u * Real.sqrt r : ℝ) : ℂ) * I - ((-(u ^ 2 / 2) : ℝ) : ℂ) =
      (r : ℂ) * (cexp x - (1 + x + x ^ 2 / 2)) := by
    push_cast at h1 h2 ⊢
    linear_combination h1 + (1 / 2 : ℂ) * h2
  rw [halg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  calc r * ‖cexp x - (1 + x + x ^ 2 / 2)‖
      ≤ r * (‖x‖ ^ 3 * (((Nat.succ 3 : ℕ) : ℝ) * ((Nat.factorial 3 : ℕ) * 3 : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_left hb hr.le
    _ = 2 / 9 * |u| ^ 3 / Real.sqrt r := by
        rw [hxn, div_pow, show Real.sqrt r ^ 3 = r * Real.sqrt r by
          rw [pow_succ, pow_two, hsq]]
        norm_num [Nat.factorial]
        field_simp

/-- The fluctuation law `(N − r)/√r` of a Poisson(`r`) variable. -/
noncomputable def poissonFluct (r : ℝ≥0) : Measure ℝ :=
  (((poissonMeasure r).map (fun n : ℕ => (n : ℝ))).map (· + (-(r : ℝ)))).map
    ((Real.sqrt r)⁻¹ * ·)

instance (r : ℝ≥0) : IsProbabilityMeasure (poissonFluct r) := by
  unfold poissonFluct; infer_instance

theorem charFun_poissonFluct (r : ℝ≥0) (u : ℝ) :
    charFun (poissonFluct r) u = cexp ((r : ℂ) * (cexp (((u / Real.sqrt r : ℝ) : ℂ) * I) - 1) -
      ((u * Real.sqrt r : ℝ) : ℂ) * I) := by
  unfold poissonFluct
  rw [charFun_map_mul, charFun_map_add_const, charFun_map_cast_poissonMeasure, ← Complex.exp_add]
  congr 1
  simp only [Real.inner_apply]
  rw [inv_mul_eq_div]
  by_cases hr : (r : ℝ) = 0
  · simp [hr]
  · have hpos : 0 < (r : ℝ) := lt_of_le_of_ne r.2 (Ne.symm hr)
    have hsq : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hpos.le
    have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hpos
    have hr1 : (r : ℝ) * (u / Real.sqrt r) = u * Real.sqrt r := by
      rw [mul_div_assoc', div_eq_iff hs.ne']; linear_combination (-u) * hsq
    have hc : ((r : ℝ) : ℂ) * ((u / Real.sqrt r : ℝ) : ℂ) = ((u * Real.sqrt r : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, hr1]
    push_cast at hc ⊢
    linear_combination (-I) * hc

/-- The fluctuation law as a probability measure. -/
noncomputable def poissonFluctPM (r : ℝ≥0) : ProbabilityMeasure ℝ := ⟨poissonFluct r, inferInstance⟩

/-- The standard Gaussian as a probability measure. -/
noncomputable def stdGaussianPM : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩

/-- **Central limit theorem for Poisson laws.** -/
theorem tendsto_poissonFluct {r : ℕ → ℝ≥0} (hr : Tendsto (fun n => (r n : ℝ)) atTop atTop) :
    Tendsto (fun n => poissonFluctPM (r n)) atTop (𝓝 stdGaussianPM) := by
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro u
  simp only [poissonFluctPM, stdGaussianPM, ProbabilityMeasure.coe_mk, charFun_poissonFluct,
    charFun_gaussianReal]
  have h := ((tendsto_poisson_exponent u).comp hr)
  have hc := (Complex.continuous_exp.tendsto _).comp h
  convert hc using 2 <;> first | rfl | (congr 1; push_cast; ring)

end CRNT
