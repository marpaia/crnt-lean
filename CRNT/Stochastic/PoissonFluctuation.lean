import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Scaled Poisson fluctuation `L²` bound

The fluctuation residual of Kurtz's law of large numbers (carried as the isolated hypothesis
`hfluct` in `CRNT.Stochastic.KurtzFluidLimit`) is driven by the centered count of a unit-rate
Poisson process evaluated at the total reaction intensity `Λ = V · a`, rescaled by the volume
`V`. This module establishes the second-moment estimate that makes that residual vanish: the
variance of a single scaled centered Poisson term is `a / V`, so it tends to `0` as `V → ∞`,
and Chebyshev's inequality turns this into convergence in probability.

The development is self-contained probability over the count space `ℕ` with the Poisson law
`Po(r)` (`ProbabilityTheory.poissonMeasure`). Mathlib carries no mean or variance of the
Poisson distribution, so both are proved here:

* `integral_id_poissonMeasure` : `E[N] = r`, the first moment.
* `integral_sq_poissonMeasure` : `E[N²] = r² + r`, the second moment.
* `variance_id_poissonMeasure` : `Var[N] = r`, from `Var = E[N²] − E[N]²`.

The scaling consequences feed the fluid limit:

* `variance_scaled_poisson` : the count rescaled by `V`, with intensity `r = V · a`, has
  variance `a / V`.
* `meas_scaled_centered_poisson_ge_le` : Chebyshev tail
  `Po(V·a){ |N/V − a| ≥ δ } ≤ a / (V · δ²)`.
* `tendsto_meas_scaled_centered_poisson` : that tail tends to `0` as `V → ∞`, i.e. the scaled
  centered count converges to its mean `a` in probability — the first concrete discharge step
  of the `η_V → 0` fluctuation hypothesis.

The full multi-reaction sum and the random time change of the Poisson clocks are a later
development; a single scaled term carries the variance order `O(1/V)` exhibited here.
-/

namespace CRNT.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-- The exponential series as an unconditional sum over `ℝ`: `∑' n, x ^ n / n! = exp x`. -/
private theorem hasSum_exp_div_factorial (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / n.factorial) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-! ## Moments of the Poisson distribution -/

/-- The first-moment summand reindexes (after dropping the zero term) to a multiple of the
exponential series: `e^{-r} r^{k+1}/(k+1)! · (k+1) = (e^{-r} r) · (r^k / k!)`. -/
private theorem pmf_mul_id_succ (r : ℝ≥0) (k : ℕ) :
    Real.exp (-r) * (r : ℝ) ^ (k + 1) / (k + 1).factorial * ((k : ℝ) + 1)
      = (Real.exp (-r) * (r : ℝ)) * ((r : ℝ) ^ k / k.factorial) := by
  have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * k.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hfac_ne : ((k + 1).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (k + 1)).ne'
  have hk_ne : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hkf_ne : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [hfac, pow_succ]
  field_simp

private theorem summable_pmf_mul_id (r : ℝ≥0) :
    Summable (fun n : ℕ => Real.exp (-r) * (r : ℝ) ^ n / n.factorial * n) := by
  have hshift : Summable (fun k : ℕ =>
      Real.exp (-r) * (r : ℝ) * ((r : ℝ) ^ k / k.factorial)) :=
    ((hasSum_exp_div_factorial (r : ℝ)).summable.mul_left _)
  refine (summable_nat_add_iff 1).mp ?_
  refine hshift.congr (fun k => ?_)
  have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hc, pmf_mul_id_succ r k]

/-- **The first moment of the Poisson distribution: `E[N] = r`.** -/
theorem integral_id_poissonMeasure (r : ℝ≥0) :
    ∫ n, (n : ℝ) ∂(poissonMeasure r) = r := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  -- The `n = 0` term vanishes; reindex `n = k + 1`.
  rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr (summable_pmf_mul_id r))]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  have hcongr : (fun k : ℕ =>
        Real.exp (-r) * (r : ℝ) ^ (k + 1) / ((k + 1 : ℕ).factorial) * ((k + 1 : ℕ) : ℝ))
      = fun k : ℕ => (Real.exp (-r) * (r : ℝ)) * ((r : ℝ) ^ k / k.factorial) := by
    funext k
    have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hc, pmf_mul_id_succ r k]
  rw [hcongr, tsum_mul_left, (hasSum_exp_div_factorial (r : ℝ)).tsum_eq, Real.exp_neg]
  field_simp

/-- The falling-factorial summand reindexes (after dropping the two zero terms) to a multiple of
the exponential series: `e^{-r} r^{k+2}/(k+2)! · (k+2)(k+1) = (e^{-r} r²) · (r^k / k!)`. -/
private theorem pmf_mul_fall_succ (r : ℝ≥0) (k : ℕ) :
    Real.exp (-r) * (r : ℝ) ^ (k + 2) / (k + 2).factorial
        * (((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) - 1))
      = (Real.exp (-r) * (r : ℝ) ^ 2) * ((r : ℝ) ^ k / k.factorial) := by
  have hfac : ((k + 2).factorial : ℝ) = ((k : ℝ) + 2) * ((k : ℝ) + 1) * k.factorial := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have hkk : (((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) - 1)) = ((k : ℝ) + 2) * ((k : ℝ) + 1) := by
    push_cast; ring
  have hk2_ne : ((k : ℝ) + 2) ≠ 0 := by positivity
  have hk1_ne : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hkf_ne : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  rw [hkk, hfac, pow_add]
  field_simp

/-- The falling-factorial weighted series `n ↦ e^{-r} r^n/n! · n(n-1)` is summable. -/
private theorem summable_pmf_mul_fall (r : ℝ≥0) :
    Summable (fun n : ℕ =>
      Real.exp (-r) * (r : ℝ) ^ n / n.factorial * ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hshift : Summable (fun k : ℕ =>
      Real.exp (-r) * (r : ℝ) ^ 2 * ((r : ℝ) ^ k / k.factorial)) :=
    ((hasSum_exp_div_factorial (r : ℝ)).summable.mul_left _)
  refine (summable_nat_add_iff 2).mp ?_
  refine hshift.congr (fun k => ?_)
  exact (pmf_mul_fall_succ r k).symm

/-- **Summability of the second moment series.** -/
private theorem summable_pmf_mul_sq (r : ℝ≥0) :
    Summable (fun n : ℕ => Real.exp (-r) * (r : ℝ) ^ n / n.factorial * n ^ 2) := by
  -- `n² = n(n-1) + n`; both pieces reduce to shifted exp series.
  have hsum := (summable_pmf_mul_fall r).add (summable_pmf_mul_id r)
  refine hsum.congr (fun n => ?_)
  have : ((n : ℝ) * ((n : ℝ) - 1)) + (n : ℝ) = (n : ℝ) ^ 2 := by ring
  rw [← mul_add, this]

/-- **The second moment of the Poisson distribution: `E[N²] = r² + r`.** -/
theorem integral_sq_poissonMeasure (r : ℝ≥0) :
    ∫ n, (n : ℝ) ^ 2 ∂(poissonMeasure r) = (r : ℝ) ^ 2 + r := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  -- Split `n² = n(n-1) + n` under the sum.
  have hsplit : (fun n : ℕ => Real.exp (-r) * (r : ℝ) ^ n / n.factorial * (n : ℝ) ^ 2)
      = fun n : ℕ => Real.exp (-r) * (r : ℝ) ^ n / n.factorial * ((n : ℝ) * ((n : ℝ) - 1))
        + Real.exp (-r) * (r : ℝ) ^ n / n.factorial * (n : ℝ) := by
    funext n; rw [← mul_add]; ring_nf
  rw [hsplit]
  rw [(summable_pmf_mul_fall r).tsum_add (summable_pmf_mul_id r)]
  -- The falling-factorial sum equals `r²`: drop the two zero terms, reindex `n = k + 2`.
  have hfall_eq : ∑' n : ℕ,
      Real.exp (-r) * (r : ℝ) ^ n / n.factorial * ((n : ℝ) * ((n : ℝ) - 1)) = (r : ℝ) ^ 2 := by
    have heq2 : ∑' n : ℕ,
        Real.exp (-r) * (r : ℝ) ^ n / n.factorial * ((n : ℝ) * ((n : ℝ) - 1))
        = ∑' k : ℕ, Real.exp (-r) * (r : ℝ) ^ (k + 2) / (k + 2).factorial
            * (((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) - 1)) := by
      rw [← (summable_pmf_mul_fall r).sum_add_tsum_nat_add 2]
      have hzero : ∑ i ∈ Finset.range 2, Real.exp (-r) * (r : ℝ) ^ i / i.factorial
          * (((i : ℕ) : ℝ) * (((i : ℕ) : ℝ) - 1)) = 0 := by
        rw [Finset.sum_range_succ, Finset.sum_range_one]; norm_num
      rw [hzero, zero_add]
    rw [heq2]
    have hcongr : (fun k : ℕ => Real.exp (-r) * (r : ℝ) ^ (k + 2) / (k + 2).factorial
          * (((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) - 1)))
        = fun k : ℕ => (Real.exp (-r) * (r : ℝ) ^ 2) * ((r : ℝ) ^ k / k.factorial) := by
      funext k; rw [pmf_mul_fall_succ r k]
    rw [hcongr, tsum_mul_left, (hasSum_exp_div_factorial (r : ℝ)).tsum_eq, Real.exp_neg]
    field_simp
  rw [hfall_eq]
  -- The linear sum equals `r` (the first moment, modulo the `integral_poissonMeasure` rewrite).
  have hid_eq : ∑' n : ℕ, Real.exp (-r) * (r : ℝ) ^ n / n.factorial * (n : ℝ) = (r : ℝ) := by
    have h := integral_id_poissonMeasure r
    rwa [integral_poissonMeasure, show (fun n : ℕ => (Real.exp (-r) * (r : ℝ) ^ n / n.factorial)
      • (n : ℝ)) = (fun n : ℕ => Real.exp (-r) * (r : ℝ) ^ n / n.factorial * (n : ℝ)) from by
        funext n; rw [smul_eq_mul]] at h
  rw [hid_eq]

/-! ## `L²` membership and the variance identity -/

/-- The real-valued count coordinate is square-integrable under `Po(r)`. -/
theorem memLp_two_id_poissonMeasure (r : ℝ≥0) :
    MemLp (fun n : ℕ => (n : ℝ)) 2 (poissonMeasure r) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  rw [integrable_poissonMeasure_iff]
  refine (summable_pmf_mul_sq r).congr (fun n => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- **The variance of the Poisson distribution: `Var[N] = r`.** Computed from the first and
second moments via `Var = E[N²] − E[N]²`. -/
theorem variance_id_poissonMeasure (r : ℝ≥0) :
    variance (fun n : ℕ => (n : ℝ)) (poissonMeasure r) = r := by
  rw [variance_eq_sub (memLp_two_id_poissonMeasure r)]
  have hsq : ∫ n, ((fun n : ℕ => (n : ℝ)) ^ 2) n ∂(poissonMeasure r)
      = (r : ℝ) ^ 2 + r := by
    simp only [Pi.pow_apply]
    exact integral_sq_poissonMeasure r
  rw [hsq, integral_id_poissonMeasure]
  ring

/-! ## Scaled fluctuation bounds -/

/-- **Variance of the volume-scaled count.** Scaling the count by `1 / V` divides its variance
by `V²`: `Var[N / V] = r / V²` for `N ∼ Po(r)`. -/
theorem variance_scaled_id_poissonMeasure (r : ℝ≥0) (V : ℝ) :
    variance (fun n : ℕ => (n : ℝ) / V) (poissonMeasure r) = (r : ℝ) / V ^ 2 := by
  have hsmul : (fun n : ℕ => (n : ℝ) / V) = fun n : ℕ => V⁻¹ * (n : ℝ) := by
    funext n; rw [div_eq_inv_mul]
  rw [hsmul, variance_const_mul, variance_id_poissonMeasure]
  rw [inv_pow, inv_mul_eq_div]

/-- **The `O(1/V)` second-moment bound for the volume-scaled centered Poisson term.** With total
intensity `r = V · a` (a fixed per-volume rate `a`), the volume-scaled count has variance
`(V · a) / V² = a / V`, which vanishes as `V → ∞`. This is the variance order that drives the
Kurtz fluctuation residual to zero. -/
theorem variance_scaled_intensity_poissonMeasure {V : ℝ} (hV : 0 < V) (a : ℝ≥0) :
    variance (fun n : ℕ => (n : ℝ) / V)
        (poissonMeasure (NNReal.mk V hV.le * a)) = (a : ℝ) / V := by
  rw [variance_scaled_id_poissonMeasure]
  have hcoe : ((NNReal.mk V hV.le * a : ℝ≥0) : ℝ) = V * a := by
    rw [NNReal.coe_mul]; rfl
  rw [hcoe, sq]
  field_simp

/-! ## Convergence in probability via Chebyshev -/

/-- **Chebyshev tail for the scaled centered Poisson term.** With total intensity `r = V · a`,
the volume-scaled count `N / V` deviates from its mean `a` by at least `δ > 0` with probability
at most `a / (V · δ²)`:

  `Po(V·a){ ω | δ ≤ |N(ω)/V − a| } ≤ a / (V · δ²)`.

This is Chebyshev's inequality applied to the `O(1/V)` variance bound. -/
theorem meas_scaled_centered_poisson_ge_le {V : ℝ} (hV : 0 < V) (a : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    (poissonMeasure (NNReal.mk V hV.le * a))
        {n : ℕ | δ ≤ |(n : ℝ) / V - a|} ≤ ENNReal.ofReal ((a : ℝ) / (V * δ ^ 2)) := by
  have hcoe : ((NNReal.mk V hV.le * a : ℝ≥0) : ℝ) = V * a := by
    rw [NNReal.coe_mul]; rfl
  have hsmul : (fun n : ℕ => (n : ℝ) / V) = fun n : ℕ => V⁻¹ * (n : ℝ) := by
    funext n; rw [div_eq_inv_mul]
  have hmean : ∫ n, ((n : ℝ) / V) ∂(poissonMeasure (NNReal.mk V hV.le * a)) = a := by
    rw [hsmul, integral_const_mul, integral_id_poissonMeasure, hcoe]
    field_simp
  have hMemLp : MemLp (fun n : ℕ => (n : ℝ) / V) 2
      (poissonMeasure (NNReal.mk V hV.le * a)) := by
    rw [memLp_two_iff_integrable_sq (by fun_prop), integrable_poissonMeasure_iff]
    refine ((summable_pmf_mul_sq (NNReal.mk V hV.le * a)).mul_left (V⁻¹ ^ 2)).congr (fun n => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow]
    field_simp
  have hcheb := meas_ge_le_variance_div_sq hMemLp hδ
  rw [hmean, variance_scaled_intensity_poissonMeasure hV a] at hcheb
  refine le_trans hcheb (le_of_eq ?_)
  congr 1
  rw [div_div]

/-- **Convergence in probability of the scaled centered Poisson term.** Along any filter on the
volume index where `V → ∞`, the deviation probability `Po(V·a){ |N/V − a| ≥ δ }` tends to `0`
for every threshold `δ > 0`. This is the first concrete discharge of the `η_V → 0` fluctuation
hypothesis isolated in `CRNT.Stochastic.KurtzFluidLimit`: a single scaled Poisson term obeys a
law of large numbers, converging to its per-volume intensity `a`. -/
theorem tendsto_meas_scaled_centered_poisson {ι : Type*} {ℓ : Filter ι} {V : ι → ℝ}
    (hVpos : ∀ i, 0 < V i) (hV : Filter.Tendsto V ℓ Filter.atTop) (a : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun i => (poissonMeasure (⟨V i, (hVpos i).le⟩ * a))
        {n : ℕ | δ ≤ |(n : ℝ) / V i - a|}) ℓ (nhds 0) := by
  -- Squeeze the tail between `0` and the vanishing bound `a / (V · δ²)`.
  have hbound : ∀ i, (poissonMeasure (⟨V i, (hVpos i).le⟩ * a))
      {n : ℕ | δ ≤ |(n : ℝ) / V i - a|}
        ≤ ENNReal.ofReal ((a : ℝ) / (V i * δ ^ 2)) :=
    fun i => meas_scaled_centered_poisson_ge_le (hVpos i) a hδ
  have htop : Filter.Tendsto (fun i => ENNReal.ofReal ((a : ℝ) / (V i * δ ^ 2))) ℓ (nhds 0) := by
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from (ENNReal.ofReal_zero).symm]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have hdenom : Filter.Tendsto (fun i => V i * δ ^ 2) ℓ Filter.atTop :=
      hV.atTop_mul_const (by positivity)
    have := (hdenom.inv_tendsto_atTop).const_mul (a : ℝ)
    rw [mul_zero] at this
    refine this.congr (fun i => ?_)
    simp only [Pi.inv_apply]
    rw [div_eq_mul_inv]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
    (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall hbound)

end CRNT.Stochastic
