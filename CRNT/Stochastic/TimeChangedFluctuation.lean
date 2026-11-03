import CRNT.Stochastic.PoissonClockFamily

/-!
# Time-changed Poisson fluctuation at a deterministic integrated intensity

Kurtz's random-time-change representation of the scaled mass-action chain is
`X^V(t) = X^V(0) + ∑_r (v_r/V) · N_r(V ∫₀ᵗ λ_r(X^V s) ds)`, with `N_r` independent unit-rate
Poisson processes. The leading-order linearization evaluates each clock at the integrated
intensity along the **limit ODE trajectory** `x`, not the random state: the deterministic time
`Λ_r(t) = V · ∫₀ᵗ λ_r(x_s) ds`. This is the leading term of the fluctuation; the difference from
the genuine state-dependent time change is a higher-order (martingale optional-stopping) residue.

This module carries the per-volume integrated rate `A_r = ∫₀ᵗ λ_r(x_s) ds` as a nonnegative time
function (`A : R → ℝ≥0`), so the deterministic time-change point is `Λ_r = V · A_r`, the intensity
of reaction `r`'s clock in `CRNT.Stochastic.PoissonClockFamily`. Reading the clock there at this
intensity gives the count `N_r ∼ Po(V · A_r)`, and the centered, volume-scaled, stoichiometrically
weighted increment is

  `M_r(ω) = weight_r · (N_r(ω) − V · A_r) / V = scaledClock weight V r ω − weight_r · A_r`.

Centering subtracts the mean `E[scaledClock weight V r] = weight_r · A_r`, so the variance is
unchanged and the existing clock-family bounds apply verbatim:

* `mean_scaledClock` : `E[weight_r · (N_r / V)] = weight_r · A_r`.
* `centeredTimeChange_eq_sub` : the centered increment is the clock minus its mean.
* `variance_centeredTimeChange` : `Var[M_r] = weight_r² · A_r / V`, the realized `O(1/V)` order.
* `variance_aggregate_centeredTimeChange` :
  `Var[∑_r M_r] = (∑_r weight_r² · A_r) / V`, aggregated over the independent clocks.
* `tendsto_meas_aggregate_centeredTimeChange` : the total centered time-changed fluctuation
  converges to `0` in probability as `V → ∞` (Chebyshev on the `O(1/V)` variance).

The bridge to the deterministic fluid-limit skeleton packages the in-probability decay into the
`η_V → 0` shape consumed by `fluidLimit_tendsto_uniformly`:

* `tendsto_timeChanged_fluctuation` : the probability of an aggregate deviation `≥ δ` tends to `0`.
* `exists_timeChanged_fluct_bound` : for each tolerance there is an eventual deviation bound, the
  `η_V → 0` data that the Grönwall envelope of `fluidLimit_tendsto_uniformly` collapses.

Here the time-change point is deterministic. The genuine state-dependent random time change —
evaluating each clock at `V ∫₀ᵗ λ_r(X^V s) ds` along the random trajectory — requires optional
stopping of the compensated Poisson martingale.
-/

namespace CRNT.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {R : Type*} [Fintype R]

/-! ## The centered time-changed increment -/

/-- The mean of the weighted volume-scaled clock under its product law: with `N_r ∼ Po(V · A_r)`,
`E[weight_r · (N_r / V)] = weight_r · A_r`. The integrated intensity `A_r` is the per-volume
deterministic time-change point along the limit trajectory. -/
theorem mean_scaledClock {V : ℝ} (hV : 0 < V) (A : R → ℝ≥0) (weight : R → ℝ) (r : R) :
    (clockMeasure hV A)[scaledClock weight V r] = weight r * (A r : ℝ) := by
  have hcoe : ((clockIntensity hV A r : ℝ≥0) : ℝ) = V * A r := by
    unfold clockIntensity
    change V * (A r : ℝ) = V * (A r : ℝ)
    rfl
  rw [scaledClock_eq_comp]
  simp only [Function.comp_apply]
  rw [← integral_map (φ := fun ω : R → ℕ => ω r) (f := fun n : ℕ => weight r * ((n : ℝ) / V))
    (measurable_pi_apply r).aemeasurable (by fun_prop)]
  rw [map_eval_clockMeasure hV A r, integral_const_mul]
  have hmean : ∫ n, ((n : ℝ) / V) ∂(poissonMeasure (clockIntensity hV A r)) = (A r : ℝ) := by
    have hsmul : (fun n : ℕ => (n : ℝ) / V) = fun n : ℕ => V⁻¹ * (n : ℝ) := by
      funext n; rw [div_eq_inv_mul]
    rw [hsmul, integral_const_mul, integral_id_poissonMeasure, hcoe]
    field_simp
  rw [hmean]

/-- **The centered, volume-scaled, weighted time-changed increment** of reaction `r`'s clock,
evaluated at the deterministic intensity `V · A_r`: `M_r(ω) = weight_r · (N_r(ω) − V · A_r) / V`.
This is the compensated (mean-zero) form of the scaled clock. -/
noncomputable def centeredTimeChange (weight : R → ℝ) (V : ℝ) (A : R → ℝ≥0) (r : R) :
    (R → ℕ) → ℝ :=
  fun ω => weight r * (((ω r : ℝ) - V * A r) / V)

omit [Fintype R] in
/-- The centered increment is the scaled clock minus its mean `weight_r · A_r`. -/
theorem centeredTimeChange_eq_sub {V : ℝ} (hV : 0 < V) (A : R → ℝ≥0) (weight : R → ℝ) (r : R) :
    centeredTimeChange weight V A r
      = fun ω => scaledClock weight V r ω - weight r * (A r : ℝ) := by
  funext ω
  unfold centeredTimeChange scaledClock
  rw [sub_div, mul_sub]
  congr 1
  field_simp

/-! ## Variance of the time-changed increment -/

/-- **The realized `O(1/V)` variance of the centered time-changed increment.** Centering shifts
by a constant, so `Var[M_r] = Var[scaledClock weight V r] = weight_r² · A_r / V`: reaction `r`'s
compensated time-changed fluctuation carries the same vanishing order as the scaled clock. -/
theorem variance_centeredTimeChange {V : ℝ} (hV : 0 < V) (A : R → ℝ≥0) (weight : R → ℝ) (r : R) :
    variance (centeredTimeChange weight V A r) (clockMeasure hV A)
      = weight r ^ 2 * (A r : ℝ) / V := by
  rw [centeredTimeChange_eq_sub hV A weight r,
    variance_sub_const (memLp_scaledClock hV A weight r).aestronglyMeasurable]
  exact variance_scaledClock hV A weight r

/-- `L²` membership of the centered increment, inherited from the scaled clock. -/
theorem memLp_centeredTimeChange {V : ℝ} (hV : 0 < V) (A : R → ℝ≥0) (weight : R → ℝ) (r : R) :
    MemLp (centeredTimeChange weight V A r) 2 (clockMeasure hV A) := by
  rw [centeredTimeChange_eq_sub hV A weight r]
  exact (memLp_scaledClock hV A weight r).sub (memLp_const _)

/-! ## Aggregate time-changed fluctuation -/

/-- The aggregate centered time-changed fluctuation is the aggregate scaled clock minus its mean
`∑_r weight_r · A_r`. -/
theorem aggregate_centeredTimeChange_eq_sub {V : ℝ} (hV : 0 < V) (A : R → ℝ≥0) (weight : R → ℝ) :
    (∑ r, centeredTimeChange weight V A r)
      = fun ω => (∑ r, scaledClock weight V r) ω - ∑ r, weight r * (A r : ℝ) := by
  funext ω
  simp only [Finset.sum_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [centeredTimeChange_eq_sub hV A weight r]

/-- **The self-contained aggregate `O(1/V)` variance of the total time-changed fluctuation.**
Summing the independent compensated clocks, `Var[∑_r M_r] = (∑_r weight_r² · A_r) / V`. The
constant `C = ∑_r weight_r² · A_r` is the stoichiometrically weighted total integrated intensity
along the limit trajectory; centering leaves the variance equal to the scaled-clock aggregate. -/
theorem variance_aggregate_centeredTimeChange {V : ℝ} (hV : 0 < V) (A : R → ℝ≥0) (weight : R → ℝ) :
    variance (∑ r, centeredTimeChange weight V A r) (clockMeasure hV A)
      = (∑ r, weight r ^ 2 * (A r : ℝ)) / V := by
  rw [aggregate_centeredTimeChange_eq_sub hV A weight,
    variance_sub_const (memLp_aggregate (fun r => memLp_scaledClock hV A weight r)).aestronglyMeasurable]
  exact variance_aggregate_scaledClock hV A weight

/-- The aggregate centered time-changed fluctuation has mean `0`: each compensated increment is
centered, so the deviation from its mean is the increment itself. -/
theorem mean_aggregate_centeredTimeChange {V : ℝ} (hV : 0 < V) (A : R → ℝ≥0) (weight : R → ℝ) :
    (clockMeasure hV A)[∑ r, centeredTimeChange weight V A r] = 0 := by
  rw [aggregate_centeredTimeChange_eq_sub hV A weight]
  rw [integral_sub
    (MemLp.integrable (by norm_num) (memLp_aggregate (fun r => memLp_scaledClock hV A weight r)))
    (integrable_const _)]
  rw [integral_const]
  have hsum : (clockMeasure hV A)[∑ r, scaledClock weight V r]
      = ∑ r, weight r * (A r : ℝ) := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _
      (fun r _ => MemLp.integrable (by norm_num) (memLp_scaledClock hV A weight r))]
    exact Finset.sum_congr rfl (fun r _ => mean_scaledClock hV A weight r)
  rw [hsum]
  simp

/-! ## Chebyshev tail and convergence in probability -/

/-- **The self-contained Chebyshev tail of the total time-changed fluctuation.** Since the
aggregate is centered, the deviation of `∑_r M_r` from `0` by at least `δ > 0` has probability at
most `(∑_r weight_r² · A_r) / (V · δ²)`. -/
theorem meas_aggregate_centeredTimeChange_ge_le {V : ℝ} (hV : 0 < V) (A : R → ℝ≥0)
    (weight : R → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (clockMeasure hV A) {ω | δ ≤ |(∑ r, centeredTimeChange weight V A r) ω|}
      ≤ ENNReal.ofReal ((∑ r, weight r ^ 2 * (A r : ℝ)) / (V * δ ^ 2)) := by
  have hcheb := meas_ge_le_variance_div_sq
    (memLp_aggregate (fun r => memLp_centeredTimeChange hV A weight r)) hδ
  rw [variance_aggregate_centeredTimeChange hV A weight,
    mean_aggregate_centeredTimeChange hV A weight] at hcheb
  simp only [sub_zero] at hcheb
  refine le_trans hcheb (le_of_eq ?_)
  congr 1
  rw [div_div]

/-- **Convergence in probability of the total centered time-changed fluctuation.** Along any
filter where `V → ∞`, the probability that the aggregate `∑_r M_r` deviates from `0` by at least
`δ > 0` tends to `0`: the leading-order time-changed fluctuation obeys a law of large numbers, with
volume-independent constant `C = ∑_r weight_r² · A_r`. -/
theorem tendsto_meas_aggregate_centeredTimeChange {ι : Type*} {ℓ : Filter ι} {V : ι → ℝ}
    (hVpos : ∀ i, 0 < V i) (A : R → ℝ≥0) (weight : R → ℝ)
    (hV : Filter.Tendsto V ℓ Filter.atTop) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto
      (fun i => (clockMeasure (hVpos i) A)
        {ω | δ ≤ |(∑ r, centeredTimeChange weight (V i) A r) ω|})
      ℓ (nhds 0) := by
  have hbound : ∀ i, (clockMeasure (hVpos i) A)
      {ω | δ ≤ |(∑ r, centeredTimeChange weight (V i) A r) ω|}
        ≤ ENNReal.ofReal ((∑ r, weight r ^ 2 * (A r : ℝ)) / (V i * δ ^ 2)) :=
    fun i => meas_aggregate_centeredTimeChange_ge_le (hVpos i) A weight hδ
  have htop : Filter.Tendsto
      (fun i => ENNReal.ofReal ((∑ r, weight r ^ 2 * (A r : ℝ)) / (V i * δ ^ 2))) ℓ (nhds 0) := by
    rw [show (0 : ℝ≥0∞) = ENNReal.ofReal 0 from (ENNReal.ofReal_zero).symm]
    refine (ENNReal.continuous_ofReal.tendsto 0).comp ?_
    have hdenom : Filter.Tendsto (fun i => V i * δ ^ 2) ℓ Filter.atTop :=
      hV.atTop_mul_const (by positivity)
    have := (hdenom.inv_tendsto_atTop).const_mul (∑ r, weight r ^ 2 * (A r : ℝ))
    rw [mul_zero] at this
    refine this.congr (fun i => ?_)
    simp only [Pi.inv_apply]
    rw [div_eq_mul_inv]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
    (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall hbound)

/-! ## Bridge to the deterministic fluid-limit skeleton -/

/-- **The `η_V → 0` packaging consumed by the fluid-limit skeleton.** The convergence in
probability of the total time-changed fluctuation supplies, for every tolerance `ε > 0` and every
deviation threshold `δ > 0`, an eventual bound on the fluctuation's tail probability. This is the
in-probability form of the residual `η_V → 0` driving `fluidLimit_tendsto_uniformly`: the
deterministic Grönwall envelope collapses once the time-changed fluctuation vanishes. -/
theorem exists_timeChanged_fluct_bound {ι : Type*} {ℓ : Filter ι} {V : ι → ℝ}
    (hVpos : ∀ i, 0 < V i) (A : R → ℝ≥0) (weight : R → ℝ)
    (hV : Filter.Tendsto V ℓ Filter.atTop) {δ : ℝ} (hδ : 0 < δ)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ i in ℓ, (clockMeasure (hVpos i) A)
        {ω | δ ≤ |(∑ r, centeredTimeChange weight (V i) A r) ω|} < ε := by
  have htend := tendsto_meas_aggregate_centeredTimeChange hVpos A weight hV hδ
  exact (htend.eventually_lt_const hε)

end CRNT.Stochastic
