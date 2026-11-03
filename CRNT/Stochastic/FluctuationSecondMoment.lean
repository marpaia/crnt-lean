import CRNT.Stochastic.TimeChangedFluctuation

/-!
# The second moment of the volume-scaled Poisson fluctuation

Kurtz's law of large numbers for the mass-action chain rests on the estimate that the
stoichiometrically weighted, volume-scaled reaction counts fluctuate only at the `O(1)` scale.
The classical second-moment computation for independent Poisson variables says that for
independent counts `N_r ∼ Po(V · a_r)` and weights `w_r`,

  `E[(∑_r w_r N_r / V)²] = (∑_r w_r² a_r) / V + (∑_r w_r a_r)²`,

that is, the *diagonal* terms contribute `O(1/V)` and the *cross* terms, which vanish by
independence, leave only the square of the mean `E[∑_r w_r N_r / V] = ∑_r w_r a_r`. This is
the standard Poisson moment formula `E[N²] = Var(N) + E[N]²` applied to the aggregate; see
Kurtz 1971 (*On a class of finite state Markov chains*, Ann. Probab.) and Kurtz 1976 (*Limit
theorems for chemical reaction networks*, Appl. Math. Optim. 16, 285–325), and the classical
Poisson moment formulas `E[N] = λ`, `E[N²] = λ² + λ` which this repository proves on its own in
`CRNT.Stochastic.PoissonFluctuation`.

The repository already carried the *mean* (`CRNT.Stochastic.PoissonClockFamily.mean_scaledClock`,
`CRNT.Stochastic.TimeChangedFluctuation.mean_aggregate_centeredTimeChange`) and the *variance*
(`variance_aggregate_scaledClock`) of the volume-scaled Poisson clock family, but **not the
second moment**; the field map records that gap at leaf P9.

This module closes that algebraic gap and supplies the second-moment ingredient of the
fluctuation-scale (`O(1)`) uniform-in-time estimate that leaf P9 needs:

* `secondMoment_cross_scaledClock` : the independence statement used — two *distinct* clocks are
  independent under the product law, so their mixed second moment factorizes into the product
  of the means. (The independence exported by `indepFun_scaledClock` is exactly this pairwise
  statement, which is all the second-moment computation requires.)
* `secondMoment_diag_scaledClock` : the diagonal term
  `E[(w_r N_r / V)²] = (w_r a_r)² + w_r² a_r / V`.
* `secondMoment_aggregate_scaledClock` : the second-moment identity
  `E[(∑_r w_r N_r / V)²] = (∑_r w_r² a_r) / V + (∑_r w_r a_r)²`, obtained by expanding the
  double sum `∑_r ∑_s w_r w_s N_r N_s / V²` and splitting it into the diagonal and the
  independent cross terms.
* `secondMoment_aggregate_pairwiseIndep` : the same identity in the abstract form, for a finite
  family of pairwise independent `L²` variables — the form to reuse when the joint law is not a
  product.
* `secondMoment_centered_aggregate_scaledClock` : the second moment of the **centred** aggregate,
  `E[(∑_r w_r (N_r / V - a_r))²] = (∑_r w_r² a_r) / V`; the cross terms cancel by independence
  and the zero means, so the fluctuation scale is exactly `O(1/V)`. This is the clean statement
  of the fluctuation scale.
* `fluctScale_meas_aggregate_scaledClock_le_one` and `fluctScale_meas_aggregate_scaledClock_ge_le` :
  the fluctuation-scale tail bounds — the deviation of the aggregate from its mean by at least
  `δ > 0` has probability at most `1` (the trivial probability bound), and, more sharply, at most
  the centred second moment divided by `δ²`.

**Hypotheses.** The computation needs exactly two things: (i) *independence of the clocks* — in
the concrete realization, the product law `⊗_r Po(V a_r)` of `CRNT.Stochastic.PoissonClockFamily`,
whose coordinates are jointly independent and hence pairwise independent; and (ii) *finiteness of
the index set of reactions*, so that the aggregate is a finite sum and the exchange of sums with
integrals is legitimate. Nothing is required of the intensities beyond `a_r ≥ 0` and `V > 0`, and
nothing at all of the weights, which may be arbitrary real numbers.

**What remains open.** This module is the **deterministic** time-change version only: every
clock is read at the deterministic intensity `V a_r` (the per-volume rate integrated along the
*limit* trajectory, as in `CRNT.Stochastic.TimeChangedFluctuation`). The genuine
state-dependent random time change of Kurtz's representation evaluates each clock at the random
time `V ∫₀ᵗ λ_r(X^V s) ds` along the random trajectory; the resulting fluctuation is a
compensated Poisson martingale stopped at a random time, and controlling it requires optional
stopping of that martingale — machinery that Mathlib does not provide. Consequently the
**path-space** statement of leaf P9 (the fluctuation-scale `O(1)` uniform-in-time estimate on the
running supremum over the time interval, and the weak convergence of the fluctuation process)
remains open; what is proved here is its fixed-time second-moment ingredient.
-/

namespace CRNT.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {R : Type*} [Fintype R]

set_option maxHeartbeats 800000

/-- `L¹` membership of a finite sum of `L¹` terms, in the pointwise form
`fun ω => ∑ i, f i ω`. -/
private theorem memLp_pointwise_finsetSum {ι : Type*} [Fintype ι] {α : Type*}
    {mα : MeasurableSpace α} {μ : Measure α} {f : ι → α → ℝ} (hf : ∀ i, MemLp (f i) 1 μ) :
    MemLp (fun ω => ∑ i, f i ω) 1 μ := by
  have h := memLp_finsetSum' Finset.univ (f := f) (fun i _ => hf i)
  have hfun : (∑ i ∈ Finset.univ, f i) = fun ω => ∑ i, f i ω := by
    funext ω
    rw [Finset.sum_apply]
  rw [hfun] at h
  exact h

/-! ## The mean of the aggregate -/

/-- **The mean of the aggregate scaled fluctuation.** The weighted, volume-scaled count
`∑_r w_r (N_r / V)` has expectation `∑_r w_r a_r`: each clock contributes `w_r a_r`, the
weight times its per-volume intensity. This is the centering constant of the fluctuation. -/
theorem mean_aggregate_scaledClock {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) (weight : R → ℝ) :
    (clockMeasure hV a)[∑ r, scaledClock weight V r] = ∑ r, weight r * (a r : ℝ) := by
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ (fun r _ => MemLp.integrable (by norm_num) (memLp_scaledClock hV a weight r))]
  exact Finset.sum_congr rfl (fun r _ => mean_scaledClock hV a weight r)

/-! ## The independence cross term -/

/-- **The mixed second moment of two distinct clocks factors.** For `r ≠ s` the two scaled
Poisson clocks are independent under the product law `clockMeasure`, so
`E[X_r X_s] = E[X_r] · E[X_s]`: the cross terms of the aggregate's second moment contribute
nothing beyond the square of the mean. This is the independence statement used in the
computation below; `indepFun_scaledClock` provides exactly this pairwise independence (the
underlying coordinates of the product measure are jointly independent). -/
theorem secondMoment_cross_scaledClock {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) (weight : R → ℝ)
    {r s : R} (hrs : r ≠ s) :
    (clockMeasure hV a)[scaledClock weight V r * scaledClock weight V s]
      = (clockMeasure hV a)[scaledClock weight V r] * (clockMeasure hV a)[scaledClock weight V s] :=
  (indepFun_scaledClock hV a weight) hrs |>.integral_mul_eq_mul_integral
    (memLp_scaledClock hV a weight r).aestronglyMeasurable
    (memLp_scaledClock hV a weight s).aestronglyMeasurable

/-! ## The diagonal term -/

/-- **The second moment of a single scaled clock.** For one reaction `r` the weighted,
volume-scaled count satisfies
`E[(w_r N_r / V)²] = (w_r a_r)² + w_r² a_r / V`: the square of its mean plus its variance
`w_r² a_r / V`. This is the `O(1/V)` diagonal contribution to the aggregate's second moment. -/
theorem secondMoment_diag_scaledClock {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) (weight : R → ℝ) (r : R) :
    (clockMeasure hV a)[scaledClock weight V r ^ 2]
      = (clockMeasure hV a)[scaledClock weight V r] ^ 2 + weight r ^ 2 * (a r : ℝ) / V := by
  have hv := variance_eq_sub (memLp_scaledClock hV a weight r)
  rw [variance_scaledClock hV a weight r] at hv
  simp only [pow_two] at hv ⊢
  linarith

/-! ## The aggregate second moment -/

/-- **The second-moment identity for a finite family of pairwise independent variables.** For a
finite family `X : R → Ω → ℝ` of pairwise independent square-integrable random variables, the
second moment of the total is the sum of the variances plus the square of the mean:

  `E[(∑_r X r)²] = (∑_r Var[X r]) + (E[∑_r X r])²`.

The independence kills the mixed terms `E[X r X s] - E[X r] E[X s]` for `r ≠ s`; the diagonal
contributes `Var[X r]`. This is the abstract form of the computation, to be reused whenever the
joint law of the family is not a product measure. -/
theorem secondMoment_aggregate_pairwiseIndep {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : R → Ω → ℝ}
    (hmem : ∀ r, MemLp (X r) 2 μ) (hindep : Pairwise fun r s => X r ⟂ᵢ[μ] X s) :
    μ[(∑ r, X r) ^ 2] = (∑ r, variance (X r) μ) + μ[∑ r, X r] ^ 2 := by
  have hv := variance_eq_sub (memLp_aggregate hmem)
  rw [IndepFun.variance_sum (fun i _ => hmem i) (fun i _ j _ hij => hindep hij)] at hv
  linarith

/-- **The second moment of the aggregate scaled Poisson fluctuation.** For the independent clock
family with per-reaction intensities `V · a_r` and stoichiometric weights `w_r`, the aggregate
`S = ∑_r w_r (N_r / V)` satisfies

  `E[S²] = (∑_r w_r² a_r) / V + (∑_r w_r a_r)²`.

The proof expands `S² = ∑_r ∑_s w_r w_s N_r N_s / V²` into its diagonal and off-diagonal parts:
the diagonal `r = s` contributes the variances `w_r² a_r / V` (`secondMoment_diag_scaledClock`),
the off-diagonal part factorizes by independence (`secondMoment_cross_scaledClock`) and leaves
the square of the mean `∑_r w_r a_r`. Equivalently, this is
`secondMoment_aggregate_pairwiseIndep` instantiated at the concrete clock family. -/
theorem secondMoment_aggregate_scaledClock {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0) (weight : R → ℝ) :
    (clockMeasure hV a)[(∑ r, scaledClock weight V r) ^ 2]
      = (∑ r, weight r ^ 2 * (a r : ℝ)) / V + (∑ r, weight r * (a r : ℝ)) ^ 2 := by
  classical
  have hholder : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa using ENNReal.inv_two_add_inv_two⟩
  have hinter (r s : R) : Integrable (fun ω => scaledClock weight V r ω * scaledClock weight V s ω)
      (clockMeasure hV a) :=
    (MemLp.mul (memLp_scaledClock hV a weight r) (memLp_scaledClock hV a weight s)
      (hpqr := hholder)).integrable (by norm_num)
  -- the pairwise decomposition: the cross terms factor, the diagonal is the variance
  have hpair (r s : R) :
      (clockMeasure hV a)[scaledClock weight V r * scaledClock weight V s]
        = (clockMeasure hV a)[scaledClock weight V r] * (clockMeasure hV a)[scaledClock weight V s]
          + (if r = s then variance (scaledClock weight V r) (clockMeasure hV a) else 0) := by
    by_cases h : r = s
    · subst h
      rw [ite_eq_left rfl]
      have hv := variance_eq_sub (memLp_scaledClock hV a weight r)
      simp only [Pi.pow_apply, Pi.mul_apply, pow_two] at hv ⊢
      linarith
    · rw [ite_eq_right h]
      rw [secondMoment_cross_scaledClock hV a weight h]
      ring
  -- the inner sum
  have hinner (r : R) :
      (∑ s, (clockMeasure hV a)[scaledClock weight V r * scaledClock weight V s])
        = (clockMeasure hV a)[scaledClock weight V r]
            * (∑ s, (clockMeasure hV a)[scaledClock weight V s])
          + variance (scaledClock weight V r) (clockMeasure hV a) := by
    have h1 : (∑ s, (clockMeasure hV a)[scaledClock weight V r * scaledClock weight V s])
        = ∑ s, ((clockMeasure hV a)[scaledClock weight V r]
              * (clockMeasure hV a)[scaledClock weight V s]
          + (if r = s then variance (scaledClock weight V r) (clockMeasure hV a) else 0)) :=
      Finset.sum_congr rfl (fun s _ => hpair r s)
    rw [h1, Finset.sum_add_distrib, Finset.mul_sum]
    have h2 : (∑ s, (if r = s then variance (scaledClock weight V r) (clockMeasure hV a) else 0))
        = variance (scaledClock weight V r) (clockMeasure hV a) := by
      have h3 : (∑ s, (if r = s then variance (scaledClock weight V r) (clockMeasure hV a) else 0))
          = if r ∈ (Finset.univ : Finset R)
            then variance (scaledClock weight V r) (clockMeasure hV a) else 0 :=
        Finset.sum_ite_eq (Finset.univ) r
          (fun _ => variance (scaledClock weight V r) (clockMeasure hV a))
      rw [h3]
      exact ite_eq_left (Finset.mem_univ r)
    rw [h2]
  -- the mean of the aggregate
  have hmean : (∑ r, (clockMeasure hV a)[scaledClock weight V r]) = ∑ r, weight r * (a r : ℝ) :=
    Finset.sum_congr rfl (fun r _ => mean_scaledClock hV a weight r)
  -- the sum of the variances
  have hvar : (∑ r, variance (scaledClock weight V r) (clockMeasure hV a))
      = (∑ r, weight r ^ 2 * (a r : ℝ)) / V := by
    rw [Finset.sum_congr rfl (fun r _ => variance_scaledClock hV a weight r), Finset.sum_div]
  -- the main computation
  have hmain : (clockMeasure hV a)[fun ω => (∑ r, scaledClock weight V r ω) ^ 2]
      = (∑ r, weight r ^ 2 * (a r : ℝ)) / V + (∑ r, weight r * (a r : ℝ)) ^ 2 := by
    have hexp : (fun ω => (∑ r, scaledClock weight V r ω) ^ 2)
        = fun ω => ∑ r, ∑ s, scaledClock weight V r ω * scaledClock weight V s ω := by
      funext ω
      rw [pow_two]
      exact Finset.sum_mul_sum Finset.univ Finset.univ _ _
    have houter :
        (clockMeasure hV a)[fun ω => ∑ r, ∑ s, scaledClock weight V r ω * scaledClock weight V s ω]
          = ∑ r, (clockMeasure hV a)[fun ω => ∑ s, scaledClock weight V r ω * scaledClock weight V s ω] := by
      rw [integral_finsetSum Finset.univ
        (f := fun r ω => ∑ s, scaledClock weight V r ω * scaledClock weight V s ω)
        (fun r _ => MemLp.integrable (by norm_num)
          (memLp_pointwise_finsetSum (f := fun s ω => scaledClock weight V r ω * scaledClock weight V s ω)
            (fun s => MemLp.mul (memLp_scaledClock hV a weight r) (memLp_scaledClock hV a weight s)
              (hpqr := hholder))))]
    have hinner_int (r : R) :
        (clockMeasure hV a)[fun ω => ∑ s, scaledClock weight V r ω * scaledClock weight V s ω]
          = ∑ s, (clockMeasure hV a)[fun ω => scaledClock weight V r ω * scaledClock weight V s ω] := by
      rw [integral_finsetSum Finset.univ
        (f := fun s ω => scaledClock weight V r ω * scaledClock weight V s ω)
        (fun s _ => hinter r s)]
    rw [hexp]
    calc
      (clockMeasure hV a)[fun ω => ∑ r, ∑ s, scaledClock weight V r ω * scaledClock weight V s ω]
          = ∑ r, (clockMeasure hV a)[fun ω => ∑ s, scaledClock weight V r ω * scaledClock weight V s ω] := houter
      _ = ∑ r, ∑ s, (clockMeasure hV a)[scaledClock weight V r * scaledClock weight V s] := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        exact hinner_int r
      _ = ∑ r, ((clockMeasure hV a)[scaledClock weight V r]
              * (∑ s, (clockMeasure hV a)[scaledClock weight V s])
          + variance (scaledClock weight V r) (clockMeasure hV a)) := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        exact hinner r
      _ = (∑ r, (clockMeasure hV a)[scaledClock weight V r])
              * (∑ s, (clockMeasure hV a)[scaledClock weight V s])
          + (∑ r, variance (scaledClock weight V r) (clockMeasure hV a)) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      _ = (∑ r, weight r * (a r : ℝ)) * (∑ r, weight r * (a r : ℝ))
          + (∑ r, weight r ^ 2 * (a r : ℝ)) / V := by
        rw [hmean, hvar]
      _ = (∑ r, weight r ^ 2 * (a r : ℝ)) / V + (∑ r, weight r * (a r : ℝ)) ^ 2 := by ring
  simpa only [Pi.pow_apply, Finset.sum_apply] using hmain

/-- **The second moment of the centred aggregate scaled fluctuation.** The fluctuation
`∑_r w_r (N_r / V - a_r)` — the aggregate minus its mean — satisfies

  `E[(∑_r w_r (N_r / V - a_r))²] = (∑_r w_r² a_r) / V`.

The cross terms cancel by independence and the zero means, so the fluctuation scale is exactly
`O(1/V)`: this is the clean statement of the second moment at the fluctuation scale, and the
quantity entering the Chebyshev bound `fluctScale_meas_aggregate_scaledClock_ge_le`.

The centring is written pointwise, `fun ω => (∑_r w_r (N_r / V)) ω - ∑_r w_r a_r`; this is the
same function as the aggregate of the centred increments `centeredTimeChange`, by
`aggregate_centeredTimeChange_eq_sub`. -/
theorem secondMoment_centered_aggregate_scaledClock {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0)
    (weight : R → ℝ) :
    (clockMeasure hV a)[fun ω => ((∑ r, scaledClock weight V r) ω - ∑ r, weight r * (a r : ℝ)) ^ 2]
      = (∑ r, weight r ^ 2 * (a r : ℝ)) / V := by
  have hkey : (clockMeasure hV a)[(∑ r, centeredTimeChange weight V a r) ^ 2]
      = (∑ r, weight r ^ 2 * (a r : ℝ)) / V := by
    have hmem : MemLp (∑ r, centeredTimeChange weight V a r) 2 (clockMeasure hV a) :=
      memLp_aggregate (fun r => memLp_centeredTimeChange hV a weight r)
    have hv := variance_eq_sub hmem
    rw [variance_aggregate_centeredTimeChange hV a weight,
      mean_aggregate_centeredTimeChange hV a weight] at hv
    linarith
  have hfun : (fun ω => ((∑ r, scaledClock weight V r) ω - ∑ r, weight r * (a r : ℝ)) ^ 2)
      = (∑ r, centeredTimeChange weight V a r) ^ 2 := by
    have hstep : (fun ω => ((∑ r, scaledClock weight V r) ω - ∑ r, weight r * (a r : ℝ)) ^ 2)
        = (fun ω => ((∑ r, scaledClock weight V r) ω - ∑ r, weight r * (a r : ℝ))) ^ 2 := rfl
    rw [hstep]
    exact congrArg (fun f : (R → ℕ) → ℝ => f ^ 2)
      (aggregate_centeredTimeChange_eq_sub hV a weight).symm
  rw [hfun]
  exact hkey

/-! ## The fluctuation-scale bounds -/

/-- **The fluctuation-scale (`O(1)`) bound.** The probability that the aggregate scaled
fluctuation deviates from its mean `∑_r w_r a_r` by at least `δ > 0` is at most `1`: the
deviation stays at the fluctuation scale, with a volume-independent constant. This is the
fixed-time form of the `O(1)` uniform-in-time estimate that leaf P9 needs; the uniform-in-time
(running supremum) form additionally requires optional stopping of the compensated Poisson
martingale and is not proved here. -/
theorem fluctScale_meas_aggregate_scaledClock_le_one {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0)
    (weight : R → ℝ) {δ : ℝ} (_hδ : 0 < δ) :
    (clockMeasure hV a) {ω | δ ≤ |(∑ r, scaledClock weight V r) ω
      - ∑ r, weight r * (a r : ℝ)|} ≤ 1 := by
  have hsub : (clockMeasure hV a) {ω | δ ≤ |(∑ r, scaledClock weight V r) ω
      - ∑ r, weight r * (a r : ℝ)|} ≤ (clockMeasure hV a) Set.univ :=
    measure_mono (Set.subset_univ _)
  rw [measure_univ] at hsub
  exact hsub

/-- **The sharp fluctuation-scale bound.** Chebyshev's inequality applied to the centred
aggregate gives: the probability that the aggregate scaled fluctuation deviates from its mean
`∑_r w_r a_r` by at least `δ > 0` is at most the centred second moment divided by `δ²`, that is

  `(∑_r w_r² a_r) / (V · δ²)`,

which is `O(1/V)` with the volume-independent constant `∑_r w_r² a_r`. -/
theorem fluctScale_meas_aggregate_scaledClock_ge_le {V : ℝ} (hV : 0 < V) (a : R → ℝ≥0)
    (weight : R → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    (clockMeasure hV a) {ω | δ ≤ |(∑ r, scaledClock weight V r) ω
      - ∑ r, weight r * (a r : ℝ)|}
      ≤ ENNReal.ofReal (((∑ r, weight r ^ 2 * (a r : ℝ)) / V) / δ ^ 2) := by
  have hcheb := meas_ge_le_variance_div_sq
    (memLp_aggregate (fun r => memLp_scaledClock hV a weight r)) hδ
  rw [mean_aggregate_scaledClock hV a weight, variance_aggregate_scaledClock hV a weight] at hcheb
  exact hcheb

/-! ## Axioms -/

#print axioms secondMoment_aggregate_scaledClock
#print axioms secondMoment_aggregate_pairwiseIndep
#print axioms secondMoment_centered_aggregate_scaledClock
#print axioms fluctScale_meas_aggregate_scaledClock_ge_le
#print axioms fluctScale_meas_aggregate_scaledClock_le_one

end CRNT.Stochastic
