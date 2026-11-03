import CRNT.Stochastic.KernelInvariant
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Predecessor-summation and measure invariance of the embedded jump kernel

This module completes the embedded-jump-chain kernel development by proving the
predecessor-summation lemma the kernel modules name as their honest gap and lifting it to
genuine measure invariance `Kernel.Invariant (jumpKernel κ) (jumpStationaryMeasure κ c)`.

The candidate stationary measure of `CRNT.Stochastic.KernelInvariant` evaluates on
singletons via two exported identities: `jumpStationaryMeasure_singleton` gives
`μ{m} = ofReal (jumpStationaryMass κ c m)`, and `jumpStationaryMeasure_bind_apply`
expands `(μ.bind (jumpKernel κ)) {m}` into a tsum over *source* counts. Equating these two
on every singleton is exactly measure invariance, since singletons generate the discrete
σ-algebra on the count lattice.

The central content is `predecessor_sum_eq`:

`∑' n, ofReal (jumpStationaryMass κ c n) * jumpKernel κ n {m} = ofReal (jumpStationaryMass κ c m)`.

Off the boundary the kernel row mass into `{m}` is
`∑_r ofReal (jumpProb κ n r) · indicator {m} (jumpNextCount n r)`, and
`jumpStationaryMass · jumpProb = productPoissonPMF · stochasticRate = generatorOutflow`
cancels the holding denominator (`ofReal_jumpStationaryMass_mul_jumpProb`). Swapping the
lattice tsum past the finite reaction sum (Tonelli for `ℝ≥0∞`) reduces the problem, reaction
by reaction, to a single predecessor. For a target `m` dominating the reaction's target
complex the unique *source-dominating* predecessor is
`predecessorCount r m = fun s => m s + source_r s - target_r s`; every other count landing on
`m` fails to dominate the source, so its falling-factorial propensity — hence its jump
probability — vanishes. The surviving term is `ofReal (generatorInflow κ c m r)`, and the
reaction-indexed sum collapses by `jumpGlobalBalance_of_complexBalanced`.

The honest hypotheses are an explicit **no-boundary / enabled-everywhere** assumption: every
count has positive exit rate and dominates every reaction's target complex. The
`exitRate = 0` holding states are absorbing, where strict pointwise balance fails, so
invariance is stated under their exclusion — the strongest sound statement. Under those hypotheses
`Kernel.Invariant (jumpKernel κ) (jumpStationaryMeasure κ c)` holds.

Depends on: `CRNT.Stochastic.KernelInvariant`,
`Mathlib.Data.Nat.Factorial.BigOperators`.
-/

open MeasureTheory ProbabilityTheory

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

attribute [local instance] CRNT.Network.instMeasurableSpaceCount

/-- The unique source-dominating predecessor of the count `m` under reaction `r`: the count
that fires `r` to land on `m`. Species by species it removes the target complex and adds the
source complex. When `m` dominates the target complex this is the only count dominating the
source whose post-firing count is `m`. -/
def predecessorCount (N : Network S) (r : N.R) (m : S → ℕ) : S → ℕ :=
  fun s => m s + (N.reaction r).source s - (N.reaction r).target s

/-- The predecessor dominates the source complex when the target count dominates the target
complex. -/
theorem source_le_predecessorCount (N : Network S) (r : N.R) (m : S → ℕ)
    (hm : ∀ s, (N.reaction r).target s ≤ m s) (s : S) :
    (N.reaction r).source s ≤ N.predecessorCount r m s := by
  unfold predecessorCount
  have h := hm s
  omega

/-- The source-shifted predecessor coincides with the target-shifted target count: firing the
source-dominating predecessor leaves the same residual count whether you subtract the source
from the predecessor or the target from the target count. -/
theorem predecessorCount_sub_source (N : Network S) (r : N.R) (m : S → ℕ)
    (hm : ∀ s, (N.reaction r).target s ≤ m s) :
    (fun s => N.predecessorCount r m s - (N.reaction r).source s) =
      (fun s => m s - (N.reaction r).target s) := by
  funext s
  unfold predecessorCount
  have h := hm s
  omega

/-- Firing reaction `r` from the source-dominating predecessor recovers the target count,
provided the target count dominates the target complex. -/
theorem jumpNextCount_predecessorCount (N : Network S) (r : N.R) (m : S → ℕ)
    (hm : ∀ s, (N.reaction r).target s ≤ m s) :
    N.jumpNextCount (N.predecessorCount r m) r = m := by
  funext s
  unfold jumpNextCount predecessorCount
  have h := hm s
  omega

/-- Any count whose post-firing count under `r` is `m` and which dominates the source complex
*is* the source-dominating predecessor. With source domination, `ℕ`-subtraction inverts and
the count is determined coordinatewise. -/
theorem eq_predecessorCount_of_jumpNextCount (N : Network S) (r : N.R) (m n : S → ℕ)
    (hsrc : ∀ s, (N.reaction r).source s ≤ n s)
    (hnext : N.jumpNextCount n r = m) :
    n = N.predecessorCount r m := by
  funext s
  unfold predecessorCount
  have hns := hsrc s
  have hn : n s - (N.reaction r).source s + (N.reaction r).target s = m s := by
    have := congrFun hnext s
    unfold jumpNextCount at this
    exact this
  omega

/-- A count that does not dominate the source complex of `r` has zero stochastic propensity:
its falling-factorial counting law vanishes in the under-resourced species. -/
theorem stochasticMassActionRate_eq_zero_of_not_source_le (N : Network S)
    (κ : RateConstants N) (n : S → ℕ) (r : N.R)
    (h : ¬ ∀ s, (N.reaction r).source s ≤ n s) :
    N.stochasticMassActionRate κ n r = 0 := by
  unfold stochasticMassActionRate
  rw [not_forall] at h
  obtain ⟨s, hs⟩ := h
  rw [not_le] at hs
  refine mul_eq_zero.mpr (Or.inr ?_)
  refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
  have : (n s).descFactorial ((N.reaction r).source s) = 0 :=
    Nat.descFactorial_eq_zero_iff_lt.mpr hs
  exact_mod_cast this

/-- The jump probability vanishes at a count not dominating the source complex of `r`: the
numerator stochastic propensity is zero. -/
theorem jumpProb_eq_zero_of_not_source_le (N : Network S) (κ : RateConstants N)
    (n : S → ℕ) (r : N.R) (h : ¬ ∀ s, (N.reaction r).source s ≤ n s) :
    N.jumpProb κ n r = 0 := by
  unfold jumpProb
  rw [N.stochasticMassActionRate_eq_zero_of_not_source_le κ n r h, zero_div]

/-- The lifted stationary weight is nonnegative at a nonnegative concentration: the
product-Poisson density and the exit rate are both nonnegative. -/
theorem jumpStationaryMass_nonneg (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (n : S → ℕ) :
    0 ≤ N.jumpStationaryMass κ c n :=
  mul_nonneg (productPoissonPMF_nonneg hc n) (N.exitRate_nonneg κ n)

/-- The generator inflow is nonnegative at a nonnegative concentration. -/
theorem generatorInflow_nonneg (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (n : S → ℕ) (r : N.R) :
    0 ≤ N.generatorInflow κ c n r :=
  mul_nonneg (N.massActionRate_nonneg κ r hc)
    (shiftedPMF_nonneg c hc n (N.reaction r).target)

/-- The real-arithmetic per-reaction cancellation: on the positive-exit part of the lattice,
for a count dominating the source complex, the stationary weight times the jump probability is
the deterministic generator outflow. The holding-rate denominator of `jumpProb` cancels the
holding-rate factor of `jumpStationaryMass`, leaving `productPoissonPMF · stochasticRate`,
which the product-form identity rewrites as `massActionRate · π(n − source)`. -/
theorem jumpStationaryMass_mul_jumpProb_eq_generatorOutflow (N : Network S)
    (κ : RateConstants N) (c : Concentration S) (n : S → ℕ) (r : N.R)
    (hpos : N.exitRate κ n ≠ 0) (hsrc : ∀ s, (N.reaction r).source s ≤ n s) :
    N.jumpStationaryMass κ c n * N.jumpProb κ n r = N.generatorOutflow κ c n r := by
  have hcancel : N.jumpStationaryMass κ c n * N.jumpProb κ n r =
      productPoissonPMF c n * N.stochasticMassActionRate κ n r := by
    unfold jumpStationaryMass jumpProb
    field_simp
  rw [hcancel]
  exact N.productPoissonPMF_mul_stochasticRate κ c n r hsrc

/-- The generator outflow at the source-dominating predecessor equals the generator inflow at
the target count: both reduce to `massActionRate · π(m − target_r)` because the predecessor's
source-shift coincides with the target count's target-shift. -/
theorem generatorOutflow_predecessorCount_eq_generatorInflow (N : Network S)
    (κ : RateConstants N) (c : Concentration S) (r : N.R) (m : S → ℕ)
    (hm : ∀ s, (N.reaction r).target s ≤ m s) :
    N.generatorOutflow κ c (N.predecessorCount r m) r = N.generatorInflow κ c m r := by
  unfold generatorOutflow generatorInflow
  rw [shiftedPMF, shiftedPMF]
  simp only [N.source_le_predecessorCount r m hm, hm, ↓reduceIte]
  rw [N.predecessorCount_sub_source r m hm]

/-- Per-reaction collapse of the predecessor tsum. Under no-boundary (`hexit`) and
target-domination (`hm`) hypotheses, the lattice tsum of the lifted stationary weight times
the reaction-`r` jump mass into `{m}` collapses to the single source-dominating predecessor,
yielding the lifted generator inflow of reaction `r` at `m`. Every other count landing on `m`
fails to dominate the reaction's source complex, vanishing its jump probability. -/
theorem tsum_reaction_term_eq_generatorInflow (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (r : N.R) (m : S → ℕ)
    (hexit : ∀ n, N.exitRate κ n ≠ 0)
    (hm : ∀ s, (N.reaction r).target s ≤ m s) :
    ∑' n : S → ℕ, ENNReal.ofReal (N.jumpStationaryMass κ c n) *
        (ENNReal.ofReal (N.jumpProb κ n r) *
          ({m} : Set (S → ℕ)).indicator 1 (N.jumpNextCount n r)) =
      ENNReal.ofReal (N.generatorInflow κ c m r) := by
  rw [tsum_eq_single (N.predecessorCount r m)]
  · have hsrc := N.source_le_predecessorCount r m hm
    have hnext := N.jumpNextCount_predecessorCount r m hm
    rw [hnext, Set.indicator_of_mem (Set.mem_singleton m), Pi.one_apply, mul_one,
      ← ENNReal.ofReal_mul (N.jumpStationaryMass_nonneg κ c hc _),
      N.jumpStationaryMass_mul_jumpProb_eq_generatorOutflow κ c _ r (hexit _) hsrc,
      N.generatorOutflow_predecessorCount_eq_generatorInflow κ c r m hm]
  · intro n hn
    by_cases hind : N.jumpNextCount n r = m
    · -- lands on `m`; if it dominated the source it would be the predecessor
      by_cases hsrc : ∀ s, (N.reaction r).source s ≤ n s
      · exact absurd (N.eq_predecessorCount_of_jumpNextCount r m n hsrc hind) hn
      · rw [N.jumpProb_eq_zero_of_not_source_le κ n r hsrc, ENNReal.ofReal_zero,
          zero_mul, mul_zero]
    · rw [Set.indicator_of_notMem (by simpa using hind), mul_zero, mul_zero]

/-- The predecessor-summation lemma — the final result of the embedded-chain kernel development.
Under the no-boundary / enabled-everywhere hypotheses, the countable sum over source counts of
the lifted stationary weight times the kernel's transition mass into `{m}` equals the lifted
stationary weight at `m`. The reaction sum is swapped past the lattice tsum, each reaction
term collapses to its source-dominating predecessor contributing the lifted generator inflow,
and the reaction-indexed inflow sum equals the lifted stationary weight by the embedded global
balance at the complex-balanced concentration. -/
theorem predecessor_sum_eq (N : Network S) (κ : RateConstants N) (c : Concentration S)
    (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c)
    (hexit : ∀ n, N.exitRate κ n ≠ 0)
    (henabled : ∀ n r, N.Enabled n r)
    (m : S → ℕ) (hm : ∀ r s, (N.reaction r).target s ≤ m s) :
    (∑' n : S → ℕ, ENNReal.ofReal (N.jumpStationaryMass κ c n) * N.jumpKernel κ n {m}) =
      ENNReal.ofReal (N.jumpStationaryMass κ c m) := by
  have hstep : ∀ n : S → ℕ, N.jumpKernel κ n {m} =
      ∑ r : N.R, ENNReal.ofReal (N.jumpProb κ n r) *
        ({m} : Set (S → ℕ)).indicator 1 (N.jumpNextCount n r) := by
    intro n
    rw [N.jumpKernel_apply_of_exitRate_pos κ n (hexit n)]
  simp_rw [hstep, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have hterm : ∀ r : N.R,
      (∑' n : S → ℕ, ENNReal.ofReal (N.jumpStationaryMass κ c n) *
          (ENNReal.ofReal (N.jumpProb κ n r) *
            ({m} : Set (S → ℕ)).indicator 1 (N.jumpNextCount n r))) =
        ENNReal.ofReal (N.generatorInflow κ c m r) := fun r =>
    N.tsum_reaction_term_eq_generatorInflow κ c hc r m hexit (hm r)
  rw [Finset.sum_congr rfl (fun r _ => hterm r)]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun r _ => N.generatorInflow_nonneg κ c hc m r)]
  congr 1
  exact N.jumpGlobalBalance_of_complexBalanced κ c m hcb (henabled m)

/-- Measure invariance of the embedded jump kernel at a complex-balanced concentration, under
the no-boundary / enabled-everywhere hypotheses.

`Kernel.Invariant (jumpKernel κ) (jumpStationaryMeasure κ c)` is by definition
`(jumpStationaryMeasure κ c).bind (jumpKernel κ) = jumpStationaryMeasure κ c`. The two measures
agree on every singleton: the pushforward singleton mass is the predecessor tsum
(`jumpStationaryMeasure_bind_apply`), which the predecessor-summation lemma equates to the
lifted stationary weight, and that is the candidate measure's own singleton mass
(`jumpStationaryMeasure_singleton`). Singletons determine a measure on the countable count
lattice with its discrete σ-algebra (`Measure.ext_of_singleton`), so the measures coincide.
This is the final result of the embedded-chain kernel development. -/
theorem jumpKernel_invariant_jumpStationaryMeasure (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c)
    (hexit : ∀ n, N.exitRate κ n ≠ 0)
    (henabled : ∀ n r, N.Enabled n r)
    (htarget : ∀ (m : S → ℕ) r s, (N.reaction r).target s ≤ m s) :
    Kernel.Invariant (N.jumpKernel κ) (N.jumpStationaryMeasure κ c) := by
  unfold Kernel.Invariant
  refine Measure.ext_of_singleton (fun m => ?_)
  rw [N.jumpStationaryMeasure_bind_apply κ c {m},
    N.predecessor_sum_eq κ c hc hcb hexit henabled m (fun r => htarget m r),
    N.jumpStationaryMeasure_singleton κ c m]

end Network

end CRNT
