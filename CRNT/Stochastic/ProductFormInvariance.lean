import CRNT.Stochastic.MinimalSemigroupStationary
import CRNT.Stochastic.Generator

/-!
# The Anderson–Craciun–Kurtz product form is invariant for the transition function

For a complex-balanced equilibrium `c ≥ 0`, the product-Poisson density
`π(n) = ∏_s e^{−c_s} c_s^{n_s} / n_s!` is stationary for the chemical master equation
(`isCMEStationary_productPoisson`, from the ACK residual identity), has finite first moments of
every propensity (`summable_productPoisson_mul_rate`), and is therefore invariant for the minimal
transition function of stochastic mass action:

`∑_n π(n) P(t)(n, m) = π(m)` for every `t ≥ 0`  (`tsum_productPoisson_mul_transition`).
-/

open MeasureTheory
open scoped BigOperators

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

omit [DecidableEq S] in
theorem sum_productPoissonPMF_le_one {c : Concentration S} (hc : c.Nonnegative)
    (F : Finset (S → ℕ)) : ∑ n ∈ F, productPoissonPMF c n ≤ 1 := by
  have h := sum_measure_singleton (μ := productPoisson c hc) (s := F)
  simp only [productPoisson_singleton] at h
  rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => productPoissonPMF_nonneg hc n)] at h
  have h2 : productPoisson c hc (↑F : Set (S → ℕ)) ≤ 1 := prob_le_one
  rw [← h] at h2
  exact ENNReal.ofReal_le_one.mp h2

theorem summable_shiftedPMF {c : Concentration S} (hc : c.Nonnegative) (y : Complex S) :
    Summable fun n => shiftedPMF c n y := by
  refine summable_of_sum_le (c := 1) (fun n => shiftedPMF_nonneg c hc n y) fun F => ?_
  have hinj : Set.InjOn (fun (n : S → ℕ) (s : S) => n s - y s)
      ↑(F.filter fun n => ∀ s, y s ≤ n s) := by
    intro n₁ h₁ n₂ h₂ h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at h₁ h₂
    funext s
    have := congrFun h s
    have := h₁.2 s; have := h₂.2 s
    simp only at *
    omega
  calc ∑ n ∈ F, shiftedPMF c n y
      = ∑ n ∈ F.filter (fun n => ∀ s, y s ≤ n s), productPoissonPMF c (fun s => n s - y s) := by
        rw [Finset.sum_filter]; rfl
    _ = ∑ m ∈ (F.filter fun n => ∀ s, y s ≤ n s).image (fun (n : S → ℕ) (s : S) => n s - y s),
          productPoissonPMF c m := (Finset.sum_image hinj).symm
    _ ≤ 1 := sum_productPoissonPMF_le_one hc _

/-- The product-form outflow identity at every count. -/
theorem productPoissonPMF_mul_rate (N : Network S) (κ : RateConstants N) (c : Concentration S)
    (n : S → ℕ) (r : N.R) :
    productPoissonPMF c n * N.stochasticMassActionRate κ n r =
      N.massActionRate κ r c * shiftedPMF c n (N.reaction r).source := by
  by_cases hn : ∀ s, (N.reaction r).source s ≤ n s
  · exact N.productPoissonPMF_mul_stochasticRate κ c n r hn
  · rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hn, mul_zero]
    unfold shiftedPMF
    rw [if_neg hn, mul_zero]

/-- The product-form inflow identity. -/
theorem cmeInflow_productPoisson (N : Network S) (κ : RateConstants N) (c : Concentration S)
    (m : S → ℕ) (r : N.R) :
    N.cmeInflow κ (productPoissonPMF c) m r =
      N.massActionRate κ r c * shiftedPMF c m (N.reaction r).target := by
  unfold cmeInflow
  by_cases h : ∀ s, (N.reaction r).target s ≤ m s
  · rw [if_pos h, productPoissonPMF_mul_rate]
    unfold shiftedPMF
    have hsrc : ∀ s, (N.reaction r).source s ≤ N.predCount m r s := fun s => by
      unfold predCount; omega
    rw [if_pos hsrc, if_pos h]
    congr 2
    funext s
    unfold predCount
    have := h s
    omega
  · rw [if_neg h]
    unfold shiftedPMF
    rw [if_neg h, mul_zero]

/-- **The product form is stationary for the chemical master equation.** -/
theorem isCMEStationary_productPoisson (N : Network S) (κ : RateConstants N)
    (c : Concentration S) (hcb : N.IsComplexBalanced κ c) :
    N.IsCMEStationary κ (productPoissonPMF c) := by
  intro m
  have h := N.productPoisson_isStationary_of_complexBalanced κ c hcb m
  unfold ackResidual generatorFlux at h
  simp only [mul_sub, Finset.sum_sub_distrib] at h
  rw [Finset.mul_sum]
  simp only [cmeInflow_productPoisson, productPoissonPMF_mul_rate]
  linarith

theorem summable_productPoisson_mul_rate (N : Network S) (κ : RateConstants N)
    {c : Concentration S} (hc : c.Nonnegative) (r : N.R) :
    Summable fun n => productPoissonPMF c n * N.stochasticMassActionRate κ n r := by
  simp only [productPoissonPMF_mul_rate]
  exact (summable_shiftedPMF hc _).mul_left _

/-- **Anderson–Craciun–Kurtz product form, dynamic version.** For a complex-balanced
equilibrium `c ≥ 0`, the product-Poisson law is invariant for the transition function of
stochastic mass action: `∑_n π(n) P(t)(n, m) = π(m)` for every `t ≥ 0` and every count `m`. -/
theorem tsum_productPoisson_mul_transition (N : Network S) (κ : RateConstants N)
    {c : Concentration S} (hc : c.Nonnegative) (hcb : N.IsComplexBalanced κ c) {t : ℝ}
    (ht : 0 ≤ t) (m : S → ℕ) :
    ∑' n, productPoissonPMF c n * N.transition κ t n m = productPoissonPMF c m :=
  N.tsum_mul_transition_of_cmeStationary κ (N.isCMEStationary_productPoisson κ c hcb)
    (fun n => productPoissonPMF_nonneg hc n)
    (summable_of_sum_le (c := 1) (fun n => productPoissonPMF_nonneg hc n)
      (sum_productPoissonPMF_le_one hc))
    (fun r => N.summable_productPoisson_mul_rate κ hc r) ht m

end Network
end CRNT
