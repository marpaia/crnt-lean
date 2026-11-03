import CRNT.Stochastic.MinimalSemigroupNonExplosion
import CRNT.Stochastic.StationaryIdentity
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Stationary laws of the master equation are invariant for the transition function

Let `π ≥ 0` be summable, stationary for the chemical master equation (global balance at every
count, `IsCMEStationary`), with `∑_n π(n) λ_r(n) < ∞` for every reaction. Then `π` is invariant
for the minimal transition function of stochastic mass action:

`∑_n π(n) P(t)(n, m) = π(m)` for all `t ≥ 0`  (`tsum_mul_transition_of_cmeStationary`).

No non-explosion hypothesis is needed. Proof: `g(t) = ∑_n π(n) P(t)(n, m)` is continuous on
`[0, ∞)` (uniform convergence, `P ≤ 1`), and for `t > 0` it can be differentiated term by term
(the backward equation gives `|∂ₜ P(t)(n, m)| ≤ 2 λ(n)`); the derivative is
`∑_n π(n) (A f)(n)` with `f = P(t)(·, m)`, which vanishes by the stationarity identity
`tsum_mul_observableGenerator_eq_zero`. Hence `g` is constant, equal to `g(0) = π(m)`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

theorem transition_zero (N : Network S) (κ : RateConstants N) (n m : S → ℕ) :
    N.transition κ 0 n m = if n = m then 1 else 0 := by
  rw [N.transition_eq κ le_rfl]; simp

theorem transition_le_one (N : Network S) (κ : RateConstants N) {t : ℝ} (ht : 0 ≤ t)
    (n m : S → ℕ) : N.transition κ t n m ≤ 1 := by
  simpa using N.sum_transition_le_one κ ht n {m}

theorem continuousOn_transition (N : Network S) (κ : RateConstants N) (n m : S → ℕ) :
    ContinuousOn (fun t => N.transition κ t n m) (Ici 0) :=
  (N.jumpSystem κ).continuousOn_Pmin n m

theorem sum_rate_mul_jumpNextCount (N : Network S) (κ : RateConstants N) (f : (S → ℕ) → ℝ)
    (n : S → ℕ) :
    ∑ r, N.stochasticMassActionRate κ n r * f (N.jumpNextCount n r) =
      ∑ r, N.stochasticMassActionRate κ n r * f (N.fireCount n r) := by
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hen : N.Enabled n r
  · rw [N.fireCount_of_enabled hen]; rfl
  · rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen, zero_mul, zero_mul]

/-- The backward-equation right-hand side is the generator applied to the column `P(t)(·, m)`. -/
theorem observableGenerator_transition (N : Network S) (κ : RateConstants N) (t : ℝ)
    (n m : S → ℕ) :
    N.observableGenerator κ (fun l => N.transition κ t l m) n =
      -N.exitRate κ n * N.transition κ t n m +
        ∑ r, N.stochasticMassActionRate κ n r * N.transition κ t (N.jumpNextCount n r) m := by
  rw [sum_rate_mul_jumpNextCount N κ (fun l => N.transition κ t l m), observableGenerator,
    exitRate]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  ring

/-- **Invariance of master-equation stationary laws** for the transition function. -/
theorem tsum_mul_transition_of_cmeStationary (N : Network S) (κ : RateConstants N)
    {π : (S → ℕ) → ℝ} (hst : N.IsCMEStationary κ π) (hπ0 : ∀ n, 0 ≤ π n) (hπs : Summable π)
    (hlam : ∀ r, Summable fun n => π n * N.stochasticMassActionRate κ n r) {t : ℝ} (ht : 0 ≤ t)
    (m : S → ℕ) : ∑' n, π n * N.transition κ t n m = π m := by
  have hP0 : ∀ τ, 0 ≤ τ → ∀ n, 0 ≤ N.transition κ τ n m := fun τ hτ n =>
    N.transition_nonneg κ hτ n m
  have hP1 : ∀ τ, 0 ≤ τ → ∀ n, N.transition κ τ n m ≤ 1 := fun τ hτ n =>
    N.transition_le_one κ hτ n m
  have hrate0 := N.stochasticMassActionRate_nonneg κ
  have hexit : Summable fun n => π n * N.exitRate κ n := by
    simp only [exitRate, Finset.mul_sum]
    exact summable_sum fun r _ => hlam r
  have hsumτ : ∀ τ, 0 ≤ τ → Summable fun n => π n * N.transition κ τ n m := fun τ hτ =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hπ0 n) (hP0 τ hτ n))
      (fun n => by have := hP1 τ hτ n; have := hπ0 n; nlinarith) hπs
  -- term-by-term derivative
  let D : (S → ℕ) → ℝ → ℝ := fun n τ => π n * (-N.exitRate κ n * N.transition κ τ n m +
    ∑ r, N.stochasticMassActionRate κ n r * N.transition κ τ (N.jumpNextCount n r) m)
  have hD : ∀ n τ, τ ∈ Ioi (0 : ℝ) →
      HasDerivAt (fun τ => π n * N.transition κ τ n m) (D n τ) τ := fun n τ hτ =>
    (N.hasDerivAt_transition κ hτ n m).const_mul (π n)
  have hDb : ∀ n τ, τ ∈ Ioi (0 : ℝ) → ‖D n τ‖ ≤ 2 * (π n * N.exitRate κ n) := by
    intro n τ hτ
    have hτ0 : 0 ≤ τ := le_of_lt hτ
    have hS0 : 0 ≤ ∑ r, N.stochasticMassActionRate κ n r *
        N.transition κ τ (N.jumpNextCount n r) m :=
      Finset.sum_nonneg fun r _ => mul_nonneg (hrate0 n r) (hP0 τ hτ0 _)
    have hS1 : ∑ r, N.stochasticMassActionRate κ n r *
        N.transition κ τ (N.jumpNextCount n r) m ≤ N.exitRate κ n := by
      unfold exitRate
      exact Finset.sum_le_sum fun r _ => mul_le_of_le_one_right (hrate0 n r) (hP1 τ hτ0 _)
    have hE0 := N.exitRate_nonneg κ n
    have hp0 := hP0 τ hτ0 n
    have hp1 := hP1 τ hτ0 n
    have hπn := hπ0 n
    rw [Real.norm_eq_abs, abs_le]
    simp only [D]
    constructor <;> nlinarith [mul_nonneg hπn hE0, mul_nonneg hπn hS0, mul_nonneg (mul_nonneg hπn hE0) hp0]
  have hderiv : ∀ τ ∈ Ioi (0 : ℝ),
      HasDerivAt (fun τ => ∑' n, π n * N.transition κ τ n m) 0 τ := by
    intro τ hτ
    have h := hasDerivAt_tsum_of_isPreconnected (hexit.mul_left 2) isOpen_Ioi isPreconnected_Ioi
      hD hDb hτ (hsumτ τ (le_of_lt hτ)) hτ
    have hτ0 : 0 ≤ τ := le_of_lt hτ
    have hzero : ∑' n, D n τ = 0 := by
      have hs1 : ∀ r, Summable fun n => π n * N.stochasticMassActionRate κ n r *
          N.transition κ τ n m := fun r =>
        Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (hπ0 n) (hrate0 n r))
          (hP0 τ hτ0 n)) (fun n => mul_le_of_le_one_right (mul_nonneg (hπ0 n) (hrate0 n r))
          (hP1 τ hτ0 n)) (hlam r)
      have hs2 : ∀ r, Summable fun n => π n * N.stochasticMassActionRate κ n r *
          N.transition κ τ (N.fireCount n r) m := fun r =>
        Summable.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (hπ0 n) (hrate0 n r))
          (hP0 τ hτ0 _)) (fun n => mul_le_of_le_one_right (mul_nonneg (hπ0 n) (hrate0 n r))
          (hP1 τ hτ0 _)) (hlam r)
      have hgen := N.tsum_mul_observableGenerator_eq_zero κ hst
        (fun l => N.transition κ τ l m) hs1 hs2
      rw [← hgen]
      refine tsum_congr fun n => ?_
      simp only [D]
      rw [observableGenerator_transition]
    rwa [hzero] at h
  have hcont : ContinuousOn (fun τ => ∑' n, π n * N.transition κ τ n m) (Ici 0) := by
    refine continuousOn_tsum (u := π) (fun n => continuousOn_const.mul
      (N.continuousOn_transition κ n m)) hπs fun n τ hτ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hπ0 n) (hP0 τ hτ n))]
    exact mul_le_of_le_one_right (hπ0 n) (hP1 τ hτ n)
  have hg0 : ∑' n, π n * N.transition κ 0 n m = π m := by
    have h : ∀ n, π n * N.transition κ 0 n m = if n = m then π m else 0 := by
      intro n; rw [transition_zero]; split_ifs with h <;> simp [h]
    simp only [h, tsum_ite_eq]
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hg0
  · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
      (fun τ => ∑' n, π n * N.transition κ τ n m) (fun _ => (0 : ℝ)) hpos
      (hcont.mono Icc_subset_Ici_self) fun x hx => hderiv x hx.1
    rw [eq_div_iff (by linarith), zero_mul] at hslope
    linarith

end Network
end CRNT
