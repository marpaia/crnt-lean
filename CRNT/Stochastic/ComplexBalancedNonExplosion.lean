import CRNT.Stochastic.ProductFormErgodic
import CRNT.Stochastic.MinimalSemigroupMinimality

/-!
# Complex-balanced stochastic mass-action systems do not explode

If the network has a positive complex-balanced equilibrium `c`, the minimal transition function of
stochastic mass action is stochastic from every count: `∑_m P(t)(n, m) = 1` for all `t ≥ 0`
(`hasSum_transition_one_of_complexBalanced`; Anderson–Cappelletti–Koyama–Kurtz 2018).

Proof: the product form `π = π_c` is invariant without any non-explosion assumption
(`tsum_productPoisson_mul_transition`). Summing the invariance over `m` and exchanging the double
series in `ℝ≥0∞` gives `∑_n π(n) = ∑_n π(n) s(n)` with `s(n) = ∑_m P(t)(n, m) ≤ 1`; since every
`π(n) > 0` and the sums are finite, `s(n) = 1` for every `n`.

Consequences: the backward integral equation determines the transition function of such a
network (`eq_transition_of_solution_of_complexBalanced`); for conservative weakly reversible
networks the rows converge in total variation to the normalized product form on the reachable
class (`tendsto_tv_productPoisson_of_conservative`).
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Non-explosion of complex-balanced stochastic mass action.** -/
theorem hasSum_transition_one_of_complexBalanced (N : Network S) (κ : RateConstants N)
    {c : Concentration S} (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) {t : ℝ}
    (ht : 0 ≤ t) (n₀ : S → ℕ) : HasSum (fun m => N.transition κ t n₀ m) 1 := by
  have hc0 : c.Nonnegative := fun s => (hc s).le
  set π : (S → ℕ) → ℝ := productPoissonPMF c with hπ
  have hπpos : ∀ n, 0 < π n := fun n => productPoissonPMF_pos hc n
  have hπs : Summable π := summable_of_sum_le (c := 1) (fun n => (hπpos n).le)
    (sum_productPoissonPMF_le_one hc0)
  have hP0 : ∀ n m, 0 ≤ N.transition κ t n m := fun n m => N.transition_nonneg κ ht n m
  have hP1 : ∀ n m, N.transition κ t n m ≤ 1 := fun n m => N.transition_le_one κ ht n m
  have hrow : ∀ n, Summable fun m => N.transition κ t n m := fun n =>
    summable_of_sum_le (c := 1) (hP0 n) (N.sum_transition_le_one κ ht n)
  set s : (S → ℕ) → ℝ := fun n => ∑' m, N.transition κ t n m with hs
  have hs1 : ∀ n, s n ≤ 1 := fun n =>
    (hrow n).tsum_le_of_sum_le (N.sum_transition_le_one κ ht n)
  have hcol : ∀ m, Summable fun n => π n * N.transition κ t n m := fun m =>
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hπpos n).le (hP0 n m))
      (fun n => mul_le_of_le_one_right (hπpos n).le (hP1 n m)) hπs
  have hinv : ∀ m, ∑' n, π n * N.transition κ t n m = π m := fun m =>
    N.tsum_productPoisson_mul_transition κ hc0 hcb ht m
  -- the exchanged double series
  have hswap : ∑' m, ENNReal.ofReal (π m) = ∑' n, ENNReal.ofReal (π n * s n) := by
    calc ∑' m, ENNReal.ofReal (π m)
        = ∑' m, ∑' n, ENNReal.ofReal (π n * N.transition κ t n m) := by
          refine tsum_congr fun m => ?_
          rw [← hinv m,
            ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hπpos n).le (hP0 n m)) (hcol m)]
      _ = ∑' n, ∑' m, ENNReal.ofReal (π n * N.transition κ t n m) := ENNReal.tsum_comm
      _ = ∑' n, ENNReal.ofReal (π n * s n) := by
          refine tsum_congr fun n => ?_
          rw [hs, ← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg
            (fun m => mul_nonneg (hπpos n).le (hP0 n m)) ((hrow n).mul_left _)]
  have hfin : ∑' m, ENNReal.ofReal (π m) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (hπpos n).le) hπs]
    exact ENNReal.ofReal_ne_top
  have heq : s n₀ = 1 := by
    by_contra hne
    have hlt : s n₀ < 1 := lt_of_le_of_ne (hs1 n₀) hne
    have hle : ∀ n, ENNReal.ofReal (π n * s n) ≤ ENNReal.ofReal (π n) := fun n =>
      ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (hπpos n).le (hs1 n))
    have hlt' : ENNReal.ofReal (π n₀ * s n₀) < ENNReal.ofReal (π n₀) :=
      (ENNReal.ofReal_lt_ofReal_iff (hπpos n₀)).mpr (by nlinarith [hπpos n₀])
    have := ENNReal.tsum_lt_tsum (hswap ▸ hfin) hle hlt'
    rw [hswap] at this
    exact lt_irrefl _ this
  have := (hrow n₀).hasSum
  rwa [show ∑' m, N.transition κ t n₀ m = 1 from heq] at this

/-- **The backward equation determines the transition function** of a network with a positive
complex-balanced equilibrium. -/
theorem eq_transition_of_solution_of_complexBalanced (N : Network S) (κ : RateConstants N)
    {c : Concentration S} (hc : c.Positive) (hcb : N.IsComplexBalanced κ c)
    (F : ℝ → (S → ℕ) → (S → ℕ) → ℝ) (hF0 : ∀ t, 0 ≤ t → ∀ n m, 0 ≤ F t n m)
    (hFc : ∀ n m, ContinuousOn (fun t => F t n m) (Set.Ici 0))
    (hsol : ∀ t, 0 ≤ t → ∀ n m, F t n m = Real.exp (-((N.jumpSystem κ).q n * t)) *
      (if n = m then 1 else 0) + ∫ s in (0 : ℝ)..t, Real.exp (-((N.jumpSystem κ).q n * s)) *
        ∑ i, (N.jumpSystem κ).rate i n * F (t - s) ((N.jumpSystem κ).next i n) m)
    (hsub : ∀ t, 0 ≤ t → ∀ n (B : Finset (S → ℕ)), ∑ m ∈ B, F t n m ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (n m : S → ℕ) : F t n m = N.transition κ t n m :=
  (N.jumpSystem κ).eq_Pmin_of_solution F hF0 hFc hsol hsub ht
    (N.hasSum_transition_one_of_complexBalanced κ hc hcb ht n) m

/-- **Total-variation convergence to the product form** for conservative weakly reversible
networks with a positive complex-balanced equilibrium. -/
theorem tendsto_tv_productPoisson_of_conservative (N : Network S) (κ : RateConstants N)
    (hWR : N.WeaklyReversible) (hcons : N.IsConservative) {c : Concentration S}
    (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) (n : S → ℕ) :
    Filter.Tendsto (fun t => ∑ m ∈ N.reachClass κ hcons n, |N.transition κ t n m -
        productPoissonPMF c m / ∑ x ∈ N.reachClass κ hcons n, productPoissonPMF c x|)
      Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun t => ∑ m ∈ N.reachClass κ hcons n, |N.transition κ t n m -
      productPoissonPMF c m / ∑ x ∈ N.reachClass κ hcons n, productPoissonPMF c x|)
      Filter.atTop (nhds (∑ m ∈ N.reachClass κ hcons n, |productPoissonPMF c m /
        ∑ x ∈ N.reachClass κ hcons n, productPoissonPMF c x - productPoissonPMF c m /
        ∑ x ∈ N.reachClass κ hcons n, productPoissonPMF c x|)) :=
    tendsto_finsetSum _ fun m hm => ((N.tendsto_transition_productPoisson_of_conservative κ hWR
      hcons hc hcb ((N.mem_reachClass κ hcons).mp hm)).sub_const _).abs
  simpa using h

end Network
end CRNT
