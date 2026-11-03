import CRNT.Stochastic.JumpAbsorption
import CRNT.Flux.PSemiflow
import CRNT.Stochastic.FosterLyapunov

/-!
# Non-explosivity of conservative stochastic reaction networks

The continuous-time Markov chain of a stochastic reaction network is built from its embedded
jump chain `n₀, n₁, …` and independent exponential holding times of rates `λ(n_k)` (the exit
rates). It explodes (infinitely many jumps in finite time) exactly on the event
`∑_k E_k / λ(n_k) < ∞`; for independent unit exponentials `E_k` this has probability zero as soon
as `∑_k 1/λ(n_k) = ∞` (Norris, *Markov Chains*, Theorem 2.3.2). The deterministic input is
therefore that the reciprocal exit rates are not summable along any jump path.

This module proves that input:
* `CRNT.Network.not_summable_inv_exitRate_of_bounded`: along a jump path with bounded exit rates
  the reciprocal exit rates are not summable;
* `CRNT.Network.weightedTotal_jumpPath`: a positive conservation law is constant along jump paths;
* `CRNT.Network.not_summable_inv_exitRate_of_conservative`: for every conservative network
  (positive P-semiflow) and every jump path, `∑_k 1/λ(n_k) = ∞` — conservative networks are
  non-explosive (Anderson–Cappelletti–Kim–Nguyen 2020 treat the non-conservative case).

The identification of the explosion event with `∑ E_k/λ(n_k) < ∞` and the exponential series
argument are not formalized here.
-/

namespace CRNT

namespace Network

open Filter Topology
open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A jump path: each step fires a reaction of positive propensity. -/
def IsJumpPath (N : Network S) (κ : RateConstants N) (n : ℕ → (S → ℕ)) : Prop :=
  ∀ k, ∃ r, 0 < N.stochasticMassActionRate κ (n k) r ∧ n (k + 1) = N.jumpNextCount (n k) r

theorem exitRate_pos_of_rate_pos (N : Network S) (κ : RateConstants N) {m : S → ℕ} {r : N.R}
    (h : 0 < N.stochasticMassActionRate κ m r) : 0 < N.exitRate κ m :=
  lt_of_lt_of_le h (Finset.single_le_sum (f := fun r => N.stochasticMassActionRate κ m r)
    (fun r _ => N.stochasticMassActionRate_nonneg κ m r) (Finset.mem_univ r))

/-- **Bounded exit rates rule out summability.** -/
theorem not_summable_inv_exitRate_of_bounded (N : Network S) (κ : RateConstants N)
    {n : ℕ → (S → ℕ)} (hpath : N.IsJumpPath κ n) {Λ : ℝ} (hΛ : ∀ k, N.exitRate κ (n k) ≤ Λ) :
    ¬ Summable (fun k => 1 / N.exitRate κ (n k)) := by
  intro hsum
  have hpos : ∀ k, 0 < N.exitRate κ (n k) := fun k => by
    obtain ⟨r, hr, -⟩ := hpath k
    exact N.exitRate_pos_of_rate_pos κ hr
  have hΛpos : 0 < Λ := lt_of_lt_of_le (hpos 0) (hΛ 0)
  have hlow : ∀ k, 1 / Λ ≤ 1 / N.exitRate κ (n k) := fun k =>
    one_div_le_one_div_of_le (hpos k) (hΛ k)
  have hlim := hsum.tendsto_atTop_zero
  have : ∀ᶠ k in atTop, 1 / N.exitRate κ (n k) < 1 / Λ :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨k, hk⟩ := this.exists
  linarith [hlow k]

/-- Weighted count total `∑_s w_s n_s`. -/
def weightedCount (w : S → ℝ) (m : S → ℕ) : ℝ := ∑ s, w s * (m s : ℝ)

/-- A P-invariant is preserved by every jump of positive propensity. -/
theorem weightedCount_jump (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : N.IsPInvariant w) {m : S → ℕ} {r : N.R} (hr : 0 < N.stochasticMassActionRate κ m r) :
    weightedCount w (N.jumpNextCount m r) = weightedCount w m := by
  have hen : N.Enabled m r := by
    by_contra h
    rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ m r h] at hr
    exact lt_irrefl _ hr
  have hinv := (mem_orthSum.mp hw) _ (N.reactionVector_mem_stoichSubspace r)
  unfold weightedCount
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← hinv]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hle := hen s
  simp only [jumpNextCount, reactionVector_apply]
  rw [Nat.cast_add, Nat.cast_sub hle]
  ring

/-- **Conservation along jump paths.** -/
theorem weightedTotal_jumpPath (N : Network S) (κ : RateConstants N) {w : S → ℝ}
    (hw : N.IsPInvariant w) {n : ℕ → (S → ℕ)} (hpath : N.IsJumpPath κ n) (k : ℕ) :
    weightedCount w (n k) = weightedCount w (n 0) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨r, hr, hnext⟩ := hpath k
    rw [hnext, N.weightedCount_jump κ hw hr, ih]

/-- Exit rates are bounded on any box of counts. -/
theorem exitRate_le_of_le (N : Network S) (κ : RateConstants N) {m : S → ℕ} {B : ℕ}
    (hm : ∀ s, m s ≤ B) :
    N.exitRate κ m ≤ ∑ r, κ.k r * ∏ s, ((B : ℝ) ^ (N.reaction r).source s) := by
  unfold exitRate
  refine Finset.sum_le_sum fun r _ => ?_
  unfold stochasticMassActionRate
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun s _ => by positivity)
    (fun s _ => ?_)) (κ.positive r).le
  have h1 : (m s).descFactorial ((N.reaction r).source s) ≤ m s ^ (N.reaction r).source s :=
    Nat.descFactorial_le_pow _ _
  have h2 : m s ^ (N.reaction r).source s ≤ B ^ (N.reaction r).source s :=
    Nat.pow_le_pow_left (hm s) _
  exact_mod_cast h1.trans h2

/-- **Conservative networks are non-explosive** (deterministic part): along every jump path of
a network with a strictly positive P-semiflow, the reciprocal exit rates are not summable. -/
theorem not_summable_inv_exitRate_of_conservative (N : Network S) (κ : RateConstants N)
    (hcons : N.IsConservative) {n : ℕ → (S → ℕ)} (hpath : N.IsJumpPath κ n) :
    ¬ Summable (fun k => 1 / N.exitRate κ (n k)) := by
  classical
  obtain ⟨w, hwinv, hwpos⟩ := hcons
  -- a uniform count bound from the conserved weighted total
  by_cases hS : (Finset.univ : Finset S).Nonempty
  · obtain ⟨s₀, -, hs₀⟩ := Finset.exists_min_image Finset.univ w hS
    set wmin := w s₀
    have hwmin : 0 < wmin := hwpos s₀
    set W := weightedCount w (n 0)
    obtain ⟨B, hB⟩ := exists_nat_ge (W / wmin)
    have hbound : ∀ k s, n k s ≤ B := by
      intro k s
      have hW := N.weightedTotal_jumpPath κ hwinv hpath k
      have hle : w s * (n k s : ℝ) ≤ weightedCount w (n k) :=
        Finset.single_le_sum (f := fun s => w s * (n k s : ℝ))
          (fun t _ => mul_nonneg (hwpos t).le (Nat.cast_nonneg _)) (Finset.mem_univ s)
      have h1 : wmin * (n k s : ℝ) ≤ w s * (n k s : ℝ) :=
        mul_le_mul_of_nonneg_right (hs₀ s (Finset.mem_univ s)) (Nat.cast_nonneg _)
      have h2 : (n k s : ℝ) ≤ W / wmin := by
        rw [le_div_iff₀ hwmin]; rw [hW] at hle; linarith
      exact_mod_cast h2.trans hB
    exact N.not_summable_inv_exitRate_of_bounded κ hpath fun k => N.exitRate_le_of_le κ (hbound k)
  · -- no species: every count is the same, so the exit rate is constant
    have hconst : ∀ k, n k = n 0 := fun k => funext fun s => absurd ⟨s, Finset.mem_univ s⟩ hS
    exact N.not_summable_inv_exitRate_of_bounded κ hpath (Λ := N.exitRate κ (n 0))
      fun k => by rw [hconst k]

end Network

end CRNT
