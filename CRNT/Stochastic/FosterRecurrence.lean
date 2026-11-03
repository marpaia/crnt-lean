import CRNT.Stochastic.JumpAbsorption
import CRNT.Stochastic.FosterLyapunov
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Foster's criterion: finite expected hitting times

Consider a Markov chain with finitely many jumps from each state: from `x`, with probability
`p x r` it jumps to `next x r` (`r` in a finite type), except at holding states, where it stays
put. For a set `C`, the *survival function* `u n x` is the probability that the chain started at
`x` avoids `C` at steps `1, …, n`:

`u 0 x = 1`, `u (n+1) x = ∑_r p x r · 𝟙[next x r ∉ C] · u n (next x r)`

(at holding states `u (n+1) x = 𝟙[x ∉ C] · u n x`), so `∑_{k<n} u k x` is the truncated expected
hitting time of `C` after time `0`.

**Foster's theorem** (Foster 1953; Meyn–Tweedie 1993, Theorem 11.3.4): if `V ≥ 0` and the drift
`PV(y) ≤ V(y) - ε` for every `y ∉ C`, then the expected hitting time of `C` is at most `V(x)/ε`
from `x ∉ C` and at most `1 + PV(x)/ε` from any `x`; in particular `C` is hit with probability
one. All quantities are finite sums, so no summability hypotheses are needed.

Main results:
* `CRNT.Foster.survival_sum_le_of_not_mem`, `CRNT.Foster.survival_sum_le`.
* `CRNT.Foster.tendsto_survival_zero`.
* `CRNT.Network.jumpChain_foster_hitting_time`: the embedded jump chain of a stochastic
  mass-action system.
-/

namespace CRNT

namespace Foster

open Filter Topology
open scoped BigOperators

/-- A Markov chain with finitely many jumps from each state. -/
structure FiniteBranchChain (X R : Type*) [Fintype R] where
  hold : X → Prop
  p : X → R → ℝ
  next : X → R → X
  p_nonneg : ∀ x r, 0 ≤ p x r
  p_sum : ∀ x, ¬ hold x → ∑ r, p x r = 1

variable {X R : Type*} [Fintype R] (M : FiniteBranchChain X R) (C : Set X)
  [DecidablePred M.hold] [DecidablePred (· ∈ C)]

namespace FiniteBranchChain

/-- One-step expectation `PV`. -/
noncomputable def expect (V : X → ℝ) (x : X) : ℝ :=
  if M.hold x then V x else ∑ r, M.p x r * V (M.next x r)

/-- The killed one-step operator: expectation over the next state, counting only next states
outside `C`. -/
noncomputable def killed (f : X → ℝ) (x : X) : ℝ :=
  if M.hold x then (if x ∈ C then 0 else f x)
  else ∑ r, M.p x r * (if M.next x r ∈ C then 0 else f (M.next x r))

/-- Survival function: probability of avoiding `C` at steps `1, …, n`. -/
noncomputable def survival : ℕ → X → ℝ
  | 0 => fun _ => 1
  | n + 1 => M.killed C (survival n)

theorem killed_mono {f g : X → ℝ} (hfg : ∀ x, f x ≤ g x) (x : X) :
    M.killed C f x ≤ M.killed C g x := by
  unfold killed
  split_ifs
  · exact le_rfl
  · exact hfg x
  · exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
      (by split_ifs <;> [exact le_rfl; exact hfg _]) (M.p_nonneg x r)

theorem killed_nonneg {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) (x : X) : 0 ≤ M.killed C f x := by
  unfold killed
  split_ifs
  · exact le_rfl
  · exact hf x
  · exact Finset.sum_nonneg fun r _ => mul_nonneg (M.p_nonneg x r)
      (by split_ifs <;> [exact le_rfl; exact hf _])

theorem killed_le_expect {V : X → ℝ} (hV : ∀ x, 0 ≤ V x) (x : X) :
    M.killed C V x ≤ M.expect V x := by
  unfold killed expect
  split_ifs
  · exact hV x
  · exact le_rfl
  · exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
      (by split_ifs <;> [exact hV _; exact le_rfl]) (M.p_nonneg x r)

theorem survival_nonneg (n : ℕ) (x : X) : 0 ≤ M.survival C n x := by
  induction n generalizing x with
  | zero => simp [survival]
  | succ n ih => exact M.killed_nonneg C ih x

theorem killed_one_le (x : X) : M.killed C (fun _ => 1) x ≤ 1 := by
  unfold killed
  split_ifs with h
  · norm_num
  · exact le_rfl
  · calc ∑ r, M.p x r * (if M.next x r ∈ C then 0 else 1) ≤ ∑ r, M.p x r :=
          Finset.sum_le_sum fun r _ => by split_ifs <;> simp [M.p_nonneg x r]
      _ = 1 := M.p_sum x h

theorem survival_antitone (x : X) : Antitone (fun n => M.survival C n x) := by
  refine antitone_nat_of_succ_le fun n => ?_
  induction n generalizing x with
  | zero => exact M.killed_one_le C x
  | succ n ih => exact M.killed_mono C ih x

/-- Killed `n`-step expectation of `V`. -/
noncomputable def killedPow (V : X → ℝ) : ℕ → X → ℝ
  | 0 => V
  | n + 1 => M.killed C (killedPow V n)

theorem killedPow_nonneg {V : X → ℝ} (hV : ∀ x, 0 ≤ V x) (n : ℕ) (x : X) :
    0 ≤ M.killedPow C V n x := by
  induction n generalizing x with
  | zero => exact hV x
  | succ n ih => exact M.killed_nonneg C ih x

/-- Linearity of `killed` on the combinations used below. -/
theorem killed_add_const_mul (f g : X → ℝ) (c : ℝ) (x : X) :
    M.killed C (fun y => f y + c * g y) x = M.killed C f x + c * M.killed C g x := by
  unfold killed
  split_ifs
  · ring
  · ring
  · rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun r _ => by split_ifs <;> ring

theorem killed_zero (x : X) : M.killed C (fun _ => 0) x = 0 := by
  unfold killed; split_ifs <;> simp

/-- `killed` commutes with finite sums over `range n`. -/
theorem killed_sum_range (f : ℕ → X → ℝ) (n : ℕ) (x : X) :
    M.killed C (fun w => ∑ k ∈ Finset.range n, f k w) x =
      ∑ k ∈ Finset.range n, M.killed C (f k) x := by
  induction n with
  | zero => simpa using M.killed_zero C x
  | succ m ih =>
    have h := M.killed_add_const_mul C (fun w => ∑ k ∈ Finset.range m, f k w) (f m) 1 x
    simp only [one_mul] at h
    simp only [Finset.sum_range_succ]
    rw [h, ih]

/-- The key comparison: `W_n + ε ∑_{k<n} u_k ≤ V` outside `C`. -/
theorem key_le {V : X → ℝ} {ε : ℝ} (hV : ∀ x, 0 ≤ V x) (_hε : 0 < ε)
    (hdrift : ∀ y, y ∉ C → M.expect V y ≤ V y - ε) :
    ∀ n y, y ∉ C → M.killedPow C V n y + ε * ∑ k ∈ Finset.range n, M.survival C k y ≤ V y := by
  intro n
  induction n with
  | zero => intro y _; simp [killedPow]
  | succ n ih =>
    intro y hy
    -- `∑_{k<n+1} u_k = 1 + killed (∑_{k<n} u_k)`
    have hsum : ∀ z, ∑ k ∈ Finset.range (n + 1), M.survival C k z =
        1 + M.killed C (fun w => ∑ k ∈ Finset.range n, M.survival C k w) z := by
      intro z
      rw [Finset.sum_range_succ', M.killed_sum_range C, add_comm]
      rfl
    have hstep : M.killedPow C V (n + 1) y +
        ε * ∑ k ∈ Finset.range (n + 1), M.survival C k y =
        ε + M.killed C (fun w => M.killedPow C V n w +
          ε * ∑ k ∈ Finset.range n, M.survival C k w) y := by
      rw [hsum, M.killed_add_const_mul C]
      simp only [killedPow]
      ring
    rw [hstep]
    -- bound the killed term using the induction hypothesis on next states outside `C`
    have hbound : M.killed C (fun w => M.killedPow C V n w +
        ε * ∑ k ∈ Finset.range n, M.survival C k w) y ≤ M.killed C V y := by
      unfold killed
      by_cases h1 : M.hold y
      · simp only [h1, ite_true, hy, ite_false]
        exact ih y hy
      · simp only [h1, ite_false]
        refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (M.p_nonneg y r)
        by_cases h3 : M.next y r ∈ C
        · simp [h3]
        · simp only [h3, ite_false]; exact ih _ h3
    have := hdrift y hy
    have := M.killed_le_expect C hV y
    linarith

/-- **Foster's bound outside `C`.** -/
theorem survival_sum_le_of_not_mem {V : X → ℝ} {ε : ℝ} (hV : ∀ x, 0 ≤ V x) (hε : 0 < ε)
    (hdrift : ∀ y, y ∉ C → M.expect V y ≤ V y - ε) {y : X} (hy : y ∉ C) (n : ℕ) :
    ∑ k ∈ Finset.range n, M.survival C k y ≤ V y / ε := by
  have h := M.key_le C hV hε hdrift n y hy
  have := M.killedPow_nonneg C hV n y
  rw [le_div_iff₀ hε]
  linarith

/-- **Foster's bound from any state**: expected hitting time of `C` after time `0` is at most
`1 + PV(x)/ε`. -/
theorem survival_sum_le {V : X → ℝ} {ε : ℝ} (hV : ∀ x, 0 ≤ V x) (hε : 0 < ε)
    (hdrift : ∀ y, y ∉ C → M.expect V y ≤ V y - ε) (x : X) (n : ℕ) :
    ∑ k ∈ Finset.range n, M.survival C k x ≤ 1 + M.expect V x / ε := by
  have hpart : ∀ z, ∑ k ∈ Finset.range n, M.survival C k z ≤
      ∑ k ∈ Finset.range (n + 1), M.survival C k z := fun z =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ n))
      fun k _ _ => M.survival_nonneg C k z
  refine (hpart x).trans ?_
  rw [Finset.sum_range_succ']
  simp only [survival]
  -- `∑_{k<n} u_{k+1}(x) = killed (∑_{k<n} u_k)(x)` and the killed sum is bounded by `PV/ε`
  have hcomm : ∑ k ∈ Finset.range n, M.killed C (M.survival C k) x =
      M.killed C (fun w => ∑ k ∈ Finset.range n, M.survival C k w) x :=
    (M.killed_sum_range C _ n x).symm
  rw [hcomm, add_comm]
  have hb : M.killed C (fun w => ∑ k ∈ Finset.range n, M.survival C k w) x ≤
      M.killed C (fun w => V w / ε) x := by
    unfold killed
    by_cases h1 : M.hold x
    · simp only [h1, ite_true]
      by_cases h2 : x ∈ C
      · simp [h2]
      · simp only [h2, ite_false]; exact M.survival_sum_le_of_not_mem C hV hε hdrift h2 n
    · simp only [h1, ite_false]
      refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (M.p_nonneg x r)
      by_cases h3 : M.next x r ∈ C
      · simp [h3]
      · simp only [h3, ite_false]; exact M.survival_sum_le_of_not_mem C hV hε hdrift h3 n
  have hk : M.killed C (fun w => V w / ε) x ≤ M.expect V x / ε := by
    have h1 : M.killed C (fun w => V w / ε) x = M.killed C V x / ε := by
      have := M.killed_add_const_mul C (fun _ => 0) V (1 / ε) x
      have h0 : M.killed C (fun _ => (0 : ℝ)) x = 0 := M.killed_zero C x
      simp only [zero_add, h0] at this
      rw [show (fun w => V w / ε) = fun y => 1 / ε * V y from funext fun w => by ring, this]
      ring
    rw [h1]
    exact div_le_div_of_nonneg_right (M.killed_le_expect C hV x) hε.le
  linarith

/-- **`C` is hit with probability one**: the survival probability tends to zero. -/
theorem tendsto_survival_zero {V : X → ℝ} {ε : ℝ} (hV : ∀ x, 0 ≤ V x) (hε : 0 < ε)
    (hdrift : ∀ y, y ∉ C → M.expect V y ≤ V y - ε) (x : X) :
    Tendsto (fun n => M.survival C n x) atTop (𝓝 0) := by
  have hsum : Summable (fun n => M.survival C n x) :=
    summable_of_sum_range_le (fun n => M.survival_nonneg C n x)
      (fun n => M.survival_sum_le C hV hε hdrift x n)
  exact hsum.tendsto_atTop_zero

end FiniteBranchChain

end Foster

namespace Network

open Foster Filter Topology
open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The embedded jump chain of a stochastic mass-action system as a finite-branch chain:
counts with zero exit rate hold, otherwise reaction `r` fires with probability `jumpProb`. -/
noncomputable def jumpChain (N : Network S) (κ : RateConstants N) :
    FiniteBranchChain (S → ℕ) N.R where
  hold n := N.exitRate κ n = 0
  p := N.jumpProb κ
  next := N.jumpNextCount
  p_nonneg := N.jumpProb_nonneg κ
  p_sum n h := N.sum_jumpProb_eq_one κ n (lt_of_le_of_ne (N.exitRate_nonneg κ n) (Ne.symm h))

noncomputable instance (N : Network S) (κ : RateConstants N) :
    DecidablePred (N.jumpChain κ).hold := Classical.decPred _

/-- The generator drift equals the exit rate times the jump-chain drift. -/
theorem observableGenerator_eq_exitRate_mul (N : Network S) (κ : RateConstants N)
    (V : (S → ℕ) → ℝ) (n : S → ℕ) (h : N.exitRate κ n ≠ 0) :
    N.observableGenerator κ V n =
      N.exitRate κ n * ((N.jumpChain κ).expect V n - V n) := by
  classical
  have hpos : 0 < N.exitRate κ n := lt_of_le_of_ne (N.exitRate_nonneg κ n) (Ne.symm h)
  simp only [FiniteBranchChain.expect, jumpChain, h, ite_false]
  rw [mul_sub, Finset.mul_sum, observableGenerator]
  have hsum : N.exitRate κ n * V n = ∑ r, N.stochasticMassActionRate κ n r * V n := by
    rw [exitRate, Finset.sum_mul]
  rw [hsum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hen : N.Enabled n r
  · have hfire : N.fireCount n r = N.jumpNextCount n r := by
      simp [fireCount, hen]; rfl
    rw [hfire, show N.exitRate κ n * (N.jumpProb κ n r *
        V (N.jumpNextCount n r)) = N.stochasticMassActionRate κ n r * V (N.jumpNextCount n r) by
      unfold jumpProb; field_simp]
    ring
  · have h0 := N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen
    rw [h0]
    simp [jumpProb, h0]

/-- A generator drift bound with bounded exit rate gives a jump-chain drift bound. -/
theorem jumpChain_drift_of_generator (N : Network S) (κ : RateConstants N)
    {V : (S → ℕ) → ℝ} {n : S → ℕ} {c Λ : ℝ} (hc : 0 < c)
    (hgen : N.observableGenerator κ V n ≤ -c) (hΛ : N.exitRate κ n ≤ Λ) :
    (N.jumpChain κ).expect V n ≤ V n - c / Λ := by
  have hne : N.exitRate κ n ≠ 0 := by
    intro h0
    have : N.observableGenerator κ V n = 0 := by
      unfold observableGenerator
      refine Finset.sum_eq_zero fun r _ => ?_
      have hr : N.stochasticMassActionRate κ n r = 0 := by
        have hle := Finset.single_le_sum (f := fun r => N.stochasticMassActionRate κ n r)
          (fun r _ => N.stochasticMassActionRate_nonneg κ n r) (Finset.mem_univ r)
        have := N.stochasticMassActionRate_nonneg κ n r
        rw [exitRate] at h0
        linarith
      rw [hr, zero_mul]
    linarith
  have hpos : 0 < N.exitRate κ n := lt_of_le_of_ne (N.exitRate_nonneg κ n) (Ne.symm hne)
  have hΛpos : 0 < Λ := lt_of_lt_of_le hpos hΛ
  rw [N.observableGenerator_eq_exitRate_mul κ V n hne] at hgen
  have hd : (N.jumpChain κ).expect V n - V n ≤ -(c / N.exitRate κ n) := by
    rw [← neg_div, le_div_iff₀ hpos]; linarith
  have : c / Λ ≤ c / N.exitRate κ n := div_le_div_of_nonneg_left hc.le hpos hΛ
  linarith

/-- **Foster's theorem for stochastic reaction networks.** If `V ≥ 0` and the jump-chain drift
satisfies `PV ≤ V - ε` off a set `C` of counts, then from every count `x` the embedded jump chain
hits `C` with probability one, and its expected hitting time is at most `1 + PV(x)/ε`. -/
theorem jumpChain_foster_hitting_time (N : Network S) (κ : RateConstants N)
    (C : Set (S → ℕ)) [DecidablePred (· ∈ C)] {V : (S → ℕ) → ℝ} {ε : ℝ}
    (hV : ∀ n, 0 ≤ V n) (hε : 0 < ε)
    (hdrift : ∀ n, n ∉ C → (N.jumpChain κ).expect V n ≤ V n - ε) (x : S → ℕ) :
    (∀ m, ∑ k ∈ Finset.range m, (N.jumpChain κ).survival C k x ≤
        1 + (N.jumpChain κ).expect V x / ε) ∧
      Tendsto (fun m => (N.jumpChain κ).survival C m x) atTop (𝓝 0) := by
  classical
  exact ⟨fun m => (N.jumpChain κ).survival_sum_le C hV hε hdrift x m,
    (N.jumpChain κ).tendsto_survival_zero C hV hε hdrift x⟩

end Network

end CRNT
