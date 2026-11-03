import CRNT.Stochastic.MinimalSemigroupStochastic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Poisson domination of the number of jumps in a window

This module supplies the **quantitative ingredient** that the path-space reading of Kurtz's law of
large numbers (leaf P8) needs, in a form that does *not* require any measure on the path space.

## 1. The classical statement

For a pure-jump process whose exit rate is bounded by `Λ`, the number of jumps in a window of
length `h` is stochastically dominated by a Poisson random variable of mean `Λ h`:

`P (N_h ≥ k + 1) ≤ P (Poisson(Λ h) ≥ k + 1) = 1 - e^{-Λ h} ∑_{j ≤ k} (Λ h)^j / j!`,

and consequently `P (N_h ≥ k + 1) ≤ (Λ h)^{k+1} / (k+1)!` (the classical Poisson tail bound).
References: O. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Chapter 13 (Poisson
processes, thinning and domination); W. Feller, *An Introduction to Probability Theory and Its
Applications*, Vol. II, Chapter X (the Poisson process and its tail estimates).

## 2. The exact reading of `JumpSystem.P`

The kernel `J.P k t a b` of `CRNT/Stochastic/MinimalSemigroup.lean` is the transition probability of
the chain started at `a` which makes **at most `k` jumps** in the time window `[0, t]` and is at
`b` at time `t`; the recursion `J.P_succ` is the first-jump recursion

`P_{k+1}(t)(a, b) = e^{-q(a) t} [a = b] + ∫₀ᵗ e^{-q(a) s} ∑_i rate_i(a) P_k(t - s)(next_i a, b) ds`,

the second term being "the first jump happens at `s` through channel `i`, and afterwards at most
`k` further jumps occur".  Consequently the kernels are **nested and increasing** in `k`
(`J.P_mono`), and

`∑ b, J.P k t a b` = the probability of **at most** `k` jumps in the window,

so that `1 - ∑ b, J.P k t a b` is the probability of **more than** `k` jumps.  In the library this
quantity is `J.defect k t a` (`CRNT/Stochastic/MinimalSemigroupStochastic.lean`), and it is exactly
the "defect" of the sub-stochastic row.  *The factorial bound of the classical statement is
therefore a bound on the defect, not on the row sum itself*: the row sum `∑ b, J.P k t a b` is at
most `1` and at least `e^{-q t}`, and for `k = 1` it is exactly `1`, so no bound
`∑ b, J.P k t a b ≤ (Λ h)^k / k!` can hold (it fails for `k = 1` and `Λ h < 1`).

## 3. What is proved here

* `poissonTail` is the tail of a Poisson process of rate `Λ`: it is *defined* by the first-jump
  recursion `Π_0(t) = 1 - e^{-Λ t}`, `Π_{k+1}(t) = ∫₀ᵗ e^{-Λ s} Λ Π_k(t - s) ds` (no event; the
  first event at `s` and then at least `k` further events), which is the standard definition of the
  Poisson tail; its classical closed form is `1 - e^{-Λ t} ∑_{j ≤ k} (Λ t)^j / j!`, which is not
  needed below.  Proved here: its continuity, its derivative, its monotonicity, its
  non-negativity and the fact that the tail decreases with the number of events.
* `poisson_defect_le_poisson` is the **stochastic domination** of the jump count:
  `J.defect k t a ≤ poissonTail Λ k t` for every `k`, `t ≥ 0` and `a`, whenever the exit rates
  are bounded by `Λ`.  This is the classical Poisson domination of pure-jump processes.
* `poisson_defect_le` is the **factorial bound** `J.defect k t a ≤ (Λ t)^{k+1} / (k+1)!` under the
  same hypothesis (a uniform version of the library's `JumpSystem.defect_le`).
* `poisson_jumpCount_tail_le` is the tail statement: the probability of more than `m` jumps in a
  window of length `h` is at most the Poisson tail `poissonTail Λ m h`, and in particular at most
  the classical Poisson tail bound `(Λ h)^{m+1} / (m+1)!`.
* `poisson_jumpCount_bounded` is the corollary that the number of jumps in a window is `O(1)` in
  probability: for every window length `t` and every `ε > 0` there is `m` with
  `J.defect m t a ≤ ε` for *every* state `a` (the bound is uniform in the starting state; the
  number `m` of jumps allowed depends on the window length).
* `poisson_hasSum_Pmin_one` records the stochasticity of the minimal transition function under the
  bounded-rate hypothesis, which is what makes the reading of `J.defect` above literal.

**No probability measure on the path space is used anywhere**: the proof manipulates the kernels
`J.P` and their recursions only.  The library has no i.i.d.-exponential measure and no strong
Markov property, so the *identification* of the exit mass with the literal path event
`CRNT.Network.LeavesDuring` still cannot be stated as an equality of probabilities of events; what
can be stated, and is stated here, is the quantitative bound on the number of jumps in a window
that such an identification would need.

## 4. What remains open

The full path-space statement — the probability, on a canonical space of sample paths equipped
with the i.i.d. exponential holding times and endowed with the strong Markov property, of the event
"the chain leaves `B_i` in the `i`-th window" — is still missing; the library has no measure on the
path space (`CRNT.Network.LeavesDuring` is a predicate on the deterministic jump-path structure
`CRNT.Network.JumpPath`, not an event of a probability space).  What this module provides is the
quantitative part of that reading: the jump count in a window is bounded by a Poisson law, so for
every window length the number of jumps is `O(1)` in probability, uniformly in the starting state.
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-! ### The tail of a Poisson process -/

/-- **The tail of a Poisson process of rate `Λ`.**  `poissonTail Λ k t` is the probability that a
Poisson process of rate `Λ` has at least `k + 1` events in the window `[0, t]`; it is defined by
the first-jump recursion, `poissonTail Λ 0 t = 1 - e^{-Λ t}` (no event) and
`poissonTail Λ (k+1) t = ∫₀ᵗ e^{-Λ s} Λ ⋅ poissonTail Λ k (t - s) ds` (the first event happens at
`s`, then at least `k` further events follow in the remaining window). -/
noncomputable def poissonTail (Λ : ℝ) : ℕ → ℝ → ℝ
  | 0, t => 1 - Real.exp (-(Λ * t))
  | k + 1, t => ∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * poissonTail Λ k (t - s))

theorem poissonTail_zero (Λ t : ℝ) : poissonTail Λ 0 t = 1 - Real.exp (-(Λ * t)) := rfl

theorem poissonTail_succ (Λ : ℝ) (k : ℕ) (t : ℝ) :
    poissonTail Λ (k + 1) t = ∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * poissonTail Λ k (t - s)) :=
  rfl

/-- The factorised form of the tail: `e^{-Λ t}` times the integral of `e^{Λ u} Λ Π_k(u)`. -/
theorem poissonTail_form (Λ : ℝ) (k : ℕ) (t : ℝ) :
    poissonTail Λ (k + 1) t
      = Real.exp (-(Λ * t)) * (∫ u in (0:ℝ)..t, Real.exp (Λ * u) * (Λ * poissonTail Λ k u)) := by
  rw [poissonTail_succ]
  have hsub : (∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * poissonTail Λ k (t - s)))
      = ∫ u in (0:ℝ)..t, Real.exp (-(Λ * (t - u))) * (Λ * poissonTail Λ k u) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun u : ℝ => Real.exp (-(Λ * (t - u))) * (Λ * poissonTail Λ k u)) (a := 0) (b := t) t
    simp only [sub_sub_cancel, sub_self, sub_zero] at h
    exact h
  rw [hsub]
  have h1 : (∫ u in (0:ℝ)..t, Real.exp (-(Λ * (t - u))) * (Λ * poissonTail Λ k u))
      = ∫ u in (0:ℝ)..t, Real.exp (-(Λ * t)) * (Real.exp (Λ * u) * (Λ * poissonTail Λ k u)) := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only
    rw [show -(Λ * (t - u)) = -(Λ * t) + Λ * u by ring, Real.exp_add]
    ring
  rw [h1, intervalIntegral.integral_const_mul]

/-- The tail is continuous in the window length. -/
theorem poissonTail_continuous (Λ : ℝ) (k : ℕ) : Continuous fun t => poissonTail Λ k t := by
  induction k with
  | zero =>
      simp only [poissonTail]
      fun_prop
  | succ k ih =>
      have hform : (fun t => poissonTail Λ (k + 1) t)
          = fun t => Real.exp (-(Λ * t))
              * (∫ u in (0:ℝ)..t, Real.exp (Λ * u) * (Λ * poissonTail Λ k u)) :=
        funext (poissonTail_form Λ k)
      rw [hform]
      have hprim : Continuous fun t : ℝ => ∫ u in (0:ℝ)..t, Real.exp (Λ * u) * (Λ * poissonTail Λ k u) :=
        intervalIntegral.continuous_primitive (μ := volume)
          (fun a b => ((by fun_prop : Continuous fun u : ℝ =>
              Real.exp (Λ * u) * (Λ * poissonTail Λ k u)).intervalIntegrable a b)) 0
      exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(Λ * t))).mul hprim

/-- The derivative of the Poisson tail. -/
noncomputable def poissonTail_deriv (Λ : ℝ) : ℕ → ℝ → ℝ
  | 0, t => Λ * Real.exp (-(Λ * t))
  | k + 1, t => Λ * (poissonTail Λ k t - poissonTail Λ (k + 1) t)

/-- The Poisson tail is differentiable, with derivative
`Λ (Π_k(t) - Π_{k+1}(t))`. -/
theorem poissonTail_hasDerivAt (Λ : ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (poissonTail Λ k) (poissonTail_deriv Λ k t) t := by
  induction k with
  | zero =>
      have hlin : HasDerivAt (fun u : ℝ => -(Λ * u)) (-Λ) t := by
        have h0 := ((hasDerivAt_id t).const_mul Λ).neg
        have hf : (fun u : ℝ => -(Λ * u)) = -(fun y => Λ * id y) := by funext y; simp
        rw [hf]
        convert h0 using 1
        ring
      have h1 : HasDerivAt (fun u : ℝ => 1 - Real.exp (-(Λ * u))) (Λ * Real.exp (-(Λ * t))) t := by
        convert hlin.exp.const_sub 1 using 1
        ring
      simpa only [poissonTail_deriv, poissonTail] using h1
  | succ k ih =>
      have hform : (fun u : ℝ => poissonTail Λ (k + 1) u)
          = fun u : ℝ => Real.exp (-(Λ * u))
              * (∫ v in (0:ℝ)..u, Real.exp (Λ * v) * (Λ * poissonTail Λ k v)) :=
        funext (poissonTail_form Λ k)
      have hcont : Continuous fun v : ℝ => Real.exp (Λ * v) * (Λ * poissonTail Λ k v) :=
        (by fun_prop : Continuous fun v : ℝ => Real.exp (Λ * v)).mul
          (continuous_const.mul (poissonTail_continuous Λ k))
      have hH : HasDerivAt (fun u : ℝ => ∫ v in (0:ℝ)..u, Real.exp (Λ * v) * (Λ * poissonTail Λ k v))
          (Real.exp (Λ * t) * (Λ * poissonTail Λ k t)) t := by
        apply intervalIntegral.integral_hasDerivAt_right
        · exact hcont.intervalIntegrable 0 t
        · exact Continuous.stronglyMeasurableAtFilter hcont volume (nhds t)
        · exact hcont.continuousAt
      have hE : HasDerivAt (fun u : ℝ => Real.exp (-(Λ * u))) (-(Λ * Real.exp (-(Λ * t)))) t := by
        have hlin : HasDerivAt (fun u : ℝ => -(Λ * u)) (-Λ) t := by
          have h0 := ((hasDerivAt_id t).const_mul Λ).neg
          have hf : (fun u : ℝ => -(Λ * u)) = -(fun y => Λ * id y) := by funext y; simp
          rw [hf]
          convert h0 using 1
          ring
        have h2 : HasDerivAt (fun u : ℝ => Real.exp (-(Λ * u))) (Real.exp (-(Λ * t)) * -Λ) t := by
          simpa only [id_eq] using hlin.exp
        convert h2 using 1
        ring
      change HasDerivAt (fun u : ℝ => poissonTail Λ (k + 1) u) (poissonTail_deriv Λ (k + 1) t) t
      rw [hform]
      simp only [poissonTail_deriv]
      have hformt : poissonTail Λ (k + 1) t
          = Real.exp (-(Λ * t)) * (∫ v in (0:ℝ)..t, Real.exp (Λ * v) * (Λ * poissonTail Λ k v)) :=
        poissonTail_form Λ k t
      rw [hformt]
      have hprod := hE.mul hH
      have hexp : Real.exp (-(Λ * t)) * Real.exp (Λ * t) = 1 := by
        rw [← Real.exp_add]
        simp
      have hdv :
          (-(Λ * Real.exp (-(Λ * t))) * (∫ v in (0:ℝ)..t, Real.exp (Λ * v) * (Λ * poissonTail Λ k v))
              + Real.exp (-(Λ * t)) * (Real.exp (Λ * t) * (Λ * poissonTail Λ k t)))
            = Λ * (poissonTail Λ k t - Real.exp (-(Λ * t)) *
                (∫ v in (0:ℝ)..t, Real.exp (Λ * v) * (Λ * poissonTail Λ k v))) := by
        linear_combination (Λ * poissonTail Λ k t) * hexp
      exact hprod.congr_deriv hdv

/-- The derivative of the Poisson tail is continuous. -/
theorem poissonTail_deriv_continuous (Λ : ℝ) (k : ℕ) : Continuous (poissonTail_deriv Λ k) := by
  induction k with
  | zero =>
      have h : poissonTail_deriv Λ 0 = fun t : ℝ => Λ * Real.exp (-(Λ * t)) := rfl
      rw [h]
      fun_prop
  | succ k ih =>
      have h : poissonTail_deriv Λ (k + 1)
          = fun t : ℝ => Λ * (poissonTail Λ k t - poissonTail Λ (k + 1) t) := rfl
      rw [h]
      have h1 : Continuous fun t : ℝ => Λ * poissonTail Λ k t :=
        (continuous_const : Continuous (fun _ : ℝ => Λ)).mul (poissonTail_continuous Λ k)
      have h2 : Continuous fun t : ℝ => Λ * poissonTail Λ (k + 1) t :=
        (continuous_const : Continuous (fun _ : ℝ => Λ)).mul (poissonTail_continuous Λ (k + 1))
      convert h1.sub h2 using 1
      funext t
      simp only [Pi.sub_apply]
      ring

/-- The Poisson tail is non-negative on non-negative windows. -/
theorem poissonTail_nonneg (Λ : ℝ) (hΛ : 0 ≤ Λ) (k : ℕ) :
    ∀ {t : ℝ}, 0 ≤ t → 0 ≤ poissonTail Λ k t := by
  induction k with
  | zero =>
      intro t ht
      have h1 : Real.exp (-(Λ * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hΛ ht])
      simp only [poissonTail]
      linarith
  | succ k ih =>
      intro t ht
      rw [poissonTail_succ]
      refine intervalIntegral.integral_nonneg ht ?_
      intro s hs
      have hts : 0 ≤ t - s := by linarith [hs.2]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hΛ (ih hts))

/-- **The tail decreases with the number of events:** `Π_{k+1}(t) ≤ Π_k(t)`. -/
theorem poissonTail_idx_antitone (Λ : ℝ) (hΛ : 0 ≤ Λ) (k : ℕ) :
    ∀ {t : ℝ}, 0 ≤ t → poissonTail Λ (k + 1) t ≤ poissonTail Λ k t := by
  induction k with
  | zero =>
      intro t ht
      have h1 : ∀ s ∈ Set.Icc 0 t, poissonTail Λ 0 (t - s) ≤ 1 := by
        intro s hs
        have hts : 0 ≤ t - s := by linarith [hs.2]
        simp only [poissonTail]
        have h2 : (0 : ℝ) ≤ Real.exp (-(Λ * (t - s))) := Real.exp_pos _ |>.le
        linarith
      have hcont : Continuous fun s : ℝ => Real.exp (-(Λ * s)) * (Λ * poissonTail Λ 0 (t - s)) :=
        (by fun_prop : Continuous fun s : ℝ => Real.exp (-(Λ * s))).mul
          (continuous_const.mul ((poissonTail_continuous Λ 0).comp
            (continuous_const.sub continuous_id)))
      have hcont1 : Continuous fun s : ℝ => Real.exp (-(Λ * s)) * (Λ * 1) :=
        (by fun_prop : Continuous fun s : ℝ => Real.exp (-(Λ * s))).mul
          (continuous_const.mul (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))))
      have hInt1 : IntervalIntegrable (fun s : ℝ => Real.exp (-(Λ * s)) * (Λ * poissonTail Λ 0 (t - s)))
          volume 0 t := hcont.intervalIntegrable 0 t
      have hInt2 : IntervalIntegrable (fun s : ℝ => Real.exp (-(Λ * s)) * (Λ * 1))
          volume 0 t := hcont1.intervalIntegrable 0 t
      have hmono : (∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * poissonTail Λ 0 (t - s)))
          ≤ ∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * 1) := by
        refine intervalIntegral.integral_mono_on ht hInt1 hInt2 ?_
        intro s hs
        have hmul := mul_le_mul_of_nonneg_left (h1 s hs)
          (mul_nonneg hΛ ((Real.exp_pos (-(Λ * s))).le))
        linarith
      have hconv : (∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * 1))
          = ∫ s in (0:ℝ)..t, Λ * Real.exp (-(Λ * s)) := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      rw [poissonTail_succ]
      calc (∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * poissonTail Λ 0 (t - s)))
          ≤ ∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * 1) := hmono
        _ = 1 - Real.exp (-(Λ * t)) := by rw [hconv]; exact integral_exp_decay Λ t
        _ = poissonTail Λ 0 t := (poissonTail_zero Λ t).symm
  | succ k ih =>
      intro t ht
      have hcont1 : Continuous fun s : ℝ => Real.exp (-(Λ * s)) * (Λ * poissonTail Λ (k + 1) (t - s)) :=
        (by fun_prop : Continuous fun s : ℝ => Real.exp (-(Λ * s))).mul
          (continuous_const.mul ((poissonTail_continuous Λ (k + 1)).comp
            (continuous_const.sub continuous_id)))
      have hcont2 : Continuous fun s : ℝ => Real.exp (-(Λ * s)) * (Λ * poissonTail Λ k (t - s)) :=
        (by fun_prop : Continuous fun s : ℝ => Real.exp (-(Λ * s))).mul
          (continuous_const.mul ((poissonTail_continuous Λ k).comp
            (continuous_const.sub continuous_id)))
      have hInt1 : IntervalIntegrable
          (fun s : ℝ => Real.exp (-(Λ * s)) * (Λ * poissonTail Λ (k + 1) (t - s)))
          volume 0 t := hcont1.intervalIntegrable 0 t
      have hInt2 : IntervalIntegrable
          (fun s : ℝ => Real.exp (-(Λ * s)) * (Λ * poissonTail Λ k (t - s)))
          volume 0 t := hcont2.intervalIntegrable 0 t
      have hmono : (∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * poissonTail Λ (k + 1) (t - s)))
          ≤ ∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * poissonTail Λ k (t - s)) := by
        refine intervalIntegral.integral_mono_on ht hInt1 hInt2 ?_
        intro s hs
        have hts : 0 ≤ t - s := by linarith [hs.2]
        have hle := ih hts
        have hmul := mul_le_mul_of_nonneg_left hle (mul_nonneg hΛ ((Real.exp_pos (-(Λ * s))).le))
        linarith
      rw [poissonTail_succ]
      calc (∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * poissonTail Λ (k + 1) (t - s)))
          ≤ ∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * poissonTail Λ k (t - s)) := hmono
        _ = poissonTail Λ (k + 1) t := (poissonTail_succ Λ k t).symm

/-- The derivative of the Poisson tail is non-negative on non-negative windows. -/
theorem poissonTail_deriv_nonneg (Λ : ℝ) (hΛ : 0 ≤ Λ) (k : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ poissonTail_deriv Λ k u := by
  cases k with
  | zero =>
      have h : poissonTail_deriv Λ 0 = fun t : ℝ => Λ * Real.exp (-(Λ * t)) := rfl
      rw [h]
      positivity
  | succ k =>
      have h : poissonTail_deriv Λ (k + 1)
          = fun t : ℝ => Λ * (poissonTail Λ k t - poissonTail Λ (k + 1) t) := rfl
      rw [h]
      have hle := poissonTail_idx_antitone Λ hΛ k hu
      have hmul := mul_nonneg hΛ (sub_nonneg.mpr hle)
      linarith

/-- **The Poisson tail is non-decreasing in the window length** (on non-negative windows). -/
theorem poissonTail_monotoneOn (Λ : ℝ) (hΛ : 0 ≤ Λ) (k : ℕ) :
    MonotoneOn (poissonTail Λ k) (Ici 0) := by
  have hdiff : ∀ x, HasDerivAt (poissonTail Λ k) (poissonTail_deriv Λ k x) x :=
    poissonTail_hasDerivAt Λ k
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    ((poissonTail_continuous Λ k).continuousOn) ?_ ?_
  · intro x _
    exact (hdiff x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hdiff x).deriv]
    exact poissonTail_deriv_nonneg Λ hΛ k hx.le

/-! ### The comparison of two exponential densities -/

/-- **The `Exp(Λ)` measure dominates the `Exp(q)` measure against a decreasing function.**
If `0 ≤ q ≤ Λ`, `t ≥ 0`, and `f` is `C¹` on `[0, t]` with `f' ≤ 0` and `f ≥ 0` there, then
`∫₀ᵗ f(s) q e^{-q s} ds ≤ ∫₀ᵗ f(s) Λ e^{-Λ s} ds`: the distribution of `Exp(q)` is stochastically
larger than that of `Exp(Λ)`, and `f` is decreasing.  This is the comparison step in the proof of
the Poisson domination. -/
theorem poisson_exp_integral_mono {q Λ t : ℝ} (ht : 0 ≤ t) (hq : 0 ≤ q) (hqΛ : q ≤ Λ)
    {f f' : ℝ → ℝ} (hf' : Continuous f') (hfd : ∀ x, HasDerivAt f (f' x) x)
    (hfp : ∀ x ∈ Set.Icc 0 t, f' x ≤ 0) (hfn : ∀ x ∈ Set.Icc 0 t, 0 ≤ f x) :
    ∫ s in (0:ℝ)..t, f s * (q * Real.exp (-(q * s)))
      ≤ ∫ s in (0:ℝ)..t, f s * (Λ * Real.exp (-(Λ * s))) := by
  have hparts (μ : ℝ) (hμ : 0 ≤ μ) :
      (∫ s in (0:ℝ)..t, f s * (μ * Real.exp (-(μ * s))))
        = f t * (-Real.exp (-(μ * t))) - f 0 * (-Real.exp (-(μ * 0)))
          - ∫ s in (0:ℝ)..t, f' s * (-Real.exp (-(μ * s))) := by
    have hv : ∀ x, HasDerivAt (fun y : ℝ => -Real.exp (-(μ * y))) (μ * Real.exp (-(μ * x))) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => -(μ * y)) (-μ) x := by
        have h0 := ((hasDerivAt_id x).const_mul μ).neg
        have hf2 : (fun y : ℝ => -(μ * y)) = -(fun y => μ * id y) := by funext y; simp
        rw [hf2]
        convert h0 using 1
        ring
      have h2 := h1.exp
      have h3 := h2.neg
      convert h3 using 1
      ring
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := f) (u' := f') (v := fun y : ℝ => -Real.exp (-(μ * y)))
      (v' := fun y : ℝ => μ * Real.exp (-(μ * y))) (a := 0) (b := t)
      (fun x _ => hfd x) (fun x _ => hv x)
      (hf'.intervalIntegrable 0 t)
      ((by fun_prop : Continuous fun y : ℝ => μ * Real.exp (-(μ * y))).intervalIntegrable 0 t)
  rw [hparts q hq, hparts Λ (le_trans hq hqΛ)]
  have hmono : (∫ s in (0:ℝ)..t, f' s * Real.exp (-(q * s)))
      ≤ ∫ s in (0:ℝ)..t, f' s * Real.exp (-(Λ * s)) := by
    refine intervalIntegral.integral_mono_on ht
      ((by fun_prop : Continuous fun s : ℝ => f' s * Real.exp (-(q * s))).intervalIntegrable 0 t)
      ((by fun_prop : Continuous fun s : ℝ => f' s * Real.exp (-(Λ * s))).intervalIntegrable 0 t) ?_
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hst : s ≤ t := hs.2
    have he : Real.exp (-(Λ * s)) ≤ Real.exp (-(q * s)) := by
      apply Real.exp_le_exp.mpr
      have hmn : -(Λ * s) ≤ -(q * s) := by
        have := mul_le_mul_of_nonneg_right hqΛ hs0
        linarith
      exact hmn
    have hf'neg : f' s ≤ 0 := hfp s ⟨hs0, hst⟩
    have hmul := mul_le_mul_of_nonpos_right he hf'neg
    linarith
  have hft : 0 ≤ f t := hfn t ⟨ht, le_rfl⟩
  have he : Real.exp (-(Λ * t)) ≤ Real.exp (-(q * t)) := by
    apply Real.exp_le_exp.mpr
    have hmn : -(Λ * t) ≤ -(q * t) := by
      have := mul_le_mul_of_nonneg_right hqΛ ht
      linarith
    exact hmn
  have hprod : 0 ≤ f t * (Real.exp (-(q * t)) - Real.exp (-(Λ * t))) :=
    mul_nonneg hft (sub_nonneg.mpr he)
  have hconv' : (∫ s in (0:ℝ)..t, f' s * (-Real.exp (-(q * s))))
      = -(∫ s in (0:ℝ)..t, f' s * Real.exp (-(q * s))) := by
    have h1 : (∫ s in (0:ℝ)..t, f' s * (-Real.exp (-(q * s))))
        = ∫ s in (0:ℝ)..t, -(f' s * Real.exp (-(q * s))) := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    rw [h1, intervalIntegral.integral_neg]
  have hconv2' : (∫ s in (0:ℝ)..t, f' s * (-Real.exp (-(Λ * s))))
      = -(∫ s in (0:ℝ)..t, f' s * Real.exp (-(Λ * s))) := by
    have h1 : (∫ s in (0:ℝ)..t, f' s * (-Real.exp (-(Λ * s))))
        = ∫ s in (0:ℝ)..t, -(f' s * Real.exp (-(Λ * s))) := by
      apply intervalIntegral.integral_congr
      intro s _
      ring
    rw [h1, intervalIntegral.integral_neg]
  rw [hconv', hconv2']
  simp only [Real.exp_zero, mul_zero, neg_zero]
  linarith

/-! ### The Poisson domination of the jump count -/

/-- **Poisson domination of the number of jumps in a window.**
If the exit rates of the jump system are bounded by `Λ`, then the probability that the chain started
at `a` makes **more than** `k` jumps in the window `[0, t]` is at most the probability that a
Poisson process of rate `Λ` makes more than `k` jumps in the same window:
`J.defect k t a ≤ poissonTail Λ k t`.  This is the classical Poisson domination of pure-jump
processes (Kallenberg, *Foundations of Modern Probability*, 2nd ed., Ch. 13). -/
theorem poisson_defect_le_poisson {Λ : ℝ} (hΛ : ∀ a, J.q a ≤ Λ) (k : ℕ) :
    ∀ (a : α) {t : ℝ}, 0 ≤ t → J.defect k t a ≤ poissonTail Λ k t := by
  induction k with
  | zero =>
      intro a t ht
      have hΛ0 : 0 ≤ Λ := le_trans (J.q_nonneg a) (hΛ a)
      have hqΛ : J.q a ≤ Λ := hΛ a
      have hexp : Real.exp (-(Λ * t)) ≤ Real.exp (-(J.q a * t)) := by
        apply Real.exp_le_exp.mpr
        have hmn : -(Λ * t) ≤ -(J.q a * t) := by
          have := mul_le_mul_of_nonneg_right hqΛ ht
          linarith
        exact hmn
      have hdef : J.defect 0 t a = 1 - Real.exp (-(J.q a * t)) := by
        have hdm : J.defect 0 t a = 1 - J.mass 0 t a := rfl
        rw [hdm, J.mass_zero]
      rw [hdef, poissonTail_zero]
      linarith
  | succ k ih =>
      intro a t ht
      have hΛ0 : 0 ≤ Λ := le_trans (J.q_nonneg a) (hΛ a)
      rw [J.defect_succ]
      have hcontD : ∀ i, Continuous fun s : ℝ => J.defect k (t - s) (J.next i a) :=
        fun i => ((continuous_const.sub (J.continuous_mass k (J.next i a))).comp
          (continuous_const.sub continuous_id))
      have hcontP : ∀ i : J.ι, Continuous fun s : ℝ => poissonTail Λ k (t - s) :=
        fun i => (poissonTail_continuous Λ k).comp (continuous_const.sub continuous_id)
      have h1 : (∫ s in (0:ℝ)..t, Real.exp (-(J.q a * s)) *
              ∑ i, J.rate i a * J.defect k (t - s) (J.next i a))
          ≤ ∫ s in (0:ℝ)..t, Real.exp (-(J.q a * s)) *
              ∑ i, J.rate i a * poissonTail Λ k (t - s) := by
        have hInt1 : IntervalIntegrable (fun s : ℝ => Real.exp (-(J.q a * s)) *
              ∑ i, J.rate i a * J.defect k (t - s) (J.next i a)) volume 0 t :=
          ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(J.q a * s))).mul
            (continuous_finsetSum _ fun i _ => continuous_const.mul (hcontD i))).intervalIntegrable 0 t
        have hInt2 : IntervalIntegrable (fun s : ℝ => Real.exp (-(J.q a * s)) *
              ∑ i, J.rate i a * poissonTail Λ k (t - s)) volume 0 t :=
          ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(J.q a * s))).mul
            (continuous_finsetSum _ fun i _ => continuous_const.mul (hcontP i))).intervalIntegrable 0 t
        refine intervalIntegral.integral_mono_on ht hInt1 hInt2 ?_
        intro s hs
        have hts : 0 ≤ t - s := by linarith [hs.2]
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (ih (J.next i a) hts) (J.rate_nonneg i a)
      have hpoint : ∀ s : ℝ, Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * poissonTail Λ k (t - s)
          = Real.exp (-(J.q a * s)) * (J.q a * poissonTail Λ k (t - s)) := by
        intro s
        have hsum : (∑ i, J.rate i a) = J.q a := rfl
        calc Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * poissonTail Λ k (t - s)
            = Real.exp (-(J.q a * s)) * ((∑ i, J.rate i a) * poissonTail Λ k (t - s)) := by
              rw [Finset.sum_mul]
            _ = Real.exp (-(J.q a * s)) * (J.q a * poissonTail Λ k (t - s)) := by
              rw [hsum]
      have h2 : (∫ s in (0:ℝ)..t, Real.exp (-(J.q a * s)) *
              ∑ i, J.rate i a * poissonTail Λ k (t - s))
          = ∫ s in (0:ℝ)..t, Real.exp (-(J.q a * s)) * (J.q a * poissonTail Λ k (t - s)) := by
        apply intervalIntegral.integral_congr
        intro s _
        exact hpoint s
      have hq : 0 ≤ J.q a := J.q_nonneg a
      have hqΛ : J.q a ≤ Λ := hΛ a
      have hfd : ∀ x, HasDerivAt (fun s : ℝ => poissonTail Λ k (t - s))
          (poissonTail_deriv Λ k (t - x) * (-1)) x := by
        intro x
        have hd : HasDerivAt (fun y : ℝ => t - y) (-1) x := by
          have h := (hasDerivAt_id x).const_sub t
          simpa only [id_eq] using h
        exact (poissonTail_hasDerivAt Λ k (t - x)).comp (x := x)
          (h := fun y : ℝ => t - y) hd
      have hf' : Continuous fun s : ℝ => poissonTail_deriv Λ k (t - s) * (-1) := by
        have hcont : Continuous fun s : ℝ => poissonTail_deriv Λ k (t - s) :=
          (poissonTail_deriv_continuous Λ k).comp
            ((continuous_const : Continuous (fun _ : ℝ => t)).sub continuous_id)
        exact hcont.mul (continuous_const : Continuous (fun _ : ℝ => (-1 : ℝ)))
      have hfp : ∀ x ∈ Set.Icc 0 t, poissonTail_deriv Λ k (t - x) * (-1) ≤ 0 := by
        intro x hx
        have hts : 0 ≤ t - x := by linarith [hx.2]
        have hnonneg := poissonTail_deriv_nonneg Λ hΛ0 k hts
        linarith
      have hfn : ∀ x ∈ Set.Icc 0 t, 0 ≤ poissonTail Λ k (t - x) := by
        intro x hx
        have hts : 0 ≤ t - x := by linarith [hx.2]
        exact poissonTail_nonneg Λ hΛ0 k hts
      have hcmp := poisson_exp_integral_mono ht hq hqΛ hf' hfd hfp hfn
      have hconvL : (∫ s in (0:ℝ)..t, poissonTail Λ k (t - s) * (J.q a * Real.exp (-(J.q a * s))))
          = ∫ s in (0:ℝ)..t, Real.exp (-(J.q a * s)) * (J.q a * poissonTail Λ k (t - s)) := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      have hconvR : (∫ s in (0:ℝ)..t, poissonTail Λ k (t - s) * (Λ * Real.exp (-(Λ * s))))
          = ∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * poissonTail Λ k (t - s)) := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      rw [hconvL, hconvR] at hcmp
      calc (∫ s in (0:ℝ)..t, Real.exp (-(J.q a * s)) *
              ∑ i, J.rate i a * J.defect k (t - s) (J.next i a))
          ≤ ∫ s in (0:ℝ)..t, Real.exp (-(J.q a * s)) *
              ∑ i, J.rate i a * poissonTail Λ k (t - s) := h1
        _ = ∫ s in (0:ℝ)..t, Real.exp (-(J.q a * s)) * (J.q a * poissonTail Λ k (t - s)) := h2
        _ ≤ ∫ s in (0:ℝ)..t, Real.exp (-(Λ * s)) * (Λ * poissonTail Λ k (t - s)) := hcmp
        _ = poissonTail Λ (k + 1) t := (poissonTail_succ Λ k t).symm

/-- **The factorial bound.**  If the exit rates are bounded by `Λ`, the probability that the chain
started at `a` makes more than `k` jumps in the window `[0, t]` is at most the classical Poisson
tail bound `(Λ t)^{k+1} / (k+1)!`.  This is the uniform version of the library's
`JumpSystem.defect_le`. -/
theorem poisson_defect_le {Λ : ℝ} (hΛ : ∀ a, J.q a ≤ Λ) (k : ℕ) :
    ∀ (a : α) {t : ℝ}, 0 ≤ t → J.defect k t a ≤ (Λ * t) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
  intro a t ht
  refine J.defect_le (fun c _ => hΛ c) k a Relation.ReflTransGen.refl t ht

/-- **The tail of the jump count.**  The probability that the chain started at `a` makes more than
`m` jumps in the window `[0, h]` is at most the Poisson tail `poissonTail Λ m h`, and in particular
at most the classical Poisson tail bound `(Λ h)^{m+1} / (m+1)!`. -/
theorem poisson_jumpCount_tail_le {Λ : ℝ} (hΛ : ∀ a, J.q a ≤ Λ) (m : ℕ) :
    ∀ (a : α) {h : ℝ}, 0 ≤ h →
      J.defect m h a ≤ poissonTail Λ m h ∧
        J.defect m h a ≤ (Λ * h) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
  intro a h hnonneg
  have h1 := poisson_defect_le_poisson J hΛ m a hnonneg
  have h2 := poisson_defect_le J hΛ m a hnonneg
  exact ⟨h1, h2⟩

/-- **The number of jumps in a window is `O(1)` in probability.**  For every `ε > 0` there is a
number `m` of jumps such that the probability of more than `m` jumps in the window `[0, t]`, started
at any state `a`, is at most `ε`; the bound is uniform in `a` and in `t`. -/
theorem poisson_jumpCount_bounded {Λ : ℝ} (hΛ : ∀ a, J.q a ≤ Λ) (t : ℝ) (ht : 0 ≤ t) :
    ∀ (ε : ℝ), 0 < ε → ∃ (m : ℕ), ∀ (a : α), J.defect m t a ≤ ε := by
  intro ε hε
  have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop (Λ * t)
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨k, ?_⟩
  intro a
  have hdef := poisson_defect_le J hΛ k a ht
  have hk1 := hk (k + 1) (Nat.le_succ k)
  exact le_of_lt (lt_of_le_of_lt hdef hk1)

/-- **Stochasticity of the minimal transition function under bounded exit rates.**  The row of
`Pmin(t)` sums to `1`, which is what makes the reading of `J.defect` (the probability of more than
`k` jumps) literal. -/
theorem poisson_hasSum_Pmin_one {Λ : ℝ} (hΛ : ∀ a, J.q a ≤ Λ) (a : α) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun b => J.Pmin t a b) 1 :=
  J.hasSum_Pmin_one (fun c _ => hΛ c) ht

/-! ### The principal declarations -/

#print axioms CRNT.JumpSystem.poisson_defect_le_poisson
#print axioms CRNT.JumpSystem.poisson_defect_le
#print axioms CRNT.JumpSystem.poisson_jumpCount_tail_le
#print axioms CRNT.JumpSystem.poisson_jumpCount_bounded
#print axioms CRNT.JumpSystem.poisson_hasSum_Pmin_one
#print axioms CRNT.JumpSystem.poisson_exp_integral_mono

end JumpSystem

end CRNT
