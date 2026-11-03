import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.Compact
import CRNT.Dynamics.DelayExistence

/-!
# The Halanay inequality and the semistability of the linear delay equation

This module supplies the last ingredient of field-map leaf **E3 (non-isothermal and delay
systems)**: the **Halanay comparison principle**, its quantitative form (the Grönwall-type
estimate with an exponential bound), and the resulting **semistability theorem** for the scalar
linear delay equation

`ẋ(t) = -a x(t) + b x(t - τ)`,   `τ > 0`.

## The Halanay inequality

The classical **Halanay inequality** compares a function satisfying a *delay differential
inequality* with the exponential decay that dominates it.  In the form used here:

> If `w` is differentiable on `[0, ∞)`, satisfies
> `w'(t) ≤ -α w(t) + β w(t - τ)` with `β ≥ 0`, and satisfies `w(t) ≤ 0` on the history
> `[-τ, 0]`, then `w(t) ≤ 0` for all `t ≥ -τ`.

Reference: A. A. Halanay, *On the theory of stability of differential equations*, Proc. 3rd
All-Union Congress on Theoretical Mechanics (Moscow, 1968), 57–72; see also J. K. Hale,
*Ordinary Differential Equations*, Wiley 1980, Chapter 3 ("The Halanay inequality"), and
Halanay, *Differential Equations and Applications*, 1983.

This is `halanay_nonpos` of this module.

The *quantitative* version (`halanay_le_exp`) says: if in addition `c > 0`, `d ≥ 0`, `ε > 0`
satisfy the **admissible rate condition**

`ε + d e^{ε τ} ≤ c`,

and `w(t) ≤ M` on the history `[-τ, 0]` with `M ≥ 0`, then

`w(t) ≤ M e^{-ε t}`   for all `t ≥ 0`.

The proof is the classical one: the exponential `z(t) = w(t) e^{ε t}` satisfies the delay
inequality `z' ≤ -(c - ε) z + d e^{ε τ} z(· - τ)`, and since `c - ε ≥ d e^{ε τ}` the shifted
function `z - M` satisfies the delay inequality of `halanay_nonpos` with `β = d e^{ε τ} ≥ 0`; the
conclusion `z ≤ M` is the estimate.

## Why the naive rate `c - d` is wrong

For the *scalar* delay inequality `w' ≤ -c w + d w(· - τ)` the rate is **not** `c - d`.  The
rate is the unique positive root `ε` of the *characteristic* equation

`ε + d e^{ε τ} = c`,

which is *smaller* than `c - d` as soon as `d ≠ 0` (`e^{ε τ} > 1`).  The rate `c - d` is not even
admissible: it satisfies `ε + d e^{ε τ} ≤ c` only if `d e^{ε τ} ≤ d`, i.e. never for `d > 0`.
The counterexample is already recorded in `CRNT.Dynamics.DelayExistence` (module docstring,
lines 65–70): for `a = 1`, `b = 1/2`, `τ = 1` and the constant history `φ ≡ 1` the solution
obeys `x(1) = (1 + e^{-1})/2 > e^{-1/2}`, so an estimate with the rate `a - |b|` fails at `t = 1`.
This module uses the *admissible* rate of `CRNT.Dynamics.delayLinear_rate_exists` throughout.

## The semistability of the linear delay equation

`delayLinear_semistability` is the headline result of this module:

> Let `τ > 0` and `a > |b|`, let `φ` be a continuous history and let `X` solve
> `ẋ(t) = -a x(t) + b x(t - τ)` on `[0, ∞)` with `X(t) = φ(t)` for `t ≤ 0`.  Then
> `X(t) → 0` as `t → ∞`.

The proof has three steps.

1. *The square of a solution satisfies a scalar delay inequality.*  If `u = x²` then
   `u' = 2 x ẋ = -2 a x² + 2 b x x(· - τ)`, and the algebraic estimate
   `2 b u v ≤ |b| (u² + v²)` (i.e. `2 |u v| ≤ u² + v²`) gives
   `u' ≤ -(2a - |b|) u + |b| u(· - τ)` (`delayLinear_sq_deriv_le`).
2. *The Halanay estimate.*  `CRNT.Dynamics.delayLinear_rate_exists` provides `ε > 0` with
   `ε + |b| e^{ε τ} ≤ 2a - |b|`, which is exactly the admissible rate condition of
   `halanay_le_exp` with `c = 2a - |b| > 0` and `d = |b| ≥ 0`.  The history is bounded
   (`φ` is continuous, the history interval is compact), so
   `x(t)² ≤ M e^{-ε t}` for `t ≥ 0`.
3. *Conclusion.*  `x(t)² → 0`, hence `|x(t)| → 0`, hence `x(t) → 0`.

The result is compatible with the rest of the repository:

* `CRNT.Dynamics.delayLinear_rate_exists` supplies the admissible rate used in step 2;
* `CRNT.Dynamics.delayLinear_constant_solution` and
  `CRNT.Dynamics.delayLinear_constant_not_tendsto` describe the *obstruction* at `b = a`:
  there the constant trajectories are solutions and do not decay.  The present theorem covers
  the complementary regime `a > |b|`, in which *every* solution decays;
* `CRNT.Dynamics.delay_constHistory_isSolution` identifies the equilibria of the delay dynamics
  with the constant trajectories, so `delayLinear_semistability` says that the only equilibrium
  is the zero equilibrium and that it attracts every trajectory.

## A remark on the sign of the bound `M`

The estimate `w(t) ≤ M e^{-ε t}` of `halanay_le_exp` requires `M ≥ 0`; for `M < 0` it is
**false**, because the delayed term `d w(t - τ)` is then *negative* and increases the solution.
A *machine-checked* counterexample is given at the end of this module: with

* `c = 2`, `d = 1`, `τ = 1`,
* the admissible rate `ε = log (4/3)` (indeed `ε + d e^{ε τ} = log (4/3) + 4/3 < 2 = c`),
* the history bound `M = -1`,
* the function `w(t) = -e^{-λ t}` with `λ = log (3/2)`,

all the hypotheses of `halanay_le_exp` hold (`halanay_le_exp_negM_w`,
`halanay_le_exp_negM_rate`), but the conclusion fails at `t = 1`, where
`w(1) = -2/3 > -3/4 = M e^{-ε}` (`halanay_le_exp_negM_fails`).

For an arbitrary bound `M` the statement that *is* true is `halanay_le_exp_max`:
`w(t) ≤ max M 0 · e^{-ε t}`; for `M < 0` the delay inequality forces `w ≤ 0` on the whole half
line (this is `halanay_nonpos` applied to `w` itself).

## What is *not* proved here

* The **full Hayes criterion** (all the roots of the characteristic equation
  `λ = -a + b e^{-λ τ}` have negative real part) is *not* formalised.  Only the two ends of the
  criterion are covered: `a > |b|` (the regime of `delayLinear_semistability`, in which the
  admissible rate exists) and `b = a` (the regime of `delayLinear_constant_not_tendsto`).  The
  intermediate case `b < 0 ≤ a` is not covered.
* The **path-space LaSalle theory** (the invariance principle for delay equations on the path
  space `C([-τ, 0], ℝ)`, the ω-limit set of the delay dynamics, and the convergence of the
  trajectories to a *connected* set of equilibria) is *not* proved here.  This module proves
  the *linear* semistability statement only; the nonlinear case would additionally require the
  boundedness of the trajectories, which is not available for the delay equations of
  `CRNT.Extensions.DelayMassAction`.
* The characteristic equation of the linear delay equation is not analysed; the rate is taken
  from `CRNT.Dynamics.delayLinear_rate_exists`.
-/
namespace CRNT
namespace Dynamics

open Filter Topology Set

set_option maxHeartbeats 800000

/-! ### The Halanay comparison principle -/

/-- **The Halanay inequality (nonpositive form).  If `w` satisfies the *delay inequality*
`w' ≤ -α w + β w(· - τ)` with `β ≥ 0` and `w ≤ 0` on the history `[-τ, 0]`, then `w ≤ 0`
on `[-τ, ∞)`.

This is the classical comparison principle of Halanay. -/
theorem halanay_nonpos {w w' : ℝ → ℝ} {α β τ : ℝ}
    (hτ : 0 < τ) (hβ : 0 ≤ β)
    (hw' : ∀ t ≥ 0, HasDerivAt w (w' t) t)
    (hbound : ∀ t ≥ 0, w' t ≤ -α * w t + β * w (t - τ))
    (hinit : ∀ t ∈ Set.Icc (-τ) 0, w t ≤ 0) :
    ∀ t ≥ -τ, w t ≤ 0 := by
  set z : ℝ → ℝ := fun t => w t * Real.exp (α * t) with hzdef
  have hexpderiv : ∀ t : ℝ, HasDerivAt (fun s => Real.exp (α * s)) (α * Real.exp (α * t)) t := by
    intro t
    have h1 := (Real.hasDerivAt_exp (α * t)).comp_of_eq t ((hasDerivAt_id t).const_mul α) rfl
    convert h1 using 1
    · funext s; rfl
    · ring
  have hz_deriv : ∀ t ≥ 0, HasDerivAt z (Real.exp (α * t) * (w' t + α * w t)) t := by
    intro t ht
    have h1 := (hw' t ht).mul (hexpderiv t)
    convert h1 using 1 ; ring
  have hz_cont : ∀ t ≥ 0, ContinuousAt z t := fun t ht => (hz_deriv t ht).continuousAt
  have hz_bound : ∀ t ≥ 0, Real.exp (α * t) * (w' t + α * w t)
      ≤ (β * Real.exp (α * τ)) * z (t - τ) := by
    intro t ht
    have h1 : w' t + α * w t ≤ β * w (t - τ) := by linarith [hbound t ht]
    have hexp : 0 < Real.exp (α * t) := Real.exp_pos _
    have h2 : Real.exp (α * t) * (w' t + α * w t) ≤ Real.exp (α * t) * (β * w (t - τ)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hexp)
    have h3 : Real.exp (α * t) * (β * w (t - τ)) = β * Real.exp (α * τ) * z (t - τ) := by
      rw [hzdef]
      have hexp2 : Real.exp (α * t) = Real.exp (α * τ) * Real.exp (α * (t - τ)) := by
        rw [show α * t = α * τ + α * (t - τ) by ring, Real.exp_add]
      rw [hexp2]
      ring
    exact h2.trans_eq h3
  have hz_nonpos : ∀ n : ℕ, ∀ t ∈ Set.Icc (-τ) (n * τ), z t ≤ 0 := by
    intro n
    induction n with
    | zero =>
        intro t ht
        rw [hzdef]
        exact mul_nonpos_of_nonpos_of_nonneg (hinit t (by simpa using ht)) (Real.exp_nonneg _)
    | succ n ih =>
        have hnτ : ((n + 1 : ℕ) : ℝ) * τ = (n : ℝ) * τ + τ := by push_cast; ring
        have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hnτ0 : 0 ≤ (n : ℝ) * τ := mul_nonneg hn0 hτ.le
        have hnegτ : -τ ≤ (n : ℝ) * τ - τ := by simpa using sub_le_sub_right hnτ0 τ
        have hminτ : -τ ≤ 0 := by linarith
        have hnτle : (n : ℝ) * τ ≤ ((n : ℝ) + 1) * τ := by
          have h1 : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
          exact mul_le_mul_of_nonneg_right h1 hτ.le
        intro t ht
        have ht2 : t ≤ (n : ℝ) * τ + τ := by linarith [ht.2]
        by_cases hle : t ≤ n * τ
        · exact ih t ⟨ht.1, hle⟩
        · have htIcc : t ∈ Set.Icc (n * τ) ((n + 1) * τ) :=
            ⟨by linarith, by linarith [ht2]⟩
          have hconv : Convex ℝ (Set.Icc (n * τ) ((n + 1) * τ)) := convex_Icc _ _
          have hcont : ContinuousOn z (Set.Icc (n * τ) ((n + 1) * τ)) := by
            intro x hx
            exact (hz_cont x (le_trans hnτ0 hx.1)).continuousWithinAt
          have hdiff : DifferentiableOn ℝ z (interior (Set.Icc (n * τ) ((n + 1) * τ))) := by
            intro x hx
            rw [interior_Icc] at hx
            have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt hnτ0 hx.1)
            exact (hz_deriv x hx0).differentiableAt.differentiableWithinAt
          have hnonpos : ∀ x ∈ interior (Set.Icc (n * τ) ((n + 1) * τ)), deriv z x ≤ 0 := by
            intro x hx
            rw [interior_Icc] at hx
            have hx0 : 0 ≤ x := le_of_lt (lt_of_le_of_lt hnτ0 hx.1)
            have hd : HasDerivAt z (Real.exp (α * x) * (w' x + α * w x)) x := hz_deriv x hx0
            rw [hd.deriv]
            have hb := hz_bound x hx0
            have hzlt : z (x - τ) ≤ 0 := by
              refine ih (x - τ) ⟨?_, ?_⟩
              · exact le_trans hnegτ (le_of_lt (sub_lt_sub_right hx.1 τ))
              · have h1 : x - τ < (n : ℝ) * τ := by
                  have h2 := sub_lt_sub_right hx.2 τ
                  convert h2 using 1 ; ring
                exact le_of_lt h1
            have hcoef : 0 ≤ β * Real.exp (α * τ) := mul_nonneg hβ (Real.exp_nonneg _)
            have hmul : (β * Real.exp (α * τ)) * z (x - τ) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos hcoef hzlt
            linarith [hb, hmul]
          have hanti : AntitoneOn z (Set.Icc (n * τ) ((n + 1) * τ)) :=
            antitoneOn_of_deriv_nonpos hconv hcont hdiff hnonpos
          have hz0 : z (n * τ) ≤ 0 := ih (n * τ) ⟨le_trans hminτ hnτ0, le_rfl⟩
          have hzle : z (n * τ) ≥ z t :=
            hanti ⟨le_rfl, hnτle⟩ htIcc (by linarith)
          linarith
  intro t ht
  obtain ⟨n, hn⟩ : ∃ n : ℕ, t < n * τ := by
    obtain ⟨n, hn⟩ := exists_nat_gt (t / τ)
    refine ⟨n, ?_⟩
    have h2 := mul_lt_mul_of_pos_right (show t / τ < (n : ℝ) from hn) hτ
    rw [div_mul_cancel₀ _ hτ.ne'] at h2
    exact h2
  have hzt : z t ≤ 0 := hz_nonpos n t ⟨ht, le_of_lt hn⟩
  rw [hzdef] at hzt
  have hexp : 0 < Real.exp (α * t) := Real.exp_pos _
  by_contra hcon
  have hcon' : 0 < w t := lt_of_not_ge hcon
  exact (not_lt_of_ge hzt) (mul_pos hcon' hexp)

/-! ### The quantitative Halanay estimate -/

/-- **The Halanay estimate.**  Let `w` satisfy `w' ≤ -c w + d w(· - τ)` with `c > 0`, `d ≥ 0`,
and let `ε > 0` be an *admissible rate*, i.e. `ε + d e^{ε τ} ≤ c`.  If `w ≤ M` on the history
`[-τ, 0]` with `M ≥ 0`, then `w t ≤ M e^{-ε t}` for all `t ≥ 0`.

The hypothesis `0 ≤ M` is necessary: for `M < 0` the estimate is false (the delayed term
*increases* the solution, because it is negative).  See `halanay_le_exp_max` for the statement
that is valid for an arbitrary bound `M`. -/
theorem halanay_le_exp {w w' : ℝ → ℝ} {c d ε τ M : ℝ}
    (hτ : 0 < τ) (hd : 0 ≤ d) (_hc : 0 < c) (hε : 0 < ε)
    (hcond : ε + d * Real.exp (ε * τ) ≤ c)
    (hw' : ∀ t ≥ 0, HasDerivAt w (w' t) t)
    (hbound : ∀ t ≥ 0, w' t ≤ -c * w t + d * w (t - τ))
    (hM0 : 0 ≤ M) (hM : ∀ t ∈ Set.Icc (-τ) 0, w t ≤ M) :
    ∀ t ≥ 0, w t ≤ M * Real.exp (-ε * t) := by
  have hmu : d * Real.exp (ε * τ) ≤ c - ε := by linarith [hcond]
  have hμ0 : 0 ≤ d * Real.exp (ε * τ) := mul_nonneg hd (Real.exp_nonneg _)
  have hexpderiv : ∀ t : ℝ, HasDerivAt (fun s => Real.exp (ε * s)) (ε * Real.exp (ε * t)) t := by
    intro t
    have h1 := (Real.hasDerivAt_exp (ε * t)).comp_of_eq t ((hasDerivAt_id t).const_mul ε) rfl
    convert h1 using 1
    · funext s; rfl
    · ring
  set z : ℝ → ℝ := fun t => w t * Real.exp (ε * t) with hzdef
  have hz_deriv : ∀ t ≥ 0, HasDerivAt z (Real.exp (ε * t) * (w' t + ε * w t)) t := by
    intro t ht
    have h1 := (hw' t ht).mul (hexpderiv t)
    convert h1 using 1 ; ring
  have hz_bound : ∀ t ≥ 0, Real.exp (ε * t) * (w' t + ε * w t)
      ≤ -(c - ε) * z t + (d * Real.exp (ε * τ)) * z (t - τ) := by
    intro t ht
    have h1 : w' t + ε * w t ≤ d * w (t - τ) - (c - ε) * w t := by linarith [hbound t ht]
    have hexp : 0 < Real.exp (ε * t) := Real.exp_pos _
    have h2 : Real.exp (ε * t) * (w' t + ε * w t)
        ≤ Real.exp (ε * t) * (d * w (t - τ) - (c - ε) * w t) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hexp)
    have hexp2 : Real.exp (ε * t) = Real.exp (ε * τ) * Real.exp (ε * (t - τ)) := by
      rw [show ε * t = ε * τ + ε * (t - τ) by ring, Real.exp_add]
    have h3 : Real.exp (ε * t) * (d * w (t - τ)) = (d * Real.exp (ε * τ)) * z (t - τ) := by
      show Real.exp (ε * t) * (d * w (t - τ))
        = (d * Real.exp (ε * τ)) * (w (t - τ) * Real.exp (ε * (t - τ)))
      rw [hexp2]
      ring
    have h4 : Real.exp (ε * t) * (d * w (t - τ) - (c - ε) * w t)
        = (d * Real.exp (ε * τ)) * z (t - τ) - (c - ε) * z t := by
      show Real.exp (ε * t) * (d * w (t - τ) - (c - ε) * w t)
        = (d * Real.exp (ε * τ)) * (w (t - τ) * Real.exp (ε * (t - τ)))
          - (c - ε) * (w t * Real.exp (ε * t))
      rw [hexp2]
      ring
    calc Real.exp (ε * t) * (w' t + ε * w t)
        ≤ Real.exp (ε * t) * (d * w (t - τ) - (c - ε) * w t) := h2
      _ = (d * Real.exp (ε * τ)) * z (t - τ) - (c - ε) * z t := h4
      _ = -(c - ε) * z t + (d * Real.exp (ε * τ)) * z (t - τ) := by ring
  set u : ℝ → ℝ := fun t => z t - M with hudef
  have hu_deriv : ∀ t ≥ 0, HasDerivAt u (Real.exp (ε * t) * (w' t + ε * w t)) t := by
    intro t ht
    have h1 := (hz_deriv t ht).sub (hasDerivAt_const t M)
    convert h1 using 1 ; ring
  have hu_bound : ∀ t ≥ 0, Real.exp (ε * t) * (w' t + ε * w t)
      ≤ -(c - ε) * u t + (d * Real.exp (ε * τ)) * u (t - τ) := by
    intro t ht
    have hb := hz_bound t ht
    have hzM : ∀ s : ℝ, z s = u s + M := by
      intro s
      rw [hudef, hzdef]
      ring
    rw [hzM, hzM] at hb
    have hconst : (d * Real.exp (ε * τ) - (c - ε)) * M ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hM0
    linarith
  have hu_init : ∀ t ∈ Set.Icc (-τ) 0, u t ≤ 0 := by
    intro t ht
    show w t * Real.exp (ε * t) - M ≤ 0
    have hze : Real.exp (ε * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hε.le ht.2)
    rcases le_total 0 (w t) with h | h
    · have h1 : w t * Real.exp (ε * t) ≤ M := by
        calc w t * Real.exp (ε * t) ≤ w t * 1 := mul_le_mul_of_nonneg_left hze h
          _ ≤ M := by simpa using hM t ht
      linarith
    · have h1 : w t * Real.exp (ε * t) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h (Real.exp_nonneg _)
      linarith
  have hnonpos := halanay_nonpos (w := u) (w' := fun t => Real.exp (ε * t) * (w' t + ε * w t))
    hτ hμ0 hu_deriv hu_bound hu_init
  intro t ht
  have hz1 : z t ≤ M := by
    have h1 := hnonpos t (by linarith)
    rw [hudef] at h1
    linarith
  have h1 : z t * Real.exp (-ε * t) ≤ M * Real.exp (-ε * t) :=
    mul_le_mul_of_nonneg_right hz1 (Real.exp_nonneg (-ε * t))
  have hzt : z t = w t * Real.exp (ε * t) := rfl
  rw [hzt] at h1
  have hexp2 : Real.exp (ε * t) * Real.exp (-ε * t) = 1 := by
    rw [← Real.exp_add, show ε * t + (-ε * t) = 0 by ring, Real.exp_zero]
  have h2 : w t * (Real.exp (ε * t) * Real.exp (-ε * t)) ≤ M * Real.exp (-ε * t) := by
    simpa only [mul_assoc] using h1
  rw [hexp2, mul_one] at h2
  exact h2

/-- **The Halanay estimate for an arbitrary bound `M` on the history.**  If `w ≤ M` on `[-τ, 0]`
then `w t ≤ max M 0 · e^{-ε t}` for `t ≥ 0`.  For `M ≥ 0` this is `halanay_le_exp`; for `M < 0`
the delay inequality forces `w ≤ 0` on the whole half line (`halanay_nonpos`). -/
theorem halanay_le_exp_max {w w' : ℝ → ℝ} {c d ε τ M : ℝ}
    (hτ : 0 < τ) (hd : 0 ≤ d) (_hc : 0 < c) (hε : 0 < ε)
    (hcond : ε + d * Real.exp (ε * τ) ≤ c)
    (hw' : ∀ t ≥ 0, HasDerivAt w (w' t) t)
    (hbound : ∀ t ≥ 0, w' t ≤ -c * w t + d * w (t - τ))
    (hM : ∀ t ∈ Set.Icc (-τ) 0, w t ≤ M) :
    ∀ t ≥ 0, w t ≤ max M 0 * Real.exp (-ε * t) := by
  by_cases hM0 : 0 ≤ M
  · have h := halanay_le_exp hτ hd _hc hε hcond hw' hbound hM0 hM
    intro t ht
    rw [max_eq_left hM0]
    exact h t ht
  · have hMneg : M ≤ 0 := le_of_not_ge hM0
    have hnonpos := halanay_nonpos hτ hd hw' hbound (fun t ht => le_trans (hM t ht) hMneg)
    intro t ht
    rw [max_eq_right hMneg]
    have h1 := hnonpos t (by linarith)
    linarith

/-! ### The square of a solution of the linear delay equation -/

/-- **The algebraic estimate behind the delay inequality for the square.**  For all real numbers
`b, u, v` one has `2 b u v ≤ |b| (u² + v²)`: this is the estimate `2 |u v| ≤ u² + v²` together
with `b u v ≤ |b| |u v|`. -/
theorem sq_cross_abs_le {b u v : ℝ} : 2 * b * u * v ≤ |b| * (u ^ 2 + v ^ 2) := by
  have h1 : 2 * |u| * |v| ≤ u ^ 2 + v ^ 2 := by
    have hsq : |u| ^ 2 = u ^ 2 := sq_abs u
    have hsq2 : |v| ^ 2 = v ^ 2 := sq_abs v
    have h : 0 ≤ (|u| - |v|) ^ 2 := sq_nonneg _
    nlinarith
  have h2 : b * (u * v) ≤ |b| * |u * v| := by
    calc b * (u * v) ≤ |b * (u * v)| := le_abs_self _
      _ = |b| * |u * v| := by rw [abs_mul]
  calc 2 * b * u * v = 2 * (b * (u * v)) := by ring
    _ ≤ 2 * (|b| * |u * v|) := mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = 2 * |u * v| * |b| := by ring
    _ ≤ (u ^ 2 + v ^ 2) * |b| := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left h1 (abs_nonneg b)
    _ = |b| * (u ^ 2 + v ^ 2) := by ring

/-- **The derivative of the square of a solution.**  If `ẋ = -a x + b x(· - τ)` then
`(x²)' = 2 x ẋ = -2 a x² + 2 b x x(· - τ)`. -/
theorem delayLinear_sq_deriv {a b τ : ℝ} {X : ℝ → ℝ}
    (hX : ∀ t, HasDerivAt X (-a * X t + b * X (t - τ)) t) (t : ℝ) :
    HasDerivAt (fun s => X s ^ 2) (2 * X t * (-a * X t + b * X (t - τ))) t := by
  have h1 := (hX t).pow 2
  convert h1 using 1
  norm_num

/-- **The delay inequality for the square of a solution.**  The square `u = x²` of a solution of
`ẋ = -a x + b x(· - τ)` satisfies the *scalar* delay inequality
`u' ≤ -(2a - |b|) u + |b| u(· - τ)`. -/
theorem delayLinear_sq_deriv_le {a b τ : ℝ} {X : ℝ → ℝ}
    (hX : ∀ t, HasDerivAt X (-a * X t + b * X (t - τ)) t) (t : ℝ) :
    HasDerivAt (fun s => X s ^ 2) (2 * X t * (-a * X t + b * X (t - τ))) t ∧
      2 * X t * (-a * X t + b * X (t - τ))
        ≤ -(2 * a - |b|) * (X t) ^ 2 + |b| * (X (t - τ)) ^ 2 := by
  refine ⟨delayLinear_sq_deriv hX t, ?_⟩
  have key := sq_cross_abs_le (b := b) (u := X t) (v := X (t - τ))
  nlinarith [key]

/-- **The delay inequality for the square of a solution, on the half line.**  This is the version
used by `delayLinear_semistability`, where the solution is only differentiable for `t ≥ 0`. -/
theorem delayLinear_sq_deriv_le_on {a b τ : ℝ} {X : ℝ → ℝ}
    (hX : ∀ t ≥ 0, HasDerivAt X (-a * X t + b * X (t - τ)) t) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (fun s => X s ^ 2) (2 * X t * (-a * X t + b * X (t - τ))) t ∧
      2 * X t * (-a * X t + b * X (t - τ))
        ≤ -(2 * a - |b|) * (X t) ^ 2 + |b| * (X (t - τ)) ^ 2 := by
  have h1 := (hX t ht).pow 2
  refine ⟨?_, ?_⟩
  · convert h1 using 1
    norm_num
  · have key := sq_cross_abs_le (b := b) (u := X t) (v := X (t - τ))
    nlinarith [key]

/-! ### The semistability of the linear delay equation -/

/-- **The semistability of the linear delay equation.**  Let `τ > 0` and `a > |b|`, let `φ` be a
continuous history and let `X` solve `ẋ(t) = -a x(t) + b x(t - τ)` on `[0, ∞)` with `X t = φ t`
for `t ≤ 0`.  Then `X t → 0` as `t → ∞`.

This is the classical Halanay argument: the square `u = x²` satisfies the scalar delay inequality
`u' ≤ -(2a - |b|) u + |b| u(· - τ)`, the admissible rate `ε` of `delayLinear_rate_exists`
turns it into the estimate `u t ≤ M e^{-ε t}` with `M` the supremum of `x²` on the history, and
hence `x t → 0`. -/
theorem delayLinear_semistability {a b τ : ℝ} (hτ : 0 < τ) (ha : |b| < a)
    {φ X : ℝ → ℝ} (hφ : Continuous φ)
    (hX : ∀ t ≥ 0, HasDerivAt X (-a * X t + b * X (t - τ)) t)
    (hhist : ∀ t ≤ 0, X t = φ t) :
    Tendsto X atTop (𝓝 0) := by
  have ha0 : 0 < a := by
    have : 0 ≤ |b| := abs_nonneg b
    linarith
  have hc : 0 < 2 * a - |b| := by
    have : 0 ≤ |b| := abs_nonneg b
    linarith
  obtain ⟨ε, hε, hcond⟩ := delayLinear_rate_exists hτ ha
  have hsq_deriv : ∀ t ≥ 0, HasDerivAt (fun s : ℝ => X s ^ 2)
      (2 * X t * (-a * X t + b * X (t - τ))) t := by
    intro t ht
    exact (delayLinear_sq_deriv_le_on hX t ht).1
  have hsq_bound : ∀ t ≥ 0, 2 * X t * (-a * X t + b * X (t - τ))
      ≤ -(2 * a - |b|) * (X t) ^ 2 + |b| * (X (t - τ)) ^ 2 := by
    intro t ht
    exact (delayLinear_sq_deriv_le_on hX t ht).2
  have hIcc : IsCompact (Set.Icc (-τ) 0) := isCompact_Icc
  have hφ2 : Continuous (fun t : ℝ => (φ t) ^ 2) := by
    exact hφ.pow 2
  obtain ⟨B, hB⟩ := hIcc.bddAbove_image (f := fun t : ℝ => (φ t) ^ 2) hφ2.continuousOn
  have hB0 : 0 ≤ B := by
    have h1 := hB (mem_image_of_mem _ (Set.left_mem_Icc.mpr (by linarith)))
    linarith [sq_nonneg (φ (-τ))]
  have hhistM : ∀ t ∈ Set.Icc (-τ) 0, (X t) ^ 2 ≤ B := by
    intro t ht
    have h1 : X t = φ t := hhist t ht.2
    have h2 : (X t) ^ 2 = (φ t) ^ 2 := by rw [h1]
    have h3 : (φ t) ^ 2 ≤ B := hB (mem_image_of_mem _ ht)
    rw [h2]
    exact h3
  have hest : ∀ t ≥ 0, (X t) ^ 2 ≤ B * Real.exp (-ε * t) := by
    have h := halanay_le_exp (w := fun t : ℝ => (X t) ^ 2)
      (w' := fun t : ℝ => 2 * X t * (-a * X t + b * X (t - τ)))
      hτ (abs_nonneg b) hc hε hcond hsq_deriv hsq_bound hB0 hhistM
    intro t ht
    exact h t ht
  have hexp0 : Tendsto (fun t : ℝ => Real.exp (-ε * t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => -ε * t) atTop atBot := by
      have h2 : Tendsto (fun t : ℝ => ε * (-t)) atTop atBot :=
        (tendsto_const_mul_atBot_of_pos hε).2 tendsto_neg_atTop_atBot
      convert h2 using 1
      funext t
      ring
    have h2 := Real.tendsto_exp_atBot.comp h1
    convert h2 using 1
    funext t
    rfl
  have hg : Tendsto (fun t : ℝ => B * Real.exp (-ε * t)) atTop (𝓝 0) := by
    have h1 := hexp0.const_mul B
    simpa using h1
  have hsq : Tendsto (fun t : ℝ => (X t) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun t : ℝ => B * Real.exp (-ε * t)) ?_ ?_ hg
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact sq_nonneg _
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hest t ht
  have habs : Tendsto (fun t : ℝ => |X t|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.sqrt ((X t) ^ 2)) atTop (𝓝 0) := by
      have h2 := (Real.continuous_sqrt.tendsto 0).comp hsq
      convert h2 using 1
      · funext t; rfl
      · simp
    simpa only [Real.sqrt_sq_eq_abs] using h1
  have hnegabs : Tendsto (fun t : ℝ => -|X t|) atTop (𝓝 0) := by
    simpa using habs.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hnegabs habs ?_ ?_
  · exact Filter.Eventually.of_forall (fun t => neg_abs_le _)
  · exact Filter.Eventually.of_forall (fun t => le_abs_self _)



/-! ### The hypothesis `0 ≤ M` of `halanay_le_exp` is necessary -/

/-- **The hypotheses of `halanay_le_exp` hold for the exponential `w t = -e^{-λ t}` with
`λ = log (3/2)`.**  Namely: `w` is differentiable on `[0, ∞)` with
`w' = λ e^{-λ t}`, it satisfies the delay inequality `w' ≤ -2 w + w(· - 1)` (this is the
admissibility `λ ≤ 2 - e^{λ} = 1/2` of the rate `λ`), and `w ≤ -1` on the history `[-1, 0]`. -/
theorem halanay_le_exp_negM_w :
    (∀ t ≥ 0, HasDerivAt (fun s : ℝ => -Real.exp (-Real.log (3/2) * s))
        (Real.log (3/2) * Real.exp (-Real.log (3/2) * t)) t) ∧
      (∀ t ≥ 0, Real.log (3/2) * Real.exp (-Real.log (3/2) * t)
        ≤ -2 * (-Real.exp (-Real.log (3/2) * t)) + (-Real.exp (-Real.log (3/2) * (t - 1)))) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 0, -Real.exp (-Real.log (3/2) * t) ≤ -1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    have h1 := (Real.hasDerivAt_exp (-Real.log (3/2) * t)).comp_of_eq t
      ((hasDerivAt_id t).const_mul (-Real.log (3/2))) rfl
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-Real.log (3/2) * s))
        (-Real.log (3/2) * Real.exp (-Real.log (3/2) * t)) t := by
      convert h1 using 1
      · funext s; rfl
      · ring
    have h3 := h2.neg
    convert h3 using 1
    ring
  · intro t ht
    have hexpL : Real.exp (Real.log (3/2)) = 3/2 := Real.exp_log (by norm_num)
    have hexp1 : Real.exp (-Real.log (3/2) * (t - 1))
        = Real.exp (-Real.log (3/2) * t) * Real.exp (Real.log (3/2)) := by
      rw [show -Real.log (3/2) * (t - 1) = -Real.log (3/2) * t + Real.log (3/2) by ring,
        Real.exp_add]
    rw [hexp1, hexpL]
    have hE : 0 < Real.exp (-Real.log (3/2) * t) := Real.exp_pos _
    have hlam : Real.log (3/2) ≤ 1/2 := by
      have h1 : (3/2 : ℝ) < Real.exp (1/2) := by
        have h := Real.add_one_lt_exp (by norm_num : (1/2 : ℝ) ≠ 0)
        linarith
      exact ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3/2)).2 h1).le
    have hmul : Real.log (3/2) * Real.exp (-Real.log (3/2) * t)
        ≤ (1/2) * Real.exp (-Real.log (3/2) * t) :=
      mul_le_mul_of_nonneg_right hlam hE.le
    nlinarith [hmul]
  · intro t ht
    have h1 : Real.exp (-Real.log (3/2) * t) ≥ 1 := by
      apply (Real.one_le_exp_iff).2
      have hlam0 : 0 < Real.log (3/2) := Real.log_pos (by norm_num)
      nlinarith [ht.2]
    linarith

/-- **The rate `ε = log (4/3)` is admissible for `c = 2`, `d = 1`, `τ = 1`.** -/
theorem halanay_le_exp_negM_rate :
    Real.log (4/3) + 1 * Real.exp (Real.log (4/3) * 1) ≤ (2 : ℝ) := by
  have h1 : Real.exp (Real.log (4/3) * 1) = 4/3 := by
    rw [mul_one, Real.exp_log (by norm_num : (0 : ℝ) < 4/3)]
  rw [h1]
  have h2 : Real.log (4/3) ≤ 2/3 := by
    have h3 : (4/3 : ℝ) < Real.exp (2/3) := by
      have h4 := Real.add_one_lt_exp (by norm_num : (2/3 : ℝ) ≠ 0)
      linarith
    exact ((Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 4/3)).2 h3).le
  linarith

/-- **The conclusion of `halanay_le_exp` fails for the example of `halanay_le_exp_negM_w`.**
At `t = 1` one has `w 1 = -2/3`, while the claimed bound is `M e^{-ε} = -3/4`. -/
theorem halanay_le_exp_negM_fails :
    ¬ (-Real.exp (-Real.log (3/2) * 1) ≤ (-1 : ℝ) * Real.exp (-Real.log (4/3) * 1)) := by
  intro h
  have h1 : Real.exp (-Real.log (3/2) * 1) = 2/3 := by
    rw [mul_one, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3/2)]
    norm_num
  have h2 : Real.exp (-Real.log (4/3) * 1) = 3/4 := by
    rw [mul_one, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4/3)]
    norm_num
  rw [h1, h2] at h
  norm_num at h

/-! ### Axioms of the principal results -/

#print axioms halanay_nonpos
#print axioms halanay_le_exp
#print axioms halanay_le_exp_max
#print axioms delayLinear_sq_deriv
#print axioms delayLinear_sq_deriv_le
#print axioms delayLinear_sq_deriv_le_on
#print axioms delayLinear_semistability
#print axioms halanay_le_exp_negM_w
#print axioms halanay_le_exp_negM_rate
#print axioms halanay_le_exp_negM_fails

end Dynamics
end CRNT
