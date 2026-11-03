import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Grönwall's inequality, the exponential comparison principle, and the maximum principle

This module collects the three analytic tools that the delay theory of the campaign needs.

## The classical Grönwall inequality

Grönwall's inequality (Grönwall 1919; Coddington & Levinson, *Theory of Ordinary Differential
Equations*, Ch. III; Hale, *Ordinary Differential Equations*, Ch. 1) states that a solution of the
differential inequality

`f' t ≤ c * f t + d`   for `t ≥ t₀`

is bounded by

`f t ≤ exp (c * (t - t₀)) * f t₀ + d * (exp (c * (t - t₀)) - 1) / c`   (for `c ≠ 0`)

`f t ≤ f t₀ + d * (t - t₀)`                                              (for `c = 0`).

**Mathlib already provides this inequality.**  `Mathlib.Analysis.ODE.Gronwall` contains the
function `gronwallBound δ K ε x` and the theorem
`le_gronwallBound_of_liminf_deriv_right_le`, which bounds `f x` on `[a, b]` by
`gronwallBound δ K ε (x - a)` under the differential inequality `f' x ≤ K * f x + ε`
(with `f a ≤ δ`).  Mathlib's version is the "fundamental inequality" of Hubbard and West,
*Differential Equations: A Dynamical Systems Approach*, Sec. 4.5.  We therefore **reuse**
Mathlib's Grönwall instead of duplicating it: `gronwall_ineq` below is Mathlib's theorem applied
with `δ = f t₀`, and `gronwall_ineq_explicit` / `gronwall_ineq_of_c_zero` merely rewrite
`gronwallBound` in the classical closed form.

## The comparison principle

Mathlib has no standalone *comparison* theorem: its Grönwall inequality contains the comparison
inequality only as the special case `ε = 0`, and only in the `gronwallBound` notation.  The
comparison principle is therefore proved here from scratch by the exponential-comparison argument:
for `f' t ≤ c * f t` the auxiliary function `g t = exp (-(c * (t - t₀))) * f t` satisfies
`g' t = exp (-(c * (t - t₀))) * (f' t - c * f t) ≤ 0`, hence `g` is non-increasing on the
interval, `g t ≤ g t₀ = f t₀`, and dividing by the positive factor `exp (-(c * (t - t₀)))` gives
`f t ≤ exp (c * (t - t₀)) * f t₀` (`gronwall_exp_comparison`, `gronwall_exp_comparison_of_ge`).

This is the `t₀ = 0` generalisation of `CRNT.ExponentialDecay.le_mul_exp_of_deriv_le`, which
sits in the Lyapunov-function argument for exponential decay on the stable subspace; here the base
time is arbitrary, which is what the delay theory needs.

## The maximum principle

The form used by the delay theory is the following ("maximum principle", the first step of the
usual proof of the Halanay estimate for delay equations): if `f' t ≥ k * f t` on `[a, b]` with
`k ≥ 0` and `f a ≥ 0`, then `f t ≥ 0` on `[a, b]`.  It is proved here by the same
exponential-comparison argument with the sign reversed: `g t = exp (-(k * (t - a))) * f t` has
`g' t = exp (-(k * (t - a))) * (f' t - k * f t) ≥ 0`, so `g` is non-decreasing, `g t ≥ g a = f a ≥ 0`,
and division by the positive factor `exp (-(k * (t - a)))` gives `f t ≥ 0`
(`gronwall_max_principle`).  The proof does not actually use the sign of `k`; the hypothesis
`0 ≤ k` is kept because it is the case needed downstream.  Its argument order is
`(hk) (hderiv) (hbound) (ha)`.

The Halanay estimate itself and the semistability of the linear delay equation are proved
separately in the campaign, in `CRNT.Dynamics.DelayHalanay`; this module only supplies the
analytic building blocks used there.

## Scope

All statements are about real-valued functions of one real variable on a compact time interval
(or on a half-line, through the `_of_ge` variants).  No measurability or integrability
assumptions are needed: differentiability on the interval suffices, the derivative bounds being
pointwise.

## What remains open

Nothing in this module is CRN-specific: it is pure real analysis and it is used verbatim by the
delay theory.  The Halanay estimate `x' t ≤ -a * x t + b * x (t - τ)` and the semistability of
the linear delay equation are *not* proved here; they are proved separately in the campaign (in
`CRNT.Dynamics.DelayHalanay`), on top of the three tools collected above.
-/

namespace CRNT.Dynamics

open Filter Set

/-! ### Auxiliary derivative computations -/

/-- The derivative of the affine function `s ↦ -(c * (s - t₀))` is `-c`. -/
private lemma hasDerivAt_neg_sub_const_mul (c t₀ t : ℝ) :
    HasDerivAt (fun s => -(c * (s - t₀))) (-c) t := by
  have h1 : HasDerivAt (fun s : ℝ => s - t₀) 1 t := (hasDerivAt_id' t).sub_const t₀
  have h2 : HasDerivAt (fun s : ℝ => (-c) * (s - t₀)) (-c) t := by
    simpa only [mul_one] using h1.const_mul (-c)
  have h3 : HasDerivAt (fun s => -(c * (s - t₀))) (-c) t := by
    convert h2 using 1
    funext s
    ring
  exact h3

/-- The derivative of `s ↦ exp (-(c * (s - t₀)))` is `exp (-(c * (t - t₀))) * (-c)`. -/
private lemma hasDerivAt_exp_neg_sub_const_mul (c t₀ t : ℝ) :
    HasDerivAt (fun s => Real.exp (-(c * (s - t₀)))) (Real.exp (-(c * (t - t₀))) * (-c)) t :=
  (hasDerivAt_neg_sub_const_mul c t₀ t).exp

/-! ### The comparison principle -/

/-- **Exponential comparison.**  Let `f : ℝ → ℝ` be differentiable on `[t₀, b]`, with derivative
`f'`, and suppose `f' t ≤ c * f t` there.  Then

`f t ≤ exp (c * (t - t₀)) * f t₀`   for every `t ∈ [t₀, b]`.

This is the classical comparison principle behind Grönwall's inequality.  No sign assumption on
`f` is needed: the auxiliary function `g t = exp (-(c * (t - t₀))) * f t` satisfies
`g' t = exp (-(c * (t - t₀))) * (f' t - c * f t) ≤ 0`, so `g` is non-increasing, whence
`g t ≤ g t₀ = f t₀`, and division by the positive number `exp (-(c * (t - t₀)))` yields the claim.

(As a by-product this is Mathlib's Grönwall inequality with `ε = 0` and `δ = f t₀`; it is proved
here directly because the delay theory needs the closed form `exp (c * (t - t₀)) * f t₀` rather
than the `gronwallBound` notation.) -/
theorem gronwall_exp_comparison {f f' : ℝ → ℝ} {c t₀ b : ℝ}
    (hderiv : ∀ t ∈ Set.Icc t₀ b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Icc t₀ b, f' t ≤ c * f t) :
    ∀ t ∈ Set.Icc t₀ b, f t ≤ Real.exp (c * (t - t₀)) * f t₀ := by
  have hg : ∀ t ∈ Set.Icc t₀ b,
      HasDerivAt (fun s => Real.exp (-(c * (s - t₀))) * f s)
        (Real.exp (-(c * (t - t₀))) * (f' t - c * f t)) t := by
    intro t ht
    have h := (hasDerivAt_exp_neg_sub_const_mul c t₀ t).mul (hderiv t ht)
    convert h using 1
    ring
  have hcont : ContinuousOn (fun s => Real.exp (-(c * (s - t₀))) * f s) (Set.Icc t₀ b) := by
    intro t ht
    exact ((hasDerivAt_exp_neg_sub_const_mul c t₀ t).continuousAt.mul
      (hderiv t ht).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => Real.exp (-(c * (s - t₀))) * f s)
      (interior (Set.Icc t₀ b)) := by
    intro t ht
    exact (hg t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ t ∈ interior (Set.Icc t₀ b),
      deriv (fun s => Real.exp (-(c * (s - t₀))) * f s) t ≤ 0 := by
    intro t ht
    rw [(hg t (interior_subset ht)).deriv]
    have h1 : f' t - c * f t ≤ 0 := sub_nonpos.mpr (hbound t (interior_subset ht))
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (Real.exp_pos _)) h1
  have hanti : AntitoneOn (fun s => Real.exp (-(c * (s - t₀))) * f s) (Set.Icc t₀ b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc t₀ b) hcont hdiff hnonpos
  intro t ht
  have hgt : Real.exp (-(c * (t - t₀))) * f t ≤ f t₀ := by
    have h1 := hanti (Set.left_mem_Icc.mpr (ht.1.trans ht.2)) ht ht.1
    simpa only [sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul] using h1
  have hexp : 0 < Real.exp (-(c * (t - t₀))) := Real.exp_pos _
  have hdiv : f t ≤ f t₀ / Real.exp (-(c * (t - t₀))) :=
    (le_div_iff₀ hexp).2 (by simpa [mul_comm] using hgt)
  have hdiv' : f t₀ / Real.exp (-(c * (t - t₀))) = f t₀ * Real.exp (c * (t - t₀)) := by
    rw [div_eq_mul_inv, Real.exp_neg, inv_inv]
  rw [hdiv'] at hdiv
  simpa [mul_comm] using hdiv

/-- **Exponential comparison on a half-line.**  If `f : ℝ → ℝ` is differentiable on `[t₀, ∞)` and
`f' t ≤ c * f t` for `t ≥ t₀`, then `f t ≤ exp (c * (t - t₀)) * f t₀` for `t ≥ t₀`. -/
theorem gronwall_exp_comparison_of_ge {f f' : ℝ → ℝ} {c t₀ : ℝ}
    (hderiv : ∀ t, t₀ ≤ t → HasDerivAt f (f' t) t)
    (hbound : ∀ t, t₀ ≤ t → f' t ≤ c * f t) :
    ∀ t, t₀ ≤ t → f t ≤ Real.exp (c * (t - t₀)) * f t₀ := by
  intro t ht
  exact gronwall_exp_comparison (fun s hs => hderiv s hs.1) (fun s hs => hbound s hs.1) t ⟨ht, le_rfl⟩

/-! ### The maximum principle -/

/-- **Maximum principle.**  Let `f : ℝ → ℝ` be differentiable on `[a, b]`, with derivative `f'`, let
`k ≥ 0`, and suppose `f' t ≥ k * f t` on `[a, b]` with `f a ≥ 0`.  Then `f t ≥ 0` on `[a, b]`.

This is the form of the maximum principle used in the proof of the Halanay estimate for delay
equations: the auxiliary function `g t = exp (-(k * (t - a))) * f t` satisfies
`g' t = exp (-(k * (t - a))) * (f' t - k * f t) ≥ 0`, so `g` is non-decreasing, whence
`g t ≥ g a = f a ≥ 0`, and division by the positive number `exp (-(k * (t - a)))` yields `f t ≥ 0`.

The sign of `k` is not used in the proof; the hypothesis `0 ≤ k` is the case needed by the delay
theory. -/
theorem gronwall_max_principle {f f' : ℝ → ℝ} {k a b : ℝ} (_hk : 0 ≤ k)
    (hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Icc a b, k * f t ≤ f' t)
    (ha : 0 ≤ f a) :
    ∀ t ∈ Set.Icc a b, 0 ≤ f t := by
  have hg : ∀ t ∈ Set.Icc a b,
      HasDerivAt (fun s => Real.exp (-(k * (s - a))) * f s)
        (Real.exp (-(k * (t - a))) * (f' t - k * f t)) t := by
    intro t ht
    have h := (hasDerivAt_exp_neg_sub_const_mul k a t).mul (hderiv t ht)
    convert h using 1
    ring
  have hcont : ContinuousOn (fun s => Real.exp (-(k * (s - a))) * f s) (Set.Icc a b) := by
    intro t ht
    exact ((hasDerivAt_exp_neg_sub_const_mul k a t).continuousAt.mul
      (hderiv t ht).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun s => Real.exp (-(k * (s - a))) * f s)
      (interior (Set.Icc a b)) := by
    intro t ht
    exact (hg t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ t ∈ interior (Set.Icc a b),
      deriv (fun s => Real.exp (-(k * (s - a))) * f s) t ≥ 0 := by
    intro t ht
    rw [(hg t (interior_subset ht)).deriv]
    have h1 : 0 ≤ f' t - k * f t := sub_nonneg.mpr (hbound t (interior_subset ht))
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) h1
  have hmono : MonotoneOn (fun s => Real.exp (-(k * (s - a))) * f s) (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff hnonneg
  intro t ht
  have hga : 0 ≤ Real.exp (-(k * (t - a))) * f t := by
    have h1 := hmono (Set.left_mem_Icc.mpr (ht.1.trans ht.2)) ht ht.1
    have h1' : f a ≤ Real.exp (-(k * (t - a))) * f t := by
      simpa only [sub_self, mul_zero, neg_zero, Real.exp_zero, one_mul] using h1
    exact le_trans ha h1'
  have hexp : 0 < Real.exp (-(k * (t - a))) := Real.exp_pos _
  refine le_of_mul_le_mul_right ?_ hexp
  have h2 : f t * Real.exp (-(k * (t - a))) ≥ 0 := by simpa [mul_comm] using hga
  simpa using h2

/-! ### Grönwall's inequality (Mathlib's, in the classical closed form) -/

/-- **Grönwall's inequality.**  Let `f : ℝ → ℝ` be differentiable on `[t₀, b]`, with derivative
`f'`, and suppose `f' t ≤ c * f t + d` on `[t₀, b]`.  Then

`f t ≤ gronwallBound (f t₀) c d (t - t₀)`   for every `t ∈ [t₀, b]`,

that is, `f t ≤ exp (c * (t - t₀)) * f t₀ + d * (exp (c * (t - t₀)) - 1) / c` when `c ≠ 0` and
`f t ≤ f t₀ + d * (t - t₀)` when `c = 0`.

This is Mathlib's Grönwall inequality `le_gronwallBound_of_liminf_deriv_right_le`
(`Mathlib.Analysis.ODE.Gronwall`) applied with `δ = f t₀`, re-exported in the closed form used
by the delay theory; see `gronwall_ineq_explicit` and `gronwall_ineq_of_c_zero`. -/
theorem gronwall_ineq {f f' : ℝ → ℝ} {c d t₀ b : ℝ}
    (hderiv : ∀ t ∈ Set.Icc t₀ b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Icc t₀ b, f' t ≤ c * f t + d) :
    ∀ t ∈ Set.Icc t₀ b, f t ≤ gronwallBound (f t₀) c d (t - t₀) := by
  intro t ht
  refine le_gronwallBound_of_liminf_deriv_right_le (f := f) (f' := f') (δ := f t₀) (K := c)
    (ε := d) (a := t₀) (b := b) ?_ ?_ le_rfl ?_ t ht
  · intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  · intro x hx r hr
    have hwd : HasDerivWithinAt f (f' x) (Ici x) x :=
      (hderiv x (Set.Ico_subset_Icc_self hx)).hasDerivWithinAt
    have hslope := hwd.liminf_right_slope_le hr
    refine hslope.mono fun z hz => ?_
    simpa only [slope, smul_eq_mul, vsub_eq_sub] using hz
  · intro x hx
    exact hbound x (Set.Ico_subset_Icc_self hx)

/-- **Grönwall's inequality in closed form, `c ≠ 0`.**  Under the hypotheses of `gronwall_ineq`
and the additional assumption `c ≠ 0`,

`f t ≤ exp (c * (t - t₀)) * f t₀ + d * (exp (c * (t - t₀)) - 1) / c`   for `t ∈ [t₀, b]`. -/
theorem gronwall_ineq_explicit {f f' : ℝ → ℝ} {c d t₀ b : ℝ} (hc : c ≠ 0)
    (hderiv : ∀ t ∈ Set.Icc t₀ b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Icc t₀ b, f' t ≤ c * f t + d) :
    ∀ t ∈ Set.Icc t₀ b,
      f t ≤ Real.exp (c * (t - t₀)) * f t₀ + d * (Real.exp (c * (t - t₀)) - 1) / c := by
  intro t ht
  have h := gronwall_ineq hderiv hbound t ht
  rw [gronwallBound_of_K_ne_0 hc] at h
  have heq : (fun x => f t₀ * Real.exp (c * x) + d / c * (Real.exp (c * x) - 1)) (t - t₀)
      = Real.exp (c * (t - t₀)) * f t₀ + d * (Real.exp (c * (t - t₀)) - 1) / c := by
    ring
  rw [heq] at h
  exact h

/-- **Grönwall's inequality in closed form, `c = 0`.**  If `f` is differentiable on `[t₀, b]` with
`f' t ≤ d` there, then `f t ≤ f t₀ + d * (t - t₀)` for `t ∈ [t₀, b]`. -/
theorem gronwall_ineq_of_c_zero {f f' : ℝ → ℝ} {d t₀ b : ℝ}
    (hderiv : ∀ t ∈ Set.Icc t₀ b, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Icc t₀ b, f' t ≤ d) :
    ∀ t ∈ Set.Icc t₀ b, f t ≤ f t₀ + d * (t - t₀) := by
  intro t ht
  have h := gronwall_ineq (c := 0) hderiv (fun t ht => by simpa using hbound t ht) t ht
  rw [gronwallBound_K0] at h
  simpa using h

/-- **Grönwall's inequality on a half-line.**  If `f : ℝ → ℝ` is differentiable on `[t₀, ∞)` and
`f' t ≤ c * f t + d` for `t ≥ t₀`, then `f t ≤ gronwallBound (f t₀) c d (t - t₀)` for `t ≥ t₀`. -/
theorem gronwall_ineq_of_ge {f f' : ℝ → ℝ} {c d t₀ : ℝ}
    (hderiv : ∀ t, t₀ ≤ t → HasDerivAt f (f' t) t)
    (hbound : ∀ t, t₀ ≤ t → f' t ≤ c * f t + d) :
    ∀ t, t₀ ≤ t → f t ≤ gronwallBound (f t₀) c d (t - t₀) := by
  intro t ht
  exact gronwall_ineq (fun s hs => hderiv s hs.1) (fun s hs => hbound s hs.1) t ⟨ht, le_rfl⟩

/-! ### Axiom audit (informational) -/

#print axioms gronwall_exp_comparison
#print axioms gronwall_exp_comparison_of_ge
#print axioms gronwall_max_principle
#print axioms gronwall_ineq
#print axioms gronwall_ineq_explicit
#print axioms gronwall_ineq_of_c_zero
#print axioms gronwall_ineq_of_ge

end CRNT.Dynamics
